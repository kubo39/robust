module robust;

import std.math : abs;
import std.typecons : tuple;


nothrow:
@nogc:
pure:
@safe:

///
struct Coord
{
    double x;
    double y;
}


// These values are precomputed from the "exactinit" method of the c-source code.
private enum double SPLITTER = 134_217_729;
private enum double EPSILON = double.epsilon / 2;  // from https://github.com/danshapero/predicates/commit/2a1ced5f61842190d255cb674769f3f9fadcbb25
private enum double RESULTERRBOUND = (3.0 + 8.0 * EPSILON) * EPSILON;
private enum double CCWERRBOUND_A = (3.0 + 16.0 * EPSILON) * EPSILON;
private enum double CCWERRBOUND_B = (2.0 + 12.0 * EPSILON) * EPSILON;
private enum double CCWERRBOUND_C = (9.0 + 64.0 * EPSILON) * EPSILON * EPSILON;
private enum double ICCERRBOUND_A = (10.0 + 96.0 * EPSILON) * EPSILON;
private enum double ICCERRBOUND_B = (4.0 + 48.0 * EPSILON) * EPSILON;
private enum double ICCERRBOUND_C = (44.0 + 576.0 * EPSILON) * EPSILON * EPSILON;


/// Returns a positive value if the coordinates `pa`, `pb`, and `pc` occur in counterclockwise order
/// (pc lies to the **left** of the directed line defined by coordinates pa and pb).
/// Returns a negative value if they occur in clockwise order (`pc` lies to the **right** of the directed line `pa, pb`).
/// Returns `0` if they are **collinear**.
double orient2d(Coord pa, Coord pb, Coord pc)
{
    const detleft = (pa.x - pc.x) * (pb.y - pc.y);
    const detright = (pa.y - pc.y) * (pb.x - pc.x);
    const det = detleft - detright;

    double detsum;
    if (detleft > 0.0)
    {
        if (detright <= 0.0)
        {
            return det;
        }
        else
        {
            detsum = detleft + detright;
        }
    }
    else if (detleft < 0.0)
    {
        if (detright >= 0.0)
        {
            return det;
        }
        else
        {
            detsum = -detleft - detright;
        }
    }
    else // detleft == 0.0
    {
        return det;
    }
    const errbound = CCWERRBOUND_A + detsum;
    if (det >= errbound || -det >= errbound)
    {
        return det;
    }
    else
    {
        return orient2dadapt(pa, pb, pc, detsum);
    }
}

private:

///
double orient2dadapt(Coord pa, Coord pb, Coord pc, double detsum)
{
    const acx = pa.x - pc.x;
    const bcx = pb.x - pc.x;
    const acy = pa.y - pc.y;
    const bcy = pb.y - pc.y;

    const detleft = twoProduct(acx, bcy);
    const detright = twoProduct(acy, bcx);

    const bt = twoTwoDiff(detleft.expand, detright.expand);
    const double[4] B = [bt[3], bt[2], bt[1], bt[0]];

    auto det = estimate(B);
    const errbound_b = CCWERRBOUND_B * detsum;
    if (det >= errbound_b || -det >= errbound_b)
        return det;

    const acxtail = twoDiffTail(pa.x, pc.x, acx);
    const bcxtail = twoDiffTail(pb.x, pc.x, bcx);
    const acytail = twoDiffTail(pa.y, pc.y, acy);
    const bcytail = twoDiffTail(pb.y, pc.y, bcy);

    if (acxtail == 0.0 && acytail == 0.0 && bcxtail == 0.0 && bcytail == 0.0)
        return det;

    const errbound_c = CCWERRBOUND_C * detsum + RESULTERRBOUND + abs(det);
    det += (acx * bcytail + bcy * acxtail) - (acy * bcxtail + bcx * acytail);

    if (det >= errbound_c || -det >= errbound_c)
        return det;

    const s1 = twoProduct(acxtail, bcy);
    const t1 = twoProduct(acytail, bcx);
    const u1 = twoTwoDiff(s1.expand, t1.expand);
    const double[4] U1 = [u1[3], u1[2], u1[1], u1[0]];

    double[8] C1 = [0.0, 0.0, 0.0, 0.0,
                    0.0, 0.0, 0.0, 0.0];
    const c1length = fastExpansionSumZeroelim(B, U1, C1[]);

    const s2 = twoProduct(acx, bcytail);
    const t2 = twoProduct(acy, bcxtail);
    const u2 = twoTwoDiff(s2.expand, t2.expand);
    const double[4] U2 = [u2[3], u2[2], u2[1], u2[0]];

    double[12] C2 = [0.0, 0.0, 0.0, 0.0,
                     0.0, 0.0, 0.0, 0.0,
                     0.0, 0.0, 0.0, 0.0];
    const c2length = fastExpansionSumZeroelim(C1[0..c1length], U2, C2[]);

    const s3 = twoProduct(acxtail, bcytail);
    const t3 = twoProduct(acytail, bcxtail);
    const u3 = twoTwoDiff(s3.expand, t3.expand);
    const double[4] U3 = [u3[3], u3[2], u3[1], u3[0]];
    double[16] D = [0.0, 0.0, 0.0, 0.0,
                    0.0, 0.0, 0.0, 0.0,
                    0.0, 0.0, 0.0, 0.0,
                    0.0, 0.0, 0.0, 0.0];
    const dlength = fastExpansionSumZeroelim(C2[0..c2length], U3, D[]);
    return D[dlength - 1];
}

///
auto twoProduct(double a, double b)
{
    const x = a * b;
    return tuple(x, twoProductTail(a, b, x));
}

///
double twoProductTail(double a, double b, double x)
{
    const splitA = split(a);
    const splitB = split(b);
    const err1 = x - (splitA[0] * splitB[0]);
    const err2 = err1 - (splitA[1] * splitB[0]);
    const err3 = err2 - (splitA[0] * splitB[1]);
    return splitA[1] * splitB[1] - err3;
}

///
auto split(double a)
{
    const c = SPLITTER * a;
    const abig = c - a;
    const ahi = c - abig;
    const alo = a - ahi;
    return tuple(ahi, alo);
}

///
auto twoTwoDiff(double a1, double a0, double b1, double b0)
{
    const t1 = twoOneDiff(a1, a0, b0);
    const t2 = twoOneDiff(t1[0], t1[1], b1);
    return tuple(t2.expand, t1[2]);
}

///
auto twoOneDiff(double a1, double a0, double b)
{
    const t1 = twoDiff(a0, b);
    const t2 = twoSum(a1, t1[0]);
    return tuple(t2[0], t2[1], t1[1]);
}

///
auto twoDiff(double a, double b)
{
    const x = a - b;
    return tuple(x, twoDiffTail(a, b, x));
}

///
double twoDiffTail(double a, double b, double x)
{
    const bvirt = a - x;
    const avirt = x + bvirt;
    const bround = bvirt - b;
    const around = a - avirt;
    return around + bround;
}

///
auto twoSum(double a, double b)
{
    const x = a + b;
    return tuple(x, twoSumTail(a, b, x));
}

///
double twoSumTail(double a, double b, double x)
{
    const bvirt = x - a;
    const avirt = x - bvirt;
    const bround = b - bvirt;
    const around = a - avirt;
    return around + bround;
}

///
double estimate(const(double[]) e)
{
    auto q = cast() e[0];
    foreach (cur; e[1..$])
    {
        q += cur;
    }
    return q;
}

///
size_t fastExpansionSumZeroelim(const(double[]) e, const(double[]) f, double[] h)
{
    auto enow = cast() e[0];
    auto fnow = cast() f[0];
    size_t eindex = 0;
    size_t findex = 0;
    double Qnew;
    double hh;
    double Q;
    if ((fnow > enow) == (fnow > -enow))
    {
        Q = enow;
        eindex++;
    }
    else
    {
        Q = fnow;
        findex++;
    }

    size_t hindex;
    if (eindex < e.length && findex < f.length)
    {
        enow = e[eindex];
        fnow = f[findex];
        if ((fnow > enow) == (fnow > -enow))
        {
            const r = fastTwoSum(enow, Q);
            Qnew = r[0];
            hh = r[1];
            eindex++;
        }
        else
        {
            const r = fastTwoSum(fnow, Q);
            Qnew = r[0];
            hh = r[1];
            findex++;
        }
        Q = Qnew;
        if (hh != 0.0)
        {
            h[hindex] = hh;
            hindex++;
        }

        while ((eindex < e.length) && (findex < f.length))
        {
            enow = e[eindex];
            fnow = f[findex];
            if ((fnow > enow) == (fnow > -enow))
            {
                const r = twoSum(Q, enow);
                Qnew = r[0];
                hh = r[1];
                eindex++;
            }
            else
            {
                const r = twoSum(Q, fnow);
                Qnew = r[0];
                hh = r[1];
                findex++;
            }
            Q = Qnew;
            if (hh != 0.0)
            {
                h[hindex] = hh;
                hindex++;
            }
        }
    }

    while (eindex < e.length)
    {
        enow = e[eindex];
        const r = twoSum(Q, enow);
        Qnew = r[0];
        hh = r[1];
        Q = Qnew;
        eindex++;
        if (hh != 0.0)
        {
            h[hindex] = hh;
            hindex++;
        }
    }

    while (findex < f.length)
    {
        fnow = f[findex];
        const r = twoSum(Q, fnow);
        Qnew = r[0];
        hh = r[1];
        Q = Qnew;
        findex++;
        if (hh != 0.0)
        {
            h[hindex] = hh;
            hindex++;
        }
    }

    if (Q != 0.0 || hindex == 0)
    {
        h[hindex] = Q;
        hindex++;
    }
    return hindex;
}

///
auto fastTwoSum(double a, double b)
{
    const x = a + b;
    return tuple(x, fastTwoSumTail(a, b, x));
}

///
double fastTwoSumTail(double a, double b, double x)
{
    const bvirt = x - a;
    return b - bvirt;
}


unittest
{
    import std.math : sgn;

    const Coord from = { x: -1.0, y: -1.0 };
    const Coord to = { x: 1.0, y: 1.0 };
    const Coord p1 = { x: double.min_normal, y: double.min_normal };
    const Coord p2 = { x: -double.min_normal, y: -double.min_normal };
    const Coord p3 = { x: -double.min_normal, y: double.min_normal };
    const Coord p4 = { x: double.min_normal, y: -double.min_normal };
    foreach (tup; [tuple(p1, 0.0), tuple(p2, 0.0), tuple(p3, 1.0), tuple(p4, -1.0)])
    {
        const det = orient2d(from, to, tup[0]);
        assert(det == tup[1] || det.sgn == tup[1].sgn);
    }
}
