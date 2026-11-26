"""Reduced Corollary 4.16 and exact signs, using only standard-library arithmetic."""
from collections import defaultdict
from fractions import Fraction
from functools import cache
from math import comb, prod


def canonical(parts):
    return tuple(sorted(parts, reverse=True))


def add_terms(out, poly, factor, dx=0, du=0):
    for (i, j), value in poly.items():
        out[i + dx,j + du] += factor * value


@cache
def reduced(h, mu):
    """Coefficients of R(x,1+u) with h=2g and positive ordered parts."""
    if h < 0:
        return {}
    if h == 0 and mu == (1,):
        return {(0,0): Fraction(1)}
    a, tail = mu[0], mu[1:]
    out = defaultdict(Fraction)
    for i, m in enumerate(tail):
        add_terms(out, reduced(h, canonical((a+m,) + tail[:i] + tail[i+1:])), a+m)
    for u in range(1, a):
        v = a-u
        add_terms(out, reduced(h-2, canonical((u,v) + tail)), u*v)
        for mask in range(1 << len(tail)):
            left = canonical((u,) + tuple(m for i,m in enumerate(tail) if (mask>>i)&1))
            right = canonical((v,) + tuple(m for i,m in enumerate(tail) if not (mask>>i)&1))
            for k in range(h+1):
                for (i,j), value in reduced(k, left).items():
                    add_terms(out, reduced(h-k, right), u*v*value,
                              i + (k % 2) * ((h-k) % 2), j)
    if a > 1:
        add_terms(out, reduced(h-1, mu), a*(a-1), dx=int(h % 2 == 0))
        add_terms(out, reduced(h, canonical((a-1,) + tail)), a-1, du=1)
    return {k: v/a for k,v in out.items() if v}


def table(mu):
    out = [[Fraction()]*3 for _ in range(sum(mu))]
    for (i,j), value in reduced(4, mu).items():
        for l in range(j+1):
            out[l][i] += prod(mu)*value*comb(j,l)*(-1)**(j-l)
    assert all(v.denominator == 1 for row in out for v in row)
    return [[v.numerator for v in row] for row in out]


def add(a,b):
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(max(len(a),len(b)))]


def scale(a,n):
    return [n*v for v in a]


def mul(a,b):
    out = [0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            out[i+j] += u*v
    return out


def at_minus_four_minus_s(a):
    return [sum(a[j]*comb(j,i)*(-4)**(j-i)*(-1)**i for j in range(i,len(a)))
            for i in range(len(a))]


def main():
    import argparse
    import json
    from pathlib import Path

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-pairs", type=Path)
    args = parser.parse_args()
    p, q = table((3,2)), table((4,2))
    assert p[0] == q[0] == [0,0,0] and p[1:] == p[:0:-1] and q[1:] == q[:0:-1]
    a, b = p[1], add(p[2],scale(p[1],-1))
    c, d, e = q[1], q[2], add(q[3],scale(q[1],-2))
    print('A,B,C,D,E:', a,b,c,d,e)
    signs = {'A': a, 'C': c, 'B-2A': add(b,scale(a,-2)),
             'f(-2)': add(add(scale(c,4), scale(d,-2)),e),
             '-A^2*f(-B/A)': add(add(mul(mul(a,b),d),scale(mul(mul(b,b),c),-1)),
                                   scale(mul(mul(a,a),e),-1))}
    for name, poly in signs.items():
        shifted = at_minus_four_minus_s(poly)
        assert min(poly) > 0 and min(shifted) > 0
        print(name, poly, shifted)
    if args.compare_pairs:
        counts = json.loads(args.compare_pairs.read_text())
        compared = 0
        for parts, rows in [((3, 2), p), ((4, 2), q)]:
            actual = counts[str(parts)]
            assert len(actual) == len(rows)
            for row, expected in zip(rows, actual):
                recovered = [0] * len(expected)
                for i, coefficient in enumerate(row):
                    for j in range(4 - i):
                        recovered[2*i+j] += comb(3-i, j)*coefficient
                assert recovered == expected, (parts, recovered, expected)
                compared += len(expected)
        print(f"Matched all {compared} coefficients of t^hive b^flip.")


if __name__ == '__main__':
    main()
