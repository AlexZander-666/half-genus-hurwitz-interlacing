"""Enumerate connected monotone factorizations with the original b,t weights.

Coulter–Do, arXiv:2506.04002v1, Definitions 3.8 and 4.1, Proposition 4.18.
The output counts equal (product of the parts) times the paper's polynomials.
Only two-part inputs are supported.
"""
from functools import cache
import json
from math import comb


def initial_matching(parts):
    partners = [None] * (2 * sum(parts))
    start = 0
    for size in parts:
        for j in range(size):
            a = 2 * (start + j) + 1
            b = 2 * (start + (j + 1) % size)
            partners[a], partners[b] = b, a
        start += size
    return tuple(partners)


def labeled_transitions(matching):
    """Current largest odd label in one-based notation is len(matching)-1."""
    charge = [None] * len(matching)
    for largest in reversed(range(len(matching))):
        if charge[largest] is not None:
            continue
        charge[largest] = 1
        stack = [largest]
        while stack:
            i = stack.pop()
            for j in (i ^ 1, matching[i]):
                if charge[j] is None:
                    charge[j] = 1 - charge[i]
                    stack.append(j)
                else:
                    assert charge[i] + charge[j] == 1
    top = len(matching) - 2
    for i in range(top):
        other_i, other_top = matching[i], matching[top]
        changed = list(matching)
        if other_i != top:
            changed[i], changed[other_top] = other_top, i
            changed[top], changed[other_i] = other_i, top
        yield i, tuple(changed), int(charge[i] != charge[top])


def enumerate_pair(parts, twice_genus):
    assert len(parts) == 2 and min(parts) > 0 and twice_genus >= 0
    k = sum(parts)
    length = k + twice_genus
    boundary = 2 * parts[0]
    # Each coefficient is bounded by the count of monotone label sequences
    # times the maximum number of choices at each step. No base digits carry.
    bits = (comb(k + length - 1, length) * (2 * k - 2) ** length).bit_length()
    stride = length + 1
    transitions = cache(lambda m: tuple(labeled_transitions(m)))

    @cache
    def paths(m, remaining, used_top, joined):
        if remaining == 0:
            return int(joined and all(j == (i ^ 1) for i, j in enumerate(m)))
        if len(m) <= 2:
            return 0
        top = len(m) - 2
        total = paths(m[:-2], remaining, False, joined) if m[top] == top + 1 else 0
        for i, updated, flip in transitions(m):
            crossed = i < boundary <= top
            value = paths(updated, remaining - 1, True, joined or crossed)
            total += value << (bits * (flip + stride * int(not used_top)))
        return total

    encoded = paths(initial_matching(parts), length, False, False)
    coeffs = []
    for hive in range(k):
        row = []
        for flip in range(stride):
            row.append(encoded % (1 << bits))
            encoded >>= bits
        coeffs.append(row)
    assert encoded == 0
    paths.cache_clear()
    transitions.cache_clear()
    return coeffs


if __name__ == '__main__':
    assert enumerate_pair((1, 1), 0)[1][:2] == [1, 1]
    print(json.dumps({str(parts): enumerate_pair(parts, 4) for parts in [(3, 2), (4, 2)]}, indent=2))
