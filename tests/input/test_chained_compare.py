def in_range(lo, x, hi):
    return lo <= x < hi


def classify(a, b, c, d):
    ordered = a < b < c < d
    same = a == b == c
    if 0 <= a < 10:
        print('digit')
    return (ordered, same)


def member(x, group, other):
    return x in group is not other
