# Python 3.11 extended iterable-unpacking regression test (PEP 3132).
def unpack_targets(seq, obj, container):
    a, *b = seq
    *head, tail = seq
    first, *middle, last = seq
    x, *rest, y, z = seq
    obj.a, *obj.rest = seq
    container[0], *container[1:] = seq


def unpack_globals(seq):
    global first_global, middle_global, last_global
    first_global, *middle_global, last_global = seq
