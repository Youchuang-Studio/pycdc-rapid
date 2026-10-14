def f(y, z):
    a = [i for i in y]
    b = [i * 2 for i in y if i]
    c = {i for i in y if i is not None}
    d = {k: v for k, v in y}
    e = [i + j for i in y if i for j in z if j]
    g = [i for i in y if not i]
    h = list((i for i in y if i > 1))
    k = any((w in z for w in y))
    return (a, b, c, d, e, g, h, k)
