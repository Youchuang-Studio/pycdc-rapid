def f(g, h):
    (a, _, _) = g()
    x = h(a)
    for p, _, _ in g():
        x = p
    return (a, x)


class A:
    def m(self, mk):
        (fd, self.path) = mk()
        return fd
