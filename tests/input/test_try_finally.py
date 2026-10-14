def a(self):
    try:
        g()
    finally:
        self.done()


def b(self, ok):
    try:
        if ok:
            self.x = 1
        else:
            self.y = 2
    finally:
        self.done()


def c(self):
    try:
        return g()
    finally:
        self.done()
