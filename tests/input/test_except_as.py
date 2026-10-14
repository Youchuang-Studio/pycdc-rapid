def a(self):
    try:
        g()
    except Exception as e:
        self.log(e)
    self.refresh()


def b(self):
    try:
        g()
    except ValueError as e:
        return e
    except KeyError as k:
        raise


def c(self):
    try:
        g()
    except (A, B) as e:
        try:
            h()
        except C as inner:
            self.log(inner, e)
    except D:
        pass
    self.refresh()
