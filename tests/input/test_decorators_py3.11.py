# Python 3.11 function and class decorator regression test.
@staticmethod
def simple():
    return 1


@app.route
@cache
def stacked():
    return 2


@registry.register
class Registered:
    pass
