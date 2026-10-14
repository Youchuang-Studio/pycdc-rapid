class Base:
    pass


class Child(Base, object):
    x = 1


class Meta(type):
    pass


class WithMeta(Base, metaclass=Meta):
    pass


class OnlyMeta(metaclass=Meta):
    x = 1


def deco(c):
    return c


@deco
class Decorated:
    y = 'first'


@deco
@deco
class Twice:
    pass
