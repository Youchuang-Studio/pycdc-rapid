class Priv:
    def __init__(self, __arg=2):
        self.__secret = __arg
        self.__dunder__ = 3

    def get(self):
        return self.__secret

    def __hidden(self):
        return self.__secret


value = Priv()._Priv__secret
