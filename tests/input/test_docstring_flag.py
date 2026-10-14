def no_doc(x):
    if x:
        return 'first const'
    return True


def with_doc():
    """real doc"""
    return 'other'


class Holder:
    """class doc"""

    def method(self):
        return 'first const'

    def documented(self):
        """method doc"""
        return 1
