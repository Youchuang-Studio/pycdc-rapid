class Base:
    def m(self):
        return 1


class Child(Base):
    def m(self):
        return super().m() + 1

    def n(self):
        return super(Child, self).m
