def a(xs):
    for x in xs:
        if x:
            break
        g(x)
    h()


def b(xs):
    for x in xs:
        if not x:
            continue
        g(x)
    h()


def c(xs):
    for x in xs:
        for y in x:
            if y:
                break
        h(x)
    h()


def d(xs):
    for x in xs:
        if x:
            print('found')
            break
    else:
        print('none')
    h()
