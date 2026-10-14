def first(a, b):
    return a or b


def both(a, b):
    return a and b


def chains(a, b, c):
    x = a or b or c
    y = a and b and c
    z = a or b and c
    return (x, y, z)


def pick(match):
    token = match.group(1) or match.group(2)
    print(token or '')
    return isinstance(token, str) and token != ''
