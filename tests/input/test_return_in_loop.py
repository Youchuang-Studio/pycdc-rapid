def find(xs):
    for x in xs:
        if x:
            return x
    done()


def find_nested(rows):
    for row in rows:
        for cell in row:
            if cell:
                return cell


def has_nested(rows):
    for row in rows:
        for cell in row:
            if cell:
                return True
    return False


def find_safe(xs):
    for x in xs:
        try:
            if check(x):
                return x
        except ValueError:
            pass
