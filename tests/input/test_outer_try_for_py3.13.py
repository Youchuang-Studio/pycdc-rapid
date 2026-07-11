# Python 3.13 outer try/for shape.
def for_in_outer_try(items):
    try:
        for item in items:
            if item == 'stop':
                break
            if item:
                continue
        return len(items)
    except TypeError:
        return 0
