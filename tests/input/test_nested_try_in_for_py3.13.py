# Python 3.13 nested try/for shape.
def nested_try_in_for(items):
    values = []
    for item in items:
        try:
            if not item:
                continue
            values.append(int(item))
        except ValueError:
            values.append(-1)
    return values
