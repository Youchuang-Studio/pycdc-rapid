# Python 3.14 with/for/try shape.
def with_for_try(path, values):
    result = []
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                try:
                    if line.strip() in values:
                        result.append(line)
                    else:
                        continue
                except AttributeError:
                    result.append('bad')
        return result
    except FileNotFoundError:
        return result


def callback(flag):
    return lambda event: event if flag else None
