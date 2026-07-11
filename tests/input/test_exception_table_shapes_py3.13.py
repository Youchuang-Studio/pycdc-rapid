# Python 3.13 exception-table control-flow shapes.
def with_for_return(path):
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                if line.strip():
                    return line
        return ''
    except FileNotFoundError:
        return ''


def with_for_continue(path):
    values = []
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                line = line.strip()
                if not line:
                    continue
                values.append(line)
        return values
    except FileNotFoundError:
        return values


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


def nested_with_try_for(path, values):
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
