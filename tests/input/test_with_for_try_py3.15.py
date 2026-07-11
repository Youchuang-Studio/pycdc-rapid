# Python 3.15 control-flow and exception-table smoke test.
def collect_lines(path, accepted):
    result = []
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                try:
                    value = line.strip()
                    if not value:
                        continue
                    if value in accepted:
                        result.append(value)
                except AttributeError:
                    result.append('invalid')
        return result
    except FileNotFoundError:
        return result


def choose(flag):
    return lambda value: value if flag else None
