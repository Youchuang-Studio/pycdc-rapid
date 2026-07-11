# Python 3.13 nested with/try/for shape.
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
