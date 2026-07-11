# Python 3.13 with/for/continue shape.
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
