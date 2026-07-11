# Python 3.13 with/for shape.
def read_nonempty_lines(path):
    lines = []
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                line = line.strip()
                if not line:
                    continue
                lines.append(line)
        return lines
    except FileNotFoundError:
        return []
