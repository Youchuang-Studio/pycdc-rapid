# Python 3.13 with/for/return shape.
def with_for_return(path):
    try:
        with open(path, 'r', encoding='utf-8') as source:
            for line in source:
                if line.strip():
                    return line
        return ''
    except FileNotFoundError:
        return ''
