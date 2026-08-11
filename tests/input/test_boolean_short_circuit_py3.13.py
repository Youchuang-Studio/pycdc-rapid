def boolean_cases(a, b, c):
    if a or b and c:
        return 1
    if a and not b:
        return 2
    return 3
