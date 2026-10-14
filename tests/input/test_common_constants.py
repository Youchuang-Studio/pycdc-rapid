def defaults():
    name = ''
    flag = True
    other = False
    nothing = None
    index = -1
    return (name, flag, other, nothing, index)


def greet(text):
    print('')
    return text or ''
