def drain(q):
    while q:
        x = q.pop()
        if x:
            break
        print(x)
    done()


def first(get):
    while True:
        x = get()
        if x:
            return x
        print(x)

