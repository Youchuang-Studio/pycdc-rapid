def continue_in_try(xs):
    for x in xs:
        try:
            a(x)
            continue
        except E:
            pass
        b(x)


def return_in_try(xs, default):
    for x in xs:
        try:
            return parse(x)
        except ValueError:
            log(x)
        retry(x)
    return default


def break_in_try(xs):
    for x in xs:
        try:
            send(x)
            break
        except IOError:
            wait()
        note(x)
    done()
