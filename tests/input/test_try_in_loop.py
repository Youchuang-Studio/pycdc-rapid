def skip_errors(items):
    for item in items:
        try:
            handle(item)
        except ValueError:
            continue
        log(item)
    done()


def first_ok(items):
    for item in items:
        try:
            value = convert(item)
        except Exception:
            value = None
        if value:
            return value
    done()


def load(n):
    ok = False
    for attempt in range(n):
        try:
            get()
            ok = True
            break
        except Exception as e:
            if attempt == n - 1:
                raise Exception(str(e))
            sleep(2)
    return ok


def load_first(n):
    for attempt in range(n):
        try:
            get()
            break
        except Exception:
            sleep(2)
    done()
