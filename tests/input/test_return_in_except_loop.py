def click(el, n):
    for i in range(n):
        try:
            el.click()
            return True
        except Exception:
            if i == n - 1:
                return False
            wait()


def click_fallback(el, n):
    for i in range(n):
        try:
            el.click()
            return True
        except Exception:
            try:
                el.tap()
            except Exception:
                if i == n - 1:
                    return False
                wait()
                continue
            return True
