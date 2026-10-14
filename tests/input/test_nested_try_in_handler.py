def pick(select, value):
    try:
        select.select_by_value(value)
    except:
        try:
            select.select_by_visible_text(value)
        except:
            pass
    select.done()


def typed(select, value):
    try:
        select.open(value)
    except KeyError as e:
        try:
            select.retry(e)
        except ValueError:
            select.log(e)
    except TypeError:
        pass
    select.done()
