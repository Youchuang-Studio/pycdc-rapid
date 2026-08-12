def safe_string(value):
    try:
        return str(value)
    except Exception:
        return None


def show_message(message, title="Error"):
    return title


def first_value(values):
    for value in values:
        return value


def local_import_aliases():
    from datetime import datetime as _dt, timedelta as _td
    return _dt, _td


def segmented_try(value):
    try:
        if value is None:
            return None
        number = int(value)
        if number <= 0:
            return 0
        return number
    except (ValueError, TypeError):
        return -1
