def increment_and_reset(value):
    try:
        return value + 1
    finally:
        value = 0
