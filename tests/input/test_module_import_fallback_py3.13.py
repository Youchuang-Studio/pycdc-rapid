# Python 3.13 module exception-table shape.
try:
    import missing_config as config
    imported_value = config.value
except ImportError:
    imported_value = 'default'

if not imported_value:
    try:
        with open('config.txt', 'r', encoding='utf-8') as source:
            value = source.read().strip()
    except FileNotFoundError:
        value = ''
else:
    value = imported_value
