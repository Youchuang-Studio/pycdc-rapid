def format_values(value, other):
    decimal = f"{value:.2f}"
    representation = f"{value!r}"
    combined = f"{value} and {other}"
    return (decimal, representation, combined)
