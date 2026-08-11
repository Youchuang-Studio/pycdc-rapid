def double_values(data):
    return [value * 2 for value in data]


def positive_values(data):
    return [value for value in data if value > 0]


def indexed_values(matrix):
    return {
        (row_index, column_index): value
        for row_index, row in enumerate(matrix)
        for column_index, value in enumerate(row)
    }
