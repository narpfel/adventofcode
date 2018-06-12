import re
import json


def sum_numbers(string):
    return sum(map(int, re.findall(r"-?\d+", string)))


def has_no_red(thing):
    try:
        return "red" not in thing.values()
    except AttributeError:
        return True


def filter_recursively(predicate, iterable):
    if isinstance(iterable, (int, str)):
        yield iterable
    elif isinstance(iterable, list):
        for thing in iterable:
            if predicate(thing):
                yield list(filter_recursively(predicate, thing))
    else:
        for key, value in iterable.items():
            if predicate(value):
                yield list(filter_recursively(predicate, value))


def main():
    with open("input") as input_file:
        json_document = input_file.read()

    print(sum_numbers(json_document))

    # Such ugly! Much wow!
    print(
        sum_numbers(
            json.dumps(
                list(filter_recursively(has_no_red, json.loads(json_document)))
            )
        )
    )


if __name__ == '__main__':
    main()
