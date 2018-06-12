from itertools import groupby


INPUT = "1113222113"


def look_and_say(string):
    for k, g in groupby(string):
        yield str(len(list(g)))
        yield k


def look_and_say_recursively(string, depth):
    for _ in range(depth):
        string = "".join(look_and_say(string))
    return string


def main():
    print(len(look_and_say_recursively(INPUT, 40)))
    print(len(look_and_say_recursively(INPUT, 50)))


if __name__ == '__main__':
    main()
