from itertools import count
from sympy import divisors


def main():
    for n in count(1):
        if not n % 10000:
            print(n)
        if 10 * sum(divisors(n, generator=True)) >= 36000000:
            print("Solution (part 1):", n)
        if 11 * sum(div for div in divisors(n, generator=True) if n / div <= 50) >= 36000000:
            print("Solution (part 2):", n)
            break


if __name__ == '__main__':
    main()
