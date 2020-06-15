#!/usr/bin/env python3
import argparse
import shlex
import subprocess
import sys
from itertools import takewhile

FG_BOLD = "\x1B[1m"
FG_GREEN = "\x1B[32m"
FG_PURPLE = "\x1B[38;2;170;034;255m"
FG_RED = "\x1B[31m"
RESET = "\x1B[m"


def replace(xs, needle, with_):
    for x in xs:
        if x == needle:
            yield with_
        else:
            yield x


def indent(lines, prefix):
    return type(lines)().join(prefix + line for line in lines.splitlines(True))


def write(buffer, value, prefix):
    buffer.write(indent(value, prefix))
    buffer.flush()


def run(command, *, quiet, fail_on):
    command = list(command)
    result = subprocess.run(command, capture_output=True)
    has_output = bool(result.stdout or result.stderr)

    if not quiet or has_output:
        print(FG_BOLD, FG_PURPLE, "==> ", shlex.join(command), RESET, sep="")

    has_failed = (
        result.returncode
        or any(
            fail in result.stdout
            or fail in result.stderr
            for fail in fail_on
        )
    )
    if (not quiet and has_output) or (quiet and has_failed):
        write(sys.stdout.buffer, result.stdout, f"{FG_PURPLE}  │ {RESET}".encode())
        write(sys.stderr.buffer, result.stderr, f"{FG_BOLD}{FG_PURPLE}  ║ {RESET}".encode())
        print(FG_BOLD, FG_RED, "=== FAILED ===", RESET, sep="")
        return result.returncode or 1
    else:
        print(FG_BOLD, FG_GREEN, "=== OK ===", RESET, sep="")
    return result.returncode


def split(xs, *, on):
    xs = iter(xs)
    return list(takewhile(lambda x: x != on, xs)), list(xs)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("-q", "--quiet-on-success", action="store_true")
    parser.add_argument("-p", "--placeholder", default="{}")
    parser.add_argument("-s", "--separator", default="---")
    parser.add_argument("-f", "--fail-on", default=[], nargs="*", type=str.encode)
    parser.add_argument("command", nargs='+')
    args = parser.parse_args(argv)
    command, params = split(args.command, on=args.separator)
    any_failed = False
    for param in params:
        any_failed |= run(
            replace(command, args.placeholder, param),
            quiet=args.quiet_on_success,
            fail_on=args.fail_on,
        )
    return bool(any_failed)


if __name__ == "__main__":
    sys.exit(main())
