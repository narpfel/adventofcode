#!/usr/bin/env python3

import argparse
import subprocess
import sys
import time
from pathlib import Path
from itertools import count


def execute(command, cwd):
    subprocess.run(command, cwd=cwd, check=True)


def run_executable(path):
    execute([path.absolute()], cwd=path.parent)


def run_haskell(path):
    execute(["stack", "build", "solution"], cwd=path.parent)
    execute(["stack", "exec", "solution"], cwd=path.parent)


def run_rust(path):
    execute(["cargo", "run", "--release"], cwd=path.parent)


LANGUAGES = {
    "solution.py": run_executable,
    "package.yaml": run_haskell,
    "Cargo.toml": run_rust,
    "solution.pl": run_executable,
}


def run_all():
    solution_count = count()
    for year_dir in sorted(Path().iterdir()):
        if year_dir.is_dir() and str(year_dir).isdigit():
            try:
                solutions = sorted(year_dir.iterdir())
            except NotADirectoryError:
                pass
            else:
                for solution_dir, _ in zip(solutions, solution_count):
                    run_solution(solution_dir)
    return next(solution_count)


def run_solution(solution_dir):
    for language_indicator, runner in LANGUAGES.items():
        path = solution_dir / language_indicator
        if path.exists():
            print(f"\n\nExecuting `{path}`...\n")
            start_time = time.perf_counter()
            runner(path)
            print(f"\nElapsed: {time.perf_counter() - start_time} s.")
            return
    raise FileNotFoundError(f"`{solution_dir}` does not contain a solution.")


def main(argv):
    parser = argparse.ArgumentParser(description="Run solutions.")
    parser.add_argument("-a", "--all", help="Run all solutions.", action="store_true")
    parser.add_argument("solutions", help="Run specified solutions.", nargs="*", type=Path)
    args = parser.parse_args(argv)

    start_time = time.perf_counter()
    if args.all:
        solution_count = run_all()
    else:
        for solution in args.solutions:
            run_solution(solution)
        solution_count = len(args.solutions)
    print(f"Found {solution_count} solutions in {time.perf_counter() - start_time} s.")



if __name__ == "__main__":
    main(sys.argv[1:])
