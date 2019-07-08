#!/usr/bin/env python3

import argparse
import subprocess
import sys
import time
from contextlib import suppress
from pathlib import Path
from itertools import count


class Runner:
    def __init__(self, output):
        self.output = output

    def run_all(self):
        solution_count = count()
        for year_dir in sorted(Path().iterdir()):
            if year_dir.is_dir() and str(year_dir).isdigit():
                try:
                    solutions = sorted(year_dir.iterdir())
                except NotADirectoryError:
                    pass
                else:
                    for solution_dir, _ in zip(solutions, solution_count):
                        self.run_solution(solution_dir)
        return next(solution_count)

    def run_solution(self, solution_dir):
        execution_time_output_prefix = f"\n{solution_dir}: " if self.output is None else ""

        for language_indicator, runner_name in self.RUNNERS.items():
            path = solution_dir / language_indicator
            if path.exists():
                if self.output is not None:
                    print(f"{solution_dir}: ", end="", flush=True)
                else:
                    print(f"\n\nExecuting `{path}`...\n")
                start_time = time.perf_counter()
                try:
                    getattr(self, runner_name)(path)
                except subprocess.CalledProcessError:
                    return 0
                else:
                    print(f"{execution_time_output_prefix}{time.perf_counter() - start_time} s.")
                    return 1

        # See if multiple solutions are present
        solutions_executed = 0
        for sub_solution in sorted(solution_dir.iterdir()):
            if sub_solution.is_dir():
                with suppress(FileNotFoundError):
                    solutions_executed += self.run_solution(sub_solution)

        if not solutions_executed:
            raise FileNotFoundError(f"`{solution_dir}` does not contain a solution.")
        return solutions_executed

    def execute(self, command, cwd):
        subprocess.run(command, cwd=cwd, check=True, stdout=self.output, stderr=self.output)

    def run_executable(self, path):
        self.execute([path.absolute()], cwd=path.parent)

    def run_haskell(self, path):
        self.execute(["stack", "build", "solution"], cwd=path.parent)
        self.execute(["stack", "exec", "solution"], cwd=path.parent)

    def run_rust(self, path):
        self.execute(["cargo", "run", "--release"], cwd=path.parent)

    def run_makefile(self, path):
        self.execute(["make", "build"], cwd=path.parent)
        self.execute(["make", "run"], cwd=path.parent)

    RUNNERS = {
        "solution.py": "run_executable",
        "package.yaml": "run_haskell",
        "Cargo.toml": "run_rust",
        "solution.pl": "run_executable",
        "Makefile": "run_makefile",
    }


def main(argv):
    parser = argparse.ArgumentParser(description="Run solutions.")
    parser.add_argument("-a", "--all", help="Run all solutions.", action="store_true")
    parser.add_argument("solutions", help="Run specified solutions.", nargs="*", type=Path)
    parser.add_argument(
        "-t", "--time",
        help="Just measure execution time, don’t print result.",
        action="store_const", const=subprocess.DEVNULL, default=None,
    )
    args = parser.parse_args(argv)

    runner = Runner(args.time)
    start_time = time.perf_counter()
    if args.all:
        solution_count = runner.run_all()
    else:
        solution_count = 0
        for solution in args.solutions:
            solution_count += runner.run_solution(solution)
    print(f"Found {solution_count} solutions in {time.perf_counter() - start_time} s.")


if __name__ == "__main__":
    try:
        main(sys.argv[1:])
    except KeyboardInterrupt:
        print("\nAborted.")
