#!/usr/bin/env python3

import argparse
import os
import shlex
import subprocess
import sys
import time
from contextlib import suppress
from itertools import count
from pathlib import Path
from tempfile import NamedTemporaryFile
from tempfile import TemporaryDirectory

from identify import identify

FG_BOLD = "\x1B[1m"
FG_RED = "\x1B[31m"
RESET = "\x1B[m"


class Runner:
    def __init__(self, *, build_output, solution_output):
        self.build_output = build_output
        self.solution_output = solution_output
        self.failed_solutions = 0

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
        execution_time_prefix = f"\n{solution_dir}: " if self.solution_output is None else ""

        try:
            runner, path = self.find_executor(solution_dir)
        except FileNotFoundError:
            # See if multiple solutions are present
            solutions_executed = 0
            for sub_solution in sorted(solution_dir.iterdir()):
                if sub_solution.is_dir():
                    with suppress(FileNotFoundError):
                        solutions_executed += self.run_solution(sub_solution)

            if not solutions_executed:
                raise FileNotFoundError(f"`{solution_dir}` does not contain a solution.")
            return solutions_executed
        else:
            if self.solution_output is not None:
                print(
                    f"{solution_dir} [{language_for(path)}]: ",
                    end="", flush=True, file=sys.stderr,
                )
            else:
                print(f"\n\nExecuting `{path}` [{language_for(path)}]...\n", file=sys.stderr)

            try:
                build_time, execution_time = runner(path)
            except subprocess.CalledProcessError:
                print(f"{FG_BOLD}{FG_RED}failed!{RESET}", file=sys.stderr)
                self.failed_solutions += 1
                return 0
            else:
                build_time_output = (
                    f" (and {build_time} s of build time)."
                    if build_time > 1
                    else "."
                )
                print(
                    f"{execution_time_prefix}{execution_time} s{build_time_output}",
                    file=sys.stderr,
                )
                return 1

    def find_executor(self, solution_dir):
        for language_indicator, runner_name in self.RUNNERS.items():
            path = solution_dir / language_indicator
            if path.exists():
                return getattr(self, runner_name), path

        with suppress(StopIteration):
            return next(
                (self.run_executable, file)
                for file in solution_dir.iterdir()
                if file.is_file() and os.access(file, os.X_OK)
            )

        raise FileNotFoundError(f"`{solution_dir}` does not contain a solution.")

    def timed_run(self, command, cwd, output):
        start_time = time.perf_counter()
        subprocess.run(command, cwd=cwd, check=True, stdout=output, stderr=output)
        return time.perf_counter() - start_time

    def execute(self, build_command, exection_command, cwd):
        if build_command is not None:
            build_time = self.timed_run(build_command, cwd, self.build_output)
        else:
            build_time = 0
        execution_time = self.timed_run(exection_command, cwd, self.solution_output)
        return build_time, execution_time

    def run_executable(self, path):
        return self.execute(None, [path.absolute()], cwd=path.parent)

    def run_haskell(self, path):
        with TemporaryDirectory() as tmpdir:
            return self.execute(
                ["stack", "build", "--local-bin-path", tmpdir, "--copy-bins", "solution"],
                [Path(tmpdir) / "solution"],
                cwd=path.parent,
            )

    def run_rust(self, path):
        return self.execute(
            ["cargo", "build", "--release"],
            ["./target/release/solution"],
            cwd=path.parent,
        )

    def run_makefile(self, path):
        return self.execute(
            ["make", "build"],
            ["make", "run"],
            cwd=path.parent,
        )

    def run_nvim(self, path):
        with NamedTemporaryFile() as tempfile:
            filename = shlex.quote(os.fspath(tempfile.name))
            # Ugly hack because `Runner.execute` does not support pipes
            return self.execute(
                None,
                [
                    "sh", "-c",
                    f'cat {shlex.quote(os.fspath(path.absolute()))} - <<<":wq! {filename}" '
                    f"| nvim --clean -s - && cat {filename}",
                ],
                cwd=path.parent,
            )

    RUNNERS = {
        "Makefile": "run_makefile",
        "package.yaml": "run_haskell",
        "Cargo.toml": "run_rust",
        "solution.vim": "run_nvim",
    }


RUNNER_TO_LANGUAGE = {
    "package.yaml": lambda _: "haskell",
    "Cargo.toml": lambda _: "rust",
    "Makefile": lambda path: subprocess.run(
        ["make", "language"],
        cwd=path.parent,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip(),
}


def language_for(path):
    if os.access(path, os.X_OK):
        return identify.parse_shebang_from_file(path)[0]
    try:
        return RUNNER_TO_LANGUAGE[path.name](path)
    except subprocess.CalledProcessError:
        return "unknown"


def main(argv):
    parser = argparse.ArgumentParser(description="Run solutions.")
    parser.add_argument("-a", "--all", help="Run all solutions.", action="store_true")
    parser.add_argument(
        "-b", "--build-output",
        help="Show build output",
        action="store_const", const=None, default=subprocess.DEVNULL,
    )
    parser.add_argument("solutions", help="Run specified solutions.", nargs="*", type=Path)
    parser.add_argument(
        "-t", "--time",
        help="Just measure execution time, don’t print result.",
        action="store_const", const=subprocess.DEVNULL, default=None,
    )
    args = parser.parse_args(argv)

    runner = Runner(
        build_output=args.time if args.time is not None else args.build_output,
        solution_output=args.time,
    )
    start_time = time.perf_counter()
    if args.all:
        solution_count = runner.run_all()
    else:
        solution_count = 0
        for solution in args.solutions:
            solution_count += runner.run_solution(solution)
    print(
        f"Found {solution_count} solutions in {time.perf_counter() - start_time} s.",
        file=sys.stderr,
    )
    if runner.failed_solutions:
        print(f"{runner.failed_solutions} solutions failed executing.", file=sys.stderr)

    return runner.failed_solutions


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except KeyboardInterrupt:
        print("\nAborted.", file=sys.stderr)
