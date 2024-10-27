#!/usr/bin/env python3

from __future__ import annotations

import argparse
import datetime
import os
import re
import shlex
import subprocess
import sys
import time
from collections.abc import Callable
from collections.abc import Iterator
from contextlib import suppress
from functools import partial
from pathlib import Path
from tempfile import NamedTemporaryFile
from tempfile import TemporaryDirectory
from typing import Literal
from typing import Self

from attr import define
from identify import identify

FG_BOLD = "\x1B[1m"
FG_RED = "\x1B[31m"
FG_GREEN = "\x1B[32m"
FG_YELLOW = "\x1B[33m"
RESET = "\x1B[m"

type StderrDefault = Literal[False]
STDERR_DEFAULT: Literal[False] = False

RESPONSE_TYPES = [
    (
        re.compile("That's the right answer!"),
        f"{FG_BOLD}{FG_GREEN}{{match[0]}}{RESET}",
    ),
    (
        re.compile(
            r"(That's not the right answer.*?\.).*([Pp]lease wait .* before trying again\.)",
        ),
        f"{FG_BOLD}{FG_RED}{{match[1]}}\n{{match[2]}}{RESET}",
    ),
    (
        re.compile(
            r"You gave an answer too recently.* You have .* left to wait\.",
        ),
        f"{FG_BOLD}{FG_YELLOW}{{match[0]}}{RESET}",
    ),
    (
        re.compile(
            r"You don't seem to be solving the right level\.  Did you already complete it\?",
        ),
        f"{FG_BOLD}{FG_YELLOW}{{match[0]}}{RESET}",
    ),
]


type Output = int | None
type Command = MultiStep | list[str | Path]


@define
class Statistics:
    succeeded: int = 0
    build_time: float = 0
    execution_time: float = 0
    skipped: int = 0
    failed: int = 0

    def add(self, result: Result) -> None:
        result.add_to(self)

    def add_to(self, stats: Self) -> None:
        stats.succeeded += self.succeeded
        stats.build_time += self.build_time
        stats.execution_time += self.execution_time
        stats.skipped += self.skipped
        stats.failed += self.failed

    def __bool__(self) -> bool:
        return any([self.succeeded, self.skipped, self.failed])


@define(frozen=True)
class Success:
    build_time: float
    execution_time: float

    def add_to(self, stats: Statistics) -> None:
        stats.succeeded += 1
        stats.build_time += self.build_time
        stats.execution_time += self.execution_time


@define(frozen=True)
class Skipped:
    def add_to(self, stats: Statistics) -> None:
        stats.skipped += 1


@define(frozen=True)
class Failed:
    def add_to(self, stats: Statistics) -> None:
        stats.failed += 1


type Result = Statistics | Success | Skipped | Failed


@define(frozen=True)
class MultiStep:
    commands: list[list[str | Path]]

    @classmethod
    def from_commands(cls, commands: Self | list[str | Path]) -> MultiStep:
        match commands:
            case MultiStep():
                return commands
            case _:
                return MultiStep([commands])

    def __iter__(self) -> Iterator[list[str | Path]]:
        return iter(self.commands)


class Runner:
    def __init__(
        self,
        *,
        build_output: Output,
        solution_output: Output,
        languages: re.Pattern[str],
    ) -> None:
        self.build_output = build_output
        self.solution_output = solution_output
        self.languages = languages
        self.captured_output: list[bytes] = []

    def run_all(self) -> Statistics:
        stats = Statistics()
        for year_dir in sorted(Path().iterdir()):
            if year_dir.is_dir() and str(year_dir).isdigit():
                try:
                    solutions = sorted(year_dir.iterdir())
                except NotADirectoryError:
                    pass
                else:
                    for solution_dir in solutions:
                        stats.add(self.run_solution(solution_dir))
        return stats

    def run_solution(self, solution_dir: Path) -> Result:
        execution_time_prefix = f"\n{solution_dir}: " if self.solution_output is None else ""

        try:
            runner, path = self.find_executor(solution_dir)
        except FileNotFoundError:
            # See if multiple solutions are present
            stats = Statistics()
            for sub_solution in sorted(solution_dir.iterdir()):
                if sub_solution.is_dir():
                    with suppress(FileNotFoundError):
                        stats.add(self.run_solution(sub_solution))

            if not stats:
                raise FileNotFoundError(f"`{solution_dir}` does not contain a solution.")
            return stats
        else:
            language = language_for(path)
            if self.languages.search(language) is None:
                return Skipped()

            if self.solution_output is not None:
                print(
                    f"{solution_dir} [{language}]: ",
                    end="", flush=True, file=sys.stderr,
                )
            else:
                print(f"\n\nExecuting `{path}` [{language}]...\n", file=sys.stderr)

            try:
                build_time, execution_time = runner(path)
            except subprocess.CalledProcessError:
                print(f"{FG_BOLD}{FG_RED}failed!{RESET}", file=sys.stderr)
                return Failed()
            else:
                print(
                    f"{execution_time_prefix}{execution_time} s{format_build_time(build_time)}",
                    file=sys.stderr,
                )
                return Success(build_time=build_time, execution_time=execution_time)

    def find_executor(
        self,
        solution_dir: Path,
    ) -> tuple[Callable[[Path], tuple[float, float]], Path]:
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

    def timed_run(
        self,
        commands_param: Command,
        cwd: Path,
        output: Output,
        stderr: Output | StderrDefault = STDERR_DEFAULT,
    ) -> tuple[float, bytes]:
        if stderr is STDERR_DEFAULT:
            stderr = output
        commands = MultiStep.from_commands(commands_param)

        start_time = time.perf_counter()

        stdouts = []
        for command in commands:
            process = subprocess.run(command, cwd=cwd, check=True, stdout=output, stderr=stderr)
            stdouts.append(process.stdout)

        return (
            time.perf_counter() - start_time,
            b"\n".join(stdout for stdout in stdouts if stdout is not None),
        )

    def execute(
        self,
        build_command: Command | None,
        exection_command: Command,
        cwd: Path,
    ) -> tuple[float, float]:
        if build_command is not None:
            build_time, _ = self.timed_run(build_command, cwd, self.build_output)
        else:
            build_time = 0
        execution_time, output = self.timed_run(
            exection_command,
            cwd,
            self.solution_output,
            stderr=None,
        )
        if output is not None:
            self.captured_output.append(output)
        return build_time, execution_time

    def run_executable(self, path: Path) -> tuple[float, float]:
        return self.execute(None, [path.absolute()], cwd=path.parent)

    def run_haskell(self, path: Path) -> tuple[float, float]:
        with TemporaryDirectory() as tmpdir:
            return self.execute(
                ["stack", "build", "--local-bin-path", tmpdir, "--copy-bins", "solution"],
                [Path(tmpdir) / "solution"],
                cwd=path.parent,
            )

    def run_rust(self, path: Path) -> tuple[float, float]:
        return self.execute(
            ["cargo", "build", "--release"],
            ["./target/release/solution"],
            cwd=path.parent,
        )

    def run_makefile(self, path: Path) -> tuple[float, float]:
        return self.execute(
            ["make", "build"],
            ["make", "run"],
            cwd=path.parent,
        )

    def run_nvim(self, path: Path) -> tuple[float, float]:
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

    def run_cmake(self, path: Path) -> tuple[float, float]:
        return self.execute(
            MultiStep([
                ["cmake", "-B", "build", "-S", ".", "-G", "Ninja"],
                ["ninja", "-C", "build", "-v"],
            ]),
            ["build/solution"],
            cwd=path.parent,
        )

    RUNNERS = {
        "Makefile": "run_makefile",
        "package.yaml": "run_haskell",
        "Cargo.toml": "run_rust",
        "solution.vim": "run_nvim",
        "CMakeLists.txt": "run_cmake",
    }


RUNNER_TO_LANGUAGE: dict[str, Callable[[Path], str]] = {
    "package.yaml": lambda _: "haskell",
    "Cargo.toml": lambda _: "rust",
    "Makefile": lambda path: subprocess.run(
        ["make", "language"],
        cwd=path.parent,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip(),
    "CMakeLists.txt": lambda _: "c++",
}


def language_for(path: Path) -> str:
    if os.access(path, os.X_OK):
        return identify.parse_shebang_from_file(os.fspath(path))[0]
    try:
        return RUNNER_TO_LANGUAGE[path.name](path)
    except subprocess.CalledProcessError:
        return "unknown"


def format_build_time(build_time: float) -> str:
    if build_time < 1:
        return "."
    else:
        return f" (and {build_time} s of build time)."


def get_year_day() -> tuple[int, int]:
    parts = list(Path(".").resolve().parts)
    while True:
        try:
            day = int(parts[-1])
        except ValueError:
            parts.pop()
        else:
            year = int(parts[-2])
            return year, day


def read_cookies() -> dict[str, str]:
    return {
        "Cookie": (Path(__file__).parent / ".env").read_text().strip(),
        "User-Agent": "github.com/narpfel",
    }


def retrieve_input(year: int, day: int) -> str:
    from urllib.request import Request
    from urllib.request import urlopen
    request = Request(
        url=f"https://adventofcode.com/{year}/day/{day}/input",
        headers=read_cookies(),
    )
    response = urlopen(request)
    input_str = response.read().decode()
    assert isinstance(input_str, str)
    return input_str


def wait_for_puzzle_unlock(year: int, day: int) -> None:
    unlock_date = datetime.datetime(year, 12, day, 5, 0, tzinfo=datetime.UTC)
    wait_end = unlock_date + datetime.timedelta(seconds=4)
    while True:
        now = datetime.datetime.now(tz=datetime.UTC)
        if wait_end <= now:
            break
        time_to_wait = wait_end - now
        print(f"sleeping until {unlock_date} ({time_to_wait})")
        time.sleep(1)


def submit_solution(year: int, day: int, part: int, solution: str) -> str:
    from urllib.parse import urlencode
    from urllib.request import Request
    from urllib.request import urlopen
    data = urlencode(dict(level=part, answer=solution))
    request = Request(
        url=f"https://adventofcode.com/{year}/day/{day}/answer",
        method="POST",
        data=data.encode(),
        headers=read_cookies(),
    )
    print(f"submitting {year}/{day} part {part} with {solution!r}")
    response = urlopen(request)
    answer = response.read().decode()
    assert isinstance(answer, str)
    return answer


def show_submission_result(response_page: str) -> None:
    for regex, format_str in RESPONSE_TYPES:
        match = regex.search(response_page)
        if match is not None:
            print(format_str.format(match=match))
            return
    assert False, response_page


def main(argv: list[str] | None = None) -> int | None:
    parser = argparse.ArgumentParser(description="Run solutions.")
    parser.add_argument("-a", "--all", help="Run all solutions.", action="store_true")
    parser.add_argument(
        "-b", "--build-output",
        help="Show build output",
        action="store_const", const=None, default=subprocess.DEVNULL,
    )
    parser.add_argument(
        "solutions",
        help="Run specified solutions.",
        nargs="*",
        default=[Path(".")],
        type=Path,
    )
    parser.add_argument(
        "-t", "--time",
        help="Just measure execution time, don’t print result.",
        action="store_const", const=subprocess.DEVNULL, default=None,
    )
    parser.add_argument(
        "-l", "--languages",
        help="Filter to languages matching the given regular expression",
        default=re.compile(""),
        type=partial(re.compile, flags=re.I),
    )
    args = parser.parse_args(argv)

    if Path("get") in args.solutions:
        if len(args.solutions) > 1:
            parser.error("can only get input for one problem")
        year, day = get_year_day()
        wait_for_puzzle_unlock(year, day)
        try:
            with open("input", "x", encoding="utf-8") as input_file:
                input_file.write(retrieve_input(year, day))
        except FileExistsError:
            print("using cached input")
        subprocess.check_call(["/usr/bin/less", "input"])
        return None

    if Path("submit") in args.solutions:
        if len(args.solutions) > 1:
            parser.error("can only submit one solution at a time")
        args.solutions = parser.get_default("solutions")
        capture_output = subprocess.PIPE
        submit = True
    else:
        capture_output = args.time
        submit = False

    runner = Runner(
        build_output=args.time if args.time is not None else args.build_output,
        solution_output=capture_output,
        languages=args.languages,
    )
    start_time = time.perf_counter()
    if args.all:
        stats = runner.run_all()
    else:
        stats = Statistics()
        for solution in args.solutions:
            stats.add(runner.run_solution(solution))
    total_duration = time.perf_counter() - start_time
    if submit and len(runner.captured_output) == 1:
        year, day = get_year_day()
        [output_bytes] = runner.captured_output
        output = output_bytes.decode("utf-8")
        print(output)
        lines = output.splitlines()

        if len(lines) == 1:
            show_submission_result(submit_solution(year, day, part=1, solution=lines[0]))
            if day == 25:
                submit_solution(year, day, part=2, solution="0")
                print(f"{FG_BOLD}{FG_GREEN}also submitting part 2...{RESET}")
        elif len(lines) == 2:
            show_submission_result(submit_solution(year, day, part=2, solution=lines[1]))
        else:
            print("weird output format, please submit manually")
    else:
        print(
            f"Found {stats.succeeded} solutions in {stats.execution_time} s"
            f"{format_build_time(stats.build_time)}",
            file=sys.stderr,
        )
        print(f"wall time elapsed: {total_duration} s", file=sys.stderr)
        if stats.failed:
            print(
                f"{FG_BOLD}{FG_RED}{stats.failed} solutions failed executing.{RESET}",
                file=sys.stderr,
            )
        if stats.skipped:
            print(f"{FG_YELLOW}{stats.skipped} solutions were skipped.{RESET}", file=sys.stderr)

    return stats.failed


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nAborted.", file=sys.stderr)
