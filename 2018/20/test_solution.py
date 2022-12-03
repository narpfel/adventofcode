import pytest
import solution


@pytest.mark.parametrize(
    "test_case, expected",
    [
        (1, 3),
        (2, 10),
        (3, 18),
        (4, 23),
        (5, 31),
    ],
)
def test_part_1(test_case, expected):
    maze = solution.read_input(f"input_test_{test_case}")
    assert solution.part_1(maze) == expected
