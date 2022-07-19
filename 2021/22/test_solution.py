import pytest
import solution


@pytest.mark.parametrize(
    "filename, region, expected",
    [
        pytest.param("input_test_1", solution.PART_1_REGION, 39),
        pytest.param("input_test_2", solution.PART_1_REGION, 590784),
        pytest.param("input_test_3", solution.PART_1_REGION, 474140),
        pytest.param("input_test_3", None, 2758514936282235),
    ],
)
def test(filename, region, expected):
    assert solution.solve(solution.read_input(filename), region=region) == expected
