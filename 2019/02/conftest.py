import hy
import pytest


@pytest.fixture()
def tmpchdir(tmpdir):
    with tmpdir.as_cwd():
        yield tmpdir


def pytest_collect_file(path, parent):
    if path.ext == ".hy":
        return pytest.Module(path, parent)
