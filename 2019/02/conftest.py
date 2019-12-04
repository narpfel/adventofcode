import hy
from _pytest.python import Module


def pytest_collect_file(path, parent):
    if path.ext == ".hy":
        return Module(path, parent)
