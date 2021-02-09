run: build
	@./venv/bin/python solution.py

build: venv
	@:

venv:
	@echo building virtualenv with dependencies
	pypy3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install pytest

.PHONY: clean
clean:
	rm -rf venv

language:
	@echo python3/pypy3
