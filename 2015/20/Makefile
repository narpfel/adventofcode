run: build
	@./venv/bin/python solution.py

build: venv
	@:

venv:
	@echo building virtualenv with dependencies
	pypy3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install sympy

language:
	@echo pypy3

.PHONY: clean
clean:
	rm -rf venv
