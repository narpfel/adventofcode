run: build
	@./venv/bin/python -c "import solution; solution.main()"

build: solution.*.so
	@:

solution.%.so: venv solution.py
	./venv/bin/python -m mypy --strict solution.py
	./venv/bin/mypyc solution.py

venv:
	@echo building virtualenv with dependencies
	python3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install mypy

language:
	@echo python3/mypyc

.PHONY: clean
clean:
	rm -rf venv build .mypy_cache solution.*.so
