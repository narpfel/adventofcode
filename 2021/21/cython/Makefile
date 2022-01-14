run: build
	@./venv/bin/python -c "import solution; solution.main()"

build: solution.*.so
	@:

solution.%.so: venv solution.py
	./venv/bin/cythonize -3 -b solution.py

venv:
	@echo building virtualenv with dependencies
	python3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install 'Cython==3.0.0a10'

language:
	@echo cython

.PHONY: clean
clean:
	rm -rf venv build .mypy_cache solution.*.so solution.c
