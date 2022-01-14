run: build
	@./venv/bin/python -c "import main; main.main()"

build: main.*.so
	@:

main.%.so: venv main.py
	./venv/bin/python -m mypy --strict main.py
	./venv/bin/mypyc main.py

venv:
	@echo building virtualenv with dependencies
	python3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install mypy

language:
	@echo python3/mypyc

.PHONY: clean
clean:
	rm -rf venv build .mypy_cache main.*.so
