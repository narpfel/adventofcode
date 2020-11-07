run: build
	@./venv/bin/python solution

build: venv
	@:

venv:
	@echo building virtualenv with dependencies
	python -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install numpy scikit-image

.PHONY: clean
clean:
	rm -rf venv
