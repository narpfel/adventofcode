run: build
	@./venv/bin/python solution

build: venv
	@:

venv:
	@echo building virtualenv with dependencies
	python3 -m venv venv
	./venv/bin/python -m pip install -U pip wheel
	./venv/bin/python -m pip install numpy scikit-image

language:
	@echo python3

.PHONY: clean
clean:
	rm -rf venv
