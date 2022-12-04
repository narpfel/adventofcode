PYTHON ?= pypy3

run: build
	@$(PYTHON) ./solution.py

build: solution.py
	@:

solution.py: generate.py
	./$< > $@

language:
	@echo pypy3

.PHONY: clean
clean:
	rm -rf solution.py
