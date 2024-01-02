run: build
	@./solution-c

build: solution-c
	@:

solution-c: ../python/solution.py pypy
	pypy pypy/rpython/bin/rpython --lto -O2 $<

pypy:
	git clone --depth=1 https://github.com/pypy/pypy

language:
	@echo rpython

.PHONY: clean
clean:
	rm -f solution-c

.PHONY: clean-all
clean-all: clean
	rm -rf pypy
