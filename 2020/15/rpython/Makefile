run: build
	@./solution-c

build: solution-c
	@:

solution-c: ../python/solution.py pypy
	pypy pypy/rpython/bin/rpython --lto $<

pypy:
	hg clone https://foss.heptapod.net/pypy/pypy

language:
	@echo rpython

.PHONY: clean
clean:
	rm -f solution-c

.PHONY: clean-all
clean-all: clean
	rm -rf pypy
