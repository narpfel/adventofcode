run: build
	@./main-c

build: main-c
	@:

main-c: main.py pypy
	pypy pypy/rpython/bin/rpython --lto -O2 --translation-jit $<

pypy:
	hg clone https://foss.heptapod.net/pypy/pypy

language:
	@echo rpython

.PHONY: clean
clean:
	rm -f main-c

.PHONY: clean-all
clean-all: clean
	rm -rf pypy
