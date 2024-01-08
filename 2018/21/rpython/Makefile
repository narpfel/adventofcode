run: build
	@./main-c

build: main-c
	@:

main-c: main.py pypy
	pypy pypy/rpython/bin/rpython --lto -Ojit --translation-jit $<

pypy:
	git clone --depth=1 https://github.com/pypy/pypy

language:
	@echo rpython

.PHONY: clean
clean:
	rm -f main-c

.PHONY: clean-all
clean-all: clean
	rm -rf pypy
