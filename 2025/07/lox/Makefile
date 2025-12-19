run: build
	@./bin/bin/crabbing-interpreters --loop=threaded solution.lox

build: bin/bin/crabbing-interpreters
	@:

bin/bin/crabbing-interpreters:
	cargo install \
		--git https://github.com/narpfel/crabbing-interpreters \
		--target-dir=bin/target \
		--root=bin \
		--locked \
		--profile=perf \
		--features=mmap

language:
	@echo lox

.PHONY: clean
clean:
	rm -rf bin
