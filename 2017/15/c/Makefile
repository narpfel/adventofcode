CC ?= clang

run: build
	@./solution

build: solution
	@:

solution: solution.c
	$(CC) \
		-std=c2x \
		-Wall \
		-Wextra \
		-pedantic \
		-O3 \
		-march=native \
		-mtune=native \
		-o solution \
		solution.c

language:
	@echo c

.PHONY: clean
clean:
	rm -f solution
