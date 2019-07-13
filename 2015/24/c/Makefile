CC = clang

run: build
	@./solution

build: solution
	@:

solution: solution.c
	$(CC) \
		-std=c18 \
		-Wall \
		-Wextra \
		-pedantic \
		-O3 \
		-march=native \
		-mtune=native \
		-o solution \
		solution.c

.PHONY: clean
clean:
	rm solution
