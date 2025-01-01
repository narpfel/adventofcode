run: build
	@./solution

build: solution
	@:

solution: solution.c
	$(CC) \
		-g \
		-std=c23 \
		-Wall \
		-Wextra \
		-Wconversion \
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
