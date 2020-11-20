CC = clang
CFLAGS ?= \
	-std=c18 \
	-Wall \
	-Wextra \
	-pedantic \
	-O3 \
	-Wno-gnu-label-as-value

run: build
	@./solution

build: solution
	@:

solution: solution.o
	$(CC) $(CFLAGS) -o $@ $<

solution.o: solution.c
	$(CC) $(CFLAGS) -c $<

solution.c: generate.py
	./$< > $@

.PHONY: clean
clean:
	rm -rf solution solution.o solution.c
