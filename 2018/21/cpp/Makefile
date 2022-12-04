CXX = g++

CFLAGS ?= \
	-std=c++20 \
	-Wall \
	-Wextra \
	-O3 \
	-lfmt

run: build
	@./solution

build: solution
	@:

solution: solution.cxx
	$(CXX) $(CFLAGS) -o $@ $<

solution.cxx: generate.py
	./$< > $@

language:
	@echo c++

.PHONY: clean
clean:
	rm -rf solution solution.cxx
