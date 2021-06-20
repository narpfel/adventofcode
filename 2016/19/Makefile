CXX = g++

run: build
	@./solution

build: solution
	@:

solution: solution.cxx
	$(CXX) \
		-std=c++20 \
		-Wall \
		-Wextra \
		-pedantic \
		-O3 \
		-march=native \
		-mtune=native \
		-o $@ \
		$<

language:
	@echo c++

.PHONY: clean
clean:
	rm -rf solution
