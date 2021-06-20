CXX = g++

run: build
	@./solution

build: solution
	@:

solution: solution.cxx
	$(CXX) \
		-std=c++2a \
		-Wall \
		-Wextra \
		-pedantic \
		-O3 \
		-march=native \
		-mtune=native \
		-o solution \
		solution.cxx

language:
	@echo c++

.PHONY: clean
clean:
	rm -f solution
