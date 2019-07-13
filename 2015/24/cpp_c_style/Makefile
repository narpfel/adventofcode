CXX = clang++

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
		solution.cxx \
		-lstdc++fs

.PHONY: clean
clean:
	rm solution
