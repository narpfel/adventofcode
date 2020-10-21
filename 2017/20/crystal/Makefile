run: build
	@./solution

build: solution
	@:

solution: solution.cr
	crystal build --release $<

.PHONY: clean
clean:
	rm -f solution
