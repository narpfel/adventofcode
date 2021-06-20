run: build
	@./solution

build: solution
	@:

solution: solution.cr
	crystal build --release $<

language:
	@echo crystal

.PHONY: clean
clean:
	rm -f solution
