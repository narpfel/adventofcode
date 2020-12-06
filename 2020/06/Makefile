run: build
	@./solution

build: solution
	@:

solution: solution.go
	go build -o $@

.PHONY: clean
clean:
	rm -rf solution
