run: build
	@./solution

build: solution
	@:

solution: solution.go
	go build $<

language:
	@echo go

.PHONY: clean
clean:
	rm -rf solution
