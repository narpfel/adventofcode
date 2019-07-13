run: build
	@(echo '[' && paste -s -d ',' input && echo ']') | ./solution | sed s/u64//g

build: solution
	@:

solution: solution.fut
	futhark c solution.fut

.PHONY: clean
clean:
	rm solution solution.c
