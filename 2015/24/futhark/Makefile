run: build
	@(echo '[' && paste -s -d ',' input && echo ']') | ./solution | sed s/u64//g

build: solution
	@:

solution: solution.fut
	futhark multicore solution.fut

.PHONY: clean
clean:
	rm -f solution solution.c
