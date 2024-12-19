run: build
	@./solution

build: solution
	@:

solution: solution.pl
	swipl \
		--goal=main \
		--toplevel=halt \
		-O \
		-o $@ \
		-c $<

language:
	@echo swipl

.PHONY: clean
clean:
	rm -f solution
