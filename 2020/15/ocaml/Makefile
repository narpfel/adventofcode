run: build
	@./solution

build: solution
	@:

solution: solution.ml
	ocamlopt \
		-O3 \
		-o $@ \
		$<

language:
	@echo ocaml

.PHONY: clean
clean:
	rm -f solution solution.cmi solution.cmx solution.o
