SBCL ?= sbcl

run: build
	@$(SBCL) --script ./solution.lisp

build: solution.lisp
	@:

solution.lisp: generate.py
	./$< > $@

language:
	@echo sbcl

.PHONY: clean
clean:
	rm -rf solution.lisp
