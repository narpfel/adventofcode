run: build
	@node solution.mjs

build: solution.mjs
	@:

solution.mjs: generate.py
	./$< > $@

language:
	@echo node

.PHONY: clean
clean:
	rm -rf solution.mjs
