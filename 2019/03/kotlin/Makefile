run: build
	@kotlin SolutionKt

build: SolutionKt.class
	@:

SolutionKt.class: Solution.kt
	kotlinc Solution.kt

language:
	@echo kotlin

.PHONY: clean
clean:
	rm -f *.class
