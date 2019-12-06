run: build
	@kotlin SolutionKt

build: SolutionKt.class
	@:

SolutionKt.class: Solution.kt
	kotlinc Solution.kt

.PHONY: clean
clean:
	rm -f *.class
