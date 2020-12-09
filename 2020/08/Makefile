run: build
	@java Solution

build: *.class
	@:

%.class: %.java
	javac $?

.PHONY: clean
clean:
	rm -f *.class
