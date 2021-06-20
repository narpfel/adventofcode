run: build
	@java Solution

build: *.class
	@:

%.class: %.java
	javac $?

language:
	@echo java

.PHONY: clean
clean:
	rm -f *.class
