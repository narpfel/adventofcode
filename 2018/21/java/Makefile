run: build
	@java Main

build: Main.class
	@:

Main.class: Main.java
	javac $<

Main.java: generate.py
	./$< > $@

language:
	@echo java

.PHONY: clean
clean:
	rm -rf Main.java Main.class
