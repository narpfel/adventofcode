run: build
	@mono Generated.exe

build: Generated.exe
	@:

Generated.exe: Generated.cs
	csc -o $<

Generated.cs: generate.py
	./$< > $@

language:
	@echo 'c#'

.PHONY: clean
clean:
	rm -rf Generated.cs Generated.exe
