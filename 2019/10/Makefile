run: build
	@mono Solution.exe

build: Solution.exe
	@:

Solution.exe: Solution.cs
	csc -o Solution.cs

.PHONY: clean
clean:
	rm -f *.exe
