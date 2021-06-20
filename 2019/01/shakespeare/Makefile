CCFLAGS = \
		-std=c18 \
		-Wall \
		-Wextra \
		-pedantic \
		-O3 \
		-march=native \
		-mtune=native \
		-Wno-unused-label

run: build
	@./solution < input

build: solution
	@:

solution: solution.o
	$(CC) $(CCFLAGS) \
		-o $@ \
		$< \
		-lspl \
		-lm

solution.o: solution.c
	$(CC) $(CCFLAGS) \
		-c $<

solution.c: solution.spl
	$(info Make sure the Shakespeare system is setup correctly:)
	$(info `spl2c` must be available in `$$PATH`)
	$(info `spl.h` must be available in the C include path `$$CPATH`)
	$(info `libspl.a` must be available in the library search path `$$LIBRARY_PATH`)
	spl2c < $< > $@

language:
	@echo shakespeare

.PHONY: clean
clean:
	rm -f solution solution.c solution.o
