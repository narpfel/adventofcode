run: quiet-build
	@./solution.pl
	@cargo run --release -q

.PHONY: quiet-build
quiet-build:
	@cargo build --release -q

.PHONY: build
build:
	cargo build --release

language:
	@echo "prolog (part 1) and rust (part 2)"

.PHONY: clean
clean:
	rm -rf grid
	cargo clean
