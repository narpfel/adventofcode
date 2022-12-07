LUA ?= luajit

run: build
	@$(LUA) ./solution.lua

build: solution.lua
	@:

solution.lua: generate.py
	./$< > $@

language:
	@echo luajit

.PHONY: clean
clean:
	rm -rf solution.lua
