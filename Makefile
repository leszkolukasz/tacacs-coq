.PHONY: all build coq clean format

all: build

build:
	$(MAKE) -C coq clean
	@dune build

coq:
	$(MAKE) -C coq

clean:
	$(MAKE) -C coq clean

format:
	@dune build @fmt --auto-promote