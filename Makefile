cool_flags = -A dead_code -A unused_variables
prod_flags =

all:
	RUSTFLAGS="${cool_flags}" cargo build 

test:
	RUSTFLAGS="${cool_flags}" cargo test

hell:
	rustc $(cool_flags) hell.rs

loader:
	rustc $(cool_flags) loader.rs
	rustc $(cool_flags) cpu.rs

.PHONY: all hell loader
