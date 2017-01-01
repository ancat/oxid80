cool_flags = #-A unused_variables -A dead_code -A unused_imports
prod_flags = 

all:
	RUSTFLAGS="${cool_flags}" cargo build && mv target/debug/gbc main

hell:
	rustc $(cool_flags) hell.rs

loader:
	rustc $(cool_flags) loader.rs
	rustc $(cool_flags) cpu.rs

.PHONY: all hell loader
