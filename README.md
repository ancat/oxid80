# oxid80
oxid80 is an incomplete [Zilog Z80](https://en.wikipedia.org/wiki/Zilog_Z80) emulator written in [Rust](https://www.rust-lang.org/).

I built this mainly by following the offical Z80 user manual with the goal of learning Rust. Originally it was meant to be compatible with Gameboy Color roms, but it turns out I didn't really read the documentation closely enough to learn that the GBC actually uses a modified version of the Z80 instruction set. So they're largely incompatible. Blah. 

The code is hopefully easy to read. There are only 4 source files, of which `src/main.rs` and `src/cpu.rs` are probably the interesting ones.

## Building

- `git clone <this repo>`
- `cargo test`
- `cargo build`

## Tests

I try to add tests as I add new functionality. Tests at this point are mostly running raw Z80 assembly and making sure that they are represented correctly as strings and have the appropriate end results.

A clean build should look something like the following:

```
running 36 tests
test cpu::tests::test_add_a_hl_mem ... ok
test cpu::tests::test_add_a_r ... ok
test cpu::tests::test_add_a_n ... ok
test cpu::tests::test_absolute_jumps ... ok
test cpu::tests::test_arithmetic_n ... ok
...
...
test mmu::tests::test_read_u8_many ... ok
test mmu::tests::test_endianness ... ok
test mmu::tests::test_read_write_u16 ... ok
test mmu::tests::test_read_write_u8 ... ok

test result: ok. 36 passed; 0 failed; 0 ignored; 0 measured
```

There are a lot of warnings right now. My plan is to treat them like I do most other problems in my life (ignore them)
