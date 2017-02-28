use std::vec::Vec;
use std::fs::File;
use std::io::Read;
use std::process::exit;
use std::env;

mod cpu;
mod mmu;
mod utils;

fn main() -> () {
    let mut args: std::env::ArgsOs = env::args_os();
    if args.len() != 2 {
        println!("{} <file.gbc>", args.next().unwrap().into_string().unwrap());
        exit(1);
    }

    let _ = args.next().unwrap();
    let file_name: String = args.next().unwrap().into_string().unwrap();
    println!("Loading up {}...", file_name);

    let mut rom_file = match File::open(file_name) {
        Err(no_idea) => {panic!("Couldn't load file: {}", no_idea)},
        Ok(rom_file) => rom_file
    };

    let mut bytes = Vec::new();

    match rom_file.read_to_end(&mut bytes) {
        Err(why) => panic!("Failed: {}", why),
        Ok(_) => {}
    }

    let mut memory: mmu::Mmu = mmu::Mmu::new_with_init(65536, &bytes);
    let mut processor: cpu::Cpu = cpu::Cpu::new(&mut memory);

    processor.print_regs();
    loop {
        let instruction = processor.next();
        if !instruction.is_some() {
            break;
        }

        let instruction = instruction.unwrap();
        println!("{} ({} bytes)", instruction, instruction.bytes);
        processor.print_regs();
    }

    exit(0);
}
