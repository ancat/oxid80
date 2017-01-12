use std::vec::Vec;
use std::fs::File;
use std::io::Read;
use std::process::exit;
use std::env;

mod cpu;
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

    let mut processor: cpu::Cpu = cpu::Cpu::new(&bytes);

    for _ in 0..5 {
        let instruction = processor.consume_instruction();
        println!("{} ({} bytes)", instruction, instruction.bytes);
    }

    exit(0);
}
