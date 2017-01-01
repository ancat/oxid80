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

    let processor: cpu::Cpu = cpu::Cpu::new(&bytes);
    processor.consume_instruction();

    /*
    let mut offset = 0;
    let mut consumed = 0;
    while offset < bytes.len() {
        consumed = 1;
        match bytes[offset] {
            x if utils::extract_bits(x, 0b01) => {println!("virtual insanilty");},
            x if x & 0b01000000 != 0 => { println!("ld r, r' {:x} {:b} {:b}", x, (x&0b00111000)>>3, x&0b00000111); consumed = 1; },
            x if x == 0x31 => { println!("ld sp, {:x}{:x}", bytes[offset+1], bytes[offset+2]); consumed = 3; }
            _ => { println!("unimpl"); consumed = 1; }
        }

        //println!("bytes consumed: {}", consumed);
        offset += consumed;
    }
    */

    exit(0);
}
