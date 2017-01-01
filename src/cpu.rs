use std::fmt;
use std::vec::Vec;
use utils;

#[derive(Debug)]
enum Register {
    RegA,
    RegB,
    RegC,
    RegD,
    RegE,
    RegF,
    RegH,
    RegL,
    RegBC,
    RegDE,
    RegHL,
    RegIX,
    RegIY,
    RegSP,
    RegPC
}

#[derive(Debug)]
pub enum OpCode {
    LD,
    INC,
    DEC,
    ADD,
    ADC
}

#[derive(Debug)]
enum OperandType {
    Register,
    Memory,
    Immediate,
    None
}

#[derive(Debug)]
enum CpuError {
    OutOfBytes
}

pub struct Instruction {
    function: OpCode,
    operand_type1: OperandType,
    operand_type2: OperandType,
    cycles: i8,
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} {:?} {:?}", self.function, self.operand_type1, self.operand_type2)
    }
}

pub struct Cpu<'cool> {
    raw_bytes: &'cool [u8],
    reg_pc: u16
}

impl<'cool> Cpu<'cool> {
    pub fn new (raw_bytes: &[u8]) -> Cpu {
        Cpu {
            raw_bytes: raw_bytes,
            reg_pc: 0
        }
    }

    pub fn print_bytes(&self) {
        for i in 0..self.raw_bytes.len() {
            println!("here ya goooOO {}", self.raw_bytes[i]);
        }
    }

    pub fn consume_instruction(&self) -> Instruction {
        //println!("reg_pc: {} <- {}", self.reg_pc, self.raw_bytes[self.reg_pc as usize]);
        // need to figure out how to test for instructions and return the instruction at the same time
        let op = self.peek_bytes(1).unwrap()[0];
        match op {
            op if self.test_ld_r_r(op)  => { println!("LD r, r'"); },
            op if self.test_ld_r_n(op)  => { println!("LD r, n"); },
            op if self.test_ld_r_hl(op) => { println!("LD r, (HL)"); },
            _ => { println!("unknown"); }
        };

        Instruction {
            function: OpCode::ADD,
            operand_type1: OperandType::Register,
            operand_type2: OperandType::Register,
            cycles: 30
        }
    }

    fn peek_bytes(&self, num_bytes: usize) -> Result<&[u8], CpuError> {
        if self.raw_bytes.len() <= num_bytes {
            return Err(CpuError::OutOfBytes);
        }

        Ok(&self.raw_bytes[0..num_bytes])
    }

    fn consume_bytes(&mut self, num_bytes: usize) -> Result<&[u8], CpuError> {
        self.reg_pc += num_bytes as u16;
        self.peek_bytes(num_bytes)
    }

    fn test_ld_r_r(&self, opcode: u8) -> bool {
        let bytes = self.peek_bytes(1).unwrap();
        utils::extract_bits(bytes[0], 0b01000000) > 0
    }

    fn test_ld_r_n(&self, opcode: u8) -> bool {
        utils::extract_bits(opcode, 0b00000110) > 0
    }

    fn test_ld_r_hl(&self, opcode: u8) -> bool {
        utils::extract_bits(opcode, 0b00000110) > 0
    }

    fn test_ld_r_ix_d(&self, opcode: u8) -> bool {
        utils::extract_bits(opcode, 0b11011101) > 0
    }
}
/*
fn main() -> () {
    let ld: Instruction = Instruction {
        function: OpCode::ADD,
        operand_type1: OperandType::Register,
        operand_type2: OperandType::Register,
        cycles: 2
    };

    println!("byeeee! {}", ld);
}
*/
