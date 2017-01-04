use utils;
use std::fmt;

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
#[derive(PartialEq)]
enum OperandType {
    Register,
    Memory,
    Immediate,
    None
}

/*
    If OperandType is Memory, then:
    value = register
    displacement = offset
    problem: what if the value is 0? that's register B!
*/
#[derive(Debug)]
pub struct Operand {
    mode: OperandType,
    value: u16, // needs to be able to hold a register and a value... what do
    displacement: u16,
}

#[derive(Debug)]
enum CpuError {
    OutOfBytes
}

pub struct Instruction {
    function: OpCode,
    operand1: Operand,
    operand2: Operand,
    cycles: i8,
    pub bytes: u8,
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let regs = ["B", "C", "D", "E", "H", "L", "(HL)", "A"];
        let opcode = &self.function;
        let operand1 = self.operand1.value.to_string();
        let operand2 = self.operand2.value.to_string();

        let operand1 = match self.operand1.mode {
            OperandType::Register => regs[self.operand1.value as usize],
            OperandType::Immediate => &operand1,
            _ => panic!("what's that"),
        };

        let operand2 = match self.operand2.mode {
            OperandType::Register => regs[self.operand2.value as usize],
            OperandType::Immediate => &operand2,
            _ => panic!("what's that"),
        };

        write!(f, "{:?} {}, {}", opcode, operand1, operand2)
    }
}

// TODO: wait a minute why am I storing the ram in the cpu? that don't make sense.
pub struct Cpu<'cool> {
    raw_bytes: &'cool [u8],
    reg_pc: u16,
    cycles: u64,
}

impl<'cool> Cpu<'cool> {
    pub fn new (raw_bytes: &[u8]) -> Cpu {
        Cpu {
            raw_bytes: raw_bytes,
            reg_pc: 0,
            cycles: 0,
        }
    }

    pub fn print_bytes(&self) {
        for i in 0..self.raw_bytes.len() {
            println!("here ya goooOO {}", self.raw_bytes[i]);
        }
    }

    pub fn consume_instruction(&mut self) -> () {
        let instruction = self.fetch_instruction();
        self.reg_pc += instruction.bytes as u16;
        self.cycles += instruction.cycles as u64;
    }

    pub fn fetch_instruction(&self) -> Instruction {
        //println!("reg_pc: {} <- {}", self.reg_pc, self.raw_bytes[self.reg_pc as usize]);
        // need to figure out how to test for instructions and return the instruction at the same time
        // also: a bunch of ld instructions have the same starting byte
        let op = self.peek_bytes(1).unwrap()[0];
        match op {
            op if utils::bitmask(op, 0b11000000) == 0b01000000 => { self.assemble_ld(op) }, // LD r, r'
            op if utils::bitmask(op, 0b11000111) == 0b00000110 => { self.assemble_ld(op) }, // LD r, n
            op if utils::bitmask(op, 0b11000111) == 0b01000110 => { self.assemble_ld(op) }, // LD r, (HL)
            op if utils::bitmask(op, 0b11111111) == 0b11011101 => { self.assemble_ld(op) }, // LD r, (IX+d)
            op if utils::bitmask(op, 0b11111111) == 0b11111101 => { self.assemble_ld(op) }, // LD r, (IY+d)
            op if utils::bitmask(op, 0b11111000) == 0b01110000 => { self.assemble_ld(op) }, // LD (HL), r
            op if utils::bitmask(op, 0b11111111) == 0b11011101 => { self.assemble_ld(op) }, // LD (IX+d), r
            op if utils::bitmask(op, 0b11111111) == 0b11111101 => { self.assemble_ld(op) }, // LD (IY+d), r
            op if utils::bitmask(op, 0b11111111) == 0b00110110 => { self.assemble_ld(op) }, // LD (HL), n
            op if utils::bitmask(op, 0b11111111) == 0b11011101 => { self.assemble_ld(op) }, // LD (IX+d), n
            op if utils::bitmask(op, 0b11111111) == 0b11111101 => { self.assemble_ld(op) }, // LD (IY+d), n
            op if utils::bitmask(op, 0b11111111) == 0b00001010 => { self.assemble_ld(op) }, // LD A, (BC)
            op if utils::bitmask(op, 0b11111111) == 0b00011010 => { self.assemble_ld(op) }, // LD A, (DE)
            op if utils::bitmask(op, 0b11111111) == 0b00111010 => { self.assemble_ld(op) }, // LD A, (nn)
            op if utils::bitmask(op, 0b11111111) == 0b00000010 => { self.assemble_ld(op) }, // LD (BC), A
            op if utils::bitmask(op, 0b11111111) == 0b00010010 => { self.assemble_ld(op) }, // LD (DE), A
            op if utils::bitmask(op, 0b11111111) == 0b00110010 => { self.assemble_ld(op) }, // LD (nn), A
            op if utils::bitmask(op, 0b11111111) == 0b11101101 => { self.assemble_ld(op) }, // LD A, I
            op if utils::bitmask(op, 0b11111111) == 0b11101101 => { self.assemble_ld(op) }, // LD A, R
            op if utils::bitmask(op, 0b11111111) == 0b11101101 => { self.assemble_ld(op) }, // LD I, A
            op if utils::bitmask(op, 0b11111111) == 0b11101101 => { self.assemble_ld(op) }, // LD R, A
            _ => { panic!("unknown"); }
        }
    }

    pub fn register_single_bitmask_to_enum(&self, mask: u8) -> Register {
        match mask {
            0b000 => { Register::RegB  },
            0b001 => { Register::RegC  },
            0b010 => { Register::RegD  },
            0b011 => { Register::RegE  },
            0b100 => { Register::RegH  },
            0b101 => { Register::RegL  },
            0b110 => { Register::RegHL },
            0b111 => { Register::RegA  },
            _     => { panic!("unknown single register bitmask"); }
        }
    }

    pub fn register_pair_bitmask_to_enum(&self, mask: u8) -> Register {
        match mask {
            0b00 => { Register::RegBC },
            0b01 => { Register::RegDE },
            0b10 => { Register::RegHL },
            0b11 => { Register::RegSP },
            _    => { panic!("unknown register pair bitmask"); }
        }
    }

    pub fn assemble_ld(&self, opcode: u8) -> Instruction {
        // Special exception for reg (HL) = 0b110
        if utils::extract_bits(opcode, 0b11000000) == 0b01 {
            // LD r, r'
            // LD r, (HL)
            let dst = utils::extract_bits(opcode, 0b00111000);
            let dst = Operand {
                mode: if dst == 0b110 { OperandType::Register } else { OperandType::Memory} ,
                value: self.register_single_bitmask_to_enum(dst),
                displacement: 0
            };

            let src = utils::extract_bits(opcode, 0b00000111);
            let src = Operand {
                mode: OperandType::Register,
                value: self.register_single_bitmask_to_enum(src),
                displacement: 0
            };

            Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 1, bytes: 1}
        } else if utils::extract_bits(opcode, 0b11000111) == 0b00000110 {
            // LD r, n
            let opcodes = self.peek_bytes(2).unwrap(); // this instruction is 2 bytes
            let dst = utils::extract_bits(opcodes[0], 0b00111000);
            let dst = Operand {
                mode: OperandType::Register,
                value: dst as u16,
                displacement: 0
            };

            let src = opcodes[1] as u16;
            let src = Operand {
                mode: OperandType::Immediate,
                value: self.register_single_bitmask_to_enum(src),
                displacement: 0
            };

            Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 2, bytes: 2}
        } else if opcode == 0b11011101 || opcode == 0b11111101 {
            // LD r, (IX+d)
            // LD r, (IY+d)
            let opcodes = self.peek_bytes(3).unwrap(); // this instruction is 3 bytes
            let displacement = opcodes[2];
            let dst = utils::extract_bits(opcodes[1], 0b00111000);
            let dst = Operand {
                mode: OperandType::Register,
                value: self.register_single_bitmask_to_enum(dst),
                displacement: 0
            };

            // handle IX, IY
            let src = match opcode {
                0b11011101 => { Register::RegIX },
                0b11111101 => { Register::RegIY },
                _ => { panic!("unknown register in ld"); }
            };
            let src = Operand {
                mode: OperandType::Register,
                value: src,
                displacement: displacement
            };

            Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 5, bytes: 3}
        } else {
            panic!("unknown ld {:x}", opcode);
        }

    }

    fn peek_bytes(&self, num_bytes: usize) -> Result<&[u8], CpuError> {
        if self.raw_bytes.len() <= num_bytes {
            return Err(CpuError::OutOfBytes);
        }

        let start = self.reg_pc as usize;
        let end = start + num_bytes;
        Ok(&self.raw_bytes[start..end])
    }

    fn consume_bytes(&mut self, num_bytes: usize) -> Result<&[u8], CpuError> {
        self.reg_pc += num_bytes as u16;
        self.peek_bytes(num_bytes)
    }
}

