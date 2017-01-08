use utils;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Register {
    None,
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

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let printable = match *self {
            Register::RegA => "A",
            Register::RegB => "B",
            Register::RegC => "C",
            Register::RegD => "D",
            Register::RegE => "E",
            Register::RegF => "F",
            Register::RegH => "H",
            Register::RegL => "L",
            Register::RegBC => "BC",
            Register::RegDE => "DE",
            Register::RegHL => "HL",
            Register::RegIX => "IX",
            Register::RegIY => "IY",
            Register::RegSP => "SP",
            Register::RegPC => "PC",
            Register::None  => panic!("Attempting to display an invalid register")
        };

        write!(f, "{}", printable)
    }
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

#[derive(Debug)]
pub struct Operand {
    mode: OperandType,
    value: u16,
    displacement: i16,
    register: Register,
}

impl Default for Operand {
    fn default() -> Operand {
        Operand {
            mode: OperandType::None,
            value: 0,
            displacement: 0,
            register: Register::None
        }
    }
}

#[derive(Debug, PartialEq)]
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

impl Instruction {
    fn format_memory(&self, operand: &Operand) -> String {
        let mut base = String::from("(");
        if operand.register != Register::None {
            base.push_str(&format!("{}", operand.register));
        } else {
            base.push_str(&format!("{}", operand.value));
        }

        if operand.displacement != 0 {
            if operand.displacement >= 0 {
                base.push_str(&format!("+{}",operand.displacement));
            } else {
                base.push_str(&format!("{}",operand.displacement)); // minus sign from the signed int
            }
        }
        base.push_str(")");

        base
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let opcode = &self.function;
        let value1: String = match self.operand1.mode {
            OperandType::Register => format!("{}", self.operand1.register),
            OperandType::Immediate => self.operand1.value.to_string(),
            OperandType::Memory => self.format_memory(&self.operand1),
            OperandType::None => format!("")
        };

        let value2: String = match self.operand2.mode {
            OperandType::Register => format!("{}", self.operand2.register),
            OperandType::Immediate => format!("{}", self.operand2.value),
            OperandType::Memory => self.format_memory(&self.operand2),
            OperandType::None => format!("")
        };

        return write!(f, "{:?} {}, {}", opcode, value1, value2);
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

    pub fn bogus_shit(&self) -> Instruction {
        let operand1 = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        let operand2 = Operand {
            mode: OperandType::Register,
            register: Register::RegB,
            ..Default::default()
        };

        Instruction {
            function: OpCode::ADC,
            operand1: operand1,
            operand2: operand2,
            bytes: 1,
            cycles: 2,
        }
    }

    pub fn consume_instruction(&mut self) -> Instruction {
        let instruction = self.fetch_instruction();
        self.reg_pc += instruction.bytes as u16;
        self.cycles += instruction.cycles as u64;
        instruction
    }

    pub fn fetch_instruction(&self) -> Instruction {
        // also: a bunch of ld instructions have the same starting byte
        let op = match self.peek_bytes(1) {
            Ok(e) => { e[0] },
            _ => panic!("out of bytes")
        };

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
            opcode => { panic!("unknown {:x}", opcode); }
        }
    }

    fn register_single_bitmask_to_enum(&self, mask: u8) -> Register {
        match mask {
            0b000 => { Register::RegB  },
            0b001 => { Register::RegC  },
            0b010 => { Register::RegD  },
            0b011 => { Register::RegE  },
            0b100 => { Register::RegH  },
            0b101 => { Register::RegL  },
            0b110 => { Register::RegHL },
            0b111 => { Register::RegA  },
            _     => { panic!("unknown single register bitmask {:?}", mask); }
        }
    }

    fn register_pair_bitmask_to_enum(&self, mask: u8) -> Register {
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
                mode: if dst == 0b110 { OperandType::Memory } else { OperandType::Register } ,
                register: self.register_single_bitmask_to_enum(dst),
                displacement: 0,
                ..Default::default()
            };

            let src = utils::extract_bits(opcode, 0b00000111);
            let src = Operand {
                mode: if src == 0b110 { OperandType::Memory } else { OperandType::Register } ,
                register: self.register_single_bitmask_to_enum(src),
                displacement: 0,
                ..Default::default()
            };

            Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 1, bytes: 2}
        } else if utils::extract_bits(opcode, 0b11000111) == 0b00000110 {
            // LD r, n
            let opcodes = self.peek_bytes(2).unwrap(); // this instruction is 2 bytes
            let dst = utils::extract_bits(opcodes[0], 0b00111000);
            let dst = Operand {
                mode: OperandType::Register,
                register: self.register_single_bitmask_to_enum(dst),
                ..Default::default()
            };

            let src = opcodes[1];
            let src = Operand {
                mode: OperandType::Immediate,
                value: src as u16,
                displacement: 0,
                ..Default::default()
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
                register: self.register_single_bitmask_to_enum(dst),
                displacement: 0,
                ..Default::default()
            };

            // handle IX, IY
            let src = match opcode {
                0b11011101 => { Register::RegIX },
                0b11111101 => { Register::RegIY },
                _ => { panic!("unknown register in ld"); }
            };
            let src = Operand {
                mode: OperandType::Memory,
                register: src,
                displacement: utils::u8_to_i16(displacement),
                ..Default::default()
            };

            Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 5, bytes: 3}
        } else {
            panic!("unknown ld {:x}", opcode);
        }

    }

    fn peek_bytes(&self, num_bytes: usize) -> Result<&[u8], CpuError> {
        if self.raw_bytes.len() as u16 -self.reg_pc < num_bytes as u16 {
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

