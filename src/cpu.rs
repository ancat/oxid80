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
    RegI,
    RegR,
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
            Register::RegI => "I",
            Register::RegR => "R",
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
    ADC,
    NOP
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

        // TODO: all LD IX/IY instructions start with the same opcode. need to defer opcode
        // checking deeper into the disassembling stage
        match op {
            op if utils::bitmask(op, 0b11000000) == 0b01000000 => { self.assemble_ld_r_r(op) }, // LD r, r'
            op if utils::bitmask(op, 0b11000111) == 0b00000110 => { self.assemble_ld_r_n(op) }, // LD r, n
            op if utils::bitmask(op, 0b11000111) == 0b01000110 => { self.assemble_ld_r_hl(op) }, // LD r, (HL)
            op if utils::bitmask(op, 0b11111111) == 0b11011101 => { self.handle_prefixes(op) }, // LD r, (IX+d)
                                                                                                // LD IX, nn

            op if utils::bitmask(op, 0b11111111) == 0b11111101 => { self.handle_prefixes(op) }, // LD r, (IY+d)
                                                                                                // LD IY, nn
            op if utils::bitmask(op, 0b11111000) == 0b01110000 => { self.assemble_ld_hl_r(op) }, // LD (HL), r
            op if utils::bitmask(op, 0b11111111) == 0b00110110 => { self.assemble_ld_hl_n(op) }, // LD (HL), n
            op if utils::bitmask(op, 0b11111111) == 0b00001010 => { self.assemble_ld_a_rp(op) }, // LD A, (BC)
            op if utils::bitmask(op, 0b11111111) == 0b00011010 => { self.assemble_ld_a_rp(op) }, // LD A, (DE)
            op if utils::bitmask(op, 0b11111111) == 0b00111010 => { self.assemble_ld_a_nn(op) }, // LD A, (nn)
            op if utils::bitmask(op, 0b11111111) == 0b00000010 => { self.assemble_ld_rp_a(op) }, // LD (BC), A
            op if utils::bitmask(op, 0b11111111) == 0b00010010 => { self.assemble_ld_rp_a(op) }, // LD (DE), A
            op if utils::bitmask(op, 0b11111111) == 0b00110010 => { self.assemble_ld_nn_a(op) }, // LD (nn), A
            op if utils::bitmask(op, 0b11111111) == 0b11101101 => { self.handle_ed_prefix(op) }, // LD A, I
                                                                                                 // LD A, R
                                                                                                 // LD I, A
                                                                                                 // LD R, A
                                                                                                 // LD dd, (nn)

            op if utils::bitmask(op, 0b11001111) == 0b00000001 => { self.assemble_ld_dd_nn(op) }, // LD dd, nn
            op if utils::bitmask(op, 0b11111111) == 0b00101010 => { self.assemble_ld_hl_nn(op) }, // LD HL, (nn)

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

    fn assemble_ld_a_rp(&self, opcode: u8) -> Instruction {
        let src = match opcode {
            0x0a => { Register::RegBC },
            0x1a => { Register::RegDE },
            _ => { panic!("unknown byte for ld_a_rp instruction"); }
        };

        let src = Operand {
            mode: OperandType::Memory,
            register: src,
            ..Default::default()
        };

        let dst = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 2, bytes: 1, operand1: dst, operand2: src }
    }

    fn assemble_ld_rp_a(&self, opcode: u8) -> Instruction {
        let dst = match opcode {
            0x02 => { Register::RegBC },
            0x12 => { Register::RegDE },
            _ => { panic!("unknown byte for ld_rp_a instruction"); }
        };

        let dst = Operand {
            mode: OperandType::Memory,
            register: dst,
            ..Default::default()
        };

        let src = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 2, bytes: 1, operand1: dst, operand2: src }
    }

    fn assemble_ld_nn_a(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(3).expect("Expecting 3 bytes for LD (NN), A");
        let dst: u16 = ((opcodes[2] as u16) << 8) | (opcodes[1] as u16);
        let dst = Operand {
            mode: OperandType::Memory,
            value: dst,
            ..Default::default()
        };

        let src = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 4, bytes: 3, operand1: dst, operand2: src }
    }

    fn assemble_ld_hl_nn(&self, opcode: u8) -> Instruction {
        panic!("ld dd nn not implemented yet");
    }

    fn assemble_ld_dd_nn(&self, opcode: u8) -> Instruction {
        panic!("ld dd nn not implemented yet");
    }

    fn assemble_ld_a_nn(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(3).expect("Expecting 3 bytes for LD A, (NN)");
        let src: u16 = ((opcodes[2] as u16) << 8) | (opcodes[1] as u16);
        let src = Operand {
            mode: OperandType::Memory,
            value: src,
            ..Default::default()
        };

        let dst = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 4, bytes: 3, operand1: dst, operand2: src }
    }

    pub fn handle_ed_prefix(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(2).expect("Expecting 2 bytes for an ED prefixed instruction");
        let reg_a = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        // LD A, I = ED 57
        // LD A, R = ED 5F
        // LD I, A = ED 47
        // LD R, A = ED 4F
        // the direction (to A / from A) can be determined by the upper 4 bits of the 2nd byte
        // the other register (I, R) can be determined by the lower 4 bits of the 2nd byte

        // determine the other register
        let other_reg = match opcodes[1] & 0b1111 {
            0b0111 => Register::RegI,
            0b1111 => Register::RegR,
            _ => { panic!("couldn't determine the other register in ed prefixed instruction") }
        };

        let other_reg = Operand {
            mode: OperandType::Register,
            register: other_reg,
            ..Default::default()
        };

        // determine the direction
        match opcodes[1] & 0b11110000 {
            0b01010000 => { Instruction { function: OpCode::LD, cycles: 2, bytes: 2, operand1: reg_a, operand2: other_reg } },
            0b01000000 => { Instruction { function: OpCode::LD, cycles: 2, bytes: 2, operand1: other_reg, operand2: reg_a } },
            _ => { panic!("couldn't determine direction from bitmask in ed prefixed instruction") }
        }
    }

    pub fn handle_prefixes(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(2).expect("Expecting at least one more byte for dd/fd prefix");

        match opcodes[1] {
            0xdd => { self.assemble_nop() },
            0xfd => { self.assemble_nop() },
            0xcb => { panic!("unimplemented cb prefix"); },
            0x36 => { self.assemble_ld_ix_iy_n(opcode) },
            op if utils::bitmask(op, 0b11_000_111) == 0b01_000_110 => { self.assemble_ld_r_ix_iy(opcode) },
            op if utils::bitmask(op, 0b11_111_000) == 0b01_110_000 => { self.assemble_ld_ix_iy_r(opcode) },
            _    => { panic!("unknown prefix instruction"); }
        }
    }

    pub fn assemble_nop(&self) -> Instruction {
        let op1 = Operand { ..Default::default() }; // blank operand
        let op2 = Operand { ..Default::default() }; // blank operand
        Instruction { function: OpCode::NOP, cycles: 1, bytes: 1, operand1: op1, operand2: op2 }
    }

    pub fn assemble_ld_ix_iy_n(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(4).expect("expects 4 bytes");
        let prefix = opcodes[0];
        let displacement = opcodes[2];
        let immediate = opcodes[3];

        let src = Operand {
            mode: OperandType::Immediate,
            value: immediate as u16,
            ..Default::default()
        };

        let dst = match prefix {
            0xdd => { Register::RegIX },
            0xfd => { Register::RegIY },
            _ => { panic!("unknown register in ld ix iy n"); }
        };
        let dst = Operand {
            mode: OperandType::Memory,
            register: dst,
            displacement: utils::u8_to_i16(displacement),
            ..Default::default()
        };

        Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 5, bytes: 4 }
    }

    pub fn assemble_ld_r_r(&self, opcode: u8) -> Instruction {
        // LD r, r'
        // LD r, (HL)
        // LD (HL), r
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

        Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 1, bytes: 1}
    }

    pub fn assemble_ld_r_hl(&self, opcode: u8) -> Instruction {
        self.assemble_ld_r_r(opcode)
    }

    pub fn assemble_ld_hl_r(&self, opcode: u8) -> Instruction {
        self.assemble_ld_r_r(opcode)
    }

    pub fn assemble_ld_hl_n(&self, opcode: u8) -> Instruction {
        self.assemble_ld_r_n(opcode)
    }

    pub fn assemble_ld_r_n(&self, opcode: u8) -> Instruction {
        // LD r, n
        let opcodes = self.peek_bytes(2).unwrap(); // this instruction is 2 bytes
        let dst = utils::extract_bits(opcodes[0], 0b00111000);
        let dst = Operand {
            mode: if dst == 0b110 { OperandType::Memory } else { OperandType::Register },
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
    }

    pub fn assemble_ld_r_ix_iy(&self, opcode: u8) -> Instruction {
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
    }

    pub fn assemble_ld_ix_iy_r(&self, opcode: u8) -> Instruction {
        // LD (IX+d), r
        // LD (IY+d), r
        let opcodes = self.peek_bytes(3).unwrap(); // this instruction is 3 bytes
        let displacement = opcodes[2];
        let src = utils::extract_bits(opcodes[1], 0b00000111);
        let src = Operand {
            mode: OperandType::Register,
            register: self.register_single_bitmask_to_enum(src),
            displacement: 0,
            ..Default::default()
        };

        // handle IX, IY
        let dst = match opcode {
            0b11011101 => { Register::RegIX },
            0b11111101 => { Register::RegIY },
            _ => { panic!("unknown register in ld"); }
        };
        let dst = Operand {
            mode: OperandType::Memory,
            register: dst,
            displacement: utils::u8_to_i16(displacement),
            ..Default::default()
        };

        Instruction { function: OpCode::LD, operand1: dst, operand2: src, cycles: 5, bytes: 3}
    }

    pub fn assemble_ld(&self, opcode: u8) -> Instruction {
        panic!("unknown ld {:x}", opcode);
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

#[cfg(test)]
mod tests {
    use cpu::Cpu;
    #[test]
    fn test_ld_r_r() {
        let bytes = vec![0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x70];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, B");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, C");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, D");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, E");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, H");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, L");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, (HL)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (HL), B");
    }

    #[test]
    fn test_ld_r_n() {
        let bytes = vec![0x16, 0x32, 0x16, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD D, 50");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD D, 127");
    }

    #[test]
    fn test_ld_r_ix_iy() {
        let bytes = vec![0xdd, 0x46, 0xff, 0xdd, 0x46, 0x7f, 0xfd, 0x46, 0xff, 0xfd, 0x46, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, (IX-1)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, (IX+127)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, (IY-1)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD B, (IY+127)");
    }

    #[test]
    fn test_ld_ix_iy_r() {
        let bytes = vec![0xdd, 0x77, 0x7f, 0xfd, 0x77, 0x7f, 0xdd, 0x77, 0xff, 0xfd, 0x77, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IX+127), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IY+127), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IX-1), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IY-1), A");
    }

    #[test]
    fn test_ld_hl_n() {
        let bytes = vec![0x36, 0xff, 0x36, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (HL), 255");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (HL), 127");
    }

    #[test]
    fn test_ld_ix_iy_n() {
        let bytes = vec![0xdd, 0x36, 0xff, 0xff, 0xfd, 0x36, 0x7f, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IX-1), 255");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (IY+127), 255");
    }

    #[test]
    fn test_ld_a_rp() {
        let bytes = vec![0x0a, 0x1a];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, (BC)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, (DE)");
    }

    #[test]
    fn test_ld_rp_a() {
        let bytes = vec![0x02, 0x12];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (BC), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (DE), A");
    }

    #[test]
    fn test_ld_a_nn() {
        let bytes = vec![0x3a, 0x41, 0x41, 0x3a, 0x0, 0x0, 0x3a, 0xff, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, (16705)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, (0)");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, (65535)");
    }

    #[test]
    fn test_ld_nn_a() {
        let bytes = vec![0x32, 0x41, 0x41, 0x32, 0x0, 0x0, 0x32, 0xff, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (16705), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (0), A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD (65535), A");
    }

    #[test]
    fn test_handle_ed_prefix() {
        let bytes = vec![0xed, 0x57, 0xed, 0x5f, 0xed, 0x47, 0xed, 0x4f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, I");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD A, R");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD I, A");
        assert_eq!(format!("{}", processor.consume_instruction()), "LD R, A");
    }
}
