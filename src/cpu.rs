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

#[derive(Debug, PartialEq)]
pub enum OpCode {
    LD,
    INC,
    DEC,
    ADD,
    ADC,
    NOP
}

#[derive(Debug, PartialEq)]
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
    pub bytes: usize,
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
    reg_a: u8,
    reg_b: u8,
    reg_c: u8,
    reg_d: u8,
    reg_e: u8,
    reg_f: u8,
    reg_h: u8,
    reg_l: u8,
    reg_i: u8,
    reg_r: u8,
    reg_bc: u16,
    reg_de: u16,
    reg_hl: u16,
    reg_ix: u16,
    reg_iy: u16,
    reg_sp: u16,
    cycles: u64,
}

impl<'cool> Iterator for Cpu<'cool> {
    type Item = Instruction;

    fn next(&mut self) -> Option<Instruction> {
        match self.fetch_instruction() {
            Ok(instr) => { self.consume_instruction(&instr); Some(instr) },
            Err(e) => { None }
        }
    }
}

impl<'cool> Cpu<'cool> {
    pub fn new (raw_bytes: &[u8]) -> Cpu {
        Cpu {
            raw_bytes: raw_bytes,
            reg_pc: 0,
            reg_a: 0,
            reg_b: 0,
            reg_c: 0,
            reg_d: 0,
            reg_e: 0,
            reg_f: 0,
            reg_h: 0,
            reg_l: 0,
            reg_i: 0,
            reg_r: 0,
            reg_bc: 0,
            reg_de: 0,
            reg_hl: 0,
            reg_ix: 0,
            reg_iy: 0,
            reg_sp: 0,
            cycles: 0,
        }
    }

    pub fn consume_instruction<'wat> (&mut self, instruction: &'wat Instruction) -> &'wat Instruction {
        /*
            it's alive!

            reg_a: 0; reg_b: 0; reg_c: 0;
            LD A, 65 (2 bytes)
            reg_a: 41; reg_b: 0; reg_c: 0;
            LD B, A (1 bytes)
            reg_a: 41; reg_b: 41; reg_c: 0;
            LD C, B (1 bytes)
            reg_a: 41; reg_b: 41; reg_c: 41;
            LD A, 0 (2 bytes)
            reg_a: 0; reg_b: 41; reg_c: 41;
        */
        if instruction.function == OpCode::LD {
            let operand1 = &instruction.operand1;
            let operand2 = &instruction.operand2;
            let src;

            if operand2.mode == OperandType::Register {
                src = match operand2.register {
                    Register::RegA => { self.reg_a },
                    Register::RegB => { self.reg_b },
                    Register::RegC => { self.reg_c },
                    _ => { 420 }
                };
            } else if operand2.mode == OperandType::Immediate {
                src = operand2.value as u8;
            } else {
                src = 421;
            }

            if operand1.mode == OperandType::Register {
                match operand1.register {
                    Register::RegA => { self.reg_a = src; },
                    Register::RegB => { self.reg_b = src; },
                    Register::RegC => { self.reg_c = src; },
                    _ => { 420; }
                };
            }
        } else if instruction.function == OpCode::ADD {
            // TODO: flags
            let operand1 = &instruction.operand1;
            let operand2 = &instruction.operand2;

            let src = match operand2.mode {
                OperandType::Immediate => operand2.value as u8,
                OperandType::Register => match operand2.register {
                    Register::RegA => { self.reg_a },
                    Register::RegB => { self.reg_b },
                    Register::RegC => { self.reg_c },
                    _ => { 42 } // blaze it
                },
                OperandType::Memory => 42,
                _ => panic!("unsupported")
            };

            if operand1.mode == OperandType::Register {
                match operand1.register {
                    Register::RegA => { self.reg_a += src; },
                    Register::RegB => { self.reg_b += src; },
                    Register::RegC => { self.reg_c += src; },
                    _ => { 42; } // blaze it
                };
            }
        } else {
            panic!("can't execute dis {:?}", instruction.function);
        }

        self.reg_pc += instruction.bytes as u16;
        self.cycles += instruction.cycles as u64;
        instruction
    }

    pub fn print_regs(&self) -> () {
        println!("reg_a: {:x}; reg_b: {:x}; reg_c: {:x};", self.reg_a, self.reg_b, self.reg_c);
    }

    pub fn fetch_instruction(&self) -> Result<Instruction, CpuError> {
        // also: a bunch of ld instructions have the same starting byte
        let op = self.peek_bytes(1);
        if !op.is_ok() {
            return Err(CpuError::OutOfBytes);
        }

        let op = op.unwrap()[0];

        // TODO: make all ed/dd/fd prefixed instructions call the non-prefixed functions
        // but with a flag so we know it's prefixed (if flag, use IX/IY instead...)
        let parsed_instruction: Instruction = match op {
            op if utils::bitmask(op, 0b11000000) == 0b01000000 => { self.assemble_ld_r_r(op) }, // LD r, r'
            op if utils::bitmask(op, 0b11000111) == 0b00000110 => { self.assemble_ld_r_n(op) }, // LD r, n
            op if utils::bitmask(op, 0b11000111) == 0b01000110 => { self.assemble_ld_r_hl(op) }, // LD r, (HL)
            op if utils::bitmask(op, 0b11111111) == 0b11011101 => { self.handle_dd_fd_prefixes(op) }, // LD r, (IX+d)
                                                                                                // LD IX, nn

            op if utils::bitmask(op, 0b11111111) == 0b11111101 => { self.handle_dd_fd_prefixes(op) }, // LD r, (IY+d)
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
            op if utils::bitmask(op, 0b11111111) == 0b00100010 => { self.assemble_nn_mem_hl(op) },

            op if utils::bitmask(op, 0b11111000) == 0b10000000 => { self.assemble_add_a_r(op) },
            op if utils::bitmask(op, 0b11111111) == 0b11000110 => { self.assemble_add_a_n(op) },
            opcode => { panic!("unknown {:x}", opcode); }
        };

        Ok(parsed_instruction)
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

    fn assemble_nn_mem_hl(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(3).expect("Expecting 3 bytes for LD HL, (nn)");

        let dst: u16 = ((opcodes[2] as u16) << 8) | (opcodes[1] as u16);
        let dst = Operand {
            mode: OperandType::Memory,
            value: dst,
            ..Default::default()
        };

        let src = Operand {
            mode: OperandType::Register,
            register: Register::RegHL,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 5, bytes: 3, operand1: dst, operand2: src }
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
        let opcodes = self.peek_bytes(3).expect("Expecting 3 bytes for LD HL, (nn)");
        let dst = Operand {
            mode: OperandType::Register,
            register: Register::RegHL,
            ..Default::default()
        };

        let src: u16 = ((opcodes[2] as u16) << 8) | (opcodes[1] as u16);
        let src = Operand {
            mode: OperandType::Memory,
            value: src,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 5, bytes: 3, operand1: dst, operand2: src }
    }

    fn assemble_ld_dd_nn(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(3).expect("Expecting 3 bytes for LD dd, nn");
        let dst = utils::extract_bits(opcodes[0], 0b00110000);
        let dst = self.register_pair_bitmask_to_enum(dst);
        let dst = Operand {
            mode: OperandType::Register,
            register: dst,
            ..Default::default()
        };

        let src: u16 = ((opcodes[2] as u16) << 8) | (opcodes[1] as u16);
        let src = Operand {
            mode: OperandType::Immediate,
            value: src,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 2, bytes: 3, operand1: dst, operand2: src }
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
        match opcodes[1]  {
            opcode if opcodes[1] & 0b11001111 == 0b01001011 => { self.assemble_ld_dd_nn_mem(opcode) },
            _ => self.handle_ld_a_i_r(opcode)
        }
    }

    pub fn assemble_ld_dd_nn_mem(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(4).expect("Expecting 3 bytes for LD dd, (nn)");
        let dst = utils::extract_bits(opcodes[1], 0b00110000);
        let dst = self.register_pair_bitmask_to_enum(dst);
        let dst = Operand {
            mode: OperandType::Register,
            register: dst,
            ..Default::default()
        };

        let src: u16 = ((opcodes[3] as u16) << 8) | (opcodes[2] as u16);
        let src = Operand {
            mode: OperandType::Memory,
            value: src,
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 6, bytes: 4, operand1: dst, operand2: src }
    }

    pub fn handle_ld_a_i_r(&self, opcode: u8) -> Instruction {
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

    pub fn handle_dd_fd_prefixes(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(2).expect("Expecting at least one more byte for dd/fd prefix");

        match opcodes[1] {
            0xdd => { self.assemble_nop() },
            0xfd => { self.assemble_nop() },
            0xcb => { panic!("unimplemented cb prefix"); },
            0x36 => { self.assemble_ld_ix_iy_n(opcode) },
            0x21 => { self.assemble_ld_ix_iy_nn(opcode) },
            0x2a => { self.assemble_ld_ix_iy_nn_mem(opcode) },
            op if utils::bitmask(op, 0b11_000_111) == 0b01_000_110 => { self.assemble_ld_r_ix_iy(opcode) },
            op if utils::bitmask(op, 0b11_111_000) == 0b01_110_000 => { self.assemble_ld_ix_iy_r(opcode) },
            whatsthis    => { panic!("unknown byte for dd prefix: {:x}", whatsthis); }
        }
    }

    pub fn assemble_ld_ix_iy_nn_mem(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(4).expect("expects 4 bytes");

        let dst = match opcodes[0] {
            0xdd => Register::RegIX,
            0xfd => Register::RegIY,
            byte => panic!("unknown instruction 0x{:x} in ld_ix_iy_nn_mem", byte)
        };
        let dst = Operand {
            mode: OperandType::Register,
            register: dst,
            ..Default::default()
        };

        let src = Operand {
            mode: OperandType::Memory,
            value: ((opcodes[3] as u16) << 8) | (opcodes[2] as u16),
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 6, bytes: 4, operand1: dst, operand2: src }
    }

    pub fn assemble_ld_ix_iy_nn(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(4).expect("expects 4 bytes");

        let dst = match opcodes[0] {
            0xdd => Register::RegIX,
            0xfd => Register::RegIY,
            byte => panic!("unknown instruction 0x{:x} in ld_ix_iy_nn", byte)
        };
        let dst = Operand {
            mode: OperandType::Register,
            register: dst,
            ..Default::default()
        };

        let src = Operand {
            mode: OperandType::Immediate,
            value: ((opcodes[3] as u16) << 8) | (opcodes[2] as u16),
            ..Default::default()
        };

        Instruction { function: OpCode::LD, cycles: 4, bytes: 4, operand1: dst, operand2: src }
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

    pub fn assemble_add_a_r(&self, opcode: u8) -> Instruction {
        let src = opcode & 0b111;
        let src = Operand {
            mode: OperandType::Register,
            register: self.register_single_bitmask_to_enum(src),
            ..Default::default()
        };

        let dst = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        return Instruction { function: OpCode::ADD, operand1: dst, operand2: src, cycles: 1, bytes: 1 }
    }

    pub fn assemble_add_a_n(&self, opcode: u8) -> Instruction {
        let opcodes = self.peek_bytes(2).unwrap();
        let src = opcodes[1] as u16;
        let src = Operand {
            mode: OperandType::Immediate,
            value: src,
            ..Default::default()
        };

        let dst = Operand {
            mode: OperandType::Register,
            register: Register::RegA,
            ..Default::default()
        };

        return Instruction { function: OpCode::ADD, operand1: dst, operand2: src, cycles: 2, bytes: 2 }
    }

    pub fn assemble_ld(&self, opcode: u8) -> Instruction {
        panic!("unknown ld {:x}", opcode);
    }

    fn peek_bytes(&self, num_bytes: usize) -> Result<&[u8], CpuError> {
        // println!("PEEK: {:x} - {:x} < {:x}", self.raw_bytes.len() as u16, self.reg_pc, num_bytes as u16);
        if self.raw_bytes.len() as u16 -self.reg_pc < num_bytes as u16 {
            return Err(CpuError::OutOfBytes);
        }

        let start = self.reg_pc as usize;
        let end = start + num_bytes;
        Ok(&self.raw_bytes[start..end])
    }
}

#[cfg(test)]
mod tests {
    use cpu::Cpu;
    #[test]
    fn test_ld_r_r() {
        let bytes = vec![0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x70];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, B");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, C");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, D");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, E");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, H");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, L");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, (HL)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (HL), B");
    }

    #[test]
    fn test_ld_r_n() {
        let bytes = vec![0x16, 0x32, 0x16, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD D, 50");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD D, 127");
    }

    #[test]
    fn test_ld_r_ix_iy() {
        let bytes = vec![0xdd, 0x46, 0xff, 0xdd, 0x46, 0x7f, 0xfd, 0x46, 0xff, 0xfd, 0x46, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, (IX-1)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, (IX+127)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, (IY-1)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD B, (IY+127)");
    }

    #[test]
    fn test_ld_ix_iy_r() {
        let bytes = vec![0xdd, 0x77, 0x7f, 0xfd, 0x77, 0x7f, 0xdd, 0x77, 0xff, 0xfd, 0x77, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IX+127), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IY+127), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IX-1), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IY-1), A");
    }

    #[test]
    fn test_ld_hl_n() {
        let bytes = vec![0x36, 0xff, 0x36, 0x7f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (HL), 255");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (HL), 127");
    }

    #[test]
    fn test_ld_ix_iy_n() {
        let bytes = vec![0xdd, 0x36, 0xff, 0xff, 0xfd, 0x36, 0x7f, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IX-1), 255");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (IY+127), 255");
    }

    #[test]
    fn test_ld_a_rp() {
        let bytes = vec![0x0a, 0x1a];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, (BC)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, (DE)");
    }

    #[test]
    fn test_ld_rp_a() {
        let bytes = vec![0x02, 0x12];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (BC), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (DE), A");
    }

    #[test]
    fn test_ld_a_nn() {
        let bytes = vec![0x3a, 0x41, 0x41, 0x3a, 0x0, 0x0, 0x3a, 0xff, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, (16705)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, (0)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, (65535)");
    }

    #[test]
    fn test_ld_nn_a() {
        let bytes = vec![0x32, 0x41, 0x41, 0x32, 0x0, 0x0, 0x32, 0xff, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (16705), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (0), A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (65535), A");
    }

    #[test]
    fn test_handle_ed_prefix() {
        let bytes = vec![0xed, 0x57, 0xed, 0x5f, 0xed, 0x47, 0xed, 0x4f];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, I");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD A, R");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD I, A");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD R, A");
    }

    #[test]
    fn test_assemble_ld_dd_nn() {
        let bytes = vec![0x31, 0x41, 0x41, 0x21, 0xff, 0xff];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD SP, 16705");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD HL, 65535");
    }

    #[test]
    fn test_assemble_ld_ix_iy_nn() {
        let bytes = vec![0xdd, 0x21, 0x41, 0x41, 0xdd, 0x21, 0xff, 0xff, 0xfd, 0x21, 0xff, 0xff, 0xfd, 0x21, 0x00, 0x00];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IX, 16705");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IX, 65535");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IY, 65535");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IY, 0");
    }

    #[test]
    fn test_assemble_ld_hl_nn() {
        let bytes = vec![0x2a, 0x41, 0x41, 0x2a, 0x00, 0x00];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD HL, (16705)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD HL, (0)");
    }

    #[test]
    fn test_handle_ed_dd_nn() {
        let bytes = vec![0xed, 0x7b, 0x00, 0x00, 0xed, 0x6b, 0x11, 0x22];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD SP, (0)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD HL, (8721)");
    }

    #[test]
    fn test_assemble_dd_ix_nn() {
        let bytes = vec![0xdd, 0x2a, 0x00, 0x00, 0xfd, 0x2a, 0x01, 0x00];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IX, (0)");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD IY, (1)");
    }

    #[test]
    fn test_ld_nn_mem_hl() {
        let bytes = vec![0x22, 0x01, 0x00, 0x22, 0x00, 0x00];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (1), HL");
        assert_eq!(format!("{}", processor.next().unwrap()), "LD (0), HL");
    }

    #[test]
    fn test_add_a_r() {
        let bytes = vec![0x80, 0x87];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "ADD A, B");
        assert_eq!(format!("{}", processor.next().unwrap()), "ADD A, A");
    }

    #[test]
    fn test_add_a_n() {
        let bytes = vec![0xc6, 0x41];
        let mut processor: Cpu = Cpu::new(&bytes);
        assert_eq!(format!("{}", processor.next().unwrap()), "ADD A, 65");
    }
}
