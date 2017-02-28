use utils;
use std::fmt;

pub struct Mmu {
    raw_bytes: Vec<u8>,
}

impl Mmu {
    pub fn new(size: usize) -> Mmu {
        Mmu {
            raw_bytes: vec![0; size]
        }
    }

    pub fn new_with_init(size: usize, data: &[u8]) -> Mmu {
        let mut mmu = Mmu::new(size);
        for i in 0..data.len() {
            mmu.write_u8(i as u16, data[i]);
        }

        mmu
    }

    pub fn read_u8(&self, address: u16) -> u8 {
        self.raw_bytes[address as usize]
    }

    pub fn read_u8_many(&self, address: u16, amount: usize) -> &[u8] {
        let address = address as usize;
        &self.raw_bytes[address..address+amount]
    }

    pub fn write_u8(&mut self, address: u16, data: u8) -> () {
        self.raw_bytes[address as usize] = data;
    }

    pub fn read_u16(&self, address: u16) -> u16 {
        let lower = self.raw_bytes[address as usize] as u16;
        let upper = self.raw_bytes[(address+1) as usize] as u16;
        (upper << 8) | lower
    }

    pub fn write_u16(&mut self, address: u16, data: u16) -> () {
        let lower = (data & 0xFF) as u8;
        let upper = ((data & 0xFF00) >> 8) as u8;
        self.raw_bytes[address as usize] = lower;
        self.raw_bytes[(address+1) as usize] = upper;
    }
}

#[cfg(test)]
mod tests {
    use mmu::Mmu;

    #[test]
    fn test_read_write_u8() {
        let mut memory: Mmu = Mmu::new(65536);
        assert_eq!(0, memory.read_u8(0x1337));
        memory.write_u8(0x1337, 0x01);
        assert_eq!(1, memory.read_u8(0x1337));
    }

    #[test]
    fn test_read_write_u16() {
        let mut memory: Mmu = Mmu::new(65536);
        assert_eq!(0, memory.read_u16(0x1337));
        memory.write_u16(0x1337, 0x1122);
        assert_eq!(0x1122, memory.read_u16(0x1337));
    }

    #[test]
    fn test_endianness() {
        let mut memory: Mmu = Mmu::new(65536);
        memory.write_u16(0x1337, 0x1122);
        assert_eq!(0x22, memory.read_u8(0x1337));
        assert_eq!(0x11, memory.read_u8(0x1338));
    }

    #[test]
    fn test_read_u8_many() {
        let mut memory: Mmu = Mmu::new(65536);
        for i in 0..10 {
            memory.write_u8(0x0000 + i, i as u8);
        }

        let read_bytes = memory.read_u8_many(0x0000, 10);
        for i in 0..read_bytes.len() {
            assert_eq!(i as u8, read_bytes[i]);
        }
    }
}
