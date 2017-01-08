pub fn extract_bits(byte: u8, bitmask: u8) -> u8 {
    let mut i_value = byte & bitmask;
    let mut i_bitmask = bitmask;

    while i_bitmask != 0 && (i_bitmask & 0b1) == 0 {
        i_value = i_value >> 1;
        i_bitmask = i_bitmask >> 1;
    }

    return i_value;
}

pub fn bitmask(byte: u8, bitmask: u8) -> u8 {
    byte & bitmask
}

pub fn bits_set(byte: u8, bitmask: u8) -> bool {
    (byte & bitmask) == bitmask
}

pub fn u8_to_i16(byte: u8) -> i16 {
    byte as i8 as i16
}
