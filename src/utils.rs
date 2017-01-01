pub fn extract_bits(byte: u8, bitmask: u8) -> u8 {
    let mut i_value = byte & bitmask;
    let mut i_bitmask = bitmask;

    while i_bitmask != 0 && (i_bitmask & 0b1) == 0 {
        i_value = i_value >> 1;
        i_bitmask = i_bitmask >> 1;
    }

    return i_value;
}
