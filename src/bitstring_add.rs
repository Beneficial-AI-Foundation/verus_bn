/// This module implements addition on bitstrings represented as Vec<bool>
/// The algorithm is based on the one in bn_add_seq_bool.rs but without Verus-specific code

/// Converts a bitstring (Vec<bool>) to its integer value
pub fn str_to_int(s: &[bool]) -> u128 {
    if s.is_empty() {
        0
    } else {
        let sub_seq = &s[0..s.len() - 1];
        let last_bit = s[s.len() - 1];
        2 * str_to_int(sub_seq) + if last_bit { 1 } else { 0 }
    }
}

/// Finds the index of the first non-zero bit starting from a given position
fn find_first_nonzero(s: &[bool], start: usize) -> usize {
    if start >= s.len() {
        s.len()
    } else if s[start] {
        start
    } else {
        find_first_nonzero(s, start + 1)
    }
}

/// Normalizes a bitstring by removing leading zeros
/// Returns a single zero bit if the input is all zeros or empty
pub fn normalize_bit_string(s: &[bool]) -> Vec<bool> {
    if s.is_empty() {
        vec![false]
    } else {
        let i = find_first_nonzero(s, 0);
        if i == s.len() {
            vec![false]
        } else {
            s[i..].to_vec()
        }
    }
}

/// Helper function for addition that handles the carry bit
fn add_helper(s1: &[bool], s2: &[bool], carry: u8) -> Vec<bool> {
    if s1.is_empty() && s2.is_empty() {
        if carry == 0 {
            vec![false]
        } else {
            vec![true]
        }
    } else {
        let bit1: u8 = if !s1.is_empty() && s1[s1.len() - 1] { 1 } else { 0 };
        let rest1 = if !s1.is_empty() { &s1[0..s1.len() - 1] } else { &[] };

        let bit2: u8 = if !s2.is_empty() && s2[s2.len() - 1] { 1 } else { 0 };
        let rest2 = if !s2.is_empty() { &s2[0..s2.len() - 1] } else { &[] };

        let sum: u8 = bit1 + bit2 + carry;
        let new_bit: bool = sum % 2 == 1;
        let new_carry: u8 = sum / 2;

        let mut result = add_helper(rest1, rest2, new_carry);
        result.push(new_bit);
        result
    }
}

/// Adds two bitstrings and returns their sum as a normalized bitstring
pub fn add(s1: &[bool], s2: &[bool]) -> Vec<bool> {
    if s1.is_empty() && s2.is_empty() {
        vec![false]
    } else if s1.is_empty() {
        normalize_bit_string(s2)
    } else if s2.is_empty() {
        normalize_bit_string(s1)
    } else {
        let intermediate = add_helper(s1, s2, 0);
        normalize_bit_string(&intermediate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_str_to_int() {
        assert_eq!(str_to_int(&[]), 0);
        assert_eq!(str_to_int(&[false]), 0);
        assert_eq!(str_to_int(&[true]), 1);
        assert_eq!(str_to_int(&[true, false]), 2);
        assert_eq!(str_to_int(&[true, true]), 3);
        assert_eq!(str_to_int(&[true, false, true]), 5);
    }

    #[test]
    fn test_normalize_bit_string() {
        assert_eq!(normalize_bit_string(&[]), vec![false]);
        assert_eq!(normalize_bit_string(&[false, false]), vec![false]);
        assert_eq!(normalize_bit_string(&[false, true]), vec![true]);
        assert_eq!(normalize_bit_string(&[false, false, true, false]), vec![true, false]);
    }

    #[test]
    fn test_add() {
        // 0 + 0 = 0
        assert_eq!(add(&[false], &[false]), vec![false]);
        
        // 1 + 1 = 2
        assert_eq!(add(&[true], &[true]), vec![true, false]);
        
        // 2 + 1 = 3
        assert_eq!(add(&[false, true], &[true]), vec![true, true]);
        
        // 5 + 3 = 8
        assert_eq!(add(&[true, false, true], &[true, true]), vec![true, false, false, false]);
        
        // Test with leading zeros
        assert_eq!(add(&[false, true], &[true]), vec![true, true]);
        
        // Test with empty arrays
        assert_eq!(add(&[], &[true, true]), vec![true, true]);
        assert_eq!(add(&[true, false, true], &[]), vec![true, false, true]);
    }
}
