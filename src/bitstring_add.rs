//! This module implements addition on bitstrings represented as Vec<bool>
//! big-endian order
use vstd::prelude::*;

use vstd::math;
use vstd::slice::{slice_subrange, slice_to_vec};

verus! {

/// Checks if a slice is empty
fn is_empty(s: &[bool]) -> (result: bool)
    ensures result == (s.len() == 0)
{
    s.len() == 0
}

/// Finds the index of the first non-zero bit starting from a given position
fn find_first_nonzero(s: &[bool], start: usize) -> (i: usize)
    ensures
            i <= s.len()
    decreases
            s.len() - start
    {
    if start >= s.len() {
        s.len() // TODO Should it return a different value?
    } else if s[start] {
        start
    } else {
        find_first_nonzero(s, start + 1)
    }
}

/// Normalizes a bitstring by removing leading zeros
/// Returns a single zero bit if the input is all zeros or empty
pub fn normalize_bit_string(s: &[bool]) -> Vec<bool> {
    if is_empty(s) {
        vec![false]
    } else {
        let i = find_first_nonzero(s, 0);
        if i == s.len() {
            vec![false]
        } else {
            assert (0 <= i <= s.len());
            slice_to_vec(slice_subrange(s, i, s.len()))
        }
    }
}

/// Helper function for addition that handles the carry bit
/// Uses MSB order (most significant bit first)
fn add_helper(s1: &[bool], s2: &[bool], carry: u8) -> Vec<bool>
    requires carry == 1 || carry == 0
    decreases s1.len() + s2.len()
    {
    if is_empty(s1) && is_empty(s2) {
        if carry == 0 {
            vec![false]
        } else {
            vec![true]
        }
    } else {
        let bit1: u8 = if !is_empty(s1) && s1[s1.len() -1 ] { 1 } else { 0 };
        let rest1 = if !is_empty(s1) { slice_subrange(s1, 0,  s1.len()-1) } else { &[] };

        let bit2: u8 = if !is_empty(s2) && s2[s2.len() -1 ] { 1 } else { 0 };
        let rest2 = if !is_empty(s2) { slice_subrange(s2, 0, s2.len()-1) } else { &[] };

        let sum: u8 = bit1 + bit2 + carry;
        let new_bit: bool = sum % 2 == 1;
        let new_carry: u8 = sum / 2;

        let mut rest_result = add_helper(&rest1, &rest2, new_carry);
        rest_result.push(new_bit);
        rest_result
    }
}

/// Adds two bitstrings and returns their sum as a normalized bitstring
pub fn add(s1: &[bool], s2: &[bool]) -> Vec<bool> {
    if is_empty(s1) && is_empty(s2) {
        vec![false]
    } else if is_empty(s1) {
        normalize_bit_string(s2)
    } else if is_empty(s2) {
        normalize_bit_string(s1)
    } else {
        let intermediate = add_helper(s1, s2, 0);
        normalize_bit_string(&intermediate)
    }
}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_bit_string() {
        assert_eq!(normalize_bit_string(&[]), vec![false]);
        assert_eq!(normalize_bit_string(&[false, false]), vec![false]);
        assert_eq!(normalize_bit_string(&[false, true]), vec![true]);
        assert_eq!(
            normalize_bit_string(&[false, false, true, false]),
            vec![true, false]
        );
    }

    #[test]
    fn test_add() {
        // 0 + 0 = 0
        assert_eq!(add(&[false], &[false]), vec![false]);

        // 1 + 1 = 2
        assert_eq!(add(&[true], &[true]), vec![true, false]);

        // 2 + 0 = 0
        assert_eq!(add(&[true, false], &[]), vec![true, false]);

        // 2 + 0 = 0
        assert_eq!(add(&[true, false], &[false]), vec![true, false]);

        // 2 + 1 = 3
        assert_eq!(add(&[true, false], &[true]), vec![true, true]);

        // 5 + 3 = 8
        assert_eq!(
            add(&[true, false, true], &[true, true]),
            vec![true, false, false, false]
        );

        // Test with leading zeros
        // 0b01 + 0b1 = 0b10
        assert_eq!(add(&[false, true], &[true]), vec![true, false]);

        // Test with empty arrays
        assert_eq!(add(&[], &[true, true]), vec![true, true]);
        assert_eq!(add(&[true, false, true], &[]), vec![true, false, true]);
    }
}
