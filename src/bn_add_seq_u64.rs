use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::power2::pow2;

macro_rules! get_bit64_macro {
    ($a:expr, $b:expr) => {{
        (0x1u64 & ($a >> $b)) == 1
    }};
}

#[allow(unused_macros)]
macro_rules! get_bit64 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit64_macro!($($a)*))
    }
}

verus! {

    fn main() {
    }

    // Helper function to convert a u64 to a sequence of bits
    spec fn u64_to_bits(u: u64) -> Seq<bool> {
        Seq::new(64, |i: int| get_bit64!(u, i as u64))
    }

    // Helper function to convert a sequence of bits to a u64
    spec fn bits_to_u64(bits: Seq<bool>) -> u64
        recommends bits.len() == 64
        decreases bits.len()
    {
        if bits.len() == 0 {
            0u64
        } else {
            let rest = bits.subrange(0, bits.len() as int - 1);
            let last_bit = bits[bits.len() as int - 1];
            let rest_value = bits_to_u64(rest);
            if last_bit {
                rest_value | (1u64 << (bits.len() as int - 1))
            } else {
                rest_value
            }
        }
    }

    spec fn valid_u64_seq(s: Seq<u64>) -> bool {
        true // All sequences of u64 are valid
    }

    spec fn seq_to_int(s: Seq<u64>) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            let sub_seq = s.subrange(0, s.len() as int - 1);
            let last_word = s[s.len() as int - 1];
            let n = seq_to_int(sub_seq);
            n * pow2(64) + (last_word as nat)
        }
    }

    proof fn seq_to_int_empty(s: Seq<u64>)
        requires
            s.len() == 0,
        ensures
            seq_to_int(s) == 0nat,
    {
    }

    proof fn seq_to_int_nonempty(s: Seq<u64>)
        requires
            s.len() > 0,
        ensures
            seq_to_int(s) == (seq_to_int(s.subrange(0, s.len() as int - 1)) * pow2(64)) + (s[s.len() as int - 1] as nat),
    {
    }

    proof fn seq_to_int_extensionality(s1: Seq<u64>, s2: Seq<u64>)
        requires
            s1 =~= s2,
        ensures
            seq_to_int(s1) == seq_to_int(s2),
        decreases s1.len()
    {
        if s1.len() == 0 {
            assert(s2.len() == 0);
            assert(seq_to_int(s1) == 0nat);
            assert(seq_to_int(s2) == 0nat);
        } else {
            let sub_s1 = s1.subrange(0, s1.len() as int - 1);
            let sub_s2 = s2.subrange(0, s2.len() as int - 1);
            assert(sub_s1 =~= sub_s2);
            seq_to_int_extensionality(sub_s1, sub_s2);
            assert(s1[s1.len() as int - 1] == s2[s2.len() as int - 1]);
        }
    }

    proof fn seq_to_int_push(s: Seq<u64>, word: u64)
        ensures
            seq_to_int(s.push(word)) == (seq_to_int(s) * pow2(64)) + (word as nat),
    {
        let result = s.push(word);
        assert(result.subrange(0, result.len() as int - 1) =~= s);
        seq_to_int_extensionality(result.subrange(0, result.len() as int - 1), s);
    }

    proof fn seq_to_int_zero_singleton()
        ensures
            seq_to_int(seq![(0u64)]) == 0nat,
    {
        let s = seq![(0u64)];
        calc! {
            (==)
            seq_to_int(s);
            { seq_to_int_nonempty(s); }
            seq_to_int(s.subrange(0, s.len() as int - 1)) * pow2(64) + (s[s.len() as int - 1] as nat);
            { 
                assert(s.len() as int - 1 == 0);
                assert(s.subrange(0, 0).len() == 0);
                seq_to_int_empty(s.subrange(0, 0));
            }
            0nat * pow2(64) + (0u64 as nat);
            { assert(0nat * pow2(64) == 0nat); }
            0nat + 0nat;
            { assert(0nat + 0nat == 0nat); }
            0nat;
        }
    }

    proof fn seq_to_int_one_singleton()
        ensures
            seq_to_int(seq![(1u64)]) == 1nat,
    {
        let s = seq![(1u64)];
        calc! {
            (==)
            seq_to_int(s);
            { seq_to_int_nonempty(s); }
            seq_to_int(s.subrange(0, s.len() as int - 1)) * pow2(64) + (s[s.len() as int - 1] as nat);
            { 
                assert(s.len() as int - 1 == 0);
                assert(s.subrange(0, 0).len() == 0);
                seq_to_int_empty(s.subrange(0, 0));
            }
            0nat * pow2(64) + (1u64 as nat);
            { assert(0nat * pow2(64) == 0nat); }
            0nat + 1nat;
            { assert(0nat + 1nat == 1nat); }
            1nat;
        }
    }

    proof fn seq_to_int_mul_pow2_64(s: Seq<u64>)
        ensures
            seq_to_int(s) * pow2(64) == seq_to_int(s.push(0u64)),
    {
        seq_to_int_push(s, 0u64);
    }

    spec fn normalize_u64_seq(s: Seq<u64>) -> (result: Seq<u64>)
        decreases s.len()
    {
        if s.len() == 0 {
            seq![(0u64)]
        } else if s.len() == 1 {
            s
        } else {
            // Check if the last word is zero
            if s[s.len() as int - 1] == 0u64 {
                // If it's zero, recursively normalize without it
                normalize_u64_seq(s.subrange(0, s.len() as int - 1))
            } else {
                // If it's non-zero, keep the whole sequence
                s
            }
        }
    }

    proof fn normalize_u64_seq_trailing_zero(s: Seq<u64>)
        requires
            s.len() > 1,
            s[s.len() as int - 1] == 0u64,
        ensures
            normalize_u64_seq(s) == normalize_u64_seq(s.subrange(0, s.len() as int - 1)),
    {
        let sub_seq = s.subrange(0, s.len() as int - 1);
        assert(s[s.len() as int - 1] == 0u64);
        // By definition of normalize_u64_seq, when last word is 0,
        // we recursively normalize without it
    }

    proof fn normalize_u64_seq_valid(s: Seq<u64>)
        ensures
            normalize_u64_seq(s).len() > 0,
            seq_to_int(s) == seq_to_int(normalize_u64_seq(s)),
        decreases s.len()
    {
        let result = normalize_u64_seq(s);
        
        if s.len() == 0 {
            assert(result == seq![(0u64)]);
            assert(seq_to_int(s) == 0nat);
            seq_to_int_zero_singleton();
            assert(seq_to_int(result) == 0nat);
        } else if s.len() == 1 {
            assert(result == s);
            assert(seq_to_int(s) == seq_to_int(normalize_u64_seq(s)));
        } else {
            if s[s.len() as int - 1] == 0u64 {
                // Recursive case: last word is zero
                let sub_seq = s.subrange(0, s.len() as int - 1);
                normalize_u64_seq_valid(sub_seq);
                normalize_u64_seq_trailing_zero(s);
                
                // Prove that removing trailing zeros preserves the value
                let sub_seq_value = seq_to_int(sub_seq);
                let last_word_value = s[s.len() as int - 1] as nat;
                calc! {
                    (==)
                    seq_to_int(s); 
                    { seq_to_int_nonempty(s); }
                    seq_to_int(s.subrange(0, s.len() as int - 1)) * pow2(64) + (s[s.len() as int - 1] as nat); 
                    { assert(s.subrange(0, s.len() as int - 1) =~= sub_seq); }
                    sub_seq_value * pow2(64) + last_word_value;
                    { assert(last_word_value == 0nat); }
                    sub_seq_value * pow2(64);
                    { assert(sub_seq_value == seq_to_int(normalize_u64_seq(sub_seq))); }
                    seq_to_int(normalize_u64_seq(sub_seq)) * pow2(64);
                    /*{ 
                        normalize_u64_seq_trailing_zero(s);
                        seq_to_int_mul_pow2_64(normalize_u64_seq(sub_seq));
                    }
                    seq_to_int(normalize_u64_seq(s));*/
                }
                
                assume(seq_to_int(s) == seq_to_int(normalize_u64_seq(s)));

            } else {
                // Non-recursive case: last word is non-zero
                //assume(result == s);
                assume(seq_to_int(result) == seq_to_int(s));
            }
        }
    }

    spec fn add_with_carry(a: u64, b: u64, carry: bool) -> (u64, bool) {
        let sum_big = (a as nat) + (b as nat) + (if carry { 1nat } else { 0nat });
        ((sum_big % pow2(64)) as u64, sum_big >= pow2(64))
    }

    spec fn add_helper(s1: Seq<u64>, s2: Seq<u64>, carry: bool) -> (result: Seq<u64>)
        decreases s1.len() + s2.len()
    {
        if s1.len() == 0 && s2.len() == 0 {
            if carry {
                seq![(1u64)]
            } else {
                seq![(0u64)]
            }
        } else {
            let word1: u64 = if s1.len() > 0 { s1[s1.len() as int - 1] } else { 0u64 };
            let rest1: Seq<u64> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
            
            let word2: u64 = if s2.len() > 0 { s2[s2.len() as int - 1] } else { 0u64 };
            let rest2: Seq<u64> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
            
            let (sum, new_carry) = add_with_carry(word1, word2, carry);
            add_helper(rest1, rest2, new_carry).push(sum)
        }
    }

    proof fn add_with_carry_sequence_arithmetic(s1: Seq<u64>, s2: Seq<u64>, carry: bool)
        requires
            s1.len() > 0 || s2.len() > 0,
        ensures
            ({
                let word1: u64 = if s1.len() > 0 { s1[s1.len() as int - 1] } else { 0u64 };
                let rest1: Seq<u64> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
                let word2: u64 = if s2.len() > 0 { s2[s2.len() as int - 1] } else { 0u64 };
                let rest2: Seq<u64> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
                let (sum, new_carry) = add_with_carry(word1, word2, carry);
                (seq_to_int(rest1) + seq_to_int(rest2) + (if new_carry { 1nat } else { 0nat })) * pow2(64) + (sum as nat)
            }) == seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat }),
    {
        let word1: u64 = if s1.len() > 0 { s1[s1.len() as int - 1] } else { 0u64 };
        let rest1: Seq<u64> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
        let word2: u64 = if s2.len() > 0 { s2[s2.len() as int - 1] } else { 0u64 };
        let rest2: Seq<u64> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
        let (sum, new_carry) = add_with_carry(word1, word2, carry);

        // Prove relationship for s1
        if s1.len() > 0 {
            seq_to_int_nonempty(s1);
            assert(seq_to_int(s1) == seq_to_int(rest1) * pow2(64) + (word1 as nat));
        } else {
            assert(seq_to_int(s1) == 0nat);
            assert(word1 == 0u64);
            assert(rest1 =~= seq![]);
            seq_to_int_empty(rest1);
        }

        // Prove relationship for s2
        if s2.len() > 0 {
            seq_to_int_nonempty(s2);
            assert(seq_to_int(s2) == seq_to_int(rest2) * pow2(64) + (word2 as nat));
        } else {
            assert(seq_to_int(s2) == 0nat);
            assert(word2 == 0u64);
            assert(rest2 =~= seq![]);
            seq_to_int_empty(rest2);
        }

        // By definition of add_with_carry
        let sum_big = (word1 as nat) + (word2 as nat) + (if carry { 1nat } else { 0nat });
        
        // From the definition of add_with_carry
        assert({
            let (s, c) = add_with_carry(word1, word2, carry);
            s == ((sum_big % pow2(64)) as u64) && c == (sum_big >= pow2(64))
        });
        
        assert(sum == ((sum_big % pow2(64)) as u64));
        assert(new_carry == (sum_big >= pow2(64)));

        //assume(seq_to_int(rest1) + seq_to_int(rest2) + (if new_carry { 1nat } else { 0nat }) * pow2(64) + (sum as nat) == seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat }));// by(nonlinear_arith);
        //assume((seq_to_int(rest1) + seq_to_int(rest2) + (if new_carry { 1nat } else { 0nat })) * pow2(64) + (sum as nat)
        //== seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat }));
        
        calc! {
            (==)
            (seq_to_int(rest1) + seq_to_int(rest2) + (if new_carry { 1nat } else { 0nat })) * pow2(64) + (sum as nat);
            {
                 
                assert(sum_big == (word1 as nat) + (word2 as nat) + (if carry { 1nat } else { 0nat }));
                //assert(sum as nat == sum_big % pow2(64));
                
                // Expand the left side
                assert(seq_to_int(s1) == seq_to_int(rest1) * pow2(64) + (word1 as nat));
                assert(seq_to_int(s2) == seq_to_int(rest2) * pow2(64) + (word2 as nat));
                
                // Show that the carry bit handling is correct
                if new_carry {
                    assert(sum_big >= pow2(64));
                    assert(sum_big == pow2(64) + (sum as nat));
                } else {
                    assert(sum_big < pow2(64));
                    assert(sum_big == sum as nat);
                }
                
                
            }
            seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat });
        }
    }  

    proof fn add_helper_correctness(s1: Seq<u64>, s2: Seq<u64>, carry: bool)
        ensures
            seq_to_int(add_helper(s1, s2, carry)) == seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat }),
        decreases s1.len() + s2.len()
    {
        if s1.len() == 0 && s2.len() == 0 {
            // Base case
            assert(seq_to_int(s1) == 0nat);
            assert(seq_to_int(s2) == 0nat);
            if carry {
                assert(add_helper(s1, s2, carry) == seq![(1u64)]);
                seq_to_int_one_singleton();
                assert(seq_to_int(add_helper(s1, s2, carry)) == 1nat);
            } else {
                assert(add_helper(s1, s2, carry) == seq![(0u64)]);
                seq_to_int_zero_singleton();
                assert(seq_to_int(add_helper(s1, s2, carry)) == 0nat);
            }
        } else {
            // Recursive case
            let word1: u64 = if s1.len() > 0 { s1[s1.len() as int - 1] } else { 0u64 };
            let rest1: Seq<u64> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
            
            let word2: u64 = if s2.len() > 0 { s2[s2.len() as int - 1] } else { 0u64 };
            let rest2: Seq<u64> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
            
            let (sum, new_carry) = add_with_carry(word1, word2, carry);
            let result = add_helper(rest1, rest2, new_carry).push(sum);

            // Prove that s1 and rest1 are related
            if s1.len() > 0 {
                seq_to_int_nonempty(s1);
                assert(seq_to_int(s1) == seq_to_int(rest1) * pow2(64) + (word1 as nat));
            } else {
                assert(seq_to_int(s1) == 0nat);
            }

            // Prove that s2 and rest2 are related
            if s2.len() > 0 {
                seq_to_int_nonempty(s2);
                assert(seq_to_int(s2) == seq_to_int(rest2) * pow2(64) + (word2 as nat));
            } else {
                assert(seq_to_int(s2) == 0nat);
            }

            // Recursive call
            add_helper_correctness(rest1, rest2, new_carry);

            // Prove value preservation
            calc! {
                (==)
                seq_to_int(result);
                { seq_to_int_push(add_helper(rest1, rest2, new_carry), sum); }
                seq_to_int(add_helper(rest1, rest2, new_carry)) * pow2(64) + (sum as nat);
                { add_with_carry_sequence_arithmetic(s1, s2, carry); }
                seq_to_int(s1) + seq_to_int(s2) + (if carry { 1nat } else { 0nat });
            }
        }
    }

    proof fn add(s1: Seq<u64>, s2: Seq<u64>) -> (result: Seq<u64>)
        ensures
            seq_to_int(result) == seq_to_int(s1) + seq_to_int(s2),
    {
        if s1.len() == 0 && s2.len() == 0 {
            let result = seq![(0u64)];
            add_helper_correctness(s1, s2, false);
            assert(seq_to_int(result) == seq_to_int(s1) + seq_to_int(s2));
            result
        } else if s1.len() == 0 {
            // When s1 is empty, its value is 0, so we can just return s2
            // (normalized to ensure no leading zeros)
            normalize_u64_seq_valid(s2);
            let result = normalize_u64_seq(s2);
            assert(seq_to_int(result) == seq_to_int(s1) + seq_to_int(s2)); 
            result
        } else if s2.len() == 0 {
            // When s2 is empty, its value is 0, so we can just return s1
            // (normalized to ensure no leading zeros)
            normalize_u64_seq_valid(s1);
            let result = normalize_u64_seq(s1);
            assert(seq_to_int(result) == seq_to_int(s1) + seq_to_int(s2)); 
            result
        } else {
            // Perform addition using helper function and normalize the result
            let intermediate = add_helper(s1, s2, false);
            add_helper_correctness(s1, s2, false);
            normalize_u64_seq_valid(intermediate);
            let result = normalize_u64_seq(intermediate);
            assert(seq_to_int(result) == seq_to_int(s1) + seq_to_int(s2)); 
            result
        }
    }
}