use vstd::prelude::*;
use vstd::calc;

verus! {

    fn main() {
    }

spec fn valid_bit_string(s: Seq<char>) -> bool {
    // All characters must be '0' or '1'
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str_to_int(s: Seq<char>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let sub_seq = s.subrange(0, s.len() as int - 1);
        let last_char = s[s.len() as int - 1];
        2 * str_to_int(sub_seq) + 
        (if last_char == '1' { 1nat } else { 0nat })
    }
}

proof fn str_to_int_empty(s: Seq<char>)
    requires
        s.len() == 0,
    ensures
        str_to_int(s) == 0nat,
{
}
proof fn str_to_int_nonempty(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        str_to_int(s) == 2 * str_to_int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }),
{
}

proof fn str_to_int_of_zero(s: Seq<char>)
    requires
        s == seq![('0')],
    ensures
        str_to_int(s) == 0nat,
{
    let sub_seq = s.subrange(0, s.len() as int - 1);
    assert(str_to_int(s) == 2 * str_to_int(sub_seq) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
}

proof fn str_to_int_of_one(s: Seq<char>)
    requires
        s == seq![('1')],
    ensures
        str_to_int(s) == 1nat,
{
    let sub_seq = s.subrange(0, s.len() as int - 1);
    assert(str_to_int(s) == 2 * str_to_int(sub_seq) + (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
    assert(sub_seq.len() == 0);
    str_to_int_empty(sub_seq);
    assert(str_to_int(sub_seq) == 0nat);
    assert(str_to_int(s) == 2 * 0nat + 1nat);
}

proof fn str_to_int_extensionality(s1: Seq<char>, s2: Seq<char>)
    requires
        s1 =~= s2,
    ensures
        str_to_int(s1) == str_to_int(s2),
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s2.len() == 0);
        assert(str_to_int(s1) == 0nat);
        assert(str_to_int(s2) == 0nat);
    } else {
        let sub_s1 = s1.subrange(0, s1.len() as int - 1);
        let sub_s2 = s2.subrange(0, s2.len() as int - 1);
        assert(sub_s1 =~= sub_s2);
        str_to_int_extensionality(sub_s1, sub_s2);
        assert(s1[s1.len() as int - 1] == s2[s2.len() as int - 1]);
    }
}

proof fn str_to_int_push(s: Seq<char>, c: char)
    requires
        c == '0' || c == '1',
    ensures
        str_to_int(s.push(c)) == 2 * str_to_int(s) + (if c == '1' { 1nat } else { 0nat }),
{
    let result = s.push(c);
    assert(result.subrange(0, result.len() as int - 1) =~= s);
    str_to_int_extensionality(result.subrange(0, result.len() as int - 1), s);
}

proof fn ignore_initial_zeros(s: Seq<char>, num_zeros: int)
    requires
        //valid_bit_string(s),
        0 <= num_zeros <= s.len(),
        forall|i: int| 0 <= i < num_zeros ==> s[i] == '0',
    ensures str_to_int(s) == str_to_int(s.subrange(num_zeros, s.len() as int)),
    decreases s.len(),
{
    if num_zeros == 0 {
        assert(s.subrange(0, s.len() as int) =~= s);
        return;
    }
    if num_zeros == s.len() {
        assert(str_to_int(s) == (2 * str_to_int(s.subrange(0, s.len() - 1))));
        ignore_initial_zeros(s.subrange(0, s.len() - 1), num_zeros - 1);
        return;
    }

    // Recursive case: strip one character from the end
    ignore_initial_zeros(s.drop_last(), num_zeros);
    let t = s.subrange(num_zeros, s.len() as int);

    calc! {
        (==)
        str_to_int(s); {
        }
        2 * str_to_int(s.drop_last()) +
        (if s.last() == '1' { 1nat } else { 0nat }); {
            ignore_initial_zeros(s.drop_last(), num_zeros);
        }
        2 * str_to_int(s.drop_last().subrange(num_zeros, s.drop_last().len() as int)) +
        (if s.last() == '1' { 1nat } else { 0nat }); {
            // Extra extensionality assertion
            assert(s.drop_last().subrange(num_zeros, s.drop_last().len() as int) == s.subrange(num_zeros, s.len() - 1));
        }
        2 * str_to_int(s.subrange(num_zeros, s.len() - 1)) +
        (if s.last() == '1' { 1nat } else { 0nat }); {
            assert(t.drop_last() =~= s.subrange(num_zeros, s.len() as int - 1));
        }
        2 * str_to_int(t.drop_last()) +
        (if t[t.len() - 1] == '1' { 1nat } else { 0nat }); {
        }
        str_to_int(t);
    }
}

proof fn all_zeros_value(s: Seq<char>)
    requires
        forall|j: int| 0 <= j < s.len() ==> s[j] == '0',
    ensures str_to_int(s) == 0nat,
    decreases s.len(),
{
    if s.len() == 0 {
        // Base case
    } else {
        // Recursive case
        assert(s[s.len() as int - 1] == '0');
        assert(str_to_int(s) == 2 * str_to_int(s.subrange(0, s.len() as int - 1)) + 0nat);
        all_zeros_value(s.subrange(0, s.len() as int - 1));
        assert(str_to_int(s.subrange(0, s.len() as int - 1)) == 0nat);
        assert(str_to_int(s) == 0nat);
    }
}

spec fn find_first_nonzero(s: Seq<char>, start: nat) -> nat
    recommends 0 <= start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() {
        s.len()
    } else if s[start as int] != '0' {
        start
    } else {
        find_first_nonzero(s, start + 1)
    }
}

proof fn find_first_nonzero_in_bounds(s: Seq<char>, start: nat)
    requires
        valid_bit_string(s),
        start <= s.len(),
    ensures
        find_first_nonzero(s, start) <= s.len(),
        start <= find_first_nonzero(s, start),
    decreases s.len() - start
{
    if start >= s.len() {
        assert(find_first_nonzero(s, start) == s.len());
    } else if s[start as int] != '0' {
        assert(find_first_nonzero(s, start) == start);
    } else {
        // If we haven't found a non-zero, we look at the next position
        assert(s[start as int] == '0');
        // Recursive case
        find_first_nonzero_in_bounds(s, start + 1);
        assert(find_first_nonzero(s, start) == find_first_nonzero(s, start + 1));
    }
}

proof fn find_first_nonzero_all_zeros_before(s: Seq<char>, start: nat)
    requires
        valid_bit_string(s),
        start <= s.len(),
    ensures
        forall|k: int| start <= k < find_first_nonzero(s, start) ==> s[k] == '0',
    decreases s.len() - start
{
    if start >= s.len() {
        assert(find_first_nonzero(s, start) == s.len());
    } else if s[start as int] != '0' {
        assert(find_first_nonzero(s, start) == start);
    } else {
        assert(s[start as int] == '0');
        find_first_nonzero_all_zeros_before(s, start + 1);
        assert(find_first_nonzero(s, start) == find_first_nonzero(s, start + 1));
        assert forall|k: int| start <= k < find_first_nonzero(s, start) implies s[k] == '0' by {
            if k == start {
                assert(s[k] == '0');
            } else {
                assert(start + 1 <= k < find_first_nonzero(s, start + 1));
            }
        }
    }
}

spec fn normalize_bit_string(s: Seq<char>) -> (result: Seq<char>)   
{
    if s.len() == 0 || !valid_bit_string(s) {
        seq![('0')]
    } else {
        let i = find_first_nonzero(s, 0);
        if i == s.len() {
            seq![('0')]
        } else {
            s.subrange(i as int, s.len() as int)
        }
    }
}

proof fn normalize_bit_string_valid(s: Seq<char>)
    requires
        valid_bit_string(s),
    ensures
        valid_bit_string(normalize_bit_string(s)),
        normalize_bit_string(s).len() > 0,
        //normalize_bit_string(s).len() > 1 ==> normalize_bit_string(s)[0] != '0',
        str_to_int(s) == str_to_int(normalize_bit_string(s)),
{
    let result = normalize_bit_string(s);
    
    if s.len() == 0 {
        // Case: empty input
        assert(result == seq![('0')]);
        assert forall|i: int| 0 <= i < result.len() implies (result[i] == '0' || result[i] == '1') by {
            assert(result.len() == 1);
            assert(result[0] == '0');
        }
        assert(str_to_int(s) == 0nat);
        assert(result == seq![('0')]);
        str_to_int_of_zero(seq![('0')]);
        assert(str_to_int(seq![('0')]) == 0nat);
        assert(str_to_int(result) == 0nat);
        assert(str_to_int(s) == str_to_int(result));
    } else {
        let i = find_first_nonzero(s, 0);
        // Prove i is in bounds
        find_first_nonzero_in_bounds(s, 0);
        assert(0 <= i <= s.len());

        if i == s.len() {
            // Case: all zeros
            assert(result == seq![('0')]);
            str_to_int_of_zero(seq![('0')]);
            assert(str_to_int(result) == 0nat);
            assert(valid_bit_string(s));
            find_first_nonzero_all_zeros_before(s, 0);
            assert forall|j: int| 0 <= j < s.len() implies s[j] == '0' by {
                assert(i == s.len());
                assert(forall|k: int| 0 <= k < i ==> s[k] == '0');
            }
            all_zeros_value(s);
            assert(str_to_int(s) == 0nat);
            assert(str_to_int(s) == str_to_int(result));
        } else {
            // Case: substring from first non-zero
            let substring = s.subrange(i as int, s.len() as int);
            assert(result == substring);
            
            // Prove that substring length is valid
            assert(0 <= i);
            assert(i <= s.len());
            assert(substring.len() == s.len() as int - i as int) by {
                // This should now be provable since we know i is in bounds
            };
            
            // Prove substring is valid_bit_string
            assert forall|j: int| 0 <= j < substring.len() implies (substring[j] == '0' || substring[j] == '1') by {
                assert(valid_bit_string(s));
                let k = j + i as int;
                assert(0 <= k < s.len()) by {
                    assert(0 <= j < substring.len());
                    assert(k < s.len());
                };
                assert(s[k] == '0' || s[k] == '1');
                assert(substring[j] == s[k]);
            }
            
            // Prove value preservation
            find_first_nonzero_all_zeros_before(s, 0);
            assert(forall|k: int| 0 <= k < i ==> s[k] == '0');
            ignore_initial_zeros(s, i as int);
            assert(str_to_int(s) == str_to_int(substring));
            assert(str_to_int(s) == str_to_int(result));
        }
    }
}

spec fn add_helper(s1: Seq<char>, s2: Seq<char>, carry: nat) -> (result: Seq<char>)
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        if carry == 0 {
            seq![('0')]
        } else {
            seq![('1')]
        }
    } else {
        let bit1: nat = if s1.len() > 0 && s1[s1.len() as int - 1] == '1' { 1nat } else { 0nat };
        let rest1: Seq<char> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
        
        let bit2: nat = if s2.len() > 0 && s2[s2.len() as int - 1] == '1' { 1nat } else { 0nat };
        let rest2: Seq<char> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
        
        let sum: nat = bit1 + bit2 + carry;
        let new_bit: char = if sum % 2nat == 1nat { '1' } else { '0' };
        let new_carry: nat = sum / 2nat;
        
        add_helper(rest1, rest2, new_carry).push(new_bit)
    }    
}


proof fn add_helper_correctness(s1: Seq<char>, s2: Seq<char>, carry: nat)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        carry <= 1,
    ensures
        valid_bit_string(add_helper(s1, s2, carry)),
        str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry,
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        // Base case: both strings are empty
        if carry == 0 {
            str_to_int_of_zero(seq![('0')]);
            assert(str_to_int(s1) == 0nat);
            assert(str_to_int(s2) == 0nat);
            assert(add_helper(s1, s2, carry) =~= seq![('0')]);
            assert(str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry);
        } else {
            assert(str_to_int(s1) == 0nat);
            assert(str_to_int(s2) == 0nat);
            assert(add_helper(s1, s2, carry) =~= seq![('1')]);
            str_to_int_of_one(seq![('1')]);
            assert(str_to_int(seq![('1')]) == 1nat);
            assert(str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry);
        }
    } else {
        // Recursive case
        let bit1: nat = if s1.len() > 0 && s1[s1.len() as int - 1] == '1' { 1nat } else { 0nat };
        let rest1: Seq<char> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };
        
        let bit2: nat = if s2.len() > 0 && s2[s2.len() as int - 1] == '1' { 1nat } else { 0nat };
        let rest2: Seq<char> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };
        
        let sum: nat = bit1 + bit2 + carry;
        let new_bit: char = if sum % 2nat == 1nat { '1' } else { '0' };
        let new_carry: nat = sum / 2nat;
        
        // Prove that rest1 and rest2 are valid bit strings
        assert forall|i: int| 0 <= i < rest1.len() implies (rest1[i] == '0' || rest1[i] == '1') by {
            assert(valid_bit_string(s1));
            assert(rest1[i] == s1[i]);
        }
        assert forall|i: int| 0 <= i < rest2.len() implies (rest2[i] == '0' || rest2[i] == '1') by {
            assert(valid_bit_string(s2));
            assert(rest2[i] == s2[i]);
        }
        
        // Recursive call
        add_helper_correctness(rest1, rest2, new_carry);
        
        // Prove the result is a valid bit string
        let result = add_helper(s1, s2, carry);
        assert(result =~= add_helper(rest1, rest2, new_carry).push(new_bit));
        assert(valid_bit_string(add_helper(rest1, rest2, new_carry)));
        assert(new_bit == '0' || new_bit == '1');
        assert(valid_bit_string(result));
        
        // Prove value preservation
        calc! {
            (==)
            str_to_int(result); {
                assert(result =~= add_helper(rest1, rest2, new_carry).push(new_bit));
                str_to_int_extensionality(result, add_helper(rest1, rest2, new_carry).push(new_bit));
            }
            str_to_int(add_helper(rest1, rest2, new_carry).push(new_bit)); {
                str_to_int_push(add_helper(rest1, rest2, new_carry), new_bit);
            }
            2 * str_to_int(add_helper(rest1, rest2, new_carry)) + (if new_bit == '1' { 1nat } else { 0nat }); {
                add_helper_correctness(rest1, rest2, new_carry);
            }
            2 * (str_to_int(rest1) + str_to_int(rest2) + new_carry) + (if new_bit == '1' { 1nat } else { 0nat }); {
                assert(2 * new_carry + (if new_bit == '1' { 1nat } else { 0nat }) == sum);
            }
            2 * (str_to_int(rest1) + str_to_int(rest2)) + sum; {
                assert(sum == bit1 + bit2 + carry);
            }
            2 * (str_to_int(rest1) + str_to_int(rest2)) + bit1 + bit2 + carry; {
                assert(str_to_int(s1) == 2 * str_to_int(rest1) + bit1);
                assert(str_to_int(s2) == 2 * str_to_int(rest2) + bit2);
            }
            str_to_int(s1) + str_to_int(s2) + carry;
        }
    }
}


proof fn add(s1: Seq<char>, s2: Seq<char>) -> (result: Seq<char>)
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
    ensures
        valid_bit_string(result),
        str_to_int(result) == str_to_int(s1) + str_to_int(s2),
{
    if s1.len() == 0 && s2.len() == 0 {
        let result = seq![('0')];
        assert forall|i: int| 0 <= i < result.len() implies (result[i] == '0' || result[i] == '1') by {
            assert(result.len() == 1);
            assert(result[0] == '0');
        }
        add_helper_correctness(s1, s2, 0nat);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2));
        result
    } else if s1.len() == 0 {
        // When s1 is empty, its value is 0, so we can just return s2
        // (normalized to ensure no leading zeros)
        normalize_bit_string_valid(s2);
        let result = normalize_bit_string(s2);
        //add_helper_correctness(s1, s2, 0nat);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2)); 
        result
    } else if s2.len() == 0 {
        // When s2 is empty, its value is 0, so we can just return s1
        // (normalized to ensure no leading zeros)
        normalize_bit_string_valid(s1);
        let result = normalize_bit_string(s1);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2)); 
        result
    } else {
        // Perform addition using helper function and normalize the result
        let intermediate = add_helper(s1, s2, 0nat);
        add_helper_correctness(s1, s2, 0nat);
        //assert(valid_bit_string(intermediate)); // From add_helper ensures        
        normalize_bit_string_valid(intermediate);
        let result = normalize_bit_string(intermediate);
        //add_helper_correctness(s1, s2, 0nat);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2)); 
        result
    }
}
}