use vstd::calc;
use vstd::prelude::*;

verus! {

    fn main() {
    }

spec fn valid_bit_string(s: Seq<bool>) -> bool {
    true // All sequences of booleans are valid bit strings
}

spec fn str_to_int(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let sub_seq = s.subrange(0, s.len() as int - 1);
        let last_bit = s[s.len() as int - 1];
        2 * str_to_int(sub_seq) +
        (if last_bit { 1nat } else { 0nat })
    }
}

proof fn str_to_int_empty(s: Seq<bool>)
    requires
        s.len() == 0,
    ensures
        str_to_int(s) == 0nat,
{
}

proof fn str_to_int_nonempty(s: Seq<bool>)
    requires
        s.len() > 0,
    ensures
        str_to_int(s) == 2 * str_to_int(s.subrange(0, s.len() as int - 1)) + (if s[s.len() as int - 1] { 1nat } else { 0nat }),
{
}

proof fn str_to_int_of_zero(s: Seq<bool>)
    requires
        s == seq![(false)],
    ensures
        str_to_int(s) == 0nat,
{
    let sub_seq = s.subrange(0, s.len() as int - 1);
    assert(str_to_int(s) == 2 * str_to_int(sub_seq) + (if s[s.len() as int - 1] { 1nat } else { 0nat }));
}

proof fn str_to_int_of_one(s: Seq<bool>)
    requires
        s == seq![(true)],
    ensures
        str_to_int(s) == 1nat,
{
    let sub_seq = s.subrange(0, s.len() as int - 1);
    assert(str_to_int(s) == 2 * str_to_int(sub_seq) + (if s[s.len() as int - 1] { 1nat } else { 0nat }));
    assert(sub_seq.len() == 0);
    str_to_int_empty(sub_seq);
    assert(str_to_int(sub_seq) == 0nat);
    assert(str_to_int(s) == 2 * 0nat + 1nat);
}

proof fn str_to_int_extensionality(s1: Seq<bool>, s2: Seq<bool>)
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

proof fn str_to_int_push(s: Seq<bool>, b: bool)
    ensures
        str_to_int(s.push(b)) == 2 * str_to_int(s) + (if b { 1nat } else { 0nat }),
{
    let result = s.push(b);
    assert(result.subrange(0, result.len() as int - 1) =~= s);
    str_to_int_extensionality(result.subrange(0, result.len() as int - 1), s);
}

proof fn ignore_initial_zeros(s: Seq<bool>, num_zeros: int)
    requires
        0 <= num_zeros <= s.len(),
        forall|i: int| 0 <= i < num_zeros ==> !s[i],
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
        (if s.last() { 1nat } else { 0nat }); {
            ignore_initial_zeros(s.drop_last(), num_zeros);
        }
        2 * str_to_int(s.drop_last().subrange(num_zeros, s.drop_last().len() as int)) +
        (if s.last() { 1nat } else { 0nat }); {
            // Extra extensionality assertion
            assert(s.drop_last().subrange(num_zeros, s.drop_last().len() as int) == s.subrange(num_zeros, s.len() - 1));
        }
        2 * str_to_int(s.subrange(num_zeros, s.len() - 1)) +
        (if s.last() { 1nat } else { 0nat }); {
            assert(t.drop_last() =~= s.subrange(num_zeros, s.len() as int - 1));
        }
        2 * str_to_int(t.drop_last()) +
        (if t[t.len() - 1] { 1nat } else { 0nat }); {
        }
        str_to_int(t);
    }
}

proof fn all_zeros_value(s: Seq<bool>)
    requires
        forall|j: int| 0 <= j < s.len() ==> !s[j],
    ensures str_to_int(s) == 0nat,
    decreases s.len(),
{
    if s.len() == 0 {
        // Base case
    } else {
        // Recursive case
        assert(!s[s.len() as int - 1]);
        assert(str_to_int(s) == 2 * str_to_int(s.subrange(0, s.len() as int - 1)) + 0nat);
        all_zeros_value(s.subrange(0, s.len() as int - 1));
        assert(str_to_int(s.subrange(0, s.len() as int - 1)) == 0nat);
        assert(str_to_int(s) == 0nat);
    }
}

spec fn find_first_nonzero(s: Seq<bool>, start: nat) -> nat
    recommends 0 <= start <= s.len()
    decreases s.len() - start
{
    if start >= s.len() {
        s.len()
    } else if s[start as int] {
        start
    } else {
        find_first_nonzero(s, start + 1)
    }
}

proof fn find_first_nonzero_in_bounds(s: Seq<bool>, start: nat)
    requires
        start <= s.len(),
    ensures
        find_first_nonzero(s, start) <= s.len(),
        start <= find_first_nonzero(s, start),
    decreases s.len() - start
{
    if start >= s.len() {
        assert(find_first_nonzero(s, start) == s.len());
    } else if s[start as int] {
        assert(find_first_nonzero(s, start) == start);
    } else {
        // If we haven't found a non-zero, we look at the next position
        assert(!s[start as int]);
        // Recursive case
        find_first_nonzero_in_bounds(s, start + 1);
        assert(find_first_nonzero(s, start) == find_first_nonzero(s, start + 1));
    }
}

proof fn find_first_nonzero_all_zeros_before(s: Seq<bool>, start: nat)
    requires
        start <= s.len(),
    ensures
        forall|k: int| start <= k < find_first_nonzero(s, start) ==> !s[k],
    decreases s.len() - start
{
    if start >= s.len() {
        assert(find_first_nonzero(s, start) == s.len());
    } else if s[start as int] {
        assert(find_first_nonzero(s, start) == start);
    } else {
        assert(!s[start as int]);
        find_first_nonzero_all_zeros_before(s, start + 1);
        assert(find_first_nonzero(s, start) == find_first_nonzero(s, start + 1));
        assert forall|k: int| start <= k < find_first_nonzero(s, start) implies !s[k] by {
            if k == start {
                assert(!s[k]);
            } else {
                assert(start + 1 <= k < find_first_nonzero(s, start + 1));
            }
        }
    }
}

spec fn normalize_bit_string(s: Seq<bool>) -> (result: Seq<bool>)
{
    if s.len() == 0 {
        seq![(false)]
    } else {
        let i = find_first_nonzero(s, 0);
        if i == s.len() {
            seq![(false)]
        } else {
            s.subrange(i as int, s.len() as int)
        }
    }
}

proof fn normalize_bit_string_valid(s: Seq<bool>)
    ensures
        normalize_bit_string(s).len() > 0,
        str_to_int(s) == str_to_int(normalize_bit_string(s)),
{
    let result = normalize_bit_string(s);

    if s.len() == 0 {
        // Case: empty input
        assert(result == seq![(false)]);
        assert(str_to_int(s) == 0nat);
        assert(result == seq![(false)]);
        str_to_int_of_zero(seq![(false)]);
        assert(str_to_int(seq![(false)]) == 0nat);
        assert(str_to_int(result) == 0nat);
        assert(str_to_int(s) == str_to_int(result));
    } else {
        let i = find_first_nonzero(s, 0);
        // Prove i is in bounds
        find_first_nonzero_in_bounds(s, 0);
        assert(0 <= i <= s.len());

        if i == s.len() {
            // Case: all zeros
            assert(result == seq![(false)]);
            str_to_int_of_zero(seq![(false)]);
            assert(str_to_int(result) == 0nat);
            find_first_nonzero_all_zeros_before(s, 0);
            assert forall|j: int| 0 <= j < s.len() implies !s[j] by {
                assert(i == s.len());
                assert(forall|k: int| 0 <= k < i ==> !s[k]);
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

            // Prove value preservation
            find_first_nonzero_all_zeros_before(s, 0);
            assert(forall|k: int| 0 <= k < i ==> !s[k]);
            ignore_initial_zeros(s, i as int);
            assert(str_to_int(s) == str_to_int(substring));
            assert(str_to_int(s) == str_to_int(result));
        }
    }
}

spec fn add_helper(s1: Seq<bool>, s2: Seq<bool>, carry: nat) -> (result: Seq<bool>)
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        if carry == 0 {
            seq![(false)]
        } else {
            seq![(true)]
        }
    } else {
        let bit1: nat = if s1.len() > 0 && s1[s1.len() as int - 1] { 1nat } else { 0nat };
        let rest1: Seq<bool> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };

        let bit2: nat = if s2.len() > 0 && s2[s2.len() as int - 1] { 1nat } else { 0nat };
        let rest2: Seq<bool> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };

        let sum: nat = bit1 + bit2 + carry;
        let new_bit: bool = sum % 2nat == 1nat;
        let new_carry: nat = sum / 2nat;

        add_helper(rest1, rest2, new_carry).push(new_bit)
    }
}

proof fn add_helper_correctness(s1: Seq<bool>, s2: Seq<bool>, carry: nat)
    requires
        carry <= 1,
    ensures
        str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry,
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        // Base case: both strings are empty
        if carry == 0 {
            str_to_int_of_zero(seq![(false)]);
            assert(str_to_int(s1) == 0nat);
            assert(str_to_int(s2) == 0nat);
            assert(add_helper(s1, s2, carry) =~= seq![(false)]);
            assert(str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry);
        } else {
            assert(str_to_int(s1) == 0nat);
            assert(str_to_int(s2) == 0nat);
            assert(add_helper(s1, s2, carry) =~= seq![(true)]);
            str_to_int_of_one(seq![(true)]);
            assert(str_to_int(seq![(true)]) == 1nat);
            assert(str_to_int(add_helper(s1, s2, carry)) == str_to_int(s1) + str_to_int(s2) + carry);
        }
    } else {
        // Recursive case
        let bit1: nat = if s1.len() > 0 && s1[s1.len() as int - 1] { 1nat } else { 0nat };
        let rest1: Seq<bool> = if s1.len() > 0 { s1.subrange(0, s1.len() as int - 1) } else { seq![] };

        let bit2: nat = if s2.len() > 0 && s2[s2.len() as int - 1] { 1nat } else { 0nat };
        let rest2: Seq<bool> = if s2.len() > 0 { s2.subrange(0, s2.len() as int - 1) } else { seq![] };

        let sum: nat = bit1 + bit2 + carry;
        let new_bit: bool = sum % 2nat == 1nat;
        let new_carry: nat = sum / 2nat;

        // Recursive call
        add_helper_correctness(rest1, rest2, new_carry);

        // Prove value preservation
        let result = add_helper(s1, s2, carry);
        assert(result =~= add_helper(rest1, rest2, new_carry).push(new_bit));

        calc! {
            (==)
            str_to_int(result); {
                assert(result =~= add_helper(rest1, rest2, new_carry).push(new_bit));
                str_to_int_extensionality(result, add_helper(rest1, rest2, new_carry).push(new_bit));
            }
            str_to_int(add_helper(rest1, rest2, new_carry).push(new_bit)); {
                str_to_int_push(add_helper(rest1, rest2, new_carry), new_bit);
            }
            2 * str_to_int(add_helper(rest1, rest2, new_carry)) + (if new_bit { 1nat } else { 0nat }); {
                add_helper_correctness(rest1, rest2, new_carry);
            }
            2 * (str_to_int(rest1) + str_to_int(rest2) + new_carry) + (if new_bit { 1nat } else { 0nat }); {
                assert(2 * new_carry + (if new_bit { 1nat } else { 0nat }) == sum);
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

proof fn add(s1: Seq<bool>, s2: Seq<bool>) -> (result: Seq<bool>)
    ensures
        str_to_int(result) == str_to_int(s1) + str_to_int(s2),
{
    if s1.len() == 0 && s2.len() == 0 {
        let result = seq![(false)];
        add_helper_correctness(s1, s2, 0nat);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2));
        result
    } else if s1.len() == 0 {
        // When s1 is empty, its value is 0, so we can just return s2
        // (normalized to ensure no leading zeros)
        normalize_bit_string_valid(s2);
        let result = normalize_bit_string(s2);
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
        normalize_bit_string_valid(intermediate);
        let result = normalize_bit_string(intermediate);
        assert(str_to_int(result) == str_to_int(s1) + str_to_int(s2));
        result
    }
}
}
