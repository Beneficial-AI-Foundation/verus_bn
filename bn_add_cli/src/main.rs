use bn_add::vec_add;
use clap::Parser;

/// CLI for adding binary numbers represented as strings
#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Args {
    /// First binary number
    #[clap(name = "FIRST")]
    first: String,

    /// Second binary number
    #[clap(name = "SECOND")]
    second: String,
}

/// Convert a string of '0's and '1's to a Vec<bool>
fn str_to_bitvec(s: &str) -> Vec<bool> {
    s.chars()
        .map(|c| match c {
            '0' => false,
            '1' => true,
            _ => panic!("Invalid binary digit: {}", c),
        })
        .collect()
}

/// Convert a Vec<bool> to a string of '0's and '1's
fn bitvec_to_str(v: &[bool]) -> String {
    v.iter()
        .map(|&b| if b { '1' } else { '0' })
        .collect()
}

fn main() {
    let args = Args::parse();
    
    let first_bits = str_to_bitvec(&args.first);
    let second_bits = str_to_bitvec(&args.second);
    
    let result = vec_add::add(&first_bits, &second_bits);
    
    println!("{}", bitvec_to_str(&result));
}
