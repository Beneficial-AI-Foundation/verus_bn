# verus_bn

A Rust library for implementing and verifying big number arithmetic operations using the Verus verification framework.

## Overview

This project implements big number arithmetic operations with formal verification using [Verus](https://github.com/verus-lang/verus), a verification framework for Rust. The goal is to provide mathematically proven correct implementations of big number operations.

Currently, bignums are represented as `Seq<Char>` and we prove correctness for addition. 

## Dependencies

- Rust
- [Verus](https://github.com/verus-lang/verus) framework components:
  - `builtin`
  - `builtin_macros`
  - `vstd`
- `num-bigint` (v0.4) for big number arithmetic

## Setup

1. Make sure you have Rust installed on your system

2. Install Verus:
   - Download the latest release from [Verus Releases](https://github.com/verus-lang/verus/releases)
   - Extract the archive to a permanent location (e.g., `~/tools/verus`)
   - Copy both the `cargo-verus` and `verus` binaries to your Cargo bin directory:
     ```bash
     cp cargo-verus verus ~/.cargo/bin/
     ```
   - Make them executable:
     ```bash
     chmod +x ~/.cargo/bin/cargo-verus ~/.cargo/bin/verus
     ```
   - Add the following to your `~/.bashrc` (or equivalent shell config):
     ```bash
     export VERUSROOT=~/tools/verus  # Replace with your actual Verus directory path
     ```
   - Reload your shell configuration:
     ```bash
     source ~/.bashrc
     ```

3. Clone this repository:
   ```bash
   git clone <repository-url>
   cd verus_bn
   ```

4. Build the project:
   ```bash
   cargo build
   ```

5. Run the verification:
   ```bash
   cargo verus verify
   ```
