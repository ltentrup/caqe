# CAQE

CAQE is a solver for quantified Boolean formulas (QBF) in prenex conjunctive normal (prenex CNF) form supporting the [QDIMACS](http://www.qbflib.org/qdimacs.html) file format.
dCAQE is a solver for dependency quantified Boolean formulas (DQBF) in prenex conjunctive normal form supporting the DQDIMACS file format.

## Installation

CAQE is written in [Rust](https://www.rust-lang.org/), the latest version of the Rust compiler is available at [rustup.rs](http://rustup.rs).
To build (d)CAQE, execute `cargo build --release` from the checkout which builds the static binaries `caqe` and `dcaqe` located at `./target/release/`.

## Usage

    caqe [FLAGS] [OPTIONS] <INPUT>

`INPUT` should be the path to an instance in [QDIMACS](http://www.qbflib.org/qdimacs.html) file format.
See `--help` for more details on `FLAGS` and `OPTIONS`.
CAQE exits with result code `10` and `20` for satisfiable and unsatisfiable instances, respectively.

CAQE also supports the QDIMACS output format, which contains partial assignments to the variables, using the flag `--qdo`:

```
$ ./caqe --qdo satisfiable.qdimacs
s cnf 1 3 4
V -1 0
```

where the instance is

```
c satisfiable.qdimacs  // comment
p cnf 3 4              // 3 variables, 4 clauses
e 1 0                  // ∃ variable 1
a 2 0                  // ∀ variable 2
e 3 0                  // ∃ variable 3
-1 2 -3 0              // (-1 or 2 or -3)
2 3 0                  // (2 or 3)
-2 3 0                 // (-2 or 3)
1 3 0                  // (1 or 3)
```