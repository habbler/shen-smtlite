# smtlite for Shen/JIT

A Shen reimplementation of [smtlite's design](https://github.com/Sing-Security/smtlite), with an SMT-LIB front end for a subset of quantifier-free bit-vector formulas. The CNF encoder and watched-literal DPLL solver are typechecked. The front end walks the Shen reader's raw S-expressions and checks SMT sorts before it calls the core.

See the [roadmap](ROADMAP.md) for the remaining work toward smtlite parity.

## Run

From this directory on Windows, with the Shen/JIT distribution in a sibling directory as shown:

```powershell
$shen = '..\shen-jit-0.9-windows-x86_64\shen-jit-stlib.exe'
& $shen script run.shenmod examples/fish.smt2
& $shen build smtlite.shenmod -o smtlite.exe
.\smtlite.exe examples/fish.smt2
```

The fish example prints `sat`, reports `german` and `fish` at house 4, then prints `unsat` after excluding the complete arrangement.

## Supported input

- Booleans and bit vectors of widths 1–64, with binary, hexadecimal and indexed decimal literals.
- Boolean `not`, `and`, `or`, `xor`, `=>`, equality, `distinct` and `ite`.
- Bit-vector addition, subtraction, negation, bitwise operations, unsigned comparisons and concatenation.
- `declare-const`, zero-argument `declare-fun`, `assert`, `check-sat`, `get-value` for declared names, `reset` and `exit`. Files may start with `(set-logic QF_BV)` and `(set-option :produce-models true)`.

The width is the number of Boolean bits in an SMT value. The solver represents each bit as a SAT literal with a Shen/JIT `fixnum` ID and prints models as binary bit patterns.

Use simple unquoted identifiers. Each `check-sat` rebuilds the search state from the accumulated clauses. The port uses chronological backtracking and a fixed variable order. Upstream features such as phase saving, resource budgets, and the remaining bit-vector operators are outside this version's scope.

## Verify

The verification script checks the two bundled examples and compares generated small formulas against Z3.

```powershell
python tests/verify.py $shen 'C:\path\to\z3.exe'
```
