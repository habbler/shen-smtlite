# Roadmap to smtlite 0.2.0 parity

The current proof of concept implements a subset of QF_BV with a typed, sealed Shen/JIT core and two-watched-literal DPLL. The bundled examples and 192 generated small formulas agree with Z3. The upstream target is [smtlite 0.2.0](https://docs.rs/crate/smtlite/0.2.0).

## Bit-vector operations

- [ ] Add wrapping multiplication, signed comparisons, extraction, zero extension, and sign extension.
- [ ] Add constant and symbolic left shifts, logical and arithmetic right shifts, and left and right rotates. Test shifts at and beyond the operand width, and rotates at both power-of-two and other widths.
- [ ] Add signed and unsigned division and remainder. Match SMT-LIB results for a zero divisor and for signed overflow. Signed remainder follows the dividend's sign.
- [ ] Expose the new operations through the corresponding syntax in the existing SMT-LIB front end where available.

## Typed Shen API and repeated queries

- [ ] Add typed constructors for 1–64-bit expressions and validate operand widths when constructing them.
- [ ] Represent reusable expressions as a shared graph. Fold constant expressions and encode each shared subexpression once.
- [ ] Support model lookup by variable name across the full unsigned 64-bit range, and expose a dependency query by variable-name prefix, equivalent to upstream `depends_on`.
- [ ] Add checking under temporary assumptions. Reuse the background encoding across checks, keep assumptions local to their query, and refresh the cache after declarations or assertions change.

## Search behavior and limits

- [ ] Normalize input clauses before search. Drop tautologies and duplicates and propagate unit clauses.
- [ ] Add conflict-activity branching and phase saving while retaining watched-literal propagation and chronological backtracking.
- [ ] Add a decision budget, a clause cap, and a monotonic wall-clock deadline. Check the applicable limits during encoding, preprocessing, propagation, and search. Return `unknown` when a limit is reached.

## Verification

- [ ] Compare each new operation with Z3 on small exhaustive cases and targeted 64-bit corner cases. Check returned models as well as `sat` and `unsat` results.
- [ ] Test repeated checks, assumption isolation, cache invalidation, and exhaustion of each budget.
- [ ] Measure encoding and search separately on representative bit-vector formulas, including repeated assumption checks and wide division. Record the test inputs and solver versions so the results are reproducible.
