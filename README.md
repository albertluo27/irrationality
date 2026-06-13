# irrationality_ar

A Lean 4 / mathlib project for formalizing the floor-sum construction

- `F_r(n) = ∑_{k=1}^n ⌊k r⌋`
- `A_r = {n ≥ 1 : n ∣ F_r(n)}`

and validating the proposed rationality characterization.

## Current status

The project formalizes the rational/eventual-AP direction, the
irrational/no-infinite-AP direction, the continued-fraction classification
layer, and the final characterization theorem.

The source tree is proof-hole free. A completed certificate should pass both
`lake build` and the no-sorry check below.

Run:

```bash
./scripts/check_no_sorry.sh
```

A completed certificate must pass that check with no proof holes.

## Setup

Install Lean using the official Lean 4 VS Code extension and `elan`, then run:

```bash
lake update
lake exe cache get
lake build
```

The project is pinned to Lean `v4.30.0` and mathlib `v4.30.0`.

## Module order

1. `Basic.lean`
   - definitions of `floorMul`, `floorSum`, `A`, rationality, irrationality
2. `FractionalParts.lean`
   - record minima and maxima of fractional parts
3. `Progressions.lean`
   - precise definitions of infinite and eventual arithmetic progressions
4. `Pairing.lean`
   - shared count `C_r(q)` and the pairing identity
5. `RationalCase.lean`
   - explicit rational tail congruence and eventual arithmetic progression
6. `IrrationalCase.lean`
   - central membership theorem via record extrema
   - translated irrational-rotation density bridge
   - no-infinite-arithmetic-progression theorem
7. `Characterization.lean`
   - combines the independent rational and irrational directions
8. `ContinuedFractions.lean`
   - continued-fraction classification of `A_α`
   - existence of simple continued fractions for positive irrational reals
   - best-approximation bridge through convergents and semiconvergents
9. `Variants.lean`
   - ceiling and nearest-integer experiments kept separate from the core proof

## Main Formalized Lemmas

The core AP argument is represented by named Lean pieces including
`two_mul_floorSum_pred_eq`, `aboveCount_eq_zero_or_eq_of_mem_A`,
`mem_A_iff_record_extreme`, `denseRange_translated_nat_toAddCircle`, and
`irrational_no_infiniteAP`.

The rational direction is represented by `mem_A_rat_iff_modEq` and
`rational_eventuallyAP`. The combined theorem is
`rational_iff_eventuallyAP`.

The continued-fraction classification is represented by
`A_eq_odd_convergent_or_semiconvergent`.
