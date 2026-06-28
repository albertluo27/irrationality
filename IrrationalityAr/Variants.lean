import IrrationalityAr.ArithmeticCircleFoundation

open scoped BigOperators

namespace IrrationalityAr

/-!
# Experimental variants

These definitions record the ceiling and nearest-integer experiments without
mixing them into the proof of the original floor-based characterization.
-/

/-- Ceiling analogue of `floorMul`. -/
noncomputable def ceilMul (r : ℝ) (n : ℕ) : ℤ :=
  Int.ceil ((n : ℝ) * r)

/-- Ceiling analogue of `floorSum`. -/
noncomputable def ceilSum (r : ℝ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, ceilMul r k

/-- Ceiling analogue of `A_r`. -/
def ACeil (r : ℝ) : Set ℕ :=
  {n | 0 < n ∧ (n : ℤ) ∣ ceilSum r n}

/-- A fixed nearest-integer convention: round half-integers upward by taking
`⌊x + 1/2⌋`. -/
noncomputable def nearestInt (x : ℝ) : ℤ :=
  Int.floor (x + (1 / 2 : ℝ))

/-- Nearest-integer analogue of the summand. -/
noncomputable def nearestMul (r : ℝ) (n : ℕ) : ℤ :=
  nearestInt ((n : ℝ) * r)

/-- Nearest-integer analogue of the sum. -/
noncomputable def nearestSum (r : ℝ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, nearestMul r k

end IrrationalityAr
