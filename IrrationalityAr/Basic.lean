import Mathlib

open scoped BigOperators

namespace IrrationalityAr

/-- The summand appearing in the project: `⌊n r⌋`. -/
noncomputable def floorMul (r : ℝ) (n : ℕ) : ℤ :=
  Int.floor ((n : ℝ) * r)

/-- `F_r(n) = ∑_{k=1}^n ⌊k r⌋`. -/
noncomputable def floorSum (r : ℝ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, floorMul r k

/-- `A_r = {n ≥ 1 : n ∣ F_r(n)}`. -/
def A (r : ℝ) : Set ℕ :=
  {n | 0 < n ∧ (n : ℤ) ∣ floorSum r n}

/-- A real number is rational when it is the image of a rational number. -/
def IsRational (r : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = r

/-- The negation of `IsRational`. -/
def IsIrrational (r : ℝ) : Prop :=
  ¬ IsRational r

@[simp] theorem mem_A_iff {r : ℝ} {n : ℕ} :
    n ∈ A r ↔ 0 < n ∧ (n : ℤ) ∣ floorSum r n :=
  Iff.rfl

@[simp] theorem zero_not_mem_A (r : ℝ) :
    0 ∉ A r := by
  simp [A]

end IrrationalityAr
