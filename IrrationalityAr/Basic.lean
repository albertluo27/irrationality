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

theorem isIrrational_of_irrational {x : ℝ} (hx : Irrational x) :
    IsIrrational x := by
  intro hrat
  exact hx hrat

theorem mul_irrational_not_int {α : ℝ} (hirr : IsIrrational α)
    {k : ℕ} (hkpos : 0 < k) :
    ∀ m : ℤ, (k : ℝ) * α ≠ (m : ℝ) := by
  intro m hm
  apply hirr
  refine ⟨(m : ℚ) / (k : ℚ), ?_⟩
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkpos
  have hcast :
      (((m : ℚ) / (k : ℚ) : ℚ) : ℝ) =
        (m : ℝ) / (k : ℝ) := by
    norm_num
  rw [hcast]
  rw [div_eq_iff hkR]
  rw [← hm]
  ring

theorem floor_lt_of_not_int {x : ℝ}
    (hnot : ∀ m : ℤ, x ≠ (m : ℝ)) :
    (Int.floor x : ℝ) < x := by
  have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hne : (Int.floor x : ℝ) ≠ x := by
    intro h
    exact hnot (Int.floor x) h.symm
  exact lt_of_le_of_ne hle hne

theorem card_filter_range_succ
    (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.range (N + 1)).filter P).card =
      ((Finset.range N).filter P).card + (if P N then 1 else 0) := by
  classical
  by_cases h : P N
  · simp [Finset.range_add_one, Finset.filter_insert, h]
  · simp [Finset.range_add_one, Finset.filter_insert, h]

@[simp] theorem mem_A_iff {r : ℝ} {n : ℕ} :
    n ∈ A r ↔ 0 < n ∧ (n : ℤ) ∣ floorSum r n :=
  Iff.rfl

@[simp] theorem zero_not_mem_A (r : ℝ) :
    0 ∉ A r := by
  simp [A]

end IrrationalityAr
