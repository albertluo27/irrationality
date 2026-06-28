import IrrationalityAr.EquivalenceClass


/-!
# Gap monotonicity for arbitrary irrational parameters

This file packages the canonical continued-fraction gap monotonicity theorem
with the period/reflection normalization from `EquivalenceClass`.
-/

namespace IrrationalityAr

/-- Gap monotonicity depends only on the floor-sum set `A α`. -/
theorem AGapsNondecreasing_congr {α β : ℝ}
    (hA : A α = A β) :
    AGapsNondecreasing α ↔ AGapsNondecreasing β := by
  simp [AGapsNondecreasing, hA]

/-- Transfer gap monotonicity across equality of `A`-sets. -/
theorem AGapsNondecreasing_of_A_eq
    {α β : ℝ}
    (hA : A β = A α)
    (hgap : AGapsNondecreasing α) :
    AGapsNondecreasing β :=
  (AGapsNondecreasing_congr hA).mpr hgap

/-- Every irrational parameter has nondecreasing consecutive gaps in `A α`.

The proof normalizes `α` to a representative in `[1,2]`, applies the positive
irrational continued-fraction theorem there, and transfers the result across
the equality of `A`-sets. -/
theorem AGapsNondecreasing_of_irrational
    {α : ℝ}
    (hαirr : IsIrrational α) :
    AGapsNondecreasing α := by
  rcases exists_normalized_representative α hαirr with
    ⟨α₀, hα₀I, hAα₀, _hOrbit⟩
  have hα₀pos : 0 < α₀ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hα₀I.1
  have hα₀irr : IsIrrational α₀ :=
    irrational_of_A_eq_irrational hαirr hAα₀
  exact (AGapsNondecreasing_congr hAα₀).mp
    (AGapsNondecreasing_of_pos_irrational hα₀pos hα₀irr)

end IrrationalityAr
