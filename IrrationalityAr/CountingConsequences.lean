import IrrationalityAr.GapMonotonicity


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

noncomputable section

/-!
# Approximation certificates and counting consequences

This file starts the public counting-consequence layer.  The first layer is a
fully formal collection of rational-approximation certificates: sufficiently
good odd reduced approximants, and odd endpoints of Farey brackets, inject into
the floor-sum divisibility set `A α`.

The harder global counting consequences are intentionally not stated here until
their two bottleneck lemmas are available:

* a coefficient-side successor lemma for selected continued-fraction
  denominators;
* a generic packing theorem for sets with nondecreasing gaps and no infinite AP.
-/

/-! ## Rational approximation certificates -/

/-- A nonzero difference of two natural rational numbers has size at least
`1 / (q*d)`. -/
lemma one_div_mul_le_abs_ratValue_sub_ratValue
    {p q c d : ℕ}
    (hq : 0 < q) (hd : 0 < d)
    (hne : ratValue p q ≠ ratValue c d) :
    1 / ((q : ℝ) * (d : ℝ)) ≤
      |ratValue p q - ratValue c d| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdenpos : 0 < (q : ℝ) * (d : ℝ) := mul_pos hqR hdR
  have hcross_ne : p * d ≠ c * q := by
    intro hcross
    apply hne
    unfold ratValue
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
    have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
    rw [div_eq_div_iff hq0 hd0]
    exact_mod_cast hcross
  have hdiff :
      ratValue p q - ratValue c d =
        (((p * d : ℕ) : ℝ) - ((c * q : ℕ) : ℝ)) /
          ((q : ℝ) * (d : ℝ)) := by
    unfold ratValue
    field_simp [ne_of_gt hqR, ne_of_gt hdR]
    simp only [Nat.cast_mul]
    ring_nf
  have hnum :
      (1 : ℝ) ≤
        |(((p * d : ℕ) : ℝ) - ((c * q : ℕ) : ℝ))| := by
    rcases lt_or_gt_of_ne hcross_ne with hlt | hgt
    · have hneg :
          (((p * d : ℕ) : ℝ) - ((c * q : ℕ) : ℝ)) < 0 := by
        have hltR : ((p * d : ℕ) : ℝ) < ((c * q : ℕ) : ℝ) := by
          exact_mod_cast hlt
        linarith
      have hsucc :
          (((p * d : ℕ) : ℝ) : ℝ) + 1 ≤ ((c * q : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      rw [abs_of_neg hneg]
      linarith
    · have hpos :
          0 < (((p * d : ℕ) : ℝ) - ((c * q : ℕ) : ℝ)) := by
        have hgtR : ((c * q : ℕ) : ℝ) < ((p * d : ℕ) : ℝ) := by
          exact_mod_cast hgt
        linarith
      have hsucc :
          (((c * q : ℕ) : ℝ) : ℝ) + 1 ≤ ((p * d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      rw [abs_of_pos hpos]
      linarith
  rw [hdiff, abs_div, abs_of_pos hdenpos]
  exact (div_le_div_iff₀ hdenpos hdenpos).2 (by nlinarith)

/-- If `y` lies strictly between `x` and `z`, its distance from `z` is
strictly smaller than the distance from `x` to `z`. -/
lemma abs_right_sub_lt_of_strictBetween
    {x y z : ℝ}
    (h : StrictBetween x y z) :
    |z - y| < |z - x| := by
  rcases h with h | h
  · rw [abs_of_pos (sub_pos.mpr h.2),
      abs_of_pos (sub_pos.mpr (h.1.trans h.2))]
    linarith
  · rw [abs_of_neg (sub_neg.mpr h.1),
      abs_of_neg (sub_neg.mpr (h.1.trans h.2))]
    linarith

/-- The project-specific strengthening of the usual Legendre threshold.
Intermediate convergents allow the radius `1 / (q(q-1))`. -/
theorem noSmallDenominatorBetween_of_error_lt_inv_mul_pred
    {α : ℝ} {p q : ℕ}
    (hq : 2 ≤ q)
    (herr :
      |α - ratValue p q| <
        1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ))) :
    NoSmallDenominatorBetween α p q := by
  intro c d hd hdq hbetween
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpredR : (0 : ℝ) < (q - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < q - 1)
  have hne : ratValue p q ≠ ratValue c d := by
    intro heq
    rw [heq] at hbetween
    rcases hbetween with h | h <;> linarith
  have hsep := one_div_mul_le_abs_ratValue_sub_ratValue
    (by omega : 0 < q) hd hne
  have hdle : d ≤ q - 1 := by omega
  have hdenle :
      (q : ℝ) * (d : ℝ) ≤
        (q : ℝ) * ((q - 1 : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast hdle : (d : ℝ) ≤ ((q - 1 : ℕ) : ℝ))
      (le_of_lt hqR)
  have hrecip :
      1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) ≤
        1 / ((q : ℝ) * (d : ℝ)) := by
    exact one_div_le_one_div_of_le (mul_pos hqR hdR) hdenle
  have hinside :
      |ratValue p q - ratValue c d| <
        |ratValue p q - α| :=
    abs_right_sub_lt_of_strictBetween hbetween
  have hcycle :
      1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) <
        1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := by
    calc
      1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ))
          ≤ 1 / ((q : ℝ) * (d : ℝ)) := hrecip
      _ ≤ |ratValue p q - ratValue c d| := hsep
      _ < |ratValue p q - α| := hinside
      _ = |α - ratValue p q| := abs_sub_comm _ _
      _ < 1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ)) := herr
  exact (lt_irrefl _ hcycle)

/-- Odd reduced approximants inside the radius `1 / (q(q-1))` inject into
`A α`. -/
theorem mem_A_of_odd_reduced_error_lt_inv_mul_pred
    {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hq : 2 ≤ q)
    (hred : ReducedFraction p q)
    (hpodd : Odd p)
    (herr :
      |α - ratValue p q| <
        1 / ((q : ℝ) * ((q - 1 : ℕ) : ℝ))) :
    q - 1 ∈ A α := by
  have hbest : NoSmallDenominatorBetween α p q :=
    noSmallDenominatorBetween_of_error_lt_inv_mul_pred hq herr
  have hcf : IsConvergentOrSemiconvergent α p q :=
    (no_small_denominator_iff_convergent_or_semiconvergent
      hαpos hαirr hq hred).1 hbest
  exact mem_A_of_odd_convergent_or_semiconvergent
    hαpos hαirr hq hred hcf hpodd


end

end IrrationalityAr
