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

/-! ## Farey bracket certificates -/

/-- The left endpoint of a determinant-one bracket is a one-sided best
approximation. -/
theorem noSmallDenominatorBetween_left_of_fareyBracket
    {α : ℝ} {p q r s : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s) :
    NoSmallDenominatorBetween α p q := by
  intro c d hd hdq hbetween
  rcases hbetween with h | h
  · have : α < ratValue p q := h.1.trans h.2
    exact (not_lt_of_ge hbracket.1.le) this
  · have hbetween' :
        ratValue p q < ratValue c d ∧
          ratValue c d < ratValue r s :=
      ⟨h.1, h.2.trans hbracket.2⟩
    have hden := farey_neighbor_denominator_lower_bound
      hq hs hd hfarey hbetween'
    omega

/-- The right endpoint of a determinant-one bracket is a one-sided best
approximation. -/
theorem noSmallDenominatorBetween_right_of_fareyBracket
    {α : ℝ} {p q r s : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s) :
    NoSmallDenominatorBetween α r s := by
  intro c d hd hds hbetween
  rcases hbetween with h | h
  · have hbetween' :
        ratValue p q < ratValue c d ∧
          ratValue c d < ratValue r s :=
      ⟨hbracket.1.trans h.1, h.2⟩
    have hden := farey_neighbor_denominator_lower_bound
      hq hs hd hfarey hbetween'
    omega
  · have : ratValue r s < α := h.1.trans h.2
    exact (not_lt_of_ge hbracket.2.le) this

/-- Odd left endpoint of a Farey bracket gives an element of `A α`. -/
theorem left_fareyBracket_mem_A
    {α : ℝ} {p q r s : ℕ}
    (hαpos : 0 < α) (hαirr : IsIrrational α)
    (hq : 2 ≤ q) (hs : 0 < s)
    (hred : ReducedFraction p q)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s)
    (hpodd : Odd p) :
    q - 1 ∈ A α := by
  have hbest := noSmallDenominatorBetween_left_of_fareyBracket
    (by omega : 0 < q) hs hfarey hbracket
  have hcf :=
    (no_small_denominator_iff_convergent_or_semiconvergent
      hαpos hαirr hq hred).1 hbest
  exact mem_A_of_odd_convergent_or_semiconvergent
    hαpos hαirr hq hred hcf hpodd

/-- Odd right endpoint of a Farey bracket gives an element of `A α`. -/
theorem right_fareyBracket_mem_A
    {α : ℝ} {p q r s : ℕ}
    (hαpos : 0 < α) (hαirr : IsIrrational α)
    (hq : 0 < q) (hs : 2 ≤ s)
    (hred : ReducedFraction r s)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s)
    (hrodd : Odd r) :
    s - 1 ∈ A α := by
  have hbest := noSmallDenominatorBetween_right_of_fareyBracket
    hq (by omega : 0 < s) hfarey hbracket
  have hcf :=
    (no_small_denominator_iff_convergent_or_semiconvergent
      hαpos hαirr hs hred).1 hbest
  exact mem_A_of_odd_convergent_or_semiconvergent
    hαpos hαirr hs hred hcf hrodd

/-- A determinant-one bracket certifies at least one endpoint denominator.
The reducedness assumptions are intentionally explicit in this first API. -/
theorem fareyBracket_certifies_A
    {α : ℝ} {p q r s : ℕ}
    (hαpos : 0 < α) (hαirr : IsIrrational α)
    (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hredL : ReducedFraction p q)
    (hredR : ReducedFraction r s)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s) :
    q - 1 ∈ A α ∨ s - 1 ∈ A α := by
  rcases Nat.even_or_odd p with hpEven | hpOdd
  · rcases Nat.even_or_odd r with hrEven | hrOdd
    · exfalso
      have hleftEven : Even (q * r) := hrEven.mul_left q
      have hrightOdd : Odd (p * s + 1) := by
        have hpsEven : Even (p * s) := by
          simpa [Nat.mul_comm] using hpEven.mul_left s
        exact hpsEven.add_one
      have hleftOdd : Odd (q * r) := by simpa [hfarey] using hrightOdd
      exact (Nat.not_even_iff_odd.mpr hleftOdd) hleftEven
    · exact Or.inr <| right_fareyBracket_mem_A
        hαpos hαirr (by omega) hs hredR hfarey hbracket hrOdd
  · exact Or.inl <| left_fareyBracket_mem_A
      hαpos hαirr hq (by omega) hredL hfarey hbracket hpOdd

/-- Determinant one also supplies reducedness of the left endpoint. -/
lemma reducedFraction_left_of_fareyDet
    {p q r s : ℕ}
    (hq : 0 < q)
    (hfarey : q * r = p * s + 1) :
    ReducedFraction p q := by
  refine ⟨hq, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  let g : ℕ := Nat.gcd p q
  have hgp : g ∣ p := Nat.gcd_dvd_left _ _
  have hgq : g ∣ q := Nat.gcd_dvd_right _ _
  have hgpZ : (g : ℤ) ∣ (p : ℤ) := by exact_mod_cast hgp
  have hgqZ : (g : ℤ) ∣ (q : ℤ) := by exact_mod_cast hgq
  have hdetZ :
      (q : ℤ) * (r : ℤ) - (p : ℤ) * (s : ℤ) = 1 := by
    have hcast : (q * r : ℤ) = (p * s + 1 : ℕ) := by
      exact_mod_cast hfarey
    omega
  have hgOneZ : (g : ℤ) ∣ (1 : ℤ) := by
    rw [← hdetZ]
    exact dvd_sub
      (dvd_mul_of_dvd_left hgqZ _)
      (dvd_mul_of_dvd_left hgpZ _)
  have hgOne : g ∣ 1 := by exact_mod_cast hgOneZ
  exact Nat.dvd_one.mp hgOne

/-- Determinant one also supplies reducedness of the right endpoint. -/
lemma reducedFraction_right_of_fareyDet
    {p q r s : ℕ}
    (hs : 0 < s)
    (hfarey : q * r = p * s + 1) :
    ReducedFraction r s := by
  refine ⟨hs, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  let g : ℕ := Nat.gcd r s
  have hgr : g ∣ r := Nat.gcd_dvd_left _ _
  have hgs : g ∣ s := Nat.gcd_dvd_right _ _
  have hgrZ : (g : ℤ) ∣ (r : ℤ) := by exact_mod_cast hgr
  have hgsZ : (g : ℤ) ∣ (s : ℤ) := by exact_mod_cast hgs
  have hdetZ :
      (q : ℤ) * (r : ℤ) - (p : ℤ) * (s : ℤ) = 1 := by
    have hcast : (q * r : ℤ) = (p * s + 1 : ℕ) := by
      exact_mod_cast hfarey
    omega
  have hgOneZ : (g : ℤ) ∣ (1 : ℤ) := by
    rw [← hdetZ]
    exact dvd_sub
      (dvd_mul_of_dvd_right hgrZ _)
      (dvd_mul_of_dvd_right hgsZ _)
  have hgOne : g ∣ 1 := by exact_mod_cast hgOneZ
  exact Nat.dvd_one.mp hgOne

/-- Clean Farey certificate: determinant one, positive denominators, and the
bracket alone imply that at least one shifted endpoint denominator lies in
`A α`. -/
theorem fareyBracket_certifies_A_of_det
    {α : ℝ} {p q r s : ℕ}
    (hαpos : 0 < α) (hαirr : IsIrrational α)
    (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hfarey : q * r = p * s + 1)
    (hbracket : ratValue p q < α ∧ α < ratValue r s) :
    q - 1 ∈ A α ∨ s - 1 ∈ A α := by
  exact fareyBracket_certifies_A
    hαpos hαirr hq hs
    (reducedFraction_left_of_fareyDet (by omega) hfarey)
    (reducedFraction_right_of_fareyDet (by omega) hfarey)
    hfarey hbracket

/-! ## Counting definitions -/

noncomputable def natSetCount (S : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n : ℕ => n ∈ S).card

abbrev ACount (α : ℝ) (N : ℕ) : ℕ := natSetCount (A α) N

@[simp] theorem one_mem_A (α : ℝ) : 1 ∈ A α := by
  rw [mem_A_iff]
  simp

/-! ## Selected-denominator seed sequence -/

private lemma mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
    {a : ℕ → ℕ} {j t : ℕ}
    (hidx : CanonicalOddCFIndex a j t)
    (hden : 2 ≤ CFBlockDenominator a j t) :
    CFBlockDenominator a j t ∈ oddBlockDenominatorSet a := by
  rcases hidx with ⟨ht1, htle, hodd⟩
  exact ⟨j, t, ht1, htle, hodd, hden, rfl⟩

private lemma CFBlockDenominator_add_two
    (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockDenominator a j (t + 2) =
      CFBlockDenominator a j t + 2 * continuantDen a j := by
  have h1 := CFBlockDenominator_succ a j t
  have h2 := CFBlockDenominator_succ a j (t + 1)
  rw [h2, h1]
  omega

private lemma two_le_of_later_den
    {Q Q' : ℕ} (hQ2 : 2 ≤ Q) (hQQ' : Q < Q') :
    2 ≤ Q' := by
  omega

private lemma odd_prevNum_of_even_currNum_and_odd_blockNum
    {a : ℕ → ℕ} {j t : ℕ}
    (hcurrEven : Even (continuantNum a j))
    (hodd : Odd (CFBlockNumerator a j t)) :
    Odd (continuantNumPrev a j) := by
  rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
  · exfalso
    have hblockEven : Even (CFBlockNumerator a j t) := by
      unfold CFBlockNumerator
      exact hprevEven.add (hcurrEven.mul_left t)
    exact (Nat.not_even_iff_odd.mpr hodd) hblockEven
  · exact hprevOdd

private lemma exists_small_canonicalOddCFIndex_or_emptyBlock
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (j : ℕ) :
    (∃ t : ℕ, (t = 1 ∨ t = 2) ∧ CanonicalOddCFIndex a j t) ∨
      (a (j + 1) = 1 ∧
        Odd (continuantNumPrev a j) ∧ Odd (continuantNum a j)) := by
  classical
  rcases exists_canonicalOddCFIndex_or_emptyBlock a hpos j with
    ⟨t, ht⟩ | hempty
  · let u : ℕ := Nat.find (show ∃ v : ℕ, CanonicalOddCFIndex a j v from ⟨t, ht⟩)
    have hu : CanonicalOddCFIndex a j u := by
      dsimp [u]
      exact Nat.find_spec (show ∃ v : ℕ, CanonicalOddCFIndex a j v from ⟨t, ht⟩)
    have hfirst : IsFirstSelectedInBlock a j u := by
      refine ⟨hu, ?_⟩
      intro v hv hvu
      exact (Nat.find_min
        (show ∃ w : ℕ, CanonicalOddCFIndex a j w from ⟨t, ht⟩) hvu) hv
    exact Or.inl ⟨u, isFirstSelectedInBlock_eq_one_or_two hfirst, hu⟩
  · exact Or.inr hempty

/-- The denominator `2` is always parity-selected. -/
lemma two_mem_oddBlockDenominatorSet
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    2 ∈ oddBlockDenominatorSet a := by
  by_cases ha2 : 2 ≤ a 1
  · refine ⟨0, 2, by norm_num, ha2, ?_, ?_, ?_⟩
    · have hodd : Odd (2 * a 0 + 1) :=
        (Even.mul_right even_two (a 0)).add_one
      simp [CFBlockNumerator, continuantNumPrev, continuantNum]
    · norm_num [CFBlockDenominator, continuantDenPrev, continuantDen]
    · norm_num [CFBlockDenominator, continuantDenPrev, continuantDen]
  · have ha1 : a 1 = 1 := by
      have hge : 1 ≤ a 1 := by simpa using hpos 0
      have hlt2 : a 1 < 2 := Nat.lt_of_not_ge ha2
      have hle : a 1 ≤ 1 := Nat.le_of_lt_succ hlt2
      exact le_antisymm hle hge
    refine ⟨1, 1, by norm_num, ?_, ?_, ?_, ?_⟩
    · simpa [ha1] using hpos 1
    · have hodd : Odd (2 * a 0 + 1) :=
        (Even.mul_right even_two (a 0)).add_one
      simp [CFBlockNumerator, continuantNumPrev, continuantNum, ha1]
    · norm_num [CFBlockDenominator, continuantDenPrev, continuantDen, ha1]
    · norm_num [CFBlockDenominator, continuantDenPrev, continuantDen, ha1]

/-- Every selected denominator has a later selected denominator at most three
times as large. -/
theorem exists_later_oddBlockDenominator_le_three_mul
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Q : ℕ}
    (hQ : Q ∈ oddBlockDenominatorSet a) :
    ∃ Q' : ℕ,
      Q' ∈ oddBlockDenominatorSet a ∧
      Q < Q' ∧
      Q' ≤ 3 * Q := by
  rcases hQ with ⟨j, t, ht1, htle, hodd, hQ2, rfl⟩
  have hqleQ : continuantDen a j ≤ CFBlockDenominator a j t := by
    unfold CFBlockDenominator
    have hmul : continuantDen a j ≤ t * continuantDen a j :=
      Nat.le_mul_of_pos_left _ ht1
    exact hmul.trans (Nat.le_add_left _ _)
  by_cases hroom : t + 2 ≤ a (j + 1)
  · rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
    · have hprevOdd :
          Odd (continuantNumPrev a j) :=
        odd_prevNum_of_even_currNum_and_odd_blockNum hcurrEven hodd
      let Q' := CFBlockDenominator a j (t + 1)
      have hidx' : CanonicalOddCFIndex a j (t + 1) := by
        refine ⟨by omega, by omega, ?_⟩
        exact odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
      have hlt : CFBlockDenominator a j t < Q' := by
        dsimp [Q']
        rw [CFBlockDenominator_succ]
        have hqpos : 0 < continuantDen a j := by
          exact lt_of_lt_of_le Nat.zero_lt_one
            (one_le_continuantDen_of_partials_pos_global a hpos j)
        omega
      have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
        dsimp [Q']
        rw [CFBlockDenominator_succ]
        have := hqleQ
        omega
      refine ⟨Q', ?_, hlt, hle⟩
      exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
        hidx' (two_le_of_later_den hQ2 hlt)
    · let Q' := CFBlockDenominator a j (t + 2)
      have hidx : CanonicalOddCFIndex a j t := ⟨ht1, htle, hodd⟩
      have hidx' : CanonicalOddCFIndex a j (t + 2) :=
        selected_add_two_of_curr_odd hcurrOdd hidx hroom
      have hlt : CFBlockDenominator a j t < Q' := by
        dsimp [Q']
        rw [CFBlockDenominator_add_two]
        have hqpos : 0 < continuantDen a j := by
          exact lt_of_lt_of_le Nat.zero_lt_one
            (one_le_continuantDen_of_partials_pos_global a hpos j)
        omega
      have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
        dsimp [Q']
        rw [CFBlockDenominator_add_two]
        have := hqleQ
        omega
      refine ⟨Q', ?_, hlt, hle⟩
      exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
        hidx' (two_le_of_later_den hQ2 hlt)
  · have hnear : a (j + 1) = t ∨ a (j + 1) = t + 1 := by
      omega
    rcases hnear with hend | hpreEnd
    · have hQendpoint :
          CFBlockDenominator a j t = continuantDen a (j + 1) := by
        rw [← hend]
        exact CFBlockDenominator_endpoint a j
      rcases exists_small_canonicalOddCFIndex_or_emptyBlock a hpos (j + 1) with
        ⟨u, hu12, hidxu⟩ | hempty
      · let Q' := CFBlockDenominator a (j + 1) u
        have hlt : CFBlockDenominator a j t < Q' := by
          rcases hu12 with rfl | rfl
          · dsimp [Q']
            rw [hQendpoint, CFBlockDenominator_next_block_first]
            have hqpos : 0 < continuantDen a j := by
              exact lt_of_lt_of_le Nat.zero_lt_one
                (one_le_continuantDen_of_partials_pos_global a hpos j)
            omega
          · dsimp [Q']
            rw [hQendpoint]
            have hfirst := CFBlockDenominator_next_block_first a j
            have hsucc := CFBlockDenominator_succ a (j + 1) 1
            rw [hfirst] at hsucc
            rw [hsucc]
            have hqpos : 0 < continuantDen a j := by
              exact lt_of_lt_of_le Nat.zero_lt_one
                (one_le_continuantDen_of_partials_pos_global a hpos j)
            omega
        have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
          have hmono : continuantDen a j ≤ continuantDen a (j + 1) :=
            continuantDen_mono_of_partials_pos a hpos j
          rcases hu12 with rfl | rfl
          · dsimp [Q']
            rw [hQendpoint, CFBlockDenominator_next_block_first]
            omega
          · dsimp [Q']
            rw [hQendpoint]
            have hfirst := CFBlockDenominator_next_block_first a j
            have hsucc := CFBlockDenominator_succ a (j + 1) 1
            rw [hfirst] at hsucc
            rw [hsucc]
            omega
        refine ⟨Q', ?_, hlt, hle⟩
        exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
          hidxu (two_le_of_later_den hQ2 hlt)
      · rcases hempty with ⟨hcoeff, hprevOdd, hcurrOdd⟩
        let Q' := CFBlockDenominator a (j + 2) 1
        have hidx' : CanonicalOddCFIndex a (j + 2) 1 :=
          canonicalOddCFIndex_next_of_emptyBlock
            (a := a) hpos (j := j + 1) hcoeff hprevOdd hcurrOdd
        have hlt : CFBlockDenominator a j t < Q' := by
          dsimp [Q']
          rw [hQendpoint]
          have hfirst :
              CFBlockDenominator a (j + 2) 1 =
                continuantDen a (j + 1) + continuantDen a (j + 2) := by
            simpa [Nat.add_assoc] using
              CFBlockDenominator_next_block_first a (j + 1)
          rw [hfirst]
          have hqpos2 : 0 < continuantDen a (j + 2) := by
            exact lt_of_lt_of_le Nat.zero_lt_one
              (one_le_continuantDen_of_partials_pos_global a hpos (j + 2))
          omega
        have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
          dsimp [Q']
          rw [hQendpoint]
          have hfirst :
              CFBlockDenominator a (j + 2) 1 =
                continuantDen a (j + 1) + continuantDen a (j + 2) := by
            simpa [Nat.add_assoc] using
              CFBlockDenominator_next_block_first a (j + 1)
          rw [hfirst]
          rw [continuantDen_succ_eq a (j + 1), hcoeff]
          simp [continuantDenPrev]
          have hmono : continuantDen a j ≤ continuantDen a (j + 1) :=
            continuantDen_mono_of_partials_pos a hpos j
          omega
        refine ⟨Q', ?_, hlt, hle⟩
        exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
          hidx' (two_le_of_later_den hQ2 hlt)
    · by_cases hendOdd : Odd (CFBlockNumerator a j (t + 1))
      · let Q' := CFBlockDenominator a j (t + 1)
        have hidx' : CanonicalOddCFIndex a j (t + 1) := by
          refine ⟨by omega, by omega, hendOdd⟩
        have hlt : CFBlockDenominator a j t < Q' := by
          dsimp [Q']
          rw [CFBlockDenominator_succ]
          have hqpos : 0 < continuantDen a j := by
            exact lt_of_lt_of_le Nat.zero_lt_one
              (one_le_continuantDen_of_partials_pos_global a hpos j)
          omega
        have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
          dsimp [Q']
          rw [CFBlockDenominator_succ]
          have := hqleQ
          omega
        refine ⟨Q', ?_, hlt, hle⟩
        exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
          hidx' (two_le_of_later_den hQ2 hlt)
      · have hendEven : Even (CFBlockNumerator a j (t + 1)) := by
          exact Nat.not_odd_iff_even.mp hendOdd
        have hcurrOdd : Odd (continuantNum a j) := by
          rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
          · have hprevOdd :=
              odd_prevNum_of_even_currNum_and_odd_blockNum hcurrEven hodd
            have hendOdd' : Odd (CFBlockNumerator a j (t + 1)) :=
              odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
            exact False.elim (hendOdd hendOdd')
          · exact hcurrOdd
        have hpnextEven : Even (continuantNum a (j + 1)) := by
          rw [← CFBlockNumerator_endpoint a j]
          simpa [hpreEnd] using hendEven
        let Q' := CFBlockDenominator a (j + 1) 1
        have hidx' : CanonicalOddCFIndex a (j + 1) 1 := by
          refine ⟨by norm_num, hpos (j + 1), ?_⟩
          exact odd_CFBlockNumerator_of_prev_odd_curr_even
            (a := a) (j := j + 1) (t := 1)
            (by simpa [continuantNumPrev] using hcurrOdd)
            hpnextEven
        have hlt : CFBlockDenominator a j t < Q' := by
          dsimp [Q']
          have hboundary := CFBlockDenominator_boundary_succ a j
          have hsucc := CFBlockDenominator_succ a j t
          have htend : t + 1 = a (j + 1) := by omega
          rw [← htend] at hboundary
          rw [hsucc] at hboundary
          rw [hboundary]
          have hqpos : 0 < continuantDen a j := by
            exact lt_of_lt_of_le Nat.zero_lt_one
              (one_le_continuantDen_of_partials_pos_global a hpos j)
          omega
        have hle : Q' ≤ 3 * CFBlockDenominator a j t := by
          dsimp [Q']
          have hboundary := CFBlockDenominator_boundary_succ a j
          have hsucc := CFBlockDenominator_succ a j t
          have htend : t + 1 = a (j + 1) := by omega
          rw [← htend] at hboundary
          rw [hsucc] at hboundary
          rw [hboundary]
          have := hqleQ
          omega
        refine ⟨Q', ?_, hlt, hle⟩
        exact mem_oddBlockDenominatorSet_of_CanonicalOddCFIndex
          hidx' (two_le_of_later_den hQ2 hlt)

abbrev SelectedDenominator (a : ℕ → ℕ) :=
  {Q : ℕ // Q ∈ oddBlockDenominatorSet a}

noncomputable def nextSelectedDenominator
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (Q : SelectedDenominator a) : SelectedDenominator a := by
  let h := exists_later_oddBlockDenominator_le_three_mul hpos Q.property
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

lemma nextSelectedDenominator_spec
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (Q : SelectedDenominator a) :
    (Q : ℕ) < nextSelectedDenominator a hpos Q ∧
      (nextSelectedDenominator a hpos Q : ℕ) ≤ 3 * (Q : ℕ) := by
  let h := exists_later_oddBlockDenominator_le_three_mul hpos Q.property
  simpa [nextSelectedDenominator, h] using (Classical.choose_spec h).2

noncomputable def selectedDenominatorSeq
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    ℕ → SelectedDenominator a
  | 0 => ⟨2, two_mem_oddBlockDenominatorSet hpos⟩
  | n + 1 => nextSelectedDenominator a hpos (selectedDenominatorSeq a hpos n)

lemma selectedDenominatorSeq_lt_succ
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (n : ℕ) :
    (selectedDenominatorSeq a hpos n : ℕ) <
      selectedDenominatorSeq a hpos (n + 1) := by
  simpa [selectedDenominatorSeq] using
    (nextSelectedDenominator_spec a hpos
      (selectedDenominatorSeq a hpos n)).1

lemma selectedDenominatorSeq_strictMono
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    StrictMono (fun n => (selectedDenominatorSeq a hpos n : ℕ)) := by
  exact strictMono_nat_of_lt_succ
    (selectedDenominatorSeq_lt_succ a hpos)

lemma selectedDenominatorSeq_le_pow
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    ∀ n : ℕ,
      (selectedDenominatorSeq a hpos n : ℕ) ≤ 2 * 3^n
  | 0 => by simp [selectedDenominatorSeq]
  | n + 1 => by
      have hnext := (nextSelectedDenominator_spec a hpos
        (selectedDenominatorSeq a hpos n)).2
      have ih := selectedDenominatorSeq_le_pow a hpos n
      calc
        (selectedDenominatorSeq a hpos (n + 1) : ℕ)
            ≤ 3 * (selectedDenominatorSeq a hpos n : ℕ) := by
              simpa [selectedDenominatorSeq] using hnext
        _ ≤ 3 * (2 * 3^n) := Nat.mul_le_mul_left 3 ih
        _ = 2 * 3^(n + 1) := by ring

lemma selectedDenominatorSeq_ge_two
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (n : ℕ) :
    2 ≤ (selectedDenominatorSeq a hpos n : ℕ) := by
  rcases (selectedDenominatorSeq a hpos n).property with
    ⟨j, t, ht1, htle, hodd, hQ2, hQ⟩
  simpa [hQ] using hQ2

noncomputable def oddBlockASeq
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (n : ℕ) : ℕ :=
  (selectedDenominatorSeq a hpos n : ℕ) - 1

lemma oddBlockASeq_mem
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (n : ℕ) :
    oddBlockASeq a hpos n ∈ oddBlockASet a := by
  rw [mem_oddBlockASet_iff_succ_mem_oddBlockDenominatorSet]
  have hge := selectedDenominatorSeq_ge_two a hpos n
  have hsucc :
      oddBlockASeq a hpos n + 1 =
        (selectedDenominatorSeq a hpos n : ℕ) := by
    unfold oddBlockASeq
    omega
  rw [hsucc]
  exact (selectedDenominatorSeq a hpos n).property

lemma oddBlockASeq_strictMono
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    StrictMono (oddBlockASeq a hpos) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hlt := selectedDenominatorSeq_lt_succ a hpos n
  have hn := selectedDenominatorSeq_ge_two a hpos n
  have hsn := selectedDenominatorSeq_ge_two a hpos (n + 1)
  unfold oddBlockASeq
  omega

lemma oddBlockASeq_zero
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    oddBlockASeq a hpos 0 = 1 := by
  simp [oddBlockASeq, selectedDenominatorSeq]

lemma oddBlockASeq_le_pow
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (n : ℕ) :
    oddBlockASeq a hpos n ≤ 2 * 3^n - 1 := by
  unfold oddBlockASeq
  have h := selectedDenominatorSeq_le_pow a hpos n
  omega

/-- Positive irrational parameters admit a strict logarithmic seed sequence
inside `A α`. -/
theorem exists_A_seed_sequence_of_pos_irrational
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α) :
    ∃ f : ℕ → ℕ,
      f 0 = 1 ∧
      StrictMono f ∧
      (∀ n : ℕ, f n ∈ A α) ∧
      ∀ n : ℕ, f n ≤ 2 * 3^n - 1 := by
  rcases exists_simpleCFExpansion_of_irrational hαpos hαirr with ⟨a, hcf⟩
  refine ⟨oddBlockASeq a hcf.1, oddBlockASeq_zero a hcf.1,
    oddBlockASeq_strictMono a hcf.1, ?_, oddBlockASeq_le_pow a hcf.1⟩
  intro n
  rw [A_eq_oddBlockASet_of_IsSimpleCFExpansion hαpos hαirr hcf]
  exact oddBlockASeq_mem a hcf.1 n

/-- Arbitrary irrational parameters inherit the same seed sequence after
period/reflection normalization. -/
theorem exists_A_seed_sequence_of_irrational
    {α : ℝ}
    (hαirr : IsIrrational α) :
    ∃ f : ℕ → ℕ,
      f 0 = 1 ∧
      StrictMono f ∧
      (∀ n : ℕ, f n ∈ A α) ∧
      ∀ n : ℕ, f n ≤ 2 * 3^n - 1 := by
  rcases exists_normalized_representative α hαirr with
    ⟨α₀, hα₀I, hA, _⟩
  have hα₀pos : 0 < α₀ := lt_of_lt_of_le (by norm_num) hα₀I.1
  have hα₀irr : IsIrrational α₀ :=
    irrational_of_A_eq_irrational hαirr hA
  rcases exists_A_seed_sequence_of_pos_irrational hα₀pos hα₀irr with
    ⟨f, hf0, hfmono, hfmem, hfbound⟩
  refine ⟨f, hf0, hfmono, ?_, hfbound⟩
  intro n
  simpa [hA] using hfmem n

private lemma strictMono_lower_linear
    {f : ℕ → ℕ}
    (hf0 : f 0 = 1)
    (hf : StrictMono f) :
    ∀ n : ℕ, n + 1 ≤ f n := by
  intro n
  induction n with
  | zero => simp [hf0]
  | succ n ih =>
      have hstep : f n + 1 ≤ f (n + 1) :=
        Nat.succ_le_of_lt (hf (Nat.lt_succ_self n))
      omega

/-- Exact count theorem at an arbitrary cap. -/
theorem one_add_le_ACount_of_two_mul_pow_le
    {α : ℝ}
    (hαirr : IsIrrational α)
    {k N : ℕ}
    (hcap : 2 * 3^k ≤ N + 1) :
    k + 1 ≤ ACount α N := by
  classical
  rcases exists_A_seed_sequence_of_irrational hαirr with
    ⟨f, hf0, hfmono, hfmem, hfbound⟩
  let F : Finset ℕ := (Finset.range (k + 1)).image f
  have hFcard : F.card = k + 1 := by
    dsimp [F]
    calc
      ((Finset.range (k + 1)).image f).card =
          (Finset.range (k + 1)).card := by
        symm
        rw [Finset.card_image_of_injOn]
        intro i hi j hj hij
        exact hfmono.injective hij
      _ = k + 1 := by simp
  have hsubset :
      F ⊆ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A α) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have hpow : 3^i ≤ 3^k := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hik
      rw [pow_add]
      exact Nat.le_mul_of_pos_right _ (by positivity : 0 < 3^d)
    have hfi : f i ≤ N := by
      have hb := hfbound i
      have hmul : 2 * 3^i ≤ 2 * 3^k := Nat.mul_le_mul_left 2 hpow
      omega
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by
      have := strictMono_lower_linear hf0 hfmono i
      omega, hfi⟩, hfmem i⟩
  calc
    k + 1 = F.card := hFcard.symm
    _ ≤ ((Finset.Icc 1 N).filter fun n : ℕ => n ∈ A α).card :=
      Finset.card_le_card hsubset
    _ = ACount α N := rfl

/-- Exact power-scale version of the logarithmic lower bound. -/
theorem ACount_pow_scale_lower_bound
    {α : ℝ}
    (hαirr : IsIrrational α)
    (k : ℕ) :
    k + 1 ≤ ACount α (2 * 3^k - 1) := by
  apply one_add_le_ACount_of_two_mul_pow_le hαirr
  have hpos : 0 < 2 * 3^k := by positivity
  omega

/-- Natural-logarithm form of the universal logarithmic lower bound. -/
theorem one_add_log_three_half_le_ACount
    {α : ℝ}
    (hαirr : IsIrrational α)
    {N : ℕ}
    (hN : 1 ≤ N) :
    Nat.log 3 ((N + 1) / 2) + 1 ≤ ACount α N := by
  apply one_add_le_ACount_of_two_mul_pow_le hαirr
  let m : ℕ := (N + 1) / 2
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hpow : 3 ^ Nat.log 3 m ≤ m :=
    Nat.pow_log_le_self 3 (Nat.ne_of_gt hmpos)
  have htwom : 2 * m ≤ N + 1 := by
    dsimp [m]
    exact Nat.mul_div_le (N + 1) 2
  exact (Nat.mul_le_mul_left 2 hpow).trans htwom

/-- The set `A α` is unbounded for irrational `α`. -/
theorem A_unbounded_of_irrational
    {α : ℝ}
    (hαirr : IsIrrational α) :
    ∀ B : ℕ, ∃ y : ℕ, y ∈ A α ∧ B < y := by
  rcases exists_A_seed_sequence_of_irrational hαirr with
    ⟨f, hf0, hfmono, hfmem, _⟩
  intro B
  refine ⟨f B, hfmem B, ?_⟩
  have hlower := strictMono_lower_linear hf0 hfmono B
  omega

/-! ## Generic sublinear-count theorem -/

namespace NatSetEnumeration

private theorem exists_next
    (S : Set ℕ)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (x : ℕ) :
    ∃ y : ℕ, x < y ∧ y ∈ S := by
  rcases hunbounded x with ⟨y, hyS, hxy⟩
  exact ⟨y, hxy, hyS⟩

noncomputable def nextInSet
    (S : Set ℕ)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (x : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_next S hunbounded x)

lemma nextInSet_gt
    (S : Set ℕ)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (x : ℕ) :
    x < nextInSet S hunbounded x := by
  classical
  exact (Nat.find_spec (exists_next S hunbounded x)).1

lemma nextInSet_mem
    (S : Set ℕ)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (x : ℕ) :
    nextInSet S hunbounded x ∈ S := by
  classical
  exact (Nat.find_spec (exists_next S hunbounded x)).2

lemma no_mem_between_nextInSet
    (S : Set ℕ)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    {x z : ℕ}
    (hzS : z ∈ S)
    (hxz : x < z)
    (hzy : z < nextInSet S hunbounded x) :
    False := by
  classical
  exact (Nat.find_min (exists_next S hunbounded x) hzy) ⟨hxz, hzS⟩

noncomputable def setEnum
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 => nextInSet S hunbounded (setEnum S h1 hunbounded n)

@[simp] lemma setEnum_zero
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y) :
    setEnum S h1 hunbounded 0 = 1 := rfl

lemma setEnum_mem
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) :
    setEnum S h1 hunbounded n ∈ S := by
  induction n with
  | zero => simpa [setEnum] using h1
  | succ n ih =>
      simpa [setEnum] using
        nextInSet_mem S hunbounded (setEnum S h1 hunbounded n)

lemma setEnum_lt_succ
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) :
    setEnum S h1 hunbounded n <
      setEnum S h1 hunbounded (n + 1) := by
  simpa [setEnum] using
    nextInSet_gt S hunbounded (setEnum S h1 hunbounded n)

lemma setEnum_strictMono
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y) :
    StrictMono (setEnum S h1 hunbounded) := by
  exact strictMono_nat_of_lt_succ
    (setEnum_lt_succ S h1 hunbounded)

lemma no_mem_between_setEnum_succ
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    {n x : ℕ}
    (hxS : x ∈ S)
    (hleft : setEnum S h1 hunbounded n < x)
    (hright : x < setEnum S h1 hunbounded (n + 1)) :
    False := by
  simpa [setEnum] using
    no_mem_between_nextInSet S hunbounded hxS hleft hright

def setGap
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) : ℕ :=
  setEnum S h1 hunbounded (n + 1) -
    setEnum S h1 hunbounded n

lemma setGap_pos
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) :
    0 < setGap S h1 hunbounded n := by
  unfold setGap
  have hlt := setEnum_lt_succ S h1 hunbounded n
  omega

lemma setEnum_succ_eq_add_gap
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) :
    setEnum S h1 hunbounded (n + 1) =
      setEnum S h1 hunbounded n + setGap S h1 hunbounded n := by
  unfold setGap
  have hlt := setEnum_lt_succ S h1 hunbounded n
  omega

lemma setGap_mono
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    (hgap : SetConsecutiveGapsNondecreasing S) :
    Monotone (setGap S h1 hunbounded) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  unfold setGap
  exact hgap
    (setEnum S h1 hunbounded n)
    (setEnum S h1 hunbounded (n + 1))
    (setEnum S h1 hunbounded (n + 2))
    (setEnum_mem S h1 hunbounded n)
    (setEnum_mem S h1 hunbounded (n + 1))
    (setEnum_mem S h1 hunbounded (n + 2))
    (setEnum_lt_succ S h1 hunbounded n)
    (setEnum_lt_succ S h1 hunbounded (n + 1))
    (by
      intro x hxS hxleft hxright
      exact no_mem_between_setEnum_succ
        S h1 hunbounded (n := n) hxS hxleft hxright)
    (by
      intro x hxS hxleft hxright
      exact no_mem_between_setEnum_succ
        S h1 hunbounded (n := n + 1) hxS hxleft hxright)

theorem containsInfiniteAP_of_bounded_nondecreasing_gaps
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    (hmono : Monotone (setGap S h1 hunbounded))
    (hbounded : ∃ M, ∀ n, setGap S h1 hunbounded n ≤ M) :
    ContainsInfiniteAP S := by
  classical
  rcases hbounded with ⟨M, hM⟩
  let V : Finset ℕ :=
    (Finset.range (M + 1)).filter
      (fun d => ∃ n : ℕ, setGap S h1 hunbounded n = d)
  have hVne : V.Nonempty := by
    refine ⟨setGap S h1 hunbounded 0, ?_⟩
    dsimp [V]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hM 0)), ⟨0, rfl⟩⟩
  let d : ℕ := V.max' hVne
  have hd_mem : d ∈ V := Finset.max'_mem V hVne
  rcases (Finset.mem_filter.mp hd_mem).2 with ⟨n0, hn0⟩
  have htail : ∀ n, n0 ≤ n → setGap S h1 hunbounded n = d := by
    intro n hn
    have hge : d ≤ setGap S h1 hunbounded n := by
      rw [← hn0]
      exact hmono hn
    have hmem : setGap S h1 hunbounded n ∈ V := by
      dsimp [V]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hM n)), ⟨n, rfl⟩⟩
    have hle : setGap S h1 hunbounded n ≤ d :=
      Finset.le_max' V _ hmem
    exact le_antisymm hle hge
  let a0 := setEnum S h1 hunbounded n0
  let d0 := setGap S h1 hunbounded n0
  have hd0pos : 0 < d0 := by
    dsimp [d0]
    exact setGap_pos S h1 hunbounded n0
  have hformula :
      ∀ k : ℕ,
        setEnum S h1 hunbounded (n0 + k) = a0 + k * d0 := by
    intro k
    induction k with
    | zero =>
        simp [a0]
    | succ k ih =>
        have hgap_eq : setGap S h1 hunbounded (n0 + k) = d0 := by
          dsimp [d0]
          rw [htail (n0 + k) (by omega)]
          rw [← hn0]
        rw [show n0 + (k + 1) = (n0 + k) + 1 by omega]
        rw [setEnum_succ_eq_add_gap S h1 hunbounded (n0 + k)]
        rw [ih, hgap_eq]
        ring
  refine ⟨a0, d0, hd0pos, ?_⟩
  intro k
  have hmem := setEnum_mem S h1 hunbounded (n0 + k)
  simpa [hformula k] using hmem

lemma eventually_gaps_ge_of_noAP
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    (hmono : Monotone (setGap S h1 hunbounded))
    (hnoAP : ¬ ContainsInfiniteAP S)
    (M : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → M ≤ setGap S h1 hunbounded n := by
  by_contra h
  have hbounded : ∃ B, ∀ n, setGap S h1 hunbounded n ≤ B := by
    refine ⟨M, ?_⟩
    intro n
    by_contra hn
    have hMle : M ≤ setGap S h1 hunbounded n := by omega
    have htail : ∀ k, n ≤ k → M ≤ setGap S h1 hunbounded k := by
      intro k hk
      exact hMle.trans (hmono hk)
    exact h ⟨n, htail⟩
  exact hnoAP
    (containsInfiniteAP_of_bounded_nondecreasing_gaps hmono hbounded)

lemma setEnum_lower_linear
    (S : Set ℕ)
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (n : ℕ) :
    n + 1 ≤ setEnum S h1 hunbounded n := by
  induction n with
  | zero => simp [setEnum]
  | succ n ih =>
      have hstep := setEnum_lt_succ S h1 hunbounded n
      omega

lemma exists_setEnum_eq_of_mem
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    {x : ℕ}
    (hxpos : 1 ≤ x)
    (hxS : x ∈ S) :
    ∃ n, setEnum S h1 hunbounded n = x := by
  classical
  let P : ℕ → Prop := fun n => x ≤ setEnum S h1 hunbounded n
  have hex : ∃ n, P n := by
    refine ⟨x, ?_⟩
    dsimp [P]
    have hlower := setEnum_lower_linear S h1 hunbounded x
    omega
  let n0 : ℕ := Nat.find hex
  have hn0 : P n0 := by
    dsimp [n0]
    exact Nat.find_spec hex
  by_cases hn0zero : n0 = 0
  · refine ⟨0, ?_⟩
    have hxle1 : x ≤ 1 := by
      dsimp [P] at hn0
      rw [hn0zero] at hn0
      simpa [setEnum] using hn0
    have hx_eq : x = 1 := le_antisymm hxle1 hxpos
    simp [setEnum, hx_eq]
  · rcases Nat.exists_eq_succ_of_ne_zero hn0zero with ⟨k, hk⟩
    have hnot : ¬ P k := by
      have hklt : k < Nat.find hex := by
        dsimp [n0] at hk
        omega
      exact Nat.find_min hex hklt
    have hleft : setEnum S h1 hunbounded k < x := by
      dsimp [P] at hnot
      omega
    by_cases hxeq : setEnum S h1 hunbounded (k + 1) = x
    · exact ⟨k + 1, hxeq⟩
    · exfalso
      have hright : x < setEnum S h1 hunbounded (k + 1) := by
        have hxle : x ≤ setEnum S h1 hunbounded (k + 1) := by
          simpa [P, hk] using hn0
        omega
      exact no_mem_between_setEnum_succ
        S h1 hunbounded (n := k) hxS hleft hright

lemma setEnum_ge_base_add_mul_of_gaps_ge
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    {M n0 : ℕ}
    (hgapM : ∀ n, n0 ≤ n → M ≤ setGap S h1 hunbounded n) :
    ∀ k : ℕ,
      setEnum S h1 hunbounded (n0 + k) ≥
        setEnum S h1 hunbounded n0 + k * M := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show n0 + (k + 1) = (n0 + k) + 1 by omega]
      rw [setEnum_succ_eq_add_gap S h1 hunbounded (n0 + k)]
      have hg := hgapM (n0 + k) (by omega)
      calc
        setEnum S h1 hunbounded n0 + (k + 1) * M
            = (setEnum S h1 hunbounded n0 + k * M) + M := by ring
        _ ≤ setEnum S h1 hunbounded (n0 + k) +
              setGap S h1 hunbounded (n0 + k) :=
            Nat.add_le_add ih hg

lemma natSetCount_le_enum_prefix
    {S : Set ℕ}
    {h1 : 1 ∈ S}
    {hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y}
    {N K : ℕ}
    (hcover :
      ∀ x : ℕ, 1 ≤ x → x ≤ N → x ∈ S →
        ∃ i : ℕ, i < K ∧ setEnum S h1 hunbounded i = x) :
    natSetCount S N ≤ K := by
  classical
  let F : Finset ℕ := (Finset.range K).image (setEnum S h1 hunbounded)
  have hsubset :
      ((Finset.Icc 1 N).filter fun n : ℕ => n ∈ S) ⊆ F := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rcases hx with ⟨⟨hx1, hxN⟩, hxS⟩
    rcases hcover x hx1 hxN hxS with ⟨i, hiK, hix⟩
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_range.mpr hiK, hix⟩
  calc
    natSetCount S N =
        ((Finset.Icc 1 N).filter fun n : ℕ => n ∈ S).card := rfl
    _ ≤ F.card := Finset.card_le_card hsubset
    _ ≤ (Finset.range K).card := Finset.card_image_le
    _ = K := by simp

end NatSetEnumeration

open NatSetEnumeration

/-- Generic theorem: an unbounded subset of `ℕ` with nondecreasing consecutive
gaps and no infinite arithmetic progression has sublinear counting function. -/
theorem natSetCount_eventually_le_mul_of_gaps
    {S : Set ℕ}
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (hgap : SetConsecutiveGapsNondecreasing S)
    (hnoAP : ¬ ContainsInfiniteAP S) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (natSetCount S N : ℝ) ≤ ε * (N : ℝ) := by
  intro ε hε
  obtain ⟨M, hMgt⟩ := exists_nat_gt (2 / ε)
  have hMposR : 0 < (M : ℝ) := by
    exact (div_pos (by norm_num : (0 : ℝ) < 2) hε).trans hMgt
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have htwoDiv : (2 : ℝ) / (M : ℝ) < ε := by
    have hmul : (2 : ℝ) < ε * (M : ℝ) := by
      calc
        (2 : ℝ) = ε * (2 / ε) := by
          field_simp [ne_of_gt hε]
        _ < ε * (M : ℝ) := mul_lt_mul_of_pos_left hMgt hε
    exact (div_lt_iff₀ hMposR).2 hmul
  have hInv : (1 : ℝ) / (M : ℝ) < ε / 2 := by
    calc
      (1 : ℝ) / (M : ℝ) = ((2 : ℝ) / (M : ℝ)) / 2 := by ring
      _ < ε / 2 := div_lt_div_of_pos_right htwoDiv (by norm_num)
  let E := setEnum S h1 hunbounded
  let G := setGap S h1 hunbounded
  have hmono : Monotone G := setGap_mono (S := S) (h1 := h1)
    (hunbounded := hunbounded) hgap
  rcases eventually_gaps_ge_of_noAP
      (S := S) (h1 := h1) (hunbounded := hunbounded)
      hmono hnoAP M with ⟨n0, hn0⟩
  obtain ⟨N0, hN0gt⟩ :=
    exists_nat_gt (((2 : ℝ) * (n0 + 1 : ℝ)) / ε)
  refine (eventually_ge_atTop N0).mono ?_
  intro N hNN0
  have hlarge :
      (n0 + 1 : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    have hNgt :
        ((2 : ℝ) * (n0 + 1 : ℝ)) / ε < (N : ℝ) := by
      exact hN0gt.trans_le (by exact_mod_cast hNN0)
    have hmul :
        (2 : ℝ) * (n0 + 1 : ℝ) < ε * (N : ℝ) := by
      calc
        (2 : ℝ) * (n0 + 1 : ℝ) =
            ε * (((2 : ℝ) * (n0 + 1 : ℝ)) / ε) := by
              field_simp [ne_of_gt hε]
        _ < ε * (N : ℝ) := mul_lt_mul_of_pos_left hNgt hε
    nlinarith
  have hcountNat :
      natSetCount S N ≤ n0 + N / M + 1 := by
    refine natSetCount_le_enum_prefix
      (S := S) (h1 := h1) (hunbounded := hunbounded)
      (N := N) (K := n0 + N / M + 1) ?_
    intro x hx1 hxN hxS
    rcases exists_setEnum_eq_of_mem
        (S := S) (h1 := h1) (hunbounded := hunbounded)
        hx1 hxS with ⟨i, hi⟩
    refine ⟨i, ?_, hi⟩
    by_cases hin : i < n0
    · have hn0ltK : n0 < n0 + N / M + 1 :=
        Nat.lt_succ_of_le (Nat.le_add_right n0 (N / M))
      exact hin.trans hn0ltK
    · have hni : n0 ≤ i := le_of_not_gt hin
      let k : ℕ := i - n0
      have hi_eq : i = n0 + k := by
        dsimp [k]
        omega
      have hlow :
          E (n0 + k) ≥ E n0 + k * M := by
        dsimp [E]
        exact setEnum_ge_base_add_mul_of_gaps_ge
          (S := S) (h1 := h1) (hunbounded := hunbounded)
          (M := M) (n0 := n0) hn0 k
      have hkMle : k * M ≤ N := by
        have hxle : E (n0 + k) ≤ N := by
          dsimp [E]
          rw [← hi_eq, hi]
          exact hxN
        exact (Nat.le_add_left (k * M) (E n0)).trans (hlow.trans hxle)
      have hkle : k ≤ N / M :=
        (Nat.le_div_iff_mul_le hMpos).2 hkMle
      dsimp [k] at hkle
      omega
  have hcountR :
      (natSetCount S N : ℝ) ≤
        (n0 + N / M + 1 : ℕ) := by
    exact_mod_cast hcountNat
  have hdivN :
      ((N / M : ℕ) : ℝ) ≤ (ε / 2) * (N : ℝ) := by
    calc
      ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) := Nat.cast_div_le
      _ = ((1 : ℝ) / (M : ℝ)) * (N : ℝ) := by ring
      _ ≤ (ε / 2) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hInv.le (by positivity)
  have hsplit :
      ((n0 + N / M + 1 : ℕ) : ℝ) =
        (n0 + 1 : ℝ) + ((N / M : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hsplit] at hcountR
  calc
    (natSetCount S N : ℝ)
        ≤ (n0 + 1 : ℝ) + ((N / M : ℕ) : ℝ) := hcountR
    _ ≤ (ε / 2) * (N : ℝ) + (ε / 2) * (N : ℝ) :=
        add_le_add hlarge hdivN
    _ = ε * (N : ℝ) := by ring

/-- Sublinear counting for every irrational floor-sum set. -/
theorem ACount_eventually_le_mul
    {α : ℝ}
    (hαirr : IsIrrational α) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (ACount α N : ℝ) ≤ ε * (N : ℝ) := by
  exact natSetCount_eventually_le_mul_of_gaps
    (one_mem_A α)
    (A_unbounded_of_irrational hαirr)
    (AGapsNondecreasing_of_irrational hαirr)
    (irrational_no_infiniteAP hαirr)

end

end IrrationalityAr
