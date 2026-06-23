import IrrationalityAr.CanonicalBlockGrowth

open Filter
open scoped BigOperators
open scoped Topology

namespace IrrationalityAr

/-!
# Reciprocal block duality

This module proves the coefficient-side reciprocal swap and the resulting
parity bicoloring for canonical continued-fraction blocks.

The global bridge
`IsSimpleCFExpansion α a → IsSimpleCFExpansion (1 / α) (reciprocalCoeff a)`
is intentionally not asserted here yet.  The membership theorems below take
that bridge as an explicit hypothesis, so the file remains fully proved.
-/

/-- Coefficients of the reciprocal continued fraction.

Mathematically, if `α = [a₀; a₁, a₂, ...]` and `α > 1`, then
`1 / α = [0; a₀, a₁, a₂, ...]`. -/
def reciprocalCoeff (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => a n

@[simp] theorem reciprocalCoeff_zero (a : ℕ → ℕ) :
    reciprocalCoeff a 0 = 0 := rfl

@[simp] theorem reciprocalCoeff_succ (a : ℕ → ℕ) (n : ℕ) :
    reciprocalCoeff a (n + 1) = a n := rfl

/-- Numerators for the reciprocal coefficient sequence are shifted original
denominators: `p'_{n+1} = q_n`. -/
theorem continuantNum_reciprocalCoeff_succ (a : ℕ → ℕ) :
    ∀ n : ℕ,
      continuantNum (reciprocalCoeff a) (n + 1) = continuantDen a n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [reciprocalCoeff, continuantNum, continuantDen]
  | one =>
      simp [reciprocalCoeff, continuantNum, continuantDen]
  | more n ih0 ih1 =>
      calc
        continuantNum (reciprocalCoeff a) ((n + 2) + 1)
            = reciprocalCoeff a (n + 3) *
                continuantNum (reciprocalCoeff a) (n + 2) +
              continuantNum (reciprocalCoeff a) (n + 1) := by
                rfl
        _ = a (n + 2) * continuantDen a (n + 1) + continuantDen a n := by
                simp [reciprocalCoeff, ih0, ih1]
        _ = continuantDen a (n + 2) := by
                rfl

/-- Denominators for the reciprocal coefficient sequence are shifted original
numerators: `q'_{n+1} = p_n`. -/
theorem continuantDen_reciprocalCoeff_succ (a : ℕ → ℕ) :
    ∀ n : ℕ,
      continuantDen (reciprocalCoeff a) (n + 1) = continuantNum a n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [reciprocalCoeff, continuantNum, continuantDen]
  | one =>
      simp [reciprocalCoeff, continuantNum, continuantDen]
  | more n ih0 ih1 =>
      calc
        continuantDen (reciprocalCoeff a) ((n + 2) + 1)
            = reciprocalCoeff a (n + 3) *
                continuantDen (reciprocalCoeff a) (n + 2) +
              continuantDen (reciprocalCoeff a) (n + 1) := by
                rfl
        _ = a (n + 2) * continuantNum a (n + 1) + continuantNum a n := by
                simp [reciprocalCoeff, ih0, ih1]
        _ = continuantNum a (n + 2) := by
                rfl

/-- Previous numerators also shift to previous original denominators. -/
theorem continuantNumPrev_reciprocalCoeff_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantNumPrev (reciprocalCoeff a) (n + 1) =
      continuantDenPrev a n := by
  cases n with
  | zero =>
      simp [reciprocalCoeff, continuantNumPrev, continuantNum,
        continuantDenPrev]
  | succ n =>
      simp [continuantNumPrev, continuantDenPrev,
        continuantNum_reciprocalCoeff_succ]

/-- Previous denominators also shift to previous original numerators. -/
theorem continuantDenPrev_reciprocalCoeff_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantDenPrev (reciprocalCoeff a) (n + 1) =
      continuantNumPrev a n := by
  cases n with
  | zero =>
      simp [continuantDenPrev, continuantDen, continuantNumPrev]
  | succ n =>
      simp [continuantDenPrev, continuantNumPrev,
        continuantDen_reciprocalCoeff_succ]

/-- The reciprocal block numerator is the original block denominator. -/
@[simp] theorem CFBlockNumerator_reciprocalCoeff_succ
    (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockNumerator (reciprocalCoeff a) (j + 1) t =
      CFBlockDenominator a j t := by
  unfold CFBlockNumerator CFBlockDenominator
  rw [continuantNumPrev_reciprocalCoeff_succ,
    continuantNum_reciprocalCoeff_succ]

/-- The reciprocal block denominator is the original block numerator. -/
@[simp] theorem CFBlockDenominator_reciprocalCoeff_succ
    (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockDenominator (reciprocalCoeff a) (j + 1) t =
      CFBlockNumerator a j t := by
  unfold CFBlockNumerator CFBlockDenominator
  rw [continuantDenPrev_reciprocalCoeff_succ,
    continuantDen_reciprocalCoeff_succ]

@[simp] theorem reciprocalCoeff_block_bound (a : ℕ → ℕ) (j : ℕ) :
    reciprocalCoeff a ((j + 1) + 1) = a (j + 1) := by
  rfl

/-! ## Local parity tools -/

/-- A reduced natural fraction cannot have both numerator and denominator even. -/
lemma odd_or_odd_of_reducedFraction {P Q : ℕ}
    (hred : ReducedFraction P Q) : Odd P ∨ Odd Q := by
  rcases Nat.even_or_odd P with hPeven | hPodd
  · rcases Nat.even_or_odd Q with hQeven | hQodd
    · exfalso
      have h2gcd : 2 ∣ Nat.gcd P Q :=
        Nat.dvd_gcd hPeven.two_dvd hQeven.two_dvd
      have hgcd : Nat.gcd P Q = 1 := hred.2.gcd_eq_one
      rw [hgcd] at h2gcd
      norm_num at h2gcd
    · exact Or.inr hQodd
  · exact Or.inl hPodd

/-- Every canonical principal/intermediate block point has an odd numerator or
an odd denominator.  This is the basic two-color cover. -/
theorem CFBlockNumerator_or_denominator_odd
    (a : ℕ → ℕ) {j t : ℕ} (ht1 : 1 ≤ t) :
    Odd (CFBlockNumerator a j t) ∨
      Odd (CFBlockDenominator a j t) := by
  have hred :
      ReducedFraction
        (CFBlockNumerator a j t)
        (CFBlockDenominator a j t) := by
    simpa [CFBlockNumerator, CFBlockDenominator] using
      reducedFraction_pathPair a (n := j) (t := t) ht1
  exact odd_or_odd_of_reducedFraction hred

/-! ## Membership from each parity color -/

/-- Original-color membership: an odd block numerator certifies the shifted
denominator in `A α`. -/
theorem mem_A_of_CFBlockNumerator_odd
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hoddP : Odd (CFBlockNumerator a j t))
    (hQ2 : 2 ≤ CFBlockDenominator a j t) :
    CFBlockDenominator a j t - 1 ∈ A α := by
  rw [A_eq_oddBlockASet_of_IsSimpleCFExpansion hαpos hαirr hcf]
  exact ⟨j, t, ht1, htle, hoddP, hQ2, rfl⟩

/-- Reciprocal-color membership, assuming `reciprocalCoeff a` is already known
to be a simple CF expansion of `1 / α`. -/
theorem mem_A_inv_of_CFBlockDenominator_odd_given_reciprocal_cf
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hβpos : 0 < 1 / α)
    (hβirr : IsIrrational (1 / α))
    (hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a))
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hoddQ : Odd (CFBlockDenominator a j t))
    (hP2 : 2 ≤ CFBlockNumerator a j t) :
    CFBlockNumerator a j t - 1 ∈ A (1 / α) := by
  rw [A_eq_oddBlockASet_of_IsSimpleCFExpansion hβpos hβirr hβcf]
  refine ⟨j + 1, t, ht1, ?_, ?_, ?_, ?_⟩
  · simpa using htle
  · simpa [CFBlockNumerator_reciprocalCoeff_succ] using hoddQ
  · simpa [CFBlockDenominator_reciprocalCoeff_succ] using hP2
  · simp [CFBlockDenominator_reciprocalCoeff_succ]

/-- One-point reciprocal block duality.  Under the reciprocal CF bridge, an odd
`P` certifies `Q - 1 ∈ A α`, while an odd `Q` certifies
`P - 1 ∈ A (1 / α)`. -/
theorem reciprocal_block_duality_point_given_reciprocal_cf
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (hβpos : 0 < 1 / α)
    (hβirr : IsIrrational (1 / α))
    (hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a))
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hQ2 : 2 ≤ CFBlockDenominator a j t)
    (hP2 : 2 ≤ CFBlockNumerator a j t) :
    (Odd (CFBlockNumerator a j t) →
        CFBlockDenominator a j t - 1 ∈ A α) ∧
      (Odd (CFBlockDenominator a j t) →
        CFBlockNumerator a j t - 1 ∈ A (1 / α)) := by
  constructor
  · intro hoddP
    exact mem_A_of_CFBlockNumerator_odd
      (α := α) (a := a) (j := j) (t := t)
      hαpos hαirr hcf ht1 htle hoddP hQ2
  · intro hoddQ
    exact mem_A_inv_of_CFBlockDenominator_odd_given_reciprocal_cf
      (α := α) (a := a) (j := j) (t := t)
      hβpos hβirr hβcf ht1 htle hoddQ hP2

/-- If the reciprocal-side denominator `P` is valid, then every canonical block
point certifies at least one side. -/
theorem reciprocal_block_point_certifies_one_side_given_reciprocal_cf
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (hβpos : 0 < 1 / α)
    (hβirr : IsIrrational (1 / α))
    (hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a))
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hP2 : 2 ≤ CFBlockNumerator a j t) :
    (CFBlockDenominator a j t - 1 ∈ A α) ∨
      (CFBlockNumerator a j t - 1 ∈ A (1 / α)) := by
  let P := CFBlockNumerator a j t
  let Q := CFBlockDenominator a j t
  have hred : ReducedFraction P Q := by
    dsimp [P, Q]
    simpa [CFBlockNumerator, CFBlockDenominator] using
      reducedFraction_pathPair a (n := j) (t := t) ht1
  rcases Nat.even_or_odd Q with hQeven | hQodd
  · have hPodd : Odd P := by
      rcases odd_or_odd_of_reducedFraction hred with hPodd | hQodd'
      · exact hPodd
      · exact False.elim ((Nat.not_even_iff_odd.mpr hQodd') hQeven)
    have hQ2 : 2 ≤ Q := by
      have hQpos : 0 < Q := hred.1
      have hQne1 : Q ≠ 1 := by
        intro hQeq
        have hEven1 : Even (1 : ℕ) := by
          rw [← hQeq]
          exact hQeven
        exact (by norm_num : ¬ Even (1 : ℕ)) hEven1
      omega
    left
    exact mem_A_of_CFBlockNumerator_odd
      (α := α) (a := a) (j := j) (t := t)
      hαpos hαirr hcf ht1 htle (by simpa [P] using hPodd)
      (by simpa [Q] using hQ2)
  · right
    exact mem_A_inv_of_CFBlockDenominator_odd_given_reciprocal_cf
      (α := α) (a := a) (j := j) (t := t)
      hβpos hβirr hβcf ht1 htle (by simpa [Q] using hQodd) hP2

/-! ## Strong finite bicoloring inside each block -/

/-- The reciprocal color in the original block: indices for which the original
denominator `Q_{j,t}` is odd. -/
def denominatorOddBlock (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (a (j + 1))).filter fun t : ℕ =>
    Odd (CFBlockDenominator a j t)

@[simp] theorem mem_denominatorOddBlock_iff
    {a : ℕ → ℕ} {j t : ℕ} :
    t ∈ denominatorOddBlock a j ↔
      1 ≤ t ∧ t ≤ a (j + 1) ∧ Odd (CFBlockDenominator a j t) := by
  simp [denominatorOddBlock, and_assoc]

/-- The reciprocal color is literally the numerator-selected block of the
reciprocal coefficient sequence, at block index `j + 1`. -/
theorem denominatorOddBlock_eq_reciprocal_canonicalOddBlock
    (a : ℕ → ℕ) (j : ℕ) :
    denominatorOddBlock a j = canonicalOddBlock (reciprocalCoeff a) (j + 1) := by
  ext t
  rw [mem_denominatorOddBlock_iff, mem_canonicalOddBlock_iff]
  constructor
  · intro ht
    exact ⟨ht.1, by simpa using ht.2.1,
      by simpa [CFBlockNumerator_reciprocalCoeff_succ] using ht.2.2⟩
  · intro ht
    exact ⟨ht.1, by simpa using ht.2.1,
      by simpa [CFBlockNumerator_reciprocalCoeff_succ] using ht.2.2⟩

/-- Numerator color has the existing half-block lower bound. -/
theorem numeratorOddBlock_card_lower_bound
    (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ (canonicalOddBlock a j).card := by
  simpa [canonicalBlockLength] using canonicalBlockLength_lower_bound a j

/-- Denominator color has the same half-block lower bound, by the reciprocal
block identity. -/
theorem denominatorOddBlock_card_lower_bound
    (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ (denominatorOddBlock a j).card := by
  have h := canonicalBlockLength_lower_bound (reciprocalCoeff a) (j + 1)
  have hcard :
      (canonicalOddBlock (reciprocalCoeff a) (j + 1)).card =
        (denominatorOddBlock a j).card := by
    rw [← denominatorOddBlock_eq_reciprocal_canonicalOddBlock a j]
  simpa [canonicalBlockLength, reciprocalCoeff, hcard] using h

/-- Strong bicoloring cover: every index in the full block lies in the
numerator color or in the denominator color. -/
theorem reciprocal_bicolor_block_cover
    (a : ℕ → ℕ) (j : ℕ) :
    Finset.Icc 1 (a (j + 1)) ⊆
      canonicalOddBlock a j ∪ denominatorOddBlock a j := by
  intro t ht
  rw [Finset.mem_union]
  rw [Finset.mem_Icc] at ht
  have hodd_or := CFBlockNumerator_or_denominator_odd
    (a := a) (j := j) (t := t) ht.1
  rcases hodd_or with hoddP | hoddQ
  · left
    rw [mem_canonicalOddBlock_iff]
    exact ⟨ht.1, ht.2, hoddP⟩
  · right
    rw [mem_denominatorOddBlock_iff]
    exact ⟨ht.1, ht.2, hoddQ⟩

/-- Strong bicoloring package for one block.  Both colors occupy at least half
the available indices, and their union covers the block. -/
theorem reciprocal_bicolor_block_package
    (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ (canonicalOddBlock a j).card ∧
      a (j + 1) / 2 ≤ (denominatorOddBlock a j).card ∧
        Finset.Icc 1 (a (j + 1)) ⊆
          canonicalOddBlock a j ∪ denominatorOddBlock a j := by
  exact ⟨numeratorOddBlock_card_lower_bound a j,
    denominatorOddBlock_card_lower_bound a j,
    reciprocal_bicolor_block_cover a j⟩

/-- Certificate-level bicoloring for a block, under the reciprocal CF bridge
and a local lower bound `2 ≤ P_{j,t}` for all indices in the block. -/
theorem reciprocal_bicolor_block_certificates_given_reciprocal_cf
    {α : ℝ} {a : ℕ → ℕ} {j : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (hβpos : 0 < 1 / α)
    (hβirr : IsIrrational (1 / α))
    (hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a))
    (hP2 : ∀ t : ℕ, 1 ≤ t → t ≤ a (j + 1) →
      2 ≤ CFBlockNumerator a j t) :
    ∀ t : ℕ, t ∈ Finset.Icc 1 (a (j + 1)) →
      (CFBlockDenominator a j t - 1 ∈ A α) ∨
        (CFBlockNumerator a j t - 1 ∈ A (1 / α)) := by
  intro t ht
  rw [Finset.mem_Icc] at ht
  exact reciprocal_block_point_certifies_one_side_given_reciprocal_cf
    (α := α) (a := a) (j := j) (t := t)
    hαpos hαirr hcf hβpos hβirr hβcf ht.1 ht.2
    (hP2 t ht.1 ht.2)

/-! ## Reciprocal continued-fraction bridge -/

/-- Project-local irrationality is preserved by reciprocal. -/
theorem isIrrational_one_div {x : ℝ} (hx : IsIrrational x) :
    IsIrrational (1 / x) := by
  intro hrat
  rcases hrat with ⟨q, hq⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    exact hx ⟨0, by simp [hxzero]⟩
  apply hx
  refine ⟨q⁻¹, ?_⟩
  rw [Rat.cast_inv, hq]
  field_simp [hx0]

/-- If `α > 1` and `a` is a simple CF expansion of `α`, then the head
coefficient is positive. -/
theorem head_pos_of_one_lt_of_IsSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a) :
    0 < a 0 := by
  have hbounds := simpleCF_head_bounds hcf
  by_contra hnot
  have ha0 : a 0 = 0 := Nat.eq_zero_of_not_pos hnot
  have hαlt1 : α < 1 := by
    have h := hbounds.2
    rw [ha0] at h
    norm_num at h
    exact h
  exact (not_lt_of_ge hαgt1.le) hαlt1

/-- Numerator continuants are positive once the head coefficient is positive. -/
theorem continuantNum_pos_of_head_pos
    {a : ℕ → ℕ}
    (hhead : 0 < a 0) :
    ∀ n : ℕ, 0 < continuantNum a n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [continuantNum] using hhead
  | one =>
      simp [continuantNum]
  | more n ih0 _ih1 =>
      rw [continuantNum]
      exact Nat.add_pos_right _ ih0

/-- Previous numerator continuants are positive from block `1` onward. -/
theorem continuantNumPrev_pos_of_head_pos
    {a : ℕ → ℕ}
    (hhead : 0 < a 0) {n : ℕ} (hn : 0 < n) :
    0 < continuantNumPrev a n := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  simpa [continuantNumPrev] using continuantNum_pos_of_head_pos hhead m

/-- For `α > 1`, every original block numerator `P_{j,t}` with `t ≥ 1` is at
least `2`. -/
theorem two_le_CFBlockNumerator_of_one_lt
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a)
    (ht1 : 1 ≤ t) :
    2 ≤ CFBlockNumerator a j t := by
  have hhead : 0 < a 0 :=
    head_pos_of_one_lt_of_IsSimpleCFExpansion hαgt1 hcf
  have hnumpos : ∀ n : ℕ, 0 < continuantNum a n :=
    continuantNum_pos_of_head_pos hhead
  unfold CFBlockNumerator
  cases j with
  | zero =>
      simp [continuantNumPrev, continuantNum]
      have hprod : 0 < t * a 0 := Nat.mul_pos ht1 hhead
      omega
  | succ j =>
      simp [continuantNumPrev]
      have hprev : 0 < continuantNum a j := hnumpos j
      have hcurr : 0 < continuantNum a (j + 1) := hnumpos (j + 1)
      have hprod : 0 < t * continuantNum a (j + 1) :=
        Nat.mul_pos ht1 hcurr
      omega

/-- Positivity helper for the numerator affine form in the original tail
formula. -/
lemma original_tail_numerator_pos
    {α β : ℝ} {a : ℕ → ℕ} {n : ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a)
    (hβpos : 0 < β) :
    0 < β * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ) := by
  have hhead : 0 < a 0 :=
    head_pos_of_one_lt_of_IsSimpleCFExpansion hαgt1 hcf
  have hnumpos : 0 < continuantNum a n :=
    continuantNum_pos_of_head_pos hhead n
  have hmain : 0 < β * (continuantNum a n : ℝ) :=
    mul_pos hβpos (by exact_mod_cast hnumpos)
  have hprev_nonneg : 0 ≤ (continuantNumPrev a n : ℝ) := by positivity
  linarith

/-- Positivity helper for the denominator affine form in the original tail
formula. -/
lemma original_tail_denominator_pos
    {β : ℝ} {a : ℕ → ℕ} {n : ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hβpos : 0 < β) :
    0 < β * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) := by
  have hqone : 1 ≤ continuantDen a n :=
    one_le_continuantDen_of_partials_pos_global a hpos n
  have hqpos : 0 < (continuantDen a n : ℝ) := by exact_mod_cast hqone
  have hmain : 0 < β * (continuantDen a n : ℝ) := mul_pos hβpos hqpos
  have hprev_nonneg : 0 ≤ (continuantDenPrev a n : ℝ) := by positivity
  linarith

/-- Algebraic reciprocal of one common-prefix map after the continuant swap. -/
lemma commonPrefixMap_reciprocalCoeff_succ_eq_inv_commonPrefixMap
    {α β : ℝ} {a : ℕ → ℕ} {n : ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a)
    (hβpos : 0 < β) :
    commonPrefixMap (reciprocalCoeff a) (n + 1) β =
      1 / commonPrefixMap a n β := by
  have hApos :
      0 < β * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ) :=
    original_tail_numerator_pos (α := α) (a := a) hαgt1 hcf hβpos
  have hBpos :
      0 < β * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) :=
    original_tail_denominator_pos (a := a) hcf.1 hβpos
  have hAne : β * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ) ≠ 0 :=
    ne_of_gt hApos
  have hBne : β * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) ≠ 0 :=
    ne_of_gt hBpos
  unfold commonPrefixMap
  rw [continuantNum_reciprocalCoeff_succ]
  rw [continuantNumPrev_reciprocalCoeff_succ]
  rw [continuantDen_reciprocalCoeff_succ]
  rw [continuantDenPrev_reciprocalCoeff_succ]
  field_simp [hAne, hBne]

/-- The reciprocal coefficient sequence has the required tail witnesses. -/
theorem reciprocalCoeff_hasContinuedFractionTails
    {α : ℝ} {a : ℕ → ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a) :
    HasContinuedFractionTails (1 / α) (reciprocalCoeff a) := by
  intro n
  cases n with
  | zero =>
      refine ⟨α, ?_, ?_, ?_⟩
      · simpa [reciprocalCoeff] using (simpleCF_head_bounds hcf).1
      · simpa [reciprocalCoeff] using (simpleCF_head_bounds hcf).2
      · simp [reciprocalCoeff, continuantNum, continuantNumPrev,
          continuantDen, continuantDenPrev]
  | succ n =>
      rcases hcf.2.2 n with ⟨β, hβlo, hβhi, hαeq⟩
      have hβpos : 0 < β := by
        have ha_pos_R : (0 : ℝ) < (a (n + 1) : ℝ) := by
          exact_mod_cast hcf.1 n
        exact lt_trans ha_pos_R hβlo
      refine ⟨β, ?_, ?_, ?_⟩
      · simpa [reciprocalCoeff] using hβlo
      · simpa [reciprocalCoeff] using hβhi
      · calc
          1 / α = 1 / commonPrefixMap a n β := by
            rw [hαeq]
            rfl
          _ = commonPrefixMap (reciprocalCoeff a) (n + 1) β := by
            rw [commonPrefixMap_reciprocalCoeff_succ_eq_inv_commonPrefixMap
              (α := α) (a := a) hαgt1 hcf hβpos]

/-- Convergents of the reciprocal coefficient sequence tend to `1 / α`. -/
theorem reciprocalCoeff_convergents_tendsto
    {α : ℝ} {a : ℕ → ℕ}
    (hαgt1 : 1 < α)
    (hcf : IsSimpleCFExpansion α a) :
    Tendsto
      (fun n : ℕ =>
        (continuantNum (reciprocalCoeff a) n : ℝ) /
          (continuantDen (reciprocalCoeff a) n : ℝ))
      atTop
      (𝓝 (1 / α)) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hαgt1
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hhead : 0 < a 0 :=
    head_pos_of_one_lt_of_IsSimpleCFExpansion hαgt1 hcf
  have hnumpos : ∀ n : ℕ, 0 < continuantNum a n :=
    continuantNum_pos_of_head_pos hhead
  have hlim_inv :
      Tendsto
        (fun n : ℕ =>
          (continuantDen a n : ℝ) / (continuantNum a n : ℝ))
        atTop
        (𝓝 (1 / α)) := by
    have hlim_original := hcf.2.1
    have hlim_recip := hlim_original.inv₀ hαne
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hlim_recip
  have hshift :
      Tendsto
        (fun n : ℕ =>
          (continuantNum (reciprocalCoeff a) (n + 1) : ℝ) /
            (continuantDen (reciprocalCoeff a) (n + 1) : ℝ))
        atTop
        (𝓝 (1 / α)) := by
    simpa [continuantNum_reciprocalCoeff_succ,
      continuantDen_reciprocalCoeff_succ] using hlim_inv
  exact (Filter.tendsto_add_atTop_iff_nat
    (f := fun n : ℕ =>
      (continuantNum (reciprocalCoeff a) n : ℝ) /
        (continuantDen (reciprocalCoeff a) n : ℝ)) 1).1 hshift

/-- Main bridge: inserting a head `0` gives the reciprocal simple CF expansion. -/
theorem reciprocalCoeff_isSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ}
    (hαgt1 : 1 < α)
    (_hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a) :
    IsSimpleCFExpansion (1 / α) (reciprocalCoeff a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        simpa [reciprocalCoeff] using
          head_pos_of_one_lt_of_IsSimpleCFExpansion hαgt1 hcf
    | succ n =>
        simpa [reciprocalCoeff] using hcf.1 n
  · exact reciprocalCoeff_convergents_tendsto hαgt1 hcf
  · exact reciprocalCoeff_hasContinuedFractionTails hαgt1 hcf

/-- Public one-point reciprocal block duality, with no explicit reciprocal-CF
hypothesis. -/
theorem reciprocal_block_duality_point
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαgt1 : 1 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hQ2 : 2 ≤ CFBlockDenominator a j t) :
    (Odd (CFBlockNumerator a j t) →
        CFBlockDenominator a j t - 1 ∈ A α) ∧
      (Odd (CFBlockDenominator a j t) →
        CFBlockNumerator a j t - 1 ∈ A (1 / α)) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hαgt1
  have hβpos : 0 < 1 / α := one_div_pos.mpr hαpos
  have hβirr : IsIrrational (1 / α) := isIrrational_one_div hαirr
  have hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a) :=
    reciprocalCoeff_isSimpleCFExpansion hαgt1 hαirr hcf
  have hP2 : 2 ≤ CFBlockNumerator a j t :=
    two_le_CFBlockNumerator_of_one_lt hαgt1 hcf ht1
  exact reciprocal_block_duality_point_given_reciprocal_cf
    (α := α) (a := a) (j := j) (t := t)
    hαpos hαirr hcf hβpos hβirr hβcf ht1 htle hQ2 hP2

/-- Public theorem: every valid block point certifies at least one of the
reciprocal `A`-sets. -/
theorem reciprocal_block_point_certifies_one_side
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hαgt1 : 1 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a)
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1)) :
    (CFBlockDenominator a j t - 1 ∈ A α) ∨
      (CFBlockNumerator a j t - 1 ∈ A (1 / α)) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hαgt1
  have hβpos : 0 < 1 / α := one_div_pos.mpr hαpos
  have hβirr : IsIrrational (1 / α) := isIrrational_one_div hαirr
  have hβcf : IsSimpleCFExpansion (1 / α) (reciprocalCoeff a) :=
    reciprocalCoeff_isSimpleCFExpansion hαgt1 hαirr hcf
  have hP2 : 2 ≤ CFBlockNumerator a j t :=
    two_le_CFBlockNumerator_of_one_lt hαgt1 hcf ht1
  exact reciprocal_block_point_certifies_one_side_given_reciprocal_cf
    (α := α) (a := a) (j := j) (t := t)
    hαpos hαirr hcf hβpos hβirr hβcf ht1 htle hP2

end IrrationalityAr
