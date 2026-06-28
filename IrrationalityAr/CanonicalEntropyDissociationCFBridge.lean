import IrrationalityAr.Ramanujan


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

noncomputable section

/-!
# Canonical entropy/dissociation: continued-fraction bridge foundations

This file starts the continued-fraction-specific layer above
`CanonicalEntropyDissociation`.  The hard remaining bridge is to prove exact
arithmetic-progression geometry for the positive part of each selected
canonical block; the lemmas here package the positive local blocks, their
canonical step, and the dyadic packets used by that later argument.
-/

/-- The selected denominator block with the possible initial shifted value
`0` removed.  Recall that `canonicalOddDenominatorBlock a j` stores
`Q_{j,t} - 1`. -/
def positiveCanonicalOddDenominatorBlock
    (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (canonicalOddDenominatorBlock a j).erase 0

/-- The usable positive length of the `j`-th selected block. -/
def positiveCanonicalBlockLength
    (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  (positiveCanonicalOddDenominatorBlock a j).card

lemma positiveCanonicalOddDenominatorBlock_subset_certifiedOddBlocks
    {a : ℕ → ℕ} {j J : ℕ}
    (hj : j < J) :
    positiveCanonicalOddDenominatorBlock a j ⊆ certifiedOddBlocks a J := by
  classical
  intro n hn
  rw [positiveCanonicalOddDenominatorBlock, Finset.mem_erase] at hn
  rcases hn with ⟨hn0, hnblock⟩
  rw [mem_certifiedOddBlocks_iff]
  exact ⟨hn0, j, hj, hnblock⟩

lemma positiveCanonicalBlockLength_le_canonicalBlockLength
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    positiveCanonicalBlockLength a j ≤ canonicalBlockLength a j := by
  classical
  unfold positiveCanonicalBlockLength positiveCanonicalOddDenominatorBlock
  calc
    ((canonicalOddDenominatorBlock a j).erase 0).card
        ≤ (canonicalOddDenominatorBlock a j).card := Finset.card_erase_le
    _ = canonicalBlockLength a j := canonicalOddDenominatorBlock_card a hpos j

lemma two_le_CFBlockDenominator_of_pos_index
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j t : ℕ}
    (hjpos : 0 < j)
    (ht : 1 ≤ t) :
    2 ≤ CFBlockDenominator a j t := by
  rcases j with _ | k
  · omega
  unfold CFBlockDenominator
  have hprev : 1 ≤ continuantDenPrev a (k + 1) := by
    simpa [continuantDenPrev] using
      one_le_continuantDen_of_partials_pos_global a hpos k
  have hq : 1 ≤ continuantDen a (k + 1) :=
    one_le_continuantDen_of_partials_pos_global a hpos (k + 1)
  have hmul : 1 ≤ t * continuantDen a (k + 1) :=
    Nat.mul_le_mul ht hq
  omega

/-- Only the first global block can contain the shifted denominator `0`. -/
lemma zero_mem_canonicalOddDenominatorBlock_imp_index_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j : ℕ}
    (hzero : 0 ∈ canonicalOddDenominatorBlock a j) :
    j = 0 := by
  classical
  by_contra hj0
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  rw [canonicalOddDenominatorBlock] at hzero
  rcases Finset.mem_image.mp hzero with ⟨t, ht, ht0⟩
  have ht1 : 1 ≤ t := (mem_canonicalOddBlock_iff.mp ht).1
  have hQ2 : 2 ≤ CFBlockDenominator a j t :=
    two_le_CFBlockDenominator_of_pos_index hpos hjpos ht1
  change CFBlockDenominator a j t - 1 = 0 at ht0
  omega

lemma positiveCanonicalBlockLength_eq_canonicalBlockLength_of_pos_index
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j : ℕ} (hj : 0 < j) :
    positiveCanonicalBlockLength a j = canonicalBlockLength a j := by
  classical
  unfold positiveCanonicalBlockLength positiveCanonicalOddDenominatorBlock
  have hznot : 0 ∉ canonicalOddDenominatorBlock a j := by
    intro hz
    have hj0 := zero_mem_canonicalOddDenominatorBlock_imp_index_zero hpos hz
    omega
  simp [hznot, canonicalOddDenominatorBlock_card a hpos j]

lemma canonicalBlockLength_le_positiveCanonicalBlockLength_add_one
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    canonicalBlockLength a j ≤ positiveCanonicalBlockLength a j + 1 := by
  classical
  unfold positiveCanonicalBlockLength positiveCanonicalOddDenominatorBlock
  rw [← canonicalOddDenominatorBlock_card a hpos j]
  by_cases h0 : 0 ∈ canonicalOddDenominatorBlock a j
  · rw [← Finset.card_erase_add_one h0]
  · simp [Finset.erase_eq_of_notMem h0]

/-- Dyadic entropy height of a positive canonical block. -/
def canonicalEntropyHeight (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.log 2 (positiveCanonicalBlockLength a j)

/-- The dyadic difference packet contributed by the `j`-th block. -/
def canonicalDyadicDifferences
    (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  dyadicScaleBlock
    (canonicalOddBlockStep a j)
    (canonicalEntropyHeight a j)

lemma canonicalDyadicDifferences_card
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (canonicalDyadicDifferences a j).card =
      canonicalEntropyHeight a j := by
  classical
  unfold canonicalDyadicDifferences
  exact dyadicScaleBlock_card (canonicalOddBlockStep_pos hpos j)

lemma canonicalDyadicDifferences_sum_eq
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (canonicalDyadicDifferences a j).sum (fun d : ℕ => d) =
      (2 ^ canonicalEntropyHeight a j - 1) *
        canonicalOddBlockStep a j := by
  classical
  unfold canonicalDyadicDifferences
  exact dyadicScaleBlock_sum (canonicalOddBlockStep_pos hpos j)

/-! ## Local AP geometry after erasing zero -/

lemma finiteArithmeticBlock_erase_zero_eq_self_of_pos_start
    {s d m : ℕ} (hs : 0 < s) :
    (finiteArithmeticBlock s d m).erase 0 = finiteArithmeticBlock s d m := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact (Finset.mem_erase.mp hx).2
  · intro hx
    rw [Finset.mem_erase]
    refine ⟨?_, hx⟩
    intro hx0
    rw [hx0] at hx
    rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, _hr, hval⟩
    omega

lemma finiteArithmeticBlock_zero_start_erase_zero
    {d m : ℕ} (hd : 0 < d) :
    (finiteArithmeticBlock 0 d m).erase 0 =
      finiteArithmeticBlock d d (m - 1) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rw [Finset.mem_erase] at hx
    rcases hx with ⟨hx0, hxblock⟩
    rcases mem_finiteArithmeticBlock_iff.mp hxblock with ⟨r, hr, hval⟩
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := by omega
      subst r
      simp at hval
      exact hx0 hval
    refine mem_finiteArithmeticBlock_iff.mpr ?_
    refine ⟨r - 1, by omega, ?_⟩
    have hr_succ : r - 1 + 1 = r :=
      Nat.sub_one_add_one_eq_of_pos hrpos
    have hmul : r * d = d + (r - 1) * d := by
      conv_lhs => rw [← hr_succ]
      rw [Nat.add_mul, one_mul, Nat.add_comm]
    calc
      x = r * d := by simpa using hval
      _ = d + (r - 1) * d := hmul
  · intro hx
    rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, hval⟩
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hx0
      rw [hx0] at hval
      have hpos : 0 < d + r * d := Nat.add_pos_left hd _
      omega
    · refine mem_finiteArithmeticBlock_iff.mpr ?_
      refine ⟨r + 1, by omega, ?_⟩
      calc
        x = d + r * d := hval
        _ = 0 + (r + 1) * d := by ring

lemma exists_start_erase_zero_finiteArithmeticBlock_eq_card
    {s d m : ℕ} (hd : 0 < d) :
    ∃ s' : ℕ,
      (finiteArithmeticBlock s d m).erase 0 =
        finiteArithmeticBlock s' d
          ((finiteArithmeticBlock s d m).erase 0).card := by
  classical
  by_cases hs0 : s = 0
  · subst s
    refine ⟨d, ?_⟩
    rw [finiteArithmeticBlock_zero_start_erase_zero (d := d) (m := m) hd]
    rw [finiteArithmeticBlock_card (s := d) (d := d) (m := m - 1) hd]
  · have hspos : 0 < s := by omega
    refine ⟨s, ?_⟩
    rw [finiteArithmeticBlock_erase_zero_eq_self_of_pos_start
      (s := s) (d := d) (m := m) hspos]
    rw [finiteArithmeticBlock_card (s := s) (d := d) (m := m) hd]

theorem exists_start_positiveCanonicalOddDenominatorBlock_eq_block
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    ∃ s : ℕ,
      positiveCanonicalOddDenominatorBlock a j =
        finiteArithmeticBlock s (canonicalOddBlockStep a j)
          (positiveCanonicalBlockLength a j) := by
  classical
  rcases exists_start_canonicalOddDenominatorBlock_eq_block
      (a := a) hpos j with ⟨s, hs⟩
  have hstep : 0 < canonicalOddBlockStep a j :=
    canonicalOddBlockStep_pos hpos j
  rcases exists_start_erase_zero_finiteArithmeticBlock_eq_card
    (s := s) (d := canonicalOddBlockStep a j)
    (m := canonicalBlockLength a j) hstep with ⟨s', hs'⟩
  refine ⟨s', ?_⟩
  change (canonicalOddDenominatorBlock a j).erase 0 =
    finiteArithmeticBlock s' (canonicalOddBlockStep a j)
      ((canonicalOddDenominatorBlock a j).erase 0).card
  rw [hs]
  exact hs'

lemma dyadic_step_mem_nonnegativeDifferenceSet_of_positiveCanonicalBlock
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j u : ℕ}
    (hu : 2 ^ u < positiveCanonicalBlockLength a j) :
    2 ^ u * canonicalOddBlockStep a j ∈
      nonnegativeDifferenceSet (positiveCanonicalOddDenominatorBlock a j) := by
  classical
  rcases exists_start_positiveCanonicalOddDenominatorBlock_eq_block
      (a := a) hpos j with ⟨s, hblock⟩
  rw [hblock]
  rw [mem_nonnegativeDifferenceSet_iff]
  refine ⟨s + 2 ^ u * canonicalOddBlockStep a j, ?_, s, ?_, ?_⟩
  · rw [mem_finiteArithmeticBlock_iff]
    exact ⟨2 ^ u, hu, rfl⟩
  · rw [mem_finiteArithmeticBlock_iff]
    exact ⟨0, (by exact (by positivity : 0 < 2 ^ u).trans hu), by simp⟩
  · omega

lemma canonicalDyadicDifferences_subset_difference_of_positiveBlock_eq
    {a : ℕ → ℕ} {j J s : ℕ}
    (hblock :
      positiveCanonicalOddDenominatorBlock a j =
        finiteArithmeticBlock s (canonicalOddBlockStep a j)
          (positiveCanonicalBlockLength a j))
    (hj : j < J) :
    canonicalDyadicDifferences a j ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  classical
  intro z hz
  unfold canonicalDyadicDifferences dyadicScaleBlock at hz
  rcases Finset.mem_image.mp hz with ⟨u, hu, hzu⟩
  rw [Finset.mem_range] at hu
  let ell : ℕ := positiveCanonicalBlockLength a j
  let step : ℕ := canonicalOddBlockStep a j
  have hu' : u < Nat.log 2 ell := by
    simpa [canonicalEntropyHeight, ell] using hu
  have hlogpos : 0 < Nat.log 2 ell := by omega
  have hell_ne : ell ≠ 0 := by
    intro hell
    simp [hell] at hlogpos
  have hpow_succ_le : 2 ^ (u + 1) ≤ ell :=
    Nat.pow_le_of_le_log hell_ne (Nat.succ_le_of_lt hu')
  have hpow_lt_succ : 2 ^ u < 2 ^ (u + 1) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self u)
  have hpow_lt_ell : 2 ^ u < ell :=
    hpow_lt_succ.trans_le hpow_succ_le
  have hell_pos : 0 < ell := by
    exact (by positivity : 0 < 2 ^ u).trans hpow_lt_ell
  have hx_local :
      s ∈ positiveCanonicalOddDenominatorBlock a j := by
    rw [hblock]
    rw [mem_finiteArithmeticBlock_iff]
    exact ⟨0, hell_pos, by simp⟩
  have hy_local :
      s + 2 ^ u * step ∈ positiveCanonicalOddDenominatorBlock a j := by
    rw [hblock]
    rw [mem_finiteArithmeticBlock_iff]
    exact ⟨2 ^ u, hpow_lt_ell, rfl⟩
  have hsub :
      positiveCanonicalOddDenominatorBlock a j ⊆ certifiedOddBlocks a J :=
    positiveCanonicalOddDenominatorBlock_subset_certifiedOddBlocks hj
  rw [mem_nonnegativeDifferenceSet_iff]
  refine ⟨s + 2 ^ u * step, hsub hy_local, s, hsub hx_local, ?_⟩
  have hzu' : z = 2 ^ u * step := by
    simpa [step] using hzu.symm
  rw [hzu']
  omega

lemma canonicalDyadicDifferences_subset_difference
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j J : ℕ}
    (hj : j < J) :
    canonicalDyadicDifferences a j ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  classical
  rcases exists_start_positiveCanonicalOddDenominatorBlock_eq_block
      (a := a) hpos j with ⟨s, hblock⟩
  exact canonicalDyadicDifferences_subset_difference_of_positiveBlock_eq
    hblock hj

/-! ## Same-block denominator differences -/

lemma mem_certifiedOddBlocks_of_index_of_two_le_denominator
    {a : ℕ → ℕ} {J j t : ℕ}
    (hj : j < J)
    (ht : CanonicalOddCFIndex a j t)
    (hQ2 : 2 ≤ CFBlockDenominator a j t) :
    CFBlockDenominator a j t - 1 ∈ certifiedOddBlocks a J := by
  classical
  rw [mem_certifiedOddBlocks_iff]
  constructor
  · omega
  · refine ⟨j, hj, ?_⟩
    rw [canonicalOddDenominatorBlock, Finset.mem_image]
    refine ⟨t, ?_, rfl⟩
    rw [mem_canonicalOddBlock_iff]
    exact ht

lemma succ_mem_of_mem_certifiedOddBlocks
    {a : ℕ → ℕ} {J x : ℕ}
    (hx : x ∈ certifiedOddBlocks a J) :
    ∃ j t : ℕ,
      j < J ∧ CanonicalOddCFIndex a j t ∧
        x + 1 = CFBlockDenominator a j t := by
  classical
  rw [mem_certifiedOddBlocks_iff] at hx
  rcases hx with ⟨hx0, j, hj, hxblock⟩
  rw [canonicalOddDenominatorBlock] at hxblock
  rcases Finset.mem_image.mp hxblock with ⟨t, ht, htx⟩
  refine ⟨j, t, hj, ?_, ?_⟩
  · simpa [CanonicalOddCFIndex] using (mem_canonicalOddBlock_iff.mp ht)
  · change CFBlockDenominator a j t - 1 = x at htx
    omega

lemma CFBlockDenominator_add_offset
    (a : ℕ → ℕ) (j t r : ℕ) :
    CFBlockDenominator a j (t + r) =
      CFBlockDenominator a j t + r * continuantDen a j := by
  unfold CFBlockDenominator
  ring

lemma CFBlockDenominator_sub_same_block
    (a : ℕ → ℕ) {j t u : ℕ}
    (htu : t ≤ u) :
    CFBlockDenominator a j u - CFBlockDenominator a j t =
      (u - t) * continuantDen a j := by
  have hu : u = t + (u - t) := (Nat.add_sub_of_le htu).symm
  rw [hu, CFBlockDenominator_add_offset]
  simp

lemma shifted_CFBlockDenominator_difference
    (a : ℕ → ℕ) {j t u : ℕ}
    (htu : t ≤ u)
    (hQt : 1 ≤ CFBlockDenominator a j t) :
    (CFBlockDenominator a j u - 1) -
      (CFBlockDenominator a j t - 1) =
    (u - t) * continuantDen a j := by
  have hdiff :
      CFBlockDenominator a j u - CFBlockDenominator a j t =
        (u - t) * continuantDen a j :=
    CFBlockDenominator_sub_same_block a (j := j) htu
  have hle : CFBlockDenominator a j t ≤ CFBlockDenominator a j u :=
    CFBlockDenominator_le_of_index_le a htu
  omega

lemma mem_nonnegativeDifferenceSet_of_mem_of_mem_of_le
    {S : Finset ℕ} {x y : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (_hxy : x ≤ y) :
    y - x ∈ nonnegativeDifferenceSet S := by
  rw [mem_nonnegativeDifferenceSet_iff]
  exact ⟨y, hy, x, hx, rfl⟩

lemma same_block_difference_mem_nonnegativeDifferenceSet
    {a : ℕ → ℕ} {J j t u : ℕ}
    (hj : j < J)
    (ht : CanonicalOddCFIndex a j t)
    (hu : CanonicalOddCFIndex a j u)
    (htu : t ≤ u)
    (hQt2 : 2 ≤ CFBlockDenominator a j t) :
    (u - t) * continuantDen a j ∈
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  let x := CFBlockDenominator a j t - 1
  let y := CFBlockDenominator a j u - 1
  have hQu2 : 2 ≤ CFBlockDenominator a j u := by
    have hle : CFBlockDenominator a j t ≤ CFBlockDenominator a j u :=
      CFBlockDenominator_le_of_index_le a htu
    exact hQt2.trans hle
  have hx : x ∈ certifiedOddBlocks a J := by
    dsimp [x]
    exact mem_certifiedOddBlocks_of_index_of_two_le_denominator hj ht hQt2
  have hy : y ∈ certifiedOddBlocks a J := by
    dsimp [y]
    exact mem_certifiedOddBlocks_of_index_of_two_le_denominator hj hu hQu2
  have hxy : x ≤ y := by
    dsimp [x, y]
    have hle : CFBlockDenominator a j t ≤ CFBlockDenominator a j u :=
      CFBlockDenominator_le_of_index_le a htu
    omega
  have hmem := mem_nonnegativeDifferenceSet_of_mem_of_mem_of_le hx hy hxy
  convert hmem using 1
  dsimp [x, y]
  exact (shifted_CFBlockDenominator_difference a htu (by omega)).symm

/-! ## Explicit parity-selected dyadic pairs inside one block -/

lemma selected_pair_dyadic_offset_of_curr_even
    {a : ℕ → ℕ} {j s : ℕ}
    (_hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hcurrEven : Even (continuantNum a j))
    (hfit : 1 + 2 ^ s ≤ a (j + 1)) :
    ∃ t u : ℕ,
      CanonicalOddCFIndex a j t ∧
      CanonicalOddCFIndex a j u ∧
      t ≤ u ∧
      u - t = 2 ^ s := by
  have hprevOdd : Odd (continuantNumPrev a j) := by
    rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
    · exact False.elim
        (continuantNumPrev_not_even_and_even a j ⟨hprevEven, hcurrEven⟩)
    · exact hprevOdd
  refine ⟨1, 1 + 2 ^ s, ?_, ?_, Nat.le_add_right _ _, ?_⟩
  · refine ⟨by norm_num, ?_, ?_⟩
    · exact (Nat.le_add_right 1 (2 ^ s)).trans hfit
    · exact odd_CFBlockNumerator_of_prev_odd_curr_even
        (a := a) (j := j) (t := 1) hprevOdd hcurrEven
  · refine ⟨Nat.le_add_right 1 (2 ^ s), hfit, ?_⟩
    exact odd_CFBlockNumerator_of_prev_odd_curr_even
      (a := a) (j := j) (t := 1 + 2 ^ s) hprevOdd hcurrEven
  · exact Nat.add_sub_cancel_left _ _

lemma selected_pair_dyadic_offset_of_curr_odd
    {a : ℕ → ℕ} {j s : ℕ}
    (_hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hcurrOdd : Odd (continuantNum a j))
    (hfit : 2 + 2 ^ (s + 1) ≤ a (j + 1)) :
    ∃ t u : ℕ,
      CanonicalOddCFIndex a j t ∧
      CanonicalOddCFIndex a j u ∧
      t ≤ u ∧
      u - t = 2 ^ (s + 1) := by
  rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
  · refine ⟨1, 1 + 2 ^ (s + 1), ?_, ?_, Nat.le_add_right _ _, ?_⟩
    · refine ⟨by norm_num, ?_, ?_⟩
      · exact (Nat.le_add_right 1 (2 ^ (s + 1))).trans
          ((Nat.add_le_add_right (by norm_num : 1 ≤ 2) _).trans hfit)
      · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
          (a := a) (j := j) (t := 1) hprevEven hcurrOdd).2
          (by norm_num)
    · refine ⟨Nat.le_add_right 1 (2 ^ (s + 1)), ?_, ?_⟩
      · exact ((Nat.add_le_add_right (by norm_num : 1 ≤ 2) _).trans hfit)
      · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
          (a := a) (j := j) (t := 1 + 2 ^ (s + 1)) hprevEven hcurrOdd).2
          (by
            have hp : Even (2 ^ (s + 1)) := by
              rw [pow_succ]
              exact even_two.mul_left (2 ^ s)
            simpa [Nat.add_comm] using hp.add_one)
    · exact Nat.add_sub_cancel_left _ _
  · refine ⟨2, 2 + 2 ^ (s + 1), ?_, ?_, Nat.le_add_right _ _, ?_⟩
    · refine ⟨by norm_num, ?_, ?_⟩
      · exact (Nat.le_add_right 2 (2 ^ (s + 1))).trans hfit
      · exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
          (a := a) (j := j) (t := 2) hprevOdd hcurrOdd).2
          (by norm_num)
    · refine ⟨(by norm_num : 1 ≤ 2).trans
          (Nat.le_add_right 2 (2 ^ (s + 1))), hfit, ?_⟩
      exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
        (a := a) (j := j) (t := 2 + 2 ^ (s + 1)) hprevOdd hcurrOdd).2
        (by
          have hp : Even (2 ^ (s + 1)) := by
            rw [pow_succ]
            exact even_two.mul_left (2 ^ s)
          exact even_two.add hp)
    · exact Nat.add_sub_cancel_left _ _

/-! ## Filtered parity dyadic differences -/

def evenDyadicOffsets (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter fun s : ℕ => 1 + 2 ^ s ≤ m

def oddDyadicOffsets (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter fun s : ℕ => 2 + 2 ^ (s + 1) ≤ m

def parityDyadicDifferences (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  if Even (continuantNum a j) then
    (evenDyadicOffsets (a (j + 1))).image fun s : ℕ =>
      2 ^ s * continuantDen a j
  else
    (oddDyadicOffsets (a (j + 1))).image fun s : ℕ =>
      2 ^ (s + 1) * continuantDen a j

theorem parityDyadicDifferences_spec_of_pos_index
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {J j : ℕ}
    (hjpos : 0 < j)
    (hj : j < J) :
    parityDyadicDifferences a j ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  intro d hd
  unfold parityDyadicDifferences at hd
  by_cases hcurrEven : Even (continuantNum a j)
  · rw [if_pos hcurrEven] at hd
    rcases Finset.mem_image.mp hd with ⟨s, hs, rfl⟩
    have hfit : 1 + 2 ^ s ≤ a (j + 1) := by
      exact (Finset.mem_filter.mp hs).2
    obtain ⟨t, u, ht, hu, htu, hdiff⟩ :=
      selected_pair_dyadic_offset_of_curr_even hpos hcurrEven hfit
    have hQt2 : 2 ≤ CFBlockDenominator a j t :=
      two_le_CFBlockDenominator_of_pos_index hpos hjpos ht.1
    convert same_block_difference_mem_nonnegativeDifferenceSet
      (a := a) (J := J) (j := j) (t := t) (u := u)
      hj ht hu htu hQt2 using 1
    rw [hdiff]
  · rw [if_neg hcurrEven] at hd
    have hcurrOdd : Odd (continuantNum a j) :=
      Nat.not_even_iff_odd.mp hcurrEven
    rcases Finset.mem_image.mp hd with ⟨s, hs, rfl⟩
    have hfit : 2 + 2 ^ (s + 1) ≤ a (j + 1) := by
      exact (Finset.mem_filter.mp hs).2
    obtain ⟨t, u, ht, hu, htu, hdiff⟩ :=
      selected_pair_dyadic_offset_of_curr_odd hpos hcurrOdd hfit
    have hQt2 : 2 ≤ CFBlockDenominator a j t :=
      two_le_CFBlockDenominator_of_pos_index hpos hjpos ht.1
    convert same_block_difference_mem_nonnegativeDifferenceSet
      (a := a) (J := J) (j := j) (t := t) (u := u)
      hj ht hu htu hQt2 using 1
    rw [hdiff]

def positiveParityDyadicDifferencesPrefix
    (a : ℕ → ℕ) (J : ℕ) : Finset ℕ :=
  ((Finset.range J).filter fun j : ℕ => 0 < j).biUnion fun j : ℕ =>
    parityDyadicDifferences a j

theorem positiveParityDyadicDifferencesPrefix_subset_nonnegativeDifferenceSet
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    positiveParityDyadicDifferencesPrefix a J ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  intro d hd
  unfold positiveParityDyadicDifferencesPrefix at hd
  rcases Finset.mem_biUnion.mp hd with ⟨j, hj, hdj⟩
  rw [Finset.mem_filter] at hj
  exact parityDyadicDifferences_spec_of_pos_index hpos hj.2
    (Finset.mem_range.mp hj.1) hdj

/-- Two-step denominator domination:
`(a_{j+1}+1)q_j ≤ q_{j+2}`. -/
lemma partial_add_one_mul_den_le_two_step
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (a (j + 1) + 1) * continuantDen a j ≤
      continuantDen a (j + 2) := by
  rw [continuantDen_succ_eq a (j + 1)]
  have hqj1_ge :
      a (j + 1) * continuantDen a j ≤ continuantDen a (j + 1) := by
    rw [continuantDen_succ_eq a j]
    exact Nat.le_add_right _ _
  have hmul :
      continuantDen a (j + 1) ≤
        a (j + 2) * continuantDen a (j + 1) := by
    exact Nat.le_mul_of_pos_left _ (hpos (j + 1))
  calc
    (a (j + 1) + 1) * continuantDen a j =
        a (j + 1) * continuantDen a j + continuantDen a j := by ring
    _ ≤ continuantDen a (j + 1) + continuantDen a j :=
        Nat.add_le_add_right hqj1_ge _
    _ ≤ a (j + 2) * continuantDen a (j + 1) + continuantDen a j :=
        Nat.add_le_add_right hmul _


/-! ## Proof-plan consequences promoted from the placeholder ledger -/

/-- Planned packet mass bound for one canonical dyadic difference packet. -/
theorem canonicalDyadicDifferences_sum_le_partial_mul_den
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (canonicalDyadicDifferences a j).sum (fun d : ℕ => d) ≤
      a (j + 1) * continuantDen a j := by
  classical
  by_cases hlen0 : positiveCanonicalBlockLength a j = 0
  · rw [canonicalDyadicDifferences_sum_eq hpos j]
    simp [canonicalEntropyHeight, hlen0]
  · have hpow :
        2 ^ canonicalEntropyHeight a j ≤ positiveCanonicalBlockLength a j := by
      simpa [canonicalEntropyHeight] using
        Nat.pow_log_le_self 2 hlen0
    have hlen_le :
        positiveCanonicalBlockLength a j ≤ canonicalBlockLength a j :=
      positiveCanonicalBlockLength_le_canonicalBlockLength hpos j
    rw [canonicalDyadicDifferences_sum_eq hpos j]
    by_cases hcurrEven : Even (continuantNum a j)
    · have hstep :
          canonicalOddBlockStep a j = continuantDen a j :=
        canonicalOddBlockStep_eq_of_curr_even hcurrEven
      rw [hstep]
      have hcoeff :
          2 ^ canonicalEntropyHeight a j - 1 ≤ a (j + 1) := by
        have hblock_le :
            canonicalBlockLength a j ≤ a (j + 1) :=
          canonicalBlockLength_le_partialQuotient a j
        omega
      exact Nat.mul_le_mul_right (continuantDen a j) hcoeff
    · have hcurrOdd : Odd (continuantNum a j) :=
        Nat.not_even_iff_odd.mp hcurrEven
      have hstep :
          canonicalOddBlockStep a j = 2 * continuantDen a j :=
        canonicalOddBlockStep_eq_of_curr_odd hcurrOdd
      rw [hstep]
      have hhalf :
          2 * (canonicalBlockLength a j - 1) ≤ a (j + 1) :=
        two_mul_canonicalBlockLength_sub_one_le_partialQuotient_of_curr_odd
          hcurrOdd
      have hcoeff :
          2 * (2 ^ canonicalEntropyHeight a j - 1) ≤ a (j + 1) := by
        omega
      calc
        (2 ^ canonicalEntropyHeight a j - 1) *
            (2 * continuantDen a j)
            = (2 * (2 ^ canonicalEntropyHeight a j - 1)) *
                continuantDen a j := by ring
        _ ≤ a (j + 1) * continuantDen a j :=
            Nat.mul_le_mul_right (continuantDen a j) hcoeff

lemma range_natLog_subset_evenDyadicOffsets (m : ℕ) :
    Finset.range (Nat.log 2 m) ⊆ evenDyadicOffsets m := by
  intro s hs
  rw [Finset.mem_range] at hs
  unfold evenDyadicOffsets
  rw [Finset.mem_filter]
  have hs_lt_m_succ : s < m + 1 := by
    have hlog_le : Nat.log 2 m ≤ m := Nat.log_le_self 2 m
    omega
  have hm_ne : m ≠ 0 := by
    intro hm
    subst m
    simp at hs
  have hslog : s + 1 ≤ Nat.log 2 m := by omega
  have hpow : 2 ^ (s + 1) ≤ m :=
    Nat.pow_le_of_le_log hm_ne hslog
  have hone : 1 ≤ 2 ^ s := by
    exact Nat.succ_le_of_lt (Nat.two_pow_pos s)
  have hfit : 1 + 2 ^ s ≤ m := by
    calc
      1 + 2 ^ s ≤ 2 ^ s + 2 ^ s := by omega
      _ = 2 ^ (s + 1) := by
          rw [pow_succ]
          ring
      _ ≤ m := hpow
  exact ⟨by simpa [Finset.mem_range] using hs_lt_m_succ, hfit⟩

lemma range_natLog_sub_two_subset_oddDyadicOffsets (m : ℕ) :
    Finset.range (Nat.log 2 m - 2) ⊆ oddDyadicOffsets m := by
  intro s hs
  rw [Finset.mem_range] at hs
  unfold oddDyadicOffsets
  rw [Finset.mem_filter]
  have hs_lt_m_succ : s < m + 1 := by
    have hlog_le : Nat.log 2 m ≤ m := Nat.log_le_self 2 m
    omega
  have hm_ne : m ≠ 0 := by
    intro hm
    subst m
    simp at hs
  have hslog : s + 2 ≤ Nat.log 2 m := by omega
  have hpow : 2 ^ (s + 2) ≤ m :=
    Nat.pow_le_of_le_log hm_ne hslog
  have htwo : 2 ≤ 2 ^ (s + 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (by omega : 1 ≤ s + 1) : 2 ^ 1 ≤ 2 ^ (s + 1))
  have hfit : 2 + 2 ^ (s + 1) ≤ m := by
    calc
      2 + 2 ^ (s + 1) ≤ 2 ^ (s + 1) + 2 ^ (s + 1) := by omega
      _ = 2 ^ (s + 2) := by
          rw [show s + 2 = s + 1 + 1 by omega, pow_succ]
          ring
      _ ≤ m := hpow
  exact ⟨by simpa [Finset.mem_range] using hs_lt_m_succ, hfit⟩

lemma parityDyadicDifferences_card_of_curr_even
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j : ℕ}
    (hcurrEven : Even (continuantNum a j)) :
    (parityDyadicDifferences a j).card =
      (evenDyadicOffsets (a (j + 1))).card := by
  classical
  unfold parityDyadicDifferences
  rw [if_pos hcurrEven]
  rw [Finset.card_image_of_injOn]
  intro s _hs t _ht hst
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hpows : 2 ^ s = 2 ^ t := by
    exact Nat.mul_right_cancel hqpos hst
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows

lemma parityDyadicDifferences_card_of_curr_odd
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j : ℕ}
    (hcurrEven : ¬ Even (continuantNum a j)) :
    (parityDyadicDifferences a j).card =
      (oddDyadicOffsets (a (j + 1))).card := by
  classical
  unfold parityDyadicDifferences
  rw [if_neg hcurrEven]
  rw [Finset.card_image_of_injOn]
  intro s _hs t _ht hst
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hpows : 2 ^ (s + 1) = 2 ^ (t + 1) := by
    exact Nat.mul_right_cancel hqpos hst
  have hs : s + 1 = t + 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows
  omega

/-- Planned lower bound for the filtered per-block packet cardinality. -/
theorem card_parityDyadicDifferences_ge_log_safeBlockLength_sub_const
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    Nat.log 2 (canonicalSafeBlockLength a j) ≤
      (parityDyadicDifferences a j).card + 4 := by
  classical
  let m : ℕ := a (j + 1)
  have hsafe_le_m : canonicalSafeBlockLength a j ≤ m := by
    exact canonicalSafeBlockLength_le_partialQuotient a (hpos j)
  have hlog_le_m :
      Nat.log 2 (canonicalSafeBlockLength a j) ≤ Nat.log 2 m :=
    Nat.log_mono_right hsafe_le_m
  by_cases hcurrEven : Even (continuantNum a j)
  · have hcard_eq :
        (parityDyadicDifferences a j).card =
          (evenDyadicOffsets m).card := by
      simpa [m] using
        parityDyadicDifferences_card_of_curr_even
          (a := a) hpos (j := j) hcurrEven
    have hcard :
        Nat.log 2 m ≤ (evenDyadicOffsets m).card := by
      calc
        Nat.log 2 m = (Finset.range (Nat.log 2 m)).card := by simp
        _ ≤ (evenDyadicOffsets m).card :=
            Finset.card_le_card (range_natLog_subset_evenDyadicOffsets m)
    calc
      Nat.log 2 (canonicalSafeBlockLength a j) ≤ Nat.log 2 m := hlog_le_m
      _ ≤ (parityDyadicDifferences a j).card + 4 := by
          rw [hcard_eq]
          omega
  · have hcard_eq :
        (parityDyadicDifferences a j).card =
          (oddDyadicOffsets m).card := by
      simpa [m] using
        parityDyadicDifferences_card_of_curr_odd
          (a := a) hpos (j := j) hcurrEven
    have hcard :
        Nat.log 2 m - 2 ≤ (oddDyadicOffsets m).card := by
      calc
        Nat.log 2 m - 2 =
            (Finset.range (Nat.log 2 m - 2)).card := by simp
        _ ≤ (oddDyadicOffsets m).card :=
            Finset.card_le_card
              (range_natLog_sub_two_subset_oddDyadicOffsets m)
    calc
      Nat.log 2 (canonicalSafeBlockLength a j) ≤ Nat.log 2 m := hlog_le_m
      _ ≤ (parityDyadicDifferences a j).card + 4 := by
          rw [hcard_eq]
          omega

/- The earlier proof plan proposed an unsplit positive-index packet route:
`positiveParityDyadicDifferencesPrefix` should have large cardinality and be
subset-sum dissociated.  That route is too strong as stated.  The proved route
below splits the packets into even and odd index families and proves the usable
replacement theorem
`sum_canonicalEntropyHeight_le_two_mul_dissociatedDimension`. -/

/-! ## Recursive parity-separated packet package from the proof plan -/

/-- Recursive same-parity union of dyadic packets from the original proof plan.

The current bridge uses the filtered per-block packet above; this definition
keeps the recursive parity-separated version visible for the next proof pass.
-/
def paritySeparatedDyadicDifferences
    (a : ℕ → ℕ) (r : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | K + 1 =>
      paritySeparatedDyadicDifferences a r K ∪
        canonicalDyadicDifferences a (r + 2 * K)

lemma subsetSumDissociated_empty_nat :
    SubsetSumDissociated (∅ : Finset ℕ) := by
  classical
  simp [SubsetSumDissociated]

/-- Planned induction package for recursive parity-separated packets. -/
theorem paritySeparatedDyadicDifferences_spec
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ r K : ℕ,
      SubsetSumDissociated (paritySeparatedDyadicDifferences a r K) ∧
      (paritySeparatedDyadicDifferences a r K).card =
      (Finset.range K).sum
          (fun k : ℕ => canonicalEntropyHeight a (r + 2 * k)) ∧
      (paritySeparatedDyadicDifferences a r K).sum (fun d : ℕ => d) <
        continuantDen a (r + 2 * K) := by
  classical
  intro r K
  induction K with
  | zero =>
      constructor
      · simp [paritySeparatedDyadicDifferences]
      constructor
      · simp [paritySeparatedDyadicDifferences]
      · have hq : 0 < continuantDen a r :=
          lt_of_lt_of_le Nat.zero_lt_one
            (one_le_continuantDen_of_partials_pos_global a hpos r)
        simpa [paritySeparatedDyadicDifferences] using hq
  | succ K ih =>
      let j : ℕ := r + 2 * K
      let D : Finset ℕ := paritySeparatedDyadicDifferences a r K
      let hgt : ℕ := canonicalEntropyHeight a j
      let step : ℕ := canonicalOddBlockStep a j

      have hD_diss : SubsetSumDissociated D := by
        simpa [D] using ih.1
      have hD_card : D.card =
          (Finset.range K).sum
            (fun k : ℕ => canonicalEntropyHeight a (r + 2 * k)) := by
        simpa [D] using ih.2.1
      have hD_sum_lt_qj : D.sum (fun d : ℕ => d) < continuantDen a j := by
        simpa [D, j] using ih.2.2

      have hstep_pos : 0 < step := by
        simpa [step, j] using canonicalOddBlockStep_pos hpos j
      have hq_le_step : continuantDen a j ≤ step := by
        simpa [step, j] using continuantDen_le_canonicalOddBlockStep hpos j
      have hD_sum_lt_step : D.sum (fun d : ℕ => d) < step :=
        hD_sum_lt_qj.trans_le hq_le_step

      have happ :=
        subsetSumDissociated_union_dyadicScaleBlock
          (D := D) (d := step) (h := hgt)
          hD_diss hstep_pos hD_sum_lt_step
      rcases happ with ⟨hnew_diss, hnew_card, hnew_sum⟩

      have hpacket_sum_le :
          (2 ^ hgt - 1) * step ≤ a (j + 1) * continuantDen a j := by
        have hsum_le :=
          canonicalDyadicDifferences_sum_le_partial_mul_den hpos j
        have hsum_eq :
            (dyadicScaleBlock step hgt).sum (fun d : ℕ => d) =
              (2 ^ hgt - 1) * step :=
          dyadicScaleBlock_sum hstep_pos
        rw [← hsum_eq]
        simpa [canonicalDyadicDifferences, step, hgt, j] using hsum_le

      have hnew_sum_lt_qnext :
          (D ∪ dyadicScaleBlock step hgt).sum (fun d : ℕ => d) <
            continuantDen a (j + 2) := by
        calc
          (D ∪ dyadicScaleBlock step hgt).sum (fun d : ℕ => d)
              = D.sum (fun d : ℕ => d) + (2 ^ hgt - 1) * step := hnew_sum
          _ < continuantDen a j + a (j + 1) * continuantDen a j :=
              Nat.add_lt_add_of_lt_of_le hD_sum_lt_qj hpacket_sum_le
          _ = (a (j + 1) + 1) * continuantDen a j := by ring
          _ ≤ continuantDen a (j + 2) :=
              partial_add_one_mul_den_le_two_step hpos j

      constructor
      · simpa [paritySeparatedDyadicDifferences, D, j, step, hgt,
          canonicalDyadicDifferences] using hnew_diss
      constructor
      · calc
          (paritySeparatedDyadicDifferences a r (K + 1)).card
              = (D ∪ dyadicScaleBlock step hgt).card := by
                  simp [paritySeparatedDyadicDifferences, D, j, step, hgt,
                    canonicalDyadicDifferences]
          _ = D.card + hgt := hnew_card
          _ = (Finset.range K).sum
                (fun k : ℕ => canonicalEntropyHeight a (r + 2 * k)) +
              canonicalEntropyHeight a (r + 2 * K) := by
                  simp [D, hD_card, hgt, j]
          _ = (Finset.range (K + 1)).sum
                (fun k : ℕ => canonicalEntropyHeight a (r + 2 * k)) := by
                  rw [Finset.sum_range_succ]
      · have hidx : r + 2 * (K + 1) = j + 2 := by
          dsimp [j]
          omega
        simpa [paritySeparatedDyadicDifferences, D, j, step, hgt,
          canonicalDyadicDifferences, hidx]
          using hnew_sum_lt_qnext

def evenCertifiedPacket (a : ℕ → ℕ) (J : ℕ) : Finset ℕ :=
  paritySeparatedDyadicDifferences a 0 ((J + 1) / 2)

def oddCertifiedPacket (a : ℕ → ℕ) (J : ℕ) : Finset ℕ :=
  paritySeparatedDyadicDifferences a 1 (J / 2)

lemma paritySeparatedDyadicDifferences_subset_difference_of_indices_lt
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {r K J : ℕ}
    (hidx : ∀ k : ℕ, k < K → r + 2 * k < J) :
    paritySeparatedDyadicDifferences a r K ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  classical
  induction K with
  | zero =>
      simp [paritySeparatedDyadicDifferences]
  | succ K ih =>
      intro d hd
      rw [paritySeparatedDyadicDifferences] at hd
      rcases Finset.mem_union.mp hd with hd | hd
      · exact ih (fun k hk => hidx k (by omega)) hd
      · exact canonicalDyadicDifferences_subset_difference hpos
          (hidx K (by omega)) hd

/-- Planned even-index packet inclusion into the certified difference set. -/
theorem evenCertifiedPacket_subset_difference
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    evenCertifiedPacket a J ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  unfold evenCertifiedPacket
  exact paritySeparatedDyadicDifferences_subset_difference_of_indices_lt
    hpos (by intro k hk; omega)

/-- Planned odd-index packet inclusion into the certified difference set. -/
theorem oddCertifiedPacket_subset_difference
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    oddCertifiedPacket a J ⊆
      nonnegativeDifferenceSet (certifiedOddBlocks a J) := by
  unfold oddCertifiedPacket
  exact paritySeparatedDyadicDifferences_subset_difference_of_indices_lt
    hpos (by intro k hk; omega)

lemma sum_range_even_length_eq_even_add_odd
    (f : ℕ → ℕ) (n : ℕ) :
    (Finset.range (2 * n)).sum f =
      (Finset.range n).sum (fun k : ℕ => f (2 * k)) +
      (Finset.range n).sum (fun k : ℕ => f (2 * k + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (Finset.range (2 * (n + 1))).sum f
            = (Finset.range (2 * n)).sum f +
                f (2 * n) + f (2 * n + 1) := by
              rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = ((Finset.range n).sum (fun k : ℕ => f (2 * k)) +
              (Finset.range n).sum (fun k : ℕ => f (2 * k + 1))) +
                f (2 * n) + f (2 * n + 1) := by rw [ih]
        _ = ((Finset.range n).sum (fun k : ℕ => f (2 * k)) + f (2 * n)) +
              ((Finset.range n).sum (fun k : ℕ => f (2 * k + 1)) +
                f (2 * n + 1)) := by omega
        _ = (Finset.range (n + 1)).sum (fun k : ℕ => f (2 * k)) +
              (Finset.range (n + 1)).sum (fun k : ℕ => f (2 * k + 1)) := by
                rw [Finset.sum_range_succ, Finset.sum_range_succ]

lemma sum_range_odd_length_eq_even_add_odd
    (f : ℕ → ℕ) (n : ℕ) :
    (Finset.range (2 * n + 1)).sum f =
      (Finset.range (n + 1)).sum (fun k : ℕ => f (2 * k)) +
      (Finset.range n).sum (fun k : ℕ => f (2 * k + 1)) := by
  calc
    (Finset.range (2 * n + 1)).sum f
        = (Finset.range (2 * n)).sum f + f (2 * n) := by
            rw [Finset.sum_range_succ]
    _ = ((Finset.range n).sum (fun k : ℕ => f (2 * k)) +
          (Finset.range n).sum (fun k : ℕ => f (2 * k + 1))) +
          f (2 * n) := by
            rw [sum_range_even_length_eq_even_add_odd]
    _ = ((Finset.range n).sum (fun k : ℕ => f (2 * k)) + f (2 * n)) +
          (Finset.range n).sum (fun k : ℕ => f (2 * k + 1)) := by
            omega
    _ = (Finset.range (n + 1)).sum (fun k : ℕ => f (2 * k)) +
          (Finset.range n).sum (fun k : ℕ => f (2 * k + 1)) := by
            rw [Finset.sum_range_succ]

/-- Planned finite parity split for sums over a prefix. -/
theorem sum_range_eq_even_add_odd
    (f : ℕ → ℕ) (J : ℕ) :
    (Finset.range J).sum f =
      (Finset.range ((J + 1) / 2)).sum (fun k : ℕ => f (2 * k)) +
      (Finset.range (J / 2)).sum (fun k : ℕ => f (2 * k + 1)) := by
  rcases Nat.even_or_odd J with hJ | hJ
  · rcases hJ with ⟨n, rfl⟩
    have htwo : 2 * n = n + n := by omega
    have hhalf1 : (n + n + 1) / 2 = n := by omega
    have hhalf2 : (n + n) / 2 = n := by omega
    have hsum := sum_range_even_length_eq_even_add_odd f n
    rw [htwo] at hsum
    simpa [hhalf1, hhalf2] using hsum
  · rcases hJ with ⟨n, rfl⟩
    have hhalf1 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    have hhalf2 : (2 * n + 1) / 2 = n := by omega
    simpa [hhalf1, hhalf2] using
      sum_range_odd_length_eq_even_add_odd f n

/-- Planned height-sum bound in terms of the certified difference dimension. -/
theorem sum_canonicalEntropyHeight_le_two_mul_dissociatedDimension
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    (Finset.range J).sum (fun j : ℕ => canonicalEntropyHeight a j) ≤
      2 * subsetSumDissociatedDimension
        (nonnegativeDifferenceSet (certifiedOddBlocks a J)) := by
  classical
  let Y : Finset ℕ := nonnegativeDifferenceSet (certifiedOddBlocks a J)
  let D : ℕ := subsetSumDissociatedDimension Y
  have heven_spec :=
    paritySeparatedDyadicDifferences_spec (a := a) hpos 0 ((J + 1) / 2)
  have hodd_spec :=
    paritySeparatedDyadicDifferences_spec (a := a) hpos 1 (J / 2)
  have heven_card :
      (evenCertifiedPacket a J).card =
        (Finset.range ((J + 1) / 2)).sum
          (fun k : ℕ => canonicalEntropyHeight a (2 * k)) := by
    simpa [evenCertifiedPacket] using heven_spec.2.1
  have hodd_card :
      (oddCertifiedPacket a J).card =
        (Finset.range (J / 2)).sum
          (fun k : ℕ => canonicalEntropyHeight a (2 * k + 1)) := by
    simpa [oddCertifiedPacket, add_comm, add_left_comm, add_assoc] using
      hodd_spec.2.1
  have heven_diss :
      SubsetSumDissociated (evenCertifiedPacket a J) := by
    simpa [evenCertifiedPacket] using heven_spec.1
  have hodd_diss :
      SubsetSumDissociated (oddCertifiedPacket a J) := by
    simpa [oddCertifiedPacket] using hodd_spec.1
  have heven_le :
      (Finset.range ((J + 1) / 2)).sum
          (fun k : ℕ => canonicalEntropyHeight a (2 * k)) ≤ D := by
    rw [← heven_card]
    exact card_le_subsetSumDissociatedDimension
      (Y := Y) (hDY := evenCertifiedPacket_subset_difference hpos J)
      heven_diss
  have hodd_le :
      (Finset.range (J / 2)).sum
          (fun k : ℕ => canonicalEntropyHeight a (2 * k + 1)) ≤ D := by
    rw [← hodd_card]
    exact card_le_subsetSumDissociatedDimension
      (Y := Y) (hDY := oddCertifiedPacket_subset_difference hpos J)
      hodd_diss
  rw [sum_range_eq_even_add_odd]
  have hsum :=
    Nat.add_le_add heven_le hodd_le
  dsimp [D, Y] at hsum ⊢
  omega

/-! ## Entropy wrappers and finite entropy theorems -/

def certifiedPositiveBlockCount (a : ℕ → ℕ) (J : ℕ) : ℕ :=
  ((Finset.range J).filter
    (fun j : ℕ => 0 < positiveCanonicalBlockLength a j)).card

noncomputable def certifiedPositiveBlockEntropy
    (a : ℕ → ℕ) (J : ℕ) : ℝ :=
  (Finset.range J).sum fun j : ℕ =>
    Real.log (1 + (positiveCanonicalBlockLength a j : ℝ))

noncomputable def certifiedBlockEntropy
    (a : ℕ → ℕ) (J : ℕ) : ℝ :=
  (Finset.range J).sum fun j : ℕ =>
    Real.log (1 + (canonicalBlockLength a j : ℝ))

/-- Planned termwise logarithm bound converting natural logarithms to dyadic
entropy height. -/
theorem log_one_add_nat_le_entropyHeight
    (ell : ℕ) :
    Real.log (1 + (ell : ℝ)) ≤
      (((Nat.log 2 ell + if 0 < ell then 1 else 0 : ℕ) : ℝ) *
        Real.log 2) := by
  by_cases hell : ell = 0
  · subst ell
    norm_num
  · have hellpos : 0 < ell := Nat.pos_of_ne_zero hell
    have hargpos : 0 < (1 + (ell : ℝ)) := by positivity
    have hpow_lt : ell < 2 ^ (Nat.log 2 ell + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two ell
    have hsucc_le : 1 + ell ≤ 2 ^ (Nat.log 2 ell + 1) := by
      omega
    have hlog_le :
        Real.log (1 + (ell : ℝ)) ≤
          Real.log ((2 ^ (Nat.log 2 ell + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log hargpos
      exact_mod_cast hsucc_le
    have hpowlog :
        Real.log ((2 ^ (Nat.log 2 ell + 1) : ℕ) : ℝ) =
          ((Nat.log 2 ell + 1 : ℕ) : ℝ) * Real.log 2 := by
      norm_num [Nat.cast_pow, Real.log_pow]
    simpa [hellpos] using hlog_le.trans_eq hpowlog

theorem certifiedPositiveBlockCount_le_certifiedBlockCount
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedPositiveBlockCount a J ≤ certifiedBlockCount a J := by
  unfold certifiedPositiveBlockCount certifiedBlockCount
  refine Finset.card_le_card ?_
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2
    (positiveCanonicalBlockLength_le_canonicalBlockLength hpos j)⟩

theorem certifiedPositiveBlockEntropy_le_count_add_height
    (a : ℕ → ℕ) (J : ℕ) :
    certifiedPositiveBlockEntropy a J ≤
      (((certifiedPositiveBlockCount a J +
          (Finset.range J).sum
            (fun j : ℕ => canonicalEntropyHeight a j) : ℕ) : ℝ) *
        Real.log 2) := by
  classical
  have hcount :
      (Finset.range J).sum
          (fun j : ℕ =>
            if 0 < positiveCanonicalBlockLength a j then 1 else 0) =
        certifiedPositiveBlockCount a J := by
    simp [certifiedPositiveBlockCount]
  have hnat :
      (Finset.range J).sum
          (fun j : ℕ =>
            canonicalEntropyHeight a j +
              if 0 < positiveCanonicalBlockLength a j then 1 else 0) =
        certifiedPositiveBlockCount a J +
          (Finset.range J).sum
            (fun j : ℕ => canonicalEntropyHeight a j) := by
    rw [Finset.sum_add_distrib, hcount]
    omega
  have hsum_eq :
      (Finset.range J).sum
          (fun j : ℕ =>
            (((canonicalEntropyHeight a j +
                if 0 < positiveCanonicalBlockLength a j then 1 else 0 : ℕ) : ℝ) *
              Real.log 2)) =
        ((((Finset.range J).sum
          (fun j : ℕ =>
            canonicalEntropyHeight a j +
              if 0 < positiveCanonicalBlockLength a j then 1 else 0) : ℕ) : ℝ) *
          Real.log 2) := by
    rw [← Finset.sum_mul]
    norm_num [Nat.cast_sum]
  calc
    certifiedPositiveBlockEntropy a J
        ≤ (Finset.range J).sum
            (fun j : ℕ =>
              (((canonicalEntropyHeight a j +
                  if 0 < positiveCanonicalBlockLength a j then 1 else 0 : ℕ) : ℝ) *
                Real.log 2)) := by
          unfold certifiedPositiveBlockEntropy
          refine Finset.sum_le_sum ?_
          intro j _hj
          simpa [canonicalEntropyHeight] using
            log_one_add_nat_le_entropyHeight
              (positiveCanonicalBlockLength a j)
    _ = ((((Finset.range J).sum
          (fun j : ℕ =>
            canonicalEntropyHeight a j +
              if 0 < positiveCanonicalBlockLength a j then 1 else 0) : ℕ) : ℝ) *
          Real.log 2) := hsum_eq
    _ = (((certifiedPositiveBlockCount a J +
          (Finset.range J).sum
            (fun j : ℕ => canonicalEntropyHeight a j) : ℕ) : ℝ) *
        Real.log 2) := by rw [hnat]

theorem certifiedPositiveBlockEntropy_le_dissociatedDifferenceDimension
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedPositiveBlockEntropy a J ≤
      (((certifiedPositiveBlockCount a J +
          2 * subsetSumDissociatedDimension
            (nonnegativeDifferenceSet (certifiedOddBlocks a J)) : ℕ) : ℝ) *
        Real.log 2) := by
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  have hbase := certifiedPositiveBlockEntropy_le_count_add_height a J
  have hheight :
      (Finset.range J).sum (fun j : ℕ => canonicalEntropyHeight a j) ≤
        2 * D := by
    dsimp [D]
    exact sum_canonicalEntropyHeight_le_two_mul_dissociatedDimension hpos J
  have hnat :
      certifiedPositiveBlockCount a J +
          (Finset.range J).sum
            (fun j : ℕ => canonicalEntropyHeight a j) ≤
        certifiedPositiveBlockCount a J + 2 * D := by
    exact Nat.add_le_add_left hheight _
  have hcast :
      (((certifiedPositiveBlockCount a J +
          (Finset.range J).sum
            (fun j : ℕ => canonicalEntropyHeight a j) : ℕ) : ℝ)) ≤
        (((certifiedPositiveBlockCount a J + 2 * D : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hlog_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact hbase.trans (mul_le_mul_of_nonneg_right hcast hlog_nonneg)

theorem certifiedPositiveBlockEntropy_le_certifiedBlockCount_add_dissDim
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedPositiveBlockEntropy a J ≤
      (((certifiedBlockCount a J +
          2 * subsetSumDissociatedDimension
            (nonnegativeDifferenceSet (certifiedOddBlocks a J)) : ℕ) : ℝ) *
        Real.log 2) := by
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  have hbase :=
    certifiedPositiveBlockEntropy_le_dissociatedDifferenceDimension
      (a := a) hpos J
  have hcount :
      certifiedPositiveBlockCount a J ≤ certifiedBlockCount a J :=
    certifiedPositiveBlockCount_le_certifiedBlockCount hpos J
  have hnat :
      certifiedPositiveBlockCount a J + 2 * D ≤
        certifiedBlockCount a J + 2 * D := by
    exact Nat.add_le_add_right hcount _
  have hcast :
      (((certifiedPositiveBlockCount a J + 2 * D : ℕ) : ℝ)) ≤
        (((certifiedBlockCount a J + 2 * D : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hlog_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact hbase.trans (mul_le_mul_of_nonneg_right hcast hlog_nonneg)

theorem raw_entropy_term_le_positive_term_add_initial_error
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    Real.log (1 + (canonicalBlockLength a j : ℝ)) ≤
      Real.log (1 + (positiveCanonicalBlockLength a j : ℝ)) +
        (if j = 0 then Real.log 2 else 0) := by
  by_cases hj0 : j = 0
  · have hlen :
        canonicalBlockLength a j ≤ positiveCanonicalBlockLength a j + 1 :=
      canonicalBlockLength_le_positiveCanonicalBlockLength_add_one hpos j
    have hargpos :
        0 < 1 + (canonicalBlockLength a j : ℝ) := by positivity
    have hbound :
        1 + (canonicalBlockLength a j : ℝ) ≤
          2 * (1 + (positiveCanonicalBlockLength a j : ℝ)) := by
      have hlenR :
          (canonicalBlockLength a j : ℝ) ≤
            (positiveCanonicalBlockLength a j : ℝ) + 1 := by
        exact_mod_cast hlen
      nlinarith [hlenR,
        show (0 : ℝ) ≤ (positiveCanonicalBlockLength a j : ℝ) by positivity]
    have hlog :
        Real.log (1 + (canonicalBlockLength a j : ℝ)) ≤
          Real.log (2 * (1 + (positiveCanonicalBlockLength a j : ℝ))) :=
      Real.log_le_log hargpos hbound
    have hmul :
        Real.log (2 * (1 + (positiveCanonicalBlockLength a j : ℝ))) =
          Real.log 2 + Real.log (1 + (positiveCanonicalBlockLength a j : ℝ)) := by
      rw [Real.log_mul]
      · norm_num
      · positivity
    have hlog' :
        Real.log (1 + (canonicalBlockLength a j : ℝ)) ≤
          Real.log 2 + Real.log (1 + (positiveCanonicalBlockLength a j : ℝ)) :=
      hlog.trans_eq hmul
    simpa [hj0, add_comm, add_left_comm, add_assoc] using hlog'
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hlen :
        positiveCanonicalBlockLength a j = canonicalBlockLength a j :=
      positiveCanonicalBlockLength_eq_canonicalBlockLength_of_pos_index
        hpos hjpos
    simp [hj0, hlen]

theorem certifiedBlockEntropy_le_positive_add_log_two
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedBlockEntropy a J ≤
      certifiedPositiveBlockEntropy a J + Real.log 2 := by
  classical
  have herror :
      (Finset.range J).sum
          (fun j : ℕ => if j = 0 then Real.log 2 else 0) ≤
        Real.log 2 := by
    cases J with
    | zero =>
        simp [le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    | succ J =>
        rw [Finset.sum_eq_single 0]
        · simp
        · intro b _hb hbne
          simp [hbne]
        · intro hnot
          exfalso
          exact hnot (by simp)
  unfold certifiedBlockEntropy certifiedPositiveBlockEntropy
  calc
    (Finset.range J).sum
        (fun j : ℕ => Real.log (1 + (canonicalBlockLength a j : ℝ)))
        ≤ (Finset.range J).sum
            (fun j : ℕ =>
              Real.log (1 + (positiveCanonicalBlockLength a j : ℝ)) +
                (if j = 0 then Real.log 2 else 0)) := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact raw_entropy_term_le_positive_term_add_initial_error hpos j
    _ = (Finset.range J).sum
          (fun j : ℕ =>
            Real.log (1 + (positiveCanonicalBlockLength a j : ℝ))) +
        (Finset.range J).sum
          (fun j : ℕ => if j = 0 then Real.log 2 else 0) := by
          rw [Finset.sum_add_distrib]
    _ ≤ (Finset.range J).sum
          (fun j : ℕ =>
            Real.log (1 + (positiveCanonicalBlockLength a j : ℝ))) +
        Real.log 2 := by
          exact add_le_add_right herror _

theorem certifiedBlockEntropy_le_certifiedBlockCount_add_dissDim
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedBlockEntropy a J ≤
      (((certifiedBlockCount a J +
          2 * subsetSumDissociatedDimension
            (nonnegativeDifferenceSet (certifiedOddBlocks a J)) + 1 : ℕ) : ℝ) *
        Real.log 2) := by
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  have hraw :
      certifiedBlockEntropy a J ≤
        certifiedPositiveBlockEntropy a J + Real.log 2 :=
    certifiedBlockEntropy_le_positive_add_log_two hpos J
  have hpos_bound :
      certifiedPositiveBlockEntropy a J ≤
        (((certifiedBlockCount a J + 2 * D : ℕ) : ℝ) *
          Real.log 2) :=
    certifiedPositiveBlockEntropy_le_certifiedBlockCount_add_dissDim
      (a := a) hpos J
  have hsum :
      certifiedBlockEntropy a J ≤
        (((certifiedBlockCount a J + 2 * D : ℕ) : ℝ) *
          Real.log 2) + Real.log 2 :=
    hraw.trans (add_le_add_left hpos_bound _)
  have hrewrite :
      (((certifiedBlockCount a J + 2 * D : ℕ) : ℝ) *
          Real.log 2) + Real.log 2 =
        (((certifiedBlockCount a J + 2 * D + 1 : ℕ) : ℝ) *
          Real.log 2) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  exact hsum.trans_eq hrewrite

theorem dissociatedDifferenceDimension_ge_entropy
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    ((certifiedPositiveBlockEntropy a J / Real.log 2) -
        (certifiedPositiveBlockCount a J : ℝ)) / 2 ≤
      (subsetSumDissociatedDimension
        (nonnegativeDifferenceSet (certifiedOddBlocks a J)) : ℝ) := by
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  let B : ℕ := certifiedPositiveBlockCount a J
  let E : ℝ := certifiedPositiveBlockEntropy a J
  have hbound :
      E ≤ (((B + 2 * D : ℕ) : ℝ) * Real.log 2) := by
    dsimp [E, B, D]
    exact certifiedPositiveBlockEntropy_le_dissociatedDifferenceDimension
      (a := a) hpos J
  have hbound' : E ≤ ((B : ℝ) + 2 * (D : ℝ)) * Real.log 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, two_mul] using hbound
  have hlogpos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hdiv : E / Real.log 2 ≤ (B : ℝ) + 2 * (D : ℝ) := by
    rw [div_le_iff₀ hlogpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbound'
  dsimp [E, B, D] at hdiv ⊢
  nlinarith

/-! ## `1 / π` wrappers from the entropy proof plan -/

noncomputable def Ent_oneOverPi (m : ℕ) : ℝ :=
  certifiedBlockEntropy oneOverPiCF (J_oneOverPi m)

noncomputable def dissDim_oneOverPi (m : ℕ) : ℕ :=
  subsetSumDissociatedDimension
    (nonnegativeDifferenceSet (certifiedAOneOverPiSubset m))

theorem Ent_oneOverPi_le_B_add_two_dissDim_add_one
    (m : ℕ) :
    Ent_oneOverPi m ≤
      (((B_oneOverPi m + 2 * dissDim_oneOverPi m + 1 : ℕ) : ℝ) *
        Real.log 2) := by
  simpa [Ent_oneOverPi, B_oneOverPi, dissDim_oneOverPi,
    certifiedAOneOverPiSubset, certifiedBlockCountAt] using
    certifiedBlockEntropy_le_certifiedBlockCount_add_dissDim
      (a := oneOverPiCF) oneOverPiCF_partials_pos (J_oneOverPi m)

/-! ## Normalized and ambient-size consequences from the proof plan -/

theorem normalizedPositiveEntropy_le_of_dissDim_le_mul_count
    {a : ℕ → ℕ} {J C : ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hB : 0 < certifiedBlockCount a J)
    (hD : subsetSumDissociatedDimension
        (nonnegativeDifferenceSet (certifiedOddBlocks a J)) ≤
      C * certifiedBlockCount a J) :
    certifiedPositiveBlockEntropy a J /
        (certifiedBlockCount a J : ℝ) ≤
      (1 + 2 * (C : ℝ)) * Real.log 2 := by
  let B : ℕ := certifiedBlockCount a J
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  let E : ℝ := certifiedPositiveBlockEntropy a J
  have hbase :
      E ≤ (((B + 2 * D : ℕ) : ℝ) * Real.log 2) := by
    dsimp [E, B, D]
    exact certifiedPositiveBlockEntropy_le_certifiedBlockCount_add_dissDim
      (a := a) hpos J
  have hbase' : E ≤ ((B : ℝ) + 2 * (D : ℝ)) * Real.log 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, two_mul] using hbase
  have hDreal : (D : ℝ) ≤ (C : ℝ) * (B : ℝ) := by
    dsimp [D, B]
    exact_mod_cast hD
  have hcoeff :
      (B : ℝ) + 2 * (D : ℝ) ≤
        (1 + 2 * (C : ℝ)) * (B : ℝ) := by
    nlinarith [hDreal]
  have hlog_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hupper :
      E ≤ ((1 + 2 * (C : ℝ)) * (B : ℝ)) * Real.log 2 :=
    hbase'.trans (mul_le_mul_of_nonneg_right hcoeff hlog_nonneg)
  have hBpos : 0 < (B : ℝ) := by
    dsimp [B]
    exact_mod_cast hB
  dsimp [E, B] at hupper ⊢
  rw [div_le_iff₀ hBpos]
  nlinarith

theorem normalizedRawEntropy_le_of_dissDim_le_mul_count
    {a : ℕ → ℕ} {J C : ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hB : 0 < certifiedBlockCount a J)
    (hD : subsetSumDissociatedDimension
        (nonnegativeDifferenceSet (certifiedOddBlocks a J)) ≤
      C * certifiedBlockCount a J) :
    certifiedBlockEntropy a J /
        (certifiedBlockCount a J : ℝ) ≤
      (2 + 2 * (C : ℝ)) * Real.log 2 := by
  let B : ℕ := certifiedBlockCount a J
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  let E : ℝ := certifiedBlockEntropy a J
  have hbase :
      E ≤ (((B + 2 * D + 1 : ℕ) : ℝ) * Real.log 2) := by
    dsimp [E, B, D]
    exact certifiedBlockEntropy_le_certifiedBlockCount_add_dissDim
      (a := a) hpos J
  have hbase' : E ≤ ((B : ℝ) + 2 * (D : ℝ) + 1) * Real.log 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, two_mul] using hbase
  have hDreal : (D : ℝ) ≤ (C : ℝ) * (B : ℝ) := by
    dsimp [D, B]
    exact_mod_cast hD
  have hBone : (1 : ℝ) ≤ (B : ℝ) := by
    dsimp [B]
    exact_mod_cast hB
  have hcoeff :
      (B : ℝ) + 2 * (D : ℝ) + 1 ≤
        (2 + 2 * (C : ℝ)) * (B : ℝ) := by
    nlinarith [hDreal, hBone]
  have hlog_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hupper :
      E ≤ ((2 + 2 * (C : ℝ)) * (B : ℝ)) * Real.log 2 :=
    hbase'.trans (mul_le_mul_of_nonneg_right hcoeff hlog_nonneg)
  have hBpos : 0 < (B : ℝ) := by
    dsimp [B]
    exact_mod_cast hB
  dsimp [E, B] at hupper ⊢
  rw [div_le_iff₀ hBpos]
  nlinarith

noncomputable def normalizedCertifiedBlockEntropy
    (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) : ℝ :=
  if certifiedBlockCount a (Jcert m) = 0 then 0
  else
    certifiedBlockEntropy a (Jcert m) /
      certifiedBlockCount a (Jcert m)

theorem eventually_normalizedCertifiedBlockEntropy_le_of_dissDim_le_mul_count
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ} {C : ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hB : ∀ᶠ m : ℕ in atTop, 0 < certifiedBlockCount a (Jcert m))
    (hD : ∀ᶠ m : ℕ in atTop,
      subsetSumDissociatedDimension
          (nonnegativeDifferenceSet (certifiedOddBlocks a (Jcert m))) ≤
        C * certifiedBlockCount a (Jcert m)) :
    ∀ᶠ m : ℕ in atTop,
      normalizedCertifiedBlockEntropy a Jcert m ≤
        (2 + 2 * (C : ℝ)) * Real.log 2 := by
  filter_upwards [hB, hD] with m hmB hmD
  unfold normalizedCertifiedBlockEntropy
  simp [Nat.ne_of_gt hmB]
  exact normalizedRawEntropy_le_of_dissDim_le_mul_count
    (a := a) (J := Jcert m) (C := C) hpos hmB hmD

theorem certifiedBlockEntropy_le_certifiedBlockCount_add_log_ambient
    {a : ℕ → ℕ} {J N : ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hN : ∀ x ∈ certifiedOddBlocks a J, x ≤ N) :
    certifiedBlockEntropy a J ≤
      (((certifiedBlockCount a J +
          4 * Nat.log 2 (N + 1) + 3 : ℕ) : ℝ) *
        Real.log 2) := by
  let D : ℕ :=
    subsetSumDissociatedDimension
      (nonnegativeDifferenceSet (certifiedOddBlocks a J))
  have hbase :
      certifiedBlockEntropy a J ≤
        (((certifiedBlockCount a J + 2 * D + 1 : ℕ) : ℝ) *
          Real.log 2) := by
    dsimp [D]
    exact certifiedBlockEntropy_le_certifiedBlockCount_add_dissDim
      (a := a) hpos J
  have hdiffN :
      ∀ y ∈ nonnegativeDifferenceSet (certifiedOddBlocks a J), y ≤ N := by
    intro y hy
    rw [mem_nonnegativeDifferenceSet_iff] at hy
    rcases hy with ⟨x, hx, z, _hz, rfl⟩
    exact (Nat.sub_le x z).trans (hN x hx)
  have hD :
      D ≤ 2 * Nat.log 2 (N + 1) + 1 := by
    dsimp [D]
    exact subsetSumDissociatedDimension_le_two_log hdiffN
  have hnat :
      certifiedBlockCount a J + 2 * D + 1 ≤
        certifiedBlockCount a J + 4 * Nat.log 2 (N + 1) + 3 := by
    omega
  have hcast :
      (((certifiedBlockCount a J + 2 * D + 1 : ℕ) : ℝ)) ≤
        (((certifiedBlockCount a J + 4 * Nat.log 2 (N + 1) + 3 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hlog_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact hbase.trans (mul_le_mul_of_nonneg_right hcast hlog_nonneg)


end

end IrrationalityAr
