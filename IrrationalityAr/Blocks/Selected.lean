import IrrationalityAr.Blocks.ContinuantBounds
import IrrationalityAr.AdditiveBlockBridge

namespace IrrationalityAr

/-!
# Parity-selected continued-fraction blocks

This module contains the finite parity combinatorics for canonical
continued-fraction blocks: which intermediate indices are selected by odd
numerator parity, how large the selected block is, and the finite arithmetic
progression contained in each selected denominator block.
-/

/-- The local parity-count estimate from the writeup:
`floor(a_{j+1}/2) ≤ L_j`. -/
def HasBlockParityLowerBound (a : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, a (j + 1) / 2 ≤ canonicalBlockLength a j

private lemma count_odd_affine_nat_lower_bound
    (u v m : ℕ)
    (hnotBothEven : ¬ (Even u ∧ Even v)) :
    m / 2 ≤ ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)).card := by
  rcases Nat.even_or_odd v with hvEven | hvOdd
  · have huOdd : Odd u := by
      rcases Nat.even_or_odd u with huEven | huOdd
      · exact False.elim (hnotBothEven ⟨huEven, hvEven⟩)
      · exact huOdd
    have hfilter :
        ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)) =
          Finset.Icc 1 m := by
      ext t
      constructor
      · intro ht
        exact (Finset.mem_filter.mp ht).1
      · intro ht
        rw [Finset.mem_filter]
        exact ⟨ht, huOdd.add_even (hvEven.mul_left t)⟩
    rw [hfilter]
    calc
      m / 2 ≤ m := Nat.div_le_self _ _
      _ = (Finset.Icc 1 m).card := by simp
  · rcases Nat.even_or_odd u with huEven | huOdd
    · let f : ℕ → ℕ := fun k => 2 * k + 1
      have himage_subset : (Finset.range (m / 2)).image f ⊆
          ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)) := by
        intro t ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨k, hk, rfl⟩
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hklt : k < m / 2 := Finset.mem_range.mp hk
        have hkle : k + 1 ≤ m / 2 := Nat.succ_le_of_lt hklt
        have htwom : 2 * (m / 2) ≤ m := by
          simpa using Nat.mul_div_le m 2
        have h2k2 : 2 * (k + 1) ≤ m := by
          exact (Nat.mul_le_mul_left 2 hkle).trans htwom
        have hle : 2 * k + 1 ≤ m := by
          have hlt : 2 * k + 1 < 2 * (k + 1) := by omega
          exact (Nat.le_of_lt hlt).trans h2k2
        have hge : 1 ≤ 2 * k + 1 :=
          Nat.succ_le_succ (Nat.zero_le (2 * k))
        have htOdd : Odd (2 * k + 1) :=
          (Even.mul_right even_two k).add_one
        exact ⟨⟨hge, hle⟩, huEven.add_odd (htOdd.mul hvOdd)⟩
      calc
        m / 2 = (Finset.range (m / 2)).card := by simp
        _ = ((Finset.range (m / 2)).image f).card := by
          rw [Finset.card_image_of_injOn]
          intro x hx y hy hxy
          dsimp [f] at hxy
          omega
        _ ≤ ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)).card :=
          Finset.card_le_card himage_subset
    · let f : ℕ → ℕ := fun k => 2 * (k + 1)
      have himage_subset : (Finset.range (m / 2)).image f ⊆
          ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)) := by
        intro t ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨k, hk, rfl⟩
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hklt : k < m / 2 := Finset.mem_range.mp hk
        have hkle : k + 1 ≤ m / 2 := Nat.succ_le_of_lt hklt
        have htwom : 2 * (m / 2) ≤ m := by
          simpa using Nat.mul_div_le m 2
        have hle : 2 * (k + 1) ≤ m := by
          exact (Nat.mul_le_mul_left 2 hkle).trans htwom
        have hge : 1 ≤ 2 * (k + 1) := by omega
        have htEven : Even (2 * (k + 1)) :=
          Even.mul_right even_two (k + 1)
        exact ⟨⟨hge, hle⟩, huOdd.add_even (htEven.mul_right v)⟩
      calc
        m / 2 = (Finset.range (m / 2)).card := by simp
        _ = ((Finset.range (m / 2)).image f).card := by
          rw [Finset.card_image_of_injOn]
          intro x hx y hy hxy
          dsimp [f] at hxy
          omega
        _ ≤ ((Finset.Icc 1 m).filter fun t : ℕ => Odd (u + t * v)).card :=
          Finset.card_le_card himage_subset

theorem hasBlockParityLowerBound (a : ℕ → ℕ) : HasBlockParityLowerBound a := by
  intro j
  unfold canonicalBlockLength canonicalOddBlock CFBlockNumerator
  exact count_odd_affine_nat_lower_bound
    (continuantNumPrev a j) (continuantNum a j) (a (j + 1))
    (continuantNumPrev_not_even_and_even a j)

lemma canonicalBlockLength_lower_bound (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ canonicalBlockLength a j :=
  hasBlockParityLowerBound a j

/-- If `p_{j-1}` is odd and `p_j` is even, every index in the block is
parity-selected. -/
lemma odd_CFBlockNumerator_of_prev_odd_curr_even
    {a : ℕ → ℕ} {j t : ℕ}
    (hprev : Odd (continuantNumPrev a j))
    (hcurr : Even (continuantNum a j)) :
    Odd (CFBlockNumerator a j t) := by
  unfold CFBlockNumerator
  exact hprev.add_even (hcurr.mul_left t)

/-- If `p_{j-1}` is even and `p_j` is odd, the selected indices in the block
are exactly the odd indices. -/
lemma odd_CFBlockNumerator_iff_of_prev_even_curr_odd
    {a : ℕ → ℕ} {j t : ℕ}
    (hprev : Even (continuantNumPrev a j))
    (hcurr : Odd (continuantNum a j)) :
    Odd (CFBlockNumerator a j t) ↔ Odd t := by
  constructor
  · intro hodd
    rcases Nat.even_or_odd t with htEven | htOdd
    · exfalso
      have hblockEven : Even (CFBlockNumerator a j t) := by
        unfold CFBlockNumerator
        exact hprev.add (htEven.mul_right (continuantNum a j))
      exact (Nat.not_even_iff_odd.mpr hodd) hblockEven
    · exact htOdd
  · intro htOdd
    unfold CFBlockNumerator
    exact hprev.add_odd (htOdd.mul hcurr)

/-- If both `p_{j-1}` and `p_j` are odd, the selected indices in the block are
exactly the even indices. -/
lemma odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
    {a : ℕ → ℕ} {j t : ℕ}
    (hprev : Odd (continuantNumPrev a j))
    (hcurr : Odd (continuantNum a j)) :
    Odd (CFBlockNumerator a j t) ↔ Even t := by
  constructor
  · intro hodd
    rcases Nat.even_or_odd t with htEven | htOdd
    · exact htEven
    · exfalso
      have hblockEven : Even (CFBlockNumerator a j t) := by
        unfold CFBlockNumerator
        exact hprev.add_odd (htOdd.mul hcurr)
      exact (Nat.not_even_iff_odd.mpr hodd) hblockEven
  · intro htEven
    unfold CFBlockNumerator
    exact hprev.add_even (htEven.mul_right (continuantNum a j))

lemma exists_canonicalOddCFIndex_or_emptyBlock
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (j : ℕ) :
    (∃ t : ℕ, CanonicalOddCFIndex a j t) ∨
      (a (j + 1) = 1 ∧
        Odd (continuantNumPrev a j) ∧ Odd (continuantNum a j)) := by
  rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
  · rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
    · exact False.elim
        (continuantNumPrev_not_even_and_even a j ⟨hprevEven, hcurrEven⟩)
    · left
      refine ⟨1, ?_, ?_, ?_⟩
      · norm_num
      · exact hpos j
      · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
          hprevEven hcurrOdd).2 (by norm_num)
  · rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
    · left
      refine ⟨1, ?_, ?_, ?_⟩
      · norm_num
      · exact hpos j
      · exact odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
    · by_cases hb : 2 ≤ a (j + 1)
      · left
        refine ⟨2, ?_, hb, ?_⟩
        · norm_num
        · exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
            hprevOdd hcurrOdd).2 (by norm_num)
      · right
        have hb1 : a (j + 1) = 1 := by
          have hge1 : 1 ≤ a (j + 1) := hpos j
          omega
        exact ⟨hb1, hprevOdd, hcurrOdd⟩

lemma canonicalOddCFIndex_next_of_emptyBlock
    (a : ℕ → ℕ)
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j : ℕ}
    (hb : a (j + 1) = 1)
    (hprev : Odd (continuantNumPrev a j))
    (hcurr : Odd (continuantNum a j)) :
    CanonicalOddCFIndex a (j + 1) 1 := by
  refine ⟨by norm_num, hpos (j + 1), ?_⟩
  have hnextEven : Even (continuantNum a (j + 1)) := by
    rw [continuantNum_succ_eq, hb]
    simpa [Nat.add_comm] using hcurr.add_odd hprev
  exact odd_CFBlockNumerator_of_prev_odd_curr_even
    (a := a) (j := j + 1) (t := 1)
    (by simpa [continuantNumPrev] using hcurr) hnextEven

lemma consecutiveCanonicalOddCFIndices_block_le_add_two
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t k s : ℕ}
    (hconsec : ConsecutiveCanonicalOddCFIndices a j t k s) :
    k ≤ j + 2 := by
  rcases hconsec with ⟨_hjt, _hks, hlt, hnone⟩
  by_contra hnot
  have hj2lt : j + 2 < k := by
    rcases hlt with hjk | ⟨hjk, hts⟩
    · omega
    · subst k
      omega
  rcases exists_canonicalOddCFIndex_or_emptyBlock a hpos (j + 1) with
    ⟨u, hu⟩ | ⟨hb, hprev, hcurr⟩
  · exact hnone (j + 1) u hu
      (Or.inl (by omega))
      (Or.inl (by omega))
  · have hnext : CanonicalOddCFIndex a (j + 2) 1 :=
      canonicalOddCFIndex_next_of_emptyBlock
        (a := a) hpos hb hprev hcurr
    exact hnone (j + 2) 1 hnext
      (Or.inl (by omega))
      (Or.inl (by omega))

lemma emptyBlock_of_consecutiveCanonicalOddCFIndices_skip_two
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t k s : ℕ}
    (hconsec : ConsecutiveCanonicalOddCFIndices a j t k s)
    (hk : k = j + 2) :
    a (j + 2) = 1 ∧
      Odd (continuantNumPrev a (j + 1)) ∧
        Odd (continuantNum a (j + 1)) := by
  rcases hconsec with ⟨_hjt, _hks, _hlt, hnone⟩
  rcases exists_canonicalOddCFIndex_or_emptyBlock a hpos (j + 1) with
    ⟨u, hu⟩ | hempty
  · have hbetween_right : CFBlockIndexLt (j + 1) u k s := by
      subst k
      exact Or.inl (by omega)
    exact False.elim
      (hnone (j + 1) u hu (Or.inl (by omega)) hbetween_right)
  · exact hempty

lemma canonicalOddCFIndex_endpoint_of_next_emptyBlock
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j : ℕ}
    (hempty :
      a (j + 2) = 1 ∧
        Odd (continuantNumPrev a (j + 1)) ∧
          Odd (continuantNum a (j + 1))) :
    CanonicalOddCFIndex a j (a (j + 1)) := by
  refine ⟨hpos j, le_rfl, ?_⟩
  rw [CFBlockNumerator_endpoint]
  exact hempty.2.2

lemma isFirstSelectedInBlock_eq_one_or_two
    {a : ℕ → ℕ} {k s : ℕ}
    (hfirst : IsFirstSelectedInBlock a k s) :
    s = 1 ∨ s = 2 := by
  rcases hfirst with ⟨hs, hminimal⟩
  rcases hs with ⟨hs1, hsle, hsOdd⟩
  rcases Nat.even_or_odd (continuantNumPrev a k) with hprevEven | hprevOdd
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · exact False.elim
        (continuantNumPrev_not_even_and_even a k ⟨hprevEven, hcurrEven⟩)
    · left
      have hsOddIndex : Odd s :=
        (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
          hprevEven hcurrOdd).1 hsOdd
      rcases hsOddIndex with ⟨m, hm⟩
      by_contra hsne
      have h1lt : 1 < s := by omega
      have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
            hprevEven hcurrOdd).2 (by norm_num)
      exact hminimal 1 hsel1 h1lt
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · left
      by_contra hsne
      have h1lt : 1 < s := by omega
      have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
      exact hminimal 1 hsel1 h1lt
    · right
      have hsEven : Even s :=
        (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
          hprevOdd hcurrOdd).1 hsOdd
      rcases hsEven with ⟨m, hm⟩
      by_contra hsne
      have h2lt : 2 < s := by
        have hsne1 : s ≠ 1 := by
          intro hsEq
          omega
        omega
      have hsel2 : CanonicalOddCFIndex a k 2 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
            hprevOdd hcurrOdd).2 (by norm_num)
      exact hminimal 2 hsel2 h2lt

lemma odd_num_pair_of_isFirstSelectedInBlock_eq_two
    {a : ℕ → ℕ} {k : ℕ}
    (hfirst : IsFirstSelectedInBlock a k 2) :
    Odd (continuantNumPrev a k) ∧ Odd (continuantNum a k) := by
  rcases hfirst with ⟨hsel2, hminimal⟩
  rcases hsel2 with ⟨_h21, h2le, _h2odd⟩
  rcases Nat.even_or_odd (continuantNumPrev a k) with hprevEven | hprevOdd
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · exact False.elim
        (continuantNumPrev_not_even_and_even a k ⟨hprevEven, hcurrEven⟩)
    · have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
            hprevEven hcurrOdd).2 (by norm_num)
      exact False.elim (hminimal 1 hsel1 (by norm_num))
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
      exact False.elim (hminimal 1 hsel1 (by norm_num))
    · exact ⟨hprevOdd, hcurrOdd⟩

lemma even_index_of_isFirstSelectedInBlock_eq_two
    {a : ℕ → ℕ} {k u : ℕ}
    (hfirst : IsFirstSelectedInBlock a k 2)
    (hu : CanonicalOddCFIndex a k u) :
    Even u := by
  rcases hfirst with ⟨hsel2, hminimal⟩
  rcases hsel2 with ⟨_h21, h2le, h2odd⟩
  rcases hu with ⟨_hu1, _hule, huodd⟩
  rcases Nat.even_or_odd (continuantNumPrev a k) with hprevEven | hprevOdd
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · exact False.elim
        (continuantNumPrev_not_even_and_even a k ⟨hprevEven, hcurrEven⟩)
    · have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact (odd_CFBlockNumerator_iff_of_prev_even_curr_odd
            hprevEven hcurrOdd).2 (by norm_num)
      exact False.elim (hminimal 1 hsel1 (by norm_num))
  · rcases Nat.even_or_odd (continuantNum a k) with hcurrEven | hcurrOdd
    · have hsel1 : CanonicalOddCFIndex a k 1 := by
        refine ⟨by norm_num, ?_, ?_⟩
        · omega
        · exact odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven
      exact False.elim (hminimal 1 hsel1 (by norm_num))
    · exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
        hprevOdd hcurrOdd).1 huodd

lemma mem_canonicalOddBlock_iff {a : ℕ → ℕ} {j t : ℕ} :
    t ∈ canonicalOddBlock a j ↔
      1 ≤ t ∧ t ≤ a (j + 1) ∧ Odd (CFBlockNumerator a j t) := by
  simp [canonicalOddBlock, and_assoc]

/-- Denominators `q - 1` coming from the parity-selected part of one
canonical continued-fraction block. -/
def canonicalOddDenominatorBlock (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (canonicalOddBlock a j).image
    fun t : ℕ => CFBlockDenominator a j t - 1

private lemma CFBlockDenominator_sub_one_injOn_canonicalOddBlock
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    Set.InjOn
      (fun t : ℕ => CFBlockDenominator a j t - 1)
      (canonicalOddBlock a j : Set ℕ) := by
  intro x hx y hy hxy
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hxone : 1 ≤ x := (mem_canonicalOddBlock_iff.mp hx).1
  have hyone : 1 ≤ y := (mem_canonicalOddBlock_iff.mp hy).1
  have hxdenpos : 0 < CFBlockDenominator a j x := by
    unfold CFBlockDenominator
    exact Nat.add_pos_right _ (Nat.mul_pos hxone hqpos)
  have hydenpos : 0 < CFBlockDenominator a j y := by
    unfold CFBlockDenominator
    exact Nat.add_pos_right _ (Nat.mul_pos hyone hqpos)
  change CFBlockDenominator a j x - 1 =
    CFBlockDenominator a j y - 1 at hxy
  have hden :
      CFBlockDenominator a j x = CFBlockDenominator a j y := by
    calc
      CFBlockDenominator a j x =
          (CFBlockDenominator a j x - 1) + 1 := by
            exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hxdenpos)).symm
      _ = (CFBlockDenominator a j y - 1) + 1 := by rw [hxy]
      _ = CFBlockDenominator a j y := by
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt hydenpos)
  have hmul : x * continuantDen a j = y * continuantDen a j := by
    unfold CFBlockDenominator at hden
    exact Nat.add_left_cancel hden
  exact mul_right_cancel₀ (Nat.ne_of_gt hqpos) hmul

lemma canonicalOddDenominatorBlock_card
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (canonicalOddDenominatorBlock a j).card =
      canonicalBlockLength a j := by
  unfold canonicalOddDenominatorBlock canonicalBlockLength
  exact Finset.card_image_of_injOn
    (CFBlockDenominator_sub_one_injOn_canonicalOddBlock a hpos j)

private lemma odd_Icc_eq_image_range (m : ℕ) :
    ((Finset.Icc 1 m).filter fun t : ℕ => Odd t) =
      (Finset.range ((m + 1) / 2)).image fun r : ℕ => 2 * r + 1 := by
  ext t
  constructor
  · intro ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht
    rcases ht with ⟨⟨ht1, htm⟩, htodd⟩
    rcases htodd with ⟨r, rfl⟩
    rw [Finset.mem_image]
    refine ⟨r, ?_, rfl⟩
    rw [Finset.mem_range]
    omega
  · intro ht
    rw [Finset.mem_image] at ht
    rcases ht with ⟨r, hr, rfl⟩
    rw [Finset.mem_range] at hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩

private lemma even_Icc_eq_image_range (m : ℕ) :
    ((Finset.Icc 1 m).filter fun t : ℕ => Even t) =
      (Finset.range (m / 2)).image fun r : ℕ => 2 * (r + 1) := by
  ext t
  constructor
  · intro ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht
    rcases ht with ⟨⟨ht1, htm⟩, hteven⟩
    rcases hteven with ⟨k, hk⟩
    have hkpos : 0 < k := by omega
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro ht
    rw [Finset.mem_image] at ht
    rcases ht with ⟨r, hr, rfl⟩
    rw [Finset.mem_range] at hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨r + 1, by omega⟩⟩

private lemma card_odd_Icc (m : ℕ) :
    (((Finset.Icc 1 m).filter fun t : ℕ => Odd t).card) = (m + 1) / 2 := by
  rw [odd_Icc_eq_image_range]
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x _ y _ hxy
    change 2 * x + 1 = 2 * y + 1 at hxy
    omega

private lemma card_even_Icc (m : ℕ) :
    (((Finset.Icc 1 m).filter fun t : ℕ => Even t).card) = m / 2 := by
  rw [even_Icc_eq_image_range]
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x _ y _ hxy
    change 2 * (x + 1) = 2 * (y + 1) at hxy
    omega

private lemma denominator_sub_one_one_step
    (b q r : ℕ) (hq : 0 < q) :
    (b + 1 * q - 1) + r * q = b + (r + 1) * q - 1 := by
  apply Nat.succ.inj
  have hleft : ((b + 1 * q - 1) + r * q) + 1 =
      b + 1 * q + r * q := by omega
  have hright : (b + (r + 1) * q - 1) + 1 =
      b + (r + 1) * q := by
    have : 1 ≤ b + (r + 1) * q := by
      exact Nat.succ_le_of_lt (Nat.add_pos_right _ (Nat.mul_pos (by omega) hq))
    omega
  calc
    ((b + 1 * q - 1) + r * q) + 1 = b + 1 * q + r * q := hleft
    _ = b + (r + 1) * q := by ring
    _ = (b + (r + 1) * q - 1) + 1 := hright.symm

private lemma denominator_sub_one_odd_step
    (b q r : ℕ) (hq : 0 < q) :
    (b + 1 * q - 1) + r * (2 * q) = b + (2 * r + 1) * q - 1 := by
  apply Nat.succ.inj
  have hleft : ((b + 1 * q - 1) + r * (2 * q)) + 1 =
      b + 1 * q + r * (2 * q) := by omega
  have hright : (b + (2 * r + 1) * q - 1) + 1 =
      b + (2 * r + 1) * q := by
    have : 1 ≤ b + (2 * r + 1) * q := by
      exact Nat.succ_le_of_lt (Nat.add_pos_right _ (Nat.mul_pos (by omega) hq))
    omega
  calc
    ((b + 1 * q - 1) + r * (2 * q)) + 1 =
        b + 1 * q + r * (2 * q) := hleft
    _ = b + (2 * r + 1) * q := by ring
    _ = (b + (2 * r + 1) * q - 1) + 1 := hright.symm

private lemma denominator_sub_one_even_step
    (b q r : ℕ) (hq : 0 < q) :
    (b + 2 * q - 1) + r * (2 * q) = b + (2 * (r + 1)) * q - 1 := by
  apply Nat.succ.inj
  have hleft : ((b + 2 * q - 1) + r * (2 * q)) + 1 =
      b + 2 * q + r * (2 * q) := by omega
  have hright : (b + (2 * (r + 1)) * q - 1) + 1 =
      b + (2 * (r + 1)) * q := by
    have : 1 ≤ b + (2 * (r + 1)) * q := by
      exact Nat.succ_le_of_lt (Nat.add_pos_right _ (Nat.mul_pos (by omega) hq))
    omega
  calc
    ((b + 2 * q - 1) + r * (2 * q)) + 1 =
        b + 2 * q + r * (2 * q) := hleft
    _ = b + (2 * (r + 1)) * q := by ring
    _ = (b + (2 * (r + 1)) * q - 1) + 1 := hright.symm

private lemma canonicalOddBlock_eq_Icc_of_prev_odd_curr_even
    {a : ℕ → ℕ} {j : ℕ}
    (hprevOdd : Odd (continuantNumPrev a j))
    (hcurrEven : Even (continuantNum a j)) :
    canonicalOddBlock a j = Finset.Icc 1 (a (j + 1)) := by
  ext t
  rw [mem_canonicalOddBlock_iff, Finset.mem_Icc]
  constructor
  · intro ht
    exact ⟨ht.1, ht.2.1⟩
  · intro ht
    exact ⟨ht.1, ht.2, odd_CFBlockNumerator_of_prev_odd_curr_even hprevOdd hcurrEven⟩

private lemma canonicalOddBlock_eq_odd_filter_of_prev_even_curr_odd
    {a : ℕ → ℕ} {j : ℕ}
    (hprevEven : Even (continuantNumPrev a j))
    (hcurrOdd : Odd (continuantNum a j)) :
    canonicalOddBlock a j =
      (Finset.Icc 1 (a (j + 1))).filter fun t : ℕ => Odd t := by
  ext t
  rw [mem_canonicalOddBlock_iff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro ht
    exact ⟨⟨ht.1, ht.2.1⟩,
      (odd_CFBlockNumerator_iff_of_prev_even_curr_odd hprevEven hcurrOdd).1 ht.2.2⟩
  · intro ht
    exact ⟨ht.1.1, ht.1.2,
      (odd_CFBlockNumerator_iff_of_prev_even_curr_odd hprevEven hcurrOdd).2 ht.2⟩

private lemma canonicalOddBlock_eq_even_filter_of_prev_odd_curr_odd
    {a : ℕ → ℕ} {j : ℕ}
    (hprevOdd : Odd (continuantNumPrev a j))
    (hcurrOdd : Odd (continuantNum a j)) :
    canonicalOddBlock a j =
      (Finset.Icc 1 (a (j + 1))).filter fun t : ℕ => Even t := by
  ext t
  rw [mem_canonicalOddBlock_iff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro ht
    exact ⟨⟨ht.1, ht.2.1⟩,
      (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd hprevOdd hcurrOdd).1 ht.2.2⟩
  · intro ht
    exact ⟨ht.1.1, ht.1.2,
      (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd hprevOdd hcurrOdd).2 ht.2⟩

lemma exists_finiteArithmeticBlock_subset_canonicalOddDenominatorBlock
    (a : ℕ → ℕ) (j : ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∃ s d m : ℕ,
      0 < d ∧
      m = canonicalBlockLength a j ∧
      finiteArithmeticBlock s d m ⊆ canonicalOddDenominatorBlock a j := by
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
  · have hprevOdd : Odd (continuantNumPrev a j) := by
      rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
      · exact False.elim
          (continuantNumPrev_not_even_and_even a j ⟨hprevEven, hcurrEven⟩)
      · exact hprevOdd
    have hblock := canonicalOddBlock_eq_Icc_of_prev_odd_curr_even
      (a := a) (j := j) hprevOdd hcurrEven
    have hlen : canonicalBlockLength a j = a (j + 1) := by
      simp [canonicalBlockLength, hblock]
    refine ⟨CFBlockDenominator a j 1 - 1, continuantDen a j,
      canonicalBlockLength a j, hqpos, rfl, ?_⟩
    intro x hx
    rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
    rw [canonicalOddDenominatorBlock, Finset.mem_image]
    refine ⟨r + 1, ?_, ?_⟩
    · rw [hblock, Finset.mem_Icc]
      omega
    · unfold CFBlockDenominator
      exact (denominator_sub_one_one_step
        (continuantDenPrev a j) (continuantDen a j) r hqpos).symm
  · rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
    · have hblock := canonicalOddBlock_eq_odd_filter_of_prev_even_curr_odd
        (a := a) (j := j) hprevEven hcurrOdd
      have hlen : canonicalBlockLength a j = (a (j + 1) + 1) / 2 := by
        simp [canonicalBlockLength, hblock, card_odd_Icc]
      refine ⟨CFBlockDenominator a j 1 - 1, 2 * continuantDen a j,
        canonicalBlockLength a j, Nat.mul_pos (by norm_num) hqpos, rfl, ?_⟩
      intro x hx
      rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
      rw [canonicalOddDenominatorBlock, Finset.mem_image]
      refine ⟨2 * r + 1, ?_, ?_⟩
      · rw [hblock, Finset.mem_filter, Finset.mem_Icc]
        rw [hlen] at hr
        exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩
      · unfold CFBlockDenominator
        exact (denominator_sub_one_odd_step
          (continuantDenPrev a j) (continuantDen a j) r hqpos).symm
    · have hblock := canonicalOddBlock_eq_even_filter_of_prev_odd_curr_odd
        (a := a) (j := j) hprevOdd hcurrOdd
      have hlen : canonicalBlockLength a j = a (j + 1) / 2 := by
        simp [canonicalBlockLength, hblock, card_even_Icc]
      refine ⟨CFBlockDenominator a j 2 - 1, 2 * continuantDen a j,
        canonicalBlockLength a j, Nat.mul_pos (by norm_num) hqpos, rfl, ?_⟩
      intro x hx
      rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
      rw [canonicalOddDenominatorBlock, Finset.mem_image]
      refine ⟨2 * (r + 1), ?_, ?_⟩
      · rw [hblock, Finset.mem_filter, Finset.mem_Icc]
        rw [hlen] at hr
        exact ⟨⟨by omega, by omega⟩, ⟨r + 1, by omega⟩⟩
      · unfold CFBlockDenominator
        exact (denominator_sub_one_even_step
          (continuantDenPrev a j) (continuantDen a j) r hqpos).symm

end IrrationalityAr
