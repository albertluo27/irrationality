import IrrationalityAr.EulerContinuedFraction


import IrrationalityAr.ArithmeticCircleFoundation

/-! ## Merged from IrrationalityAr/RamanujanCertifiedSubsequence.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Ramanujan-certified canonical subsequences

This file contains the coefficient-side, finite part of the Ramanujan strategy
for `A_{1 / π}`.  The analytic Ramanujan interval machinery is intentionally
kept out of this layer: once a continued-fraction prefix is certified, the
corresponding finite union of canonical odd denominator blocks is an exact
finite subset of the floor-sum divisibility set.
-/

/-- The finite set consisting of the first `J` parity-selected canonical
continued-fraction denominator blocks, with the harmless initial shifted value
`0` removed.

Recall that `canonicalOddDenominatorBlock a j` stores shifted denominators
`Q_{j,t} - 1`, not raw denominators `Q_{j,t}`. -/
noncomputable def certifiedOddBlocks (a : ℕ → ℕ) (J : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.range J).biUnion fun j : ℕ =>
    canonicalOddDenominatorBlock a j).erase 0

@[simp] theorem mem_certifiedOddBlocks_iff
    {a : ℕ → ℕ} {J n : ℕ} :
    n ∈ certifiedOddBlocks a J ↔
      n ≠ 0 ∧
        ∃ j : ℕ, j < J ∧ n ∈ canonicalOddDenominatorBlock a j := by
  classical
  unfold certifiedOddBlocks
  rw [Finset.mem_erase, Finset.mem_biUnion]
  constructor
  · rintro ⟨hne, j, hj, hn⟩
    exact ⟨hne, j, Finset.mem_range.mp hj, hn⟩
  · rintro ⟨hne, j, hj, hn⟩
    exact ⟨hne, j, Finset.mem_range.mpr hj, hn⟩

/-- A member of a local canonical odd denominator block belongs to the
coefficient-side set `oddBlockASet`, provided the shifted denominator is not
`0`. -/
theorem mem_oddBlockASet_of_mem_canonicalOddDenominatorBlock
    {a : ℕ → ℕ} {j n : ℕ}
    (hn0 : n ≠ 0)
    (hn : n ∈ canonicalOddDenominatorBlock a j) :
    n ∈ oddBlockASet a := by
  classical
  rw [canonicalOddDenominatorBlock] at hn
  rcases Finset.mem_image.mp hn with ⟨t, ht, htn⟩
  have hsel := mem_canonicalOddBlock_iff.mp ht
  rcases hsel with ⟨ht1, htle, hodd⟩
  have hQ2 : 2 ≤ CFBlockDenominator a j t := by
    omega
  exact ⟨j, t, ht1, htle, hodd, hQ2, htn.symm⟩

/-- The first `J` certified canonical odd blocks form an exact finite subset of
`A α`. -/
theorem certifiedOddBlocks_subset_A_of_IsSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ} {J : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a) :
    ↑(certifiedOddBlocks a J) ⊆ A α := by
  intro n hn
  have hA : A α = oddBlockASet a :=
    A_eq_oddBlockASet_of_IsSimpleCFExpansion hαpos hαirr hcf
  rw [hA]
  change n ∈ certifiedOddBlocks a J at hn
  rw [mem_certifiedOddBlocks_iff] at hn
  rcases hn with ⟨hn0, j, _hj, hnblock⟩
  exact mem_oddBlockASet_of_mem_canonicalOddDenominatorBlock hn0 hnblock

/-- A version using a pre-proved equality `A α = oddBlockASet a`. -/
theorem certifiedOddBlocks_subset_A_of_A_eq_oddBlockASet
    {α : ℝ} {a : ℕ → ℕ} {J : ℕ}
    (hA : A α = oddBlockASet a) :
  ↑(certifiedOddBlocks a J) ⊆ A α := by
  intro n hn
  rw [hA]
  change n ∈ certifiedOddBlocks a J at hn
  rw [mem_certifiedOddBlocks_iff] at hn
  rcases hn with ⟨hn0, j, _hj, hnblock⟩
  exact mem_oddBlockASet_of_mem_canonicalOddDenominatorBlock hn0 hnblock

/-! ## Block counts -/

/-- The number of nonempty parity-selected canonical blocks among the first
`J` blocks.  This is the coefficient-side version of the informal block count
before plugging in a particular certified prefix length. -/
def certifiedBlockCount (a : ℕ → ℕ) (J : ℕ) : ℕ :=
  ((Finset.range J).filter fun j : ℕ => 0 < canonicalBlockLength a j).card

@[simp] theorem mem_certifiedBlockCount_filter
    {a : ℕ → ℕ} {J j : ℕ} :
    j ∈ (Finset.range J).filter
        (fun j : ℕ => 0 < canonicalBlockLength a j) ↔
      j < J ∧ 0 < canonicalBlockLength a j := by
  simp

lemma certifiedBlockCount_le (a : ℕ → ℕ) (J : ℕ) :
    certifiedBlockCount a J ≤ J := by
  unfold certifiedBlockCount
  calc
    ((Finset.range J).filter fun j : ℕ =>
        0 < canonicalBlockLength a j).card
        ≤ (Finset.range J).card := Finset.card_filter_le _ _
    _ = J := by simp

lemma certifiedBlockCount_eq_of_all_nonempty
    {a : ℕ → ℕ} {J : ℕ}
    (h : ∀ j : ℕ, j < J → 0 < canonicalBlockLength a j) :
    certifiedBlockCount a J = J := by
  classical
  unfold certifiedBlockCount
  have hfilter :
      ((Finset.range J).filter fun j : ℕ =>
          0 < canonicalBlockLength a j) = Finset.range J := by
    ext j
    constructor
    · intro hj
      exact (Finset.mem_filter.mp hj).1
    · intro hj
      exact Finset.mem_filter.mpr ⟨hj, h j (Finset.mem_range.mp hj)⟩
  rw [hfilter]
  simp

/-- There is no pair of consecutive empty selected blocks below `J`.

This is a finite structural hypothesis, separated from the analytic Ramanujan
input.  It should later be proved directly from parity of continuant
numerators, or reused if an equivalent lemma already exists. -/
def NoTwoConsecutiveEmptyBlocksUpTo (a : ℕ → ℕ) (J : ℕ) : Prop :=
  ∀ j : ℕ, j + 1 < J →
    0 < canonicalBlockLength a j ∨ 0 < canonicalBlockLength a (j + 1)

/-! ## Pure finite pairing lemma -/

/-- Pure finite combinatorics: if every adjacent pair below `J` has at least
one selected index, then at least half of the first `J` indices are selected. -/
private theorem half_le_card_filter_range_of_pair
    (P : ℕ → Prop) [DecidablePred P] :
    ∀ J : ℕ,
      (∀ j : ℕ, j + 1 < J → P j ∨ P (j + 1)) →
        J / 2 ≤ ((Finset.range J).filter P).card := by
  intro J
  refine Nat.strong_induction_on J ?_
  intro J ih hpair
  cases J with
  | zero =>
      simp
  | succ J1 =>
      cases J1 with
      | zero =>
          simp
      | succ K =>
          have hpairK :
              ∀ j : ℕ, j + 1 < K → P j ∨ P (j + 1) := by
            intro j hj
            exact hpair j (by omega)
          have ihK : K / 2 ≤ ((Finset.range K).filter P).card :=
            ih K (by omega) hpairK
          have hnew : P K ∨ P (K + 1) :=
            hpair K (by omega)
          have hif :
              1 ≤ (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
            rcases hnew with hK | hK1
            · by_cases hK1 : P (K + 1) <;> simp [hK, hK1]
            · by_cases hK : P K <;> simp [hK, hK1]
          have hstep :
              ((Finset.range (K + 2)).filter P).card =
                ((Finset.range K).filter P).card +
                  (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
            have h1 := card_filter_range_succ (P := P) (K + 1)
            have h0 := card_filter_range_succ (P := P) K
            calc
              ((Finset.range (K + 2)).filter P).card =
                  ((Finset.range (K + 1)).filter P).card +
                    (if P (K + 1) then 1 else 0) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
              _ = (((Finset.range K).filter P).card +
                    (if P K then 1 else 0)) +
                    (if P (K + 1) then 1 else 0) := by
                    rw [h0]
              _ = ((Finset.range K).filter P).card +
                    (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
                    omega
          rw [hstep]
          omega

/-- Pairing lemma for certified nonempty canonical blocks. -/
theorem half_le_certifiedBlockCount_of_no_two_consecutive_empty
    {a : ℕ → ℕ} {J : ℕ}
    (hpair : NoTwoConsecutiveEmptyBlocksUpTo a J) :
    J / 2 ≤ certifiedBlockCount a J := by
  classical
  unfold certifiedBlockCount
  exact half_le_card_filter_range_of_pair
    (P := fun j : ℕ => 0 < canonicalBlockLength a j)
    J
    (by
      intro j hj
      exact hpair j hj)

/-! ## Canonical no-two-empty blocks -/

private lemma canonicalBlockLength_pos_of_index
    {a : ℕ → ℕ} {j t : ℕ}
    (ht : CanonicalOddCFIndex a j t) :
    0 < canonicalBlockLength a j := by
  classical
  unfold canonicalBlockLength
  exact Finset.card_pos.mpr ⟨t, by
    rw [mem_canonicalOddBlock_iff]
    exact ht⟩

/-- Positive partial quotients imply that two consecutive parity-selected
canonical blocks cannot both be empty. -/
theorem noTwoConsecutiveEmptyBlocks_of_partials_pos
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    ∀ j : ℕ,
      0 < canonicalBlockLength a j ∨
        0 < canonicalBlockLength a (j + 1) := by
  intro j
  rcases exists_canonicalOddCFIndex_or_emptyBlock a hpos j with
    ⟨t, ht⟩ | ⟨hb, hprev, hcurr⟩
  · exact Or.inl (canonicalBlockLength_pos_of_index ht)
  · have hnext : CanonicalOddCFIndex a (j + 1) 1 :=
      canonicalOddCFIndex_next_of_emptyBlock a hpos hb hprev hcurr
    exact Or.inr (canonicalBlockLength_pos_of_index hnext)

/-- Positive partial quotients give the finite `NoTwoConsecutiveEmptyBlocksUpTo`
hypothesis for every prefix length. -/
theorem noTwoConsecutiveEmptyBlocksUpTo_of_partials_pos
    {a : ℕ → ℕ} {J : ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    NoTwoConsecutiveEmptyBlocksUpTo a J := by
  intro j _hj
  exact noTwoConsecutiveEmptyBlocks_of_partials_pos hpos j

/-- Fully usable version: for any positive coefficient sequence, at least half
of the first `J` canonical blocks are nonempty. -/
theorem half_le_certifiedBlockCount_of_partials_pos
    {a : ℕ → ℕ} {J : ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    J / 2 ≤ certifiedBlockCount a J :=
  half_le_certifiedBlockCount_of_no_two_consecutive_empty
    (noTwoConsecutiveEmptyBlocksUpTo_of_partials_pos (a := a) (J := J) hpos)

/-- The informal block count after plugging in a certified prefix length. -/
def certifiedBlockCountAt (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) : ℕ :=
  certifiedBlockCount a (Jcert m)

@[simp] theorem certifiedBlockCountAt_apply
    (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) :
    certifiedBlockCountAt a Jcert m = certifiedBlockCount a (Jcert m) := rfl

/-! ## Certified block-count at a certified prefix length -/

/-- Pointwise half-prefix lower bound, using positive partial quotients. -/
theorem certifiedBlockCountAt_ge_half_of_partials_pos
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (Jcert : ℕ → ℕ) (m : ℕ) :
    Jcert m / 2 ≤ certifiedBlockCountAt a Jcert m := by
  unfold certifiedBlockCountAt
  exact half_le_certifiedBlockCount_of_partials_pos
    (a := a) (J := Jcert m) hpos

/-- Any eventual natural-number lower bound for `Jcert` transfers with a
factor `1/2` to the certified block count. -/
theorem eventually_nat_lower_certifiedBlockCountAt_of_nat_lower_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert g : ℕ → ℕ}
    (hJ : ∀ᶠ m : ℕ in atTop, g m ≤ Jcert m) :
    ∀ᶠ m : ℕ in atTop, g m / 2 ≤ certifiedBlockCountAt a Jcert m := by
  filter_upwards [hJ] with m hm
  have hhalf : Jcert m / 2 ≤ certifiedBlockCountAt a Jcert m :=
    certifiedBlockCountAt_ge_half_of_partials_pos
      (a := a) hpos Jcert m
  exact le_trans (Nat.div_le_div_right hm) hhalf

/-- Integer-slope linear version.  If eventually `C*m ≤ Jcert m`, then
eventually `(C*m)/2 ≤ Bcert m`. -/
theorem eventually_nat_linear_certifiedBlockCountAt_of_nat_linear_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {C : ℕ}
    (hJ : ∀ᶠ m : ℕ in atTop, C * m ≤ Jcert m) :
    ∀ᶠ m : ℕ in atTop,
      (C * m) / 2 ≤ certifiedBlockCountAt a Jcert m :=
  eventually_nat_lower_certifiedBlockCountAt_of_nat_lower_Jcert
    (a := a) hpos (Jcert := Jcert) (g := fun m => C * m) hJ

/-! ## Real-valued lower-bound predicates -/

/-- Eventually `c*m ≤ f(m)`.  This states linear lower production without
committing to a particular floor convention. -/
def EventuallyLinearLowerBound (f : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ≤ (f m : ℝ)

/-- Eventually `c*log(m) ≤ f(m)`. -/
def EventuallyLogLowerBound (f : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, c * Real.log (m : ℝ) ≤ (f m : ℝ)

/-- Harmless floor estimate: as a real number, `n/2` rounded down is at least
`n/2 - 1`. -/
lemma nat_div_two_cast_lower (n : ℕ) :
    (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
  have hnat : n ≤ 2 * (n / 2 + 1) := by omega
  have hreal : (n : ℝ) ≤ (2 * (n / 2 + 1) : ℕ) := by
    exact_mod_cast hnat
  have hreal' : (n : ℝ) ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_mul] using hreal
  nlinarith

/-- Auxiliary real linear transfer.  The hypothesis `hlarge` says the positive
gap `(c/2-c')*m` eventually beats the floor-loss `1`. -/
theorem eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert_aux
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound Jcert c)
    (hlarge : ∀ᶠ m : ℕ in atTop, 1 ≤ (c / 2 - c') * (m : ℝ)) :
    EventuallyLinearLowerBound (certifiedBlockCountAt a Jcert) c' := by
  unfold EventuallyLinearLowerBound at *
  filter_upwards [hJ, hlarge] with m hJm hlarge_m
  have hhalf_nat : Jcert m / 2 ≤ certifiedBlockCountAt a Jcert m :=
    certifiedBlockCountAt_ge_half_of_partials_pos
      (a := a) hpos Jcert m
  have hhalf_real :
      ((Jcert m / 2 : ℕ) : ℝ) ≤
        (certifiedBlockCountAt a Jcert m : ℝ) := by
    exact_mod_cast hhalf_nat
  have hfloor :
      (Jcert m : ℝ) / 2 - 1 ≤ ((Jcert m / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower (Jcert m)
  have hB :
      (Jcert m : ℝ) / 2 - 1 ≤
        (certifiedBlockCountAt a Jcert m : ℝ) :=
    le_trans hfloor hhalf_real
  have hJhalf : c * (m : ℝ) / 2 ≤ (Jcert m : ℝ) / 2 := by
    nlinarith
  have htarget_to_J :
      c' * (m : ℝ) ≤ (Jcert m : ℝ) / 2 - 1 := by
    nlinarith
  exact le_trans htarget_to_J hB

/-- Elementary eventual domination for a positive linear function. -/
lemma eventually_one_le_pos_mul_natCast
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 1 ≤ δ * (m : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hNm : (1 / δ : ℝ) < (m : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hm)
  have hlt : 1 < δ * (m : ℝ) := by
    calc
      1 = δ * (1 / δ) := by field_simp [ne_of_gt hδ]
      _ < δ * (m : ℝ) := mul_lt_mul_of_pos_left hNm hδ
  exact le_of_lt hlt

/-- Real linear production transfers from certified CF-prefix length to
certified nonempty block count, with strict constant loss. -/
theorem eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedBlockCountAt a Jcert) c' := by
  have hδ : 0 < c / 2 - c' := by linarith
  exact eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert_aux
    (a := a) hpos (Jcert := Jcert) (c := c) (c' := c')
    hJ (eventually_one_le_pos_mul_natCast hδ)

/-- Auxiliary logarithmic transfer. -/
theorem eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert_aux
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLogLowerBound Jcert c)
    (hlarge : ∀ᶠ m : ℕ in atTop,
      1 ≤ (c / 2 - c') * Real.log (m : ℝ)) :
    EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c' := by
  unfold EventuallyLogLowerBound at *
  filter_upwards [hJ, hlarge] with m hJm hlarge_m
  have hhalf_nat : Jcert m / 2 ≤ certifiedBlockCountAt a Jcert m :=
    certifiedBlockCountAt_ge_half_of_partials_pos
      (a := a) hpos Jcert m
  have hhalf_real :
      ((Jcert m / 2 : ℕ) : ℝ) ≤
        (certifiedBlockCountAt a Jcert m : ℝ) := by
    exact_mod_cast hhalf_nat
  have hfloor :
      (Jcert m : ℝ) / 2 - 1 ≤ ((Jcert m / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower (Jcert m)
  have hB :
      (Jcert m : ℝ) / 2 - 1 ≤
        (certifiedBlockCountAt a Jcert m : ℝ) :=
    le_trans hfloor hhalf_real
  have htarget_to_J :
      c' * Real.log (m : ℝ) ≤ (Jcert m : ℝ) / 2 - 1 := by
    nlinarith
  exact le_trans htarget_to_J hB

/-- Elementary eventual domination for a positive multiple of `log m`. -/
lemma eventually_one_le_pos_mul_log_natCast
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 1 ≤ δ * Real.log (m : ℝ) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun m : ℕ => δ * Real.log (m : ℝ)) atTop atTop := by
    exact hlog.const_mul_atTop hδ
  exact htend.eventually_ge_atTop 1

/-- Logarithmic lower production transfers from certified CF-prefix length to
certified nonempty block count, with strict factor loss. -/
theorem eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLogLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c' := by
  have hδ : 0 < c / 2 - c' := by linarith
  exact eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert_aux
    (a := a) hpos (Jcert := Jcert) (c := c) (c' := c')
    hJ (eventually_one_le_pos_mul_log_natCast hδ)

/-! ## Cardinality of the extracted certified set -/

private lemma finset_card_le_card_erase_add_one (s : Finset ℕ) (x : ℕ) :
    s.card ≤ (s.erase x).card + 1 := by
  classical
  by_cases hx : x ∈ s
  · have hcard : (s.erase x).card = s.card - 1 := by
      simpa using Finset.card_erase_of_mem hx
    omega
  · have herase : s.erase x = s := Finset.erase_eq_of_notMem hx
    simp [herase]

/-- Different canonical denominator blocks are disjoint, after shifting by
`-1`. -/
theorem canonicalOddDenominatorBlock_disjoint_of_ne
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (canonicalOddDenominatorBlock a j)
      (canonicalOddDenominatorBlock a k) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxj hxk
  rw [canonicalOddDenominatorBlock, Finset.mem_image] at hxj hxk
  rcases hxj with ⟨t, ht, htx⟩
  rcases hxk with ⟨s, hs, hsx⟩
  have htinfo := mem_canonicalOddBlock_iff.mp ht
  have hsinfo := mem_canonicalOddBlock_iff.mp hs
  have ht_bounds : 1 ≤ t ∧ t ≤ a (j + 1) := ⟨htinfo.1, htinfo.2.1⟩
  have hs_bounds : 1 ≤ s ∧ s ≤ a (k + 1) := ⟨hsinfo.1, hsinfo.2.1⟩
  have hqjpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hqkpos : 0 < continuantDen a k :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos k)
  have hQjt_pos : 0 < CFBlockDenominator a j t := by
    unfold CFBlockDenominator
    exact Nat.add_pos_right _ (Nat.mul_pos htinfo.1 hqjpos)
  have hQks_pos : 0 < CFBlockDenominator a k s := by
    unfold CFBlockDenominator
    exact Nat.add_pos_right _ (Nat.mul_pos hsinfo.1 hqkpos)
  have hsubeq :
      CFBlockDenominator a j t - 1 =
        CFBlockDenominator a k s - 1 := by
    rw [htx, hsx]
  have hQeq : CFBlockDenominator a j t = CFBlockDenominator a k s := by
    omega
  rcases lt_or_gt_of_ne hjk with hjk_lt | hkj_lt
  · have hlt : CFBlockDenominator a j t < CFBlockDenominator a k s :=
      CFBlockDenominator_lt_of_block_lt hpos ht_bounds hs_bounds hjk_lt
    omega
  · have hlt : CFBlockDenominator a k s < CFBlockDenominator a j t :=
      CFBlockDenominator_lt_of_block_lt hpos hs_bounds ht_bounds hkj_lt
    omega

/-- The nonempty-block count is bounded by the sum of the local block lengths. -/
lemma certifiedBlockCount_le_sum_canonicalBlockLength
    (a : ℕ → ℕ) (J : ℕ) :
    certifiedBlockCount a J ≤
      (Finset.range J).sum fun j : ℕ => canonicalBlockLength a j := by
  classical
  unfold certifiedBlockCount
  calc
    ((Finset.range J).filter fun j : ℕ => 0 < canonicalBlockLength a j).card
        = ((Finset.range J).filter fun j : ℕ =>
            0 < canonicalBlockLength a j).sum (fun _ : ℕ => 1) := by
          simp
    _ ≤ ((Finset.range J).filter fun j : ℕ =>
            0 < canonicalBlockLength a j).sum
              (fun j : ℕ => canonicalBlockLength a j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact Nat.succ_le_of_lt (Finset.mem_filter.mp hj).2
    _ ≤ (Finset.range J).sum fun j : ℕ => canonicalBlockLength a j := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro j hj; exact (Finset.mem_filter.mp hj).1)
            (by intro x hxrange hxnot; exact Nat.zero_le _)

/-- The sum of local block lengths over the first `J` blocks is exactly the
cardinality of the un-erased union of the denominator blocks. -/
lemma card_biUnion_canonicalOddDenominatorBlock
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    (((Finset.range J).biUnion fun j : ℕ =>
        canonicalOddDenominatorBlock a j).card) =
      (Finset.range J).sum fun j : ℕ => canonicalBlockLength a j := by
  classical
  let F : ℕ → Finset ℕ := fun j => canonicalOddDenominatorBlock a j
  have hdisj :
      ∀ j ∈ Finset.range J, ∀ k ∈ Finset.range J, j ≠ k →
        Disjoint (F j) (F k) := by
    intro j _hj k _hk hjk
    exact canonicalOddDenominatorBlock_disjoint_of_ne
      (a := a) hpos hjk
  calc
    (((Finset.range J).biUnion fun j : ℕ =>
        canonicalOddDenominatorBlock a j).card)
        = (Finset.range J).sum fun j : ℕ =>
            (canonicalOddDenominatorBlock a j).card := by
          simpa [F] using Finset.card_biUnion hdisj
    _ = (Finset.range J).sum fun j : ℕ => canonicalBlockLength a j := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact canonicalOddDenominatorBlock_card a hpos j

/-- The actual certified finite subset has at least one element for every
nonempty block, except for the one possible erased zero. -/
theorem certifiedBlockCount_le_certifiedOddBlocks_card_add_one
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    certifiedBlockCount a J ≤ (certifiedOddBlocks a J).card + 1 := by
  classical
  let U : Finset ℕ :=
    (Finset.range J).biUnion fun j : ℕ => canonicalOddDenominatorBlock a j
  have hcount_le_sum := certifiedBlockCount_le_sum_canonicalBlockLength a J
  have hUcard : U.card =
      (Finset.range J).sum fun j : ℕ => canonicalBlockLength a j := by
    dsimp [U]
    exact card_biUnion_canonicalOddDenominatorBlock hpos J
  have hU_le_erase : U.card ≤ (U.erase 0).card + 1 :=
    finset_card_le_card_erase_add_one U 0
  have hcert : certifiedOddBlocks a J = U.erase 0 := by
    unfold certifiedOddBlocks
    rfl
  rw [hcert]
  exact hcount_le_sum.trans (hUcard ▸ hU_le_erase)

/-- Combining no-two-empty blocks with the cardinal extraction lemma gives a
literal extracted finite subset of size at least `J/2 - 1`. -/
theorem half_prefix_sub_one_le_certifiedOddBlocks_card_of_partials_pos
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (J : ℕ) :
    J / 2 - 1 ≤ (certifiedOddBlocks a J).card := by
  have hhalf : J / 2 ≤ certifiedBlockCount a J :=
    half_le_certifiedBlockCount_of_partials_pos
      (a := a) (J := J) hpos
  have hcard : certifiedBlockCount a J ≤
      (certifiedOddBlocks a J).card + 1 :=
    certifiedBlockCount_le_certifiedOddBlocks_card_add_one
      (a := a) hpos J
  omega

/-! ## Cardinality at a certified prefix length -/

/-- Cardinality of the actual finite extracted subset associated to a certified
prefix function `Jcert`. -/
noncomputable def certifiedOddBlocksCardAt (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) : ℕ :=
  (certifiedOddBlocks a (Jcert m)).card

@[simp] theorem certifiedOddBlocksCardAt_apply
    (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) :
    certifiedOddBlocksCardAt a Jcert m =
      (certifiedOddBlocks a (Jcert m)).card := rfl

/-- Exact Nat-valued extraction transfer from `Jcert` to the cardinality of the
actual certified subset. -/
theorem eventually_nat_lower_certifiedOddBlocksCardAt_of_nat_lower_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert g : ℕ → ℕ}
    (hJ : ∀ᶠ m : ℕ in atTop, g m ≤ Jcert m) :
    ∀ᶠ m : ℕ in atTop,
      g m / 2 - 1 ≤ certifiedOddBlocksCardAt a Jcert m := by
  filter_upwards [hJ] with m hm
  have hmono : g m / 2 ≤ Jcert m / 2 := Nat.div_le_div_right hm
  have hcard : Jcert m / 2 - 1 ≤ certifiedOddBlocksCardAt a Jcert m := by
    unfold certifiedOddBlocksCardAt
    exact half_prefix_sub_one_le_certifiedOddBlocks_card_of_partials_pos
      (a := a) hpos (Jcert m)
  omega

/-- Real linear lower bound for the cardinality of the actual extracted
subset.  The strict loss `c' < c/2` absorbs the floor loss and the erased-zero
loss. -/
theorem eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedOddBlocksCardAt a Jcert) c' := by
  unfold EventuallyLinearLowerBound at *
  have hδ : 0 < c / 2 - c' := sub_pos.mpr hc'
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 ≤ (c / 2 - c') * (m : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (c / 2 - c'))
    filter_upwards [eventually_ge_atTop N] with m hm
    have hNm : (2 / (c / 2 - c') : ℝ) < (m : ℝ) := by
      exact lt_of_lt_of_le hN (by exact_mod_cast hm)
    have hlt : 2 < (c / 2 - c') * (m : ℝ) := by
      calc
        2 = (c / 2 - c') * (2 / (c / 2 - c')) := by
              have hden : c - 2 * c' ≠ 0 := by nlinarith
              field_simp [hden]
        _ < (c / 2 - c') * (m : ℝ) := mul_lt_mul_of_pos_left hNm hδ
    exact le_of_lt hlt
  filter_upwards [hJ, hlarge] with m hJm hlarge_m
  let C : ℕ := certifiedOddBlocksCardAt a Jcert m
  have hhalf_nat : Jcert m / 2 ≤ C + 1 := by
    dsimp [C, certifiedOddBlocksCardAt]
    have htmp := half_prefix_sub_one_le_certifiedOddBlocks_card_of_partials_pos
      (a := a) hpos (Jcert m)
    omega
  have hhalf_real : ((Jcert m / 2 : ℕ) : ℝ) ≤ (C : ℝ) + 1 := by
    exact_mod_cast hhalf_nat
  have hfloor : (Jcert m : ℝ) / 2 - 1 ≤ ((Jcert m / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower (Jcert m)
  have hC_lower : (Jcert m : ℝ) / 2 - 2 ≤ (C : ℝ) := by
    nlinarith
  have htarget_to_J : c' * (m : ℝ) ≤ (Jcert m : ℝ) / 2 - 2 := by
    nlinarith
  exact le_trans htarget_to_J hC_lower

/-- Real logarithmic lower bound for the cardinality of the actual extracted
subset.  Again, `c' < c/2` absorbs floors and the erased-zero loss. -/
theorem eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLogLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedOddBlocksCardAt a Jcert) c' := by
  unfold EventuallyLogLowerBound at *
  have hδ : 0 < c / 2 - c' := sub_pos.mpr hc'
  have hlog_large : ∀ᶠ m : ℕ in atTop,
      2 ≤ (c / 2 - c') * Real.log (m : ℝ) := by
    have hlog_tendsto : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have htend : Tendsto
        (fun m : ℕ => (c / 2 - c') * Real.log (m : ℝ)) atTop atTop := by
      exact hlog_tendsto.const_mul_atTop hδ
    exact htend.eventually_ge_atTop 2
  filter_upwards [hJ, hlog_large] with m hJm hlarge_m
  let C : ℕ := certifiedOddBlocksCardAt a Jcert m
  have hhalf_nat : Jcert m / 2 ≤ C + 1 := by
    dsimp [C, certifiedOddBlocksCardAt]
    have htmp := half_prefix_sub_one_le_certifiedOddBlocks_card_of_partials_pos
      (a := a) hpos (Jcert m)
    omega
  have hhalf_real : ((Jcert m / 2 : ℕ) : ℝ) ≤ (C : ℝ) + 1 := by
    exact_mod_cast hhalf_nat
  have hfloor : (Jcert m : ℝ) / 2 - 1 ≤ ((Jcert m / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower (Jcert m)
  have hC_lower : (Jcert m : ℝ) / 2 - 2 ≤ (C : ℝ) := by
    nlinarith
  have htarget_to_J : c' * Real.log (m : ℝ) ≤
      (Jcert m : ℝ) / 2 - 2 := by
    nlinarith
  exact le_trans htarget_to_J hC_lower

/-! ## Specialization names for `1 / π` -/

noncomputable def oneOverPi : ℝ := 1 / Real.pi

noncomputable def oneOverPiCF : ℕ → ℕ := simplePartialQuotient oneOverPi

/-- Placeholder certified-prefix length supplied by a future Ramanujan interval
computation. -/
noncomputable def J_oneOverPi : ℕ → ℕ := fun _ => 0

/-- Formal version of the informal `B_π(m)`, before any analytic lower bound on
the certified prefix length is supplied. -/
noncomputable def B_oneOverPi (m : ℕ) : ℕ :=
  certifiedBlockCountAt oneOverPiCF J_oneOverPi m

/-- Exact finite subset of `A_{1 / π}` generated by the first `J_oneOverPi m`
certified canonical blocks. -/
noncomputable def certifiedAOneOverPiSubset (m : ℕ) : Finset ℕ :=
  certifiedOddBlocks oneOverPiCF (J_oneOverPi m)

/-- Actual cardinality of the Ramanujan-certified finite subset of `A_{1 / π}`,
using the placeholder certified-prefix function `J_oneOverPi`. -/
noncomputable def certifiedAOneOverPiCard (m : ℕ) : ℕ :=
  certifiedOddBlocksCardAt oneOverPiCF J_oneOverPi m

@[simp] theorem certifiedAOneOverPiCard_apply (m : ℕ) :
    certifiedAOneOverPiCard m =
      (certifiedOddBlocks oneOverPiCF (J_oneOverPi m)).card := rfl

theorem oneOverPiCF_partials_pos :
    ∀ j : ℕ, 0 < oneOverPiCF (j + 1) := by
  have hpos : 0 < oneOverPi := by
    unfold oneOverPi
    exact one_div_pos.mpr Real.pi_pos
  have hirr : IsIrrational oneOverPi := by
    unfold oneOverPi
    simpa [one_div] using isIrrational_of_irrational irrational_pi.inv
  exact (simplePartialQuotient_isSimpleCFExpansion hpos hirr).1

theorem certifiedAOneOverPiCard_eq_card (m : ℕ) :
    certifiedAOneOverPiCard m = (certifiedAOneOverPiSubset m).card := by
  rfl

theorem certifiedAOneOverPiSubset_mem_A
    (hpos : 0 < oneOverPi)
    (hirr : IsIrrational oneOverPi)
    (hcf : IsSimpleCFExpansion oneOverPi oneOverPiCF)
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubset m) :
    x ∈ A oneOverPi := by
  unfold certifiedAOneOverPiSubset at hx
  exact certifiedOddBlocks_subset_A_of_IsSimpleCFExpansion hpos hirr hcf hx

theorem certifiedAOneOverPiSubset_mem_A_from_A_eq
    (hA : A oneOverPi = oddBlockASet oneOverPiCF)
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubset m) :
    x ∈ A oneOverPi := by
  unfold certifiedAOneOverPiSubset at hx
  exact certifiedOddBlocks_subset_A_of_A_eq_oddBlockASet hA hx

theorem certifiedAOneOverPiSubset_le_endpoint_denominator
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubset m) :
    x ≤ continuantDen oneOverPiCF (J_oneOverPi m) := by
  unfold certifiedAOneOverPiSubset at hx
  rw [mem_certifiedOddBlocks_iff] at hx
  rcases hx with ⟨_hx0, j, hj, hxblock⟩
  have hx_endpoint :
      x ≤ continuantDen oneOverPiCF (j + 1) :=
    canonicalOddDenominatorBlock_le_endpoint
      (a := oneOverPiCF) oneOverPiCF_partials_pos hxblock
  have hmono :
      continuantDen oneOverPiCF (j + 1) ≤
        continuantDen oneOverPiCF (J_oneOverPi m) :=
    continuantDen_mono_of_partials_pos_le
      oneOverPiCF oneOverPiCF_partials_pos (by omega)
  exact hx_endpoint.trans hmono

theorem certifiedAOneOverPiSubset_bound_of_endpoint_denominator_le_exp
    {m x : ℕ} {Λ : ℝ}
    (hden :
      (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)))
    (hx : x ∈ certifiedAOneOverPiSubset m) :
    (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  have hxden_nat := certifiedAOneOverPiSubset_le_endpoint_denominator hx
  have hxden_real :
      (x : ℝ) ≤
        (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) := by
    exact_mod_cast hxden_nat
  exact hxden_real.trans hden

noncomputable def certifiedAOneOverPiSubsetBelowExp
    (m : ℕ) (Λ : ℝ) : Finset ℕ := by
  classical
  exact (certifiedAOneOverPiSubset m).filter
    (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))

@[simp] theorem mem_certifiedAOneOverPiSubsetBelowExp_iff
    {m x : ℕ} {Λ : ℝ} :
    x ∈ certifiedAOneOverPiSubsetBelowExp m Λ ↔
      x ∈ certifiedAOneOverPiSubset m ∧
        (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  classical
  unfold certifiedAOneOverPiSubsetBelowExp
  simp

theorem certifiedAOneOverPiSubsetBelowExp_eq_self_of_endpoint_denominator_le_exp
    {m : ℕ} {Λ : ℝ}
    (hden :
      (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ))) :
    certifiedAOneOverPiSubsetBelowExp m Λ = certifiedAOneOverPiSubset m := by
  classical
  ext x
  rw [mem_certifiedAOneOverPiSubsetBelowExp_iff]
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx,
      certifiedAOneOverPiSubset_bound_of_endpoint_denominator_le_exp hden hx⟩

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_card_lower_and_endpoint_bound
    {ρ Λ : ℝ}
    (hcard : EventuallyLinearLowerBound certifiedAOneOverPiCard ρ)
    (hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExp m Λ).card : ℝ) := by
  unfold EventuallyLinearLowerBound at hcard
  filter_upwards [hcard, hden] with m hcardm hdenm
  rw [certifiedAOneOverPiSubsetBelowExp_eq_self_of_endpoint_denominator_le_exp hdenm]
  simpa [certifiedAOneOverPiCard_eq_card] using hcardm

/-- Any eventual lower bound for the certified CF-prefix length of `1 / π`
transfers, with a factor `1/2`, to `B_oneOverPi`. -/
theorem eventually_nat_lower_B_oneOverPi_of_nat_lower_J_oneOverPi
    {g : ℕ → ℕ}
    (hJ : ∀ᶠ m : ℕ in atTop, g m ≤ J_oneOverPi m) :
    ∀ᶠ m : ℕ in atTop, g m / 2 ≤ B_oneOverPi m := by
  simpa [B_oneOverPi] using
    eventually_nat_lower_certifiedBlockCountAt_of_nat_lower_Jcert
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      (Jcert := J_oneOverPi)
      (g := g)
      hJ

/-- Real linear production transfer for `1 / π`. -/
theorem eventuallyLinearLowerBound_B_oneOverPi_of_J_oneOverPi
    {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound J_oneOverPi c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      (Jcert := J_oneOverPi)
      (c := c) (c' := c') hJ hc'

/-- Logarithmic production transfer for `1 / π`. -/
theorem eventuallyLogLowerBound_B_oneOverPi_of_J_oneOverPi
    {c c' : ℝ}
    (hJ : EventuallyLogLowerBound J_oneOverPi c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      (Jcert := J_oneOverPi)
      (c := c) (c' := c') hJ hc'

/-- Exact finite lower bound for the actual extracted certified subset. -/
theorem certifiedAOneOverPiCard_ge_half_J_sub_one (m : ℕ) :
    J_oneOverPi m / 2 - 1 ≤ certifiedAOneOverPiCard m := by
  unfold certifiedAOneOverPiCard certifiedOddBlocksCardAt
  exact half_prefix_sub_one_le_certifiedOddBlocks_card_of_partials_pos
    (a := oneOverPiCF) oneOverPiCF_partials_pos (J_oneOverPi m)

/-- Linear transfer specialized to the actual extracted set cardinality. -/
theorem eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_J
    {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound J_oneOverPi c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_Jcert
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Jcert := J_oneOverPi) hJ hc'

/-- Logarithmic transfer specialized to the actual extracted set cardinality. -/
theorem eventuallyLogLowerBound_certifiedAOneOverPiCard_of_J
    {c c' : ℝ}
    (hJ : EventuallyLogLowerBound J_oneOverPi c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Jcert := J_oneOverPi) hJ hc'

/-- Once `oneOverPiCF` is known to be a simple CF expansion of `1 / π`, every
certified finite subset is contained in `A (1 / π)`. -/
theorem certifiedAOneOverPiSubset_subset_A
    (hpos : 0 < oneOverPi)
    (hirr : IsIrrational oneOverPi)
    (hcf : IsSimpleCFExpansion oneOverPi oneOverPiCF)
    (m : ℕ) :
    ↑(certifiedAOneOverPiSubset m) ⊆ A oneOverPi := by
  unfold certifiedAOneOverPiSubset
  exact certifiedOddBlocks_subset_A_of_IsSimpleCFExpansion hpos hirr hcf

/-- Same finite-subset theorem with the project's `A = oddBlockASet` bridge
supplied directly. -/
theorem certifiedAOneOverPiSubset_subset_A_from_A_eq
    (hA : A oneOverPi = oddBlockASet oneOverPiCF)
    (m : ℕ) :
    ↑(certifiedAOneOverPiSubset m) ⊆ A oneOverPi := by
  unfold certifiedAOneOverPiSubset
  exact certifiedOddBlocks_subset_A_of_A_eq_oddBlockASet hA

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanAnalyticInterface.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Analytic interface for Ramanujan-certified subsequences

This file is intentionally abstract.  The future analytic work should prove a
`CertifiedPrefixCriterion` from the Ramanujan interval width and the continued-
fraction cylinder-boundary estimate.  Once that criterion is available,
everything below is pure order/asymptotic bookkeeping.
-/

/-- Abstract denominator-log boundary criterion for certified
continued-fraction prefixes.

`Qlog n` should be read as a nonnegative logarithmic size of a continued-
fraction principal denominator, typically `log q_n`.  The criterion says that,
eventually in the Ramanujan truncation parameter `m`, any index `n` satisfying

`C0 + 2 * Qlog (n + shift) ≤ kappa * m`

is certified by the interval computation, so `n ≤ Jcert m`.  The constants and
the shift are abstract because the precise cylinder-boundary lemma may use
`q_{n+1}`, `q_{n+2}`, or a nearby denominator. -/
def CertifiedPrefixCriterion
    (Qlog : ℕ → ℝ) (Jcert : ℕ → ℕ)
    (kappa C0 : ℝ) (shift : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ n : ℕ,
    C0 + 2 * Qlog (n + shift) ≤ kappa * (m : ℝ) → n ≤ Jcert m

/-- A trial lower-bound function `g` is admissible if the same boundary
inequality holds at `n = g m` eventually. -/
def EventuallyPrefixAdmissible
    (Qlog : ℕ → ℝ) (kappa C0 : ℝ) (shift : ℕ)
    (g : ℕ → ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    C0 + 2 * Qlog (g m + shift) ≤ kappa * (m : ℝ)

/-- Prefix criterion plus an admissible trial function gives the corresponding
natural-number lower bound for the certified prefix length. -/
theorem eventually_nat_lower_Jcert_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g) :
    ∀ᶠ m : ℕ in atTop, g m ≤ Jcert m := by
  unfold CertifiedPrefixCriterion EventuallyPrefixAdmissible at *
  filter_upwards [hcrit, hadm] with m hcrit_m hadm_m
  exact hcrit_m (g m) hadm_m

/-- Prefix criterion plus admissibility transfers immediately to the certified
nonempty block count. -/
theorem eventually_nat_lower_certifiedBlockCountAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g) :
    ∀ᶠ m : ℕ in atTop, g m / 2 ≤ certifiedBlockCountAt a Jcert m :=
  eventually_nat_lower_certifiedBlockCountAt_of_nat_lower_Jcert
    (a := a) hpos
    (Jcert := Jcert) (g := g)
    (eventually_nat_lower_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hadm)

/-- Prefix criterion plus admissibility gives a real linear lower bound for
`Jcert`, provided the trial has that real linear lower bound. -/
theorem eventuallyLinearLowerBound_Jcert_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLinearLowerBound g c) :
    EventuallyLinearLowerBound Jcert c := by
  unfold EventuallyLinearLowerBound at *
  filter_upwards
    [eventually_nat_lower_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (Jcert := Jcert) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm,
     hg] with m hgm hglin
  exact le_trans hglin (by exact_mod_cast hgm)

/-- Prefix criterion plus admissibility gives a real logarithmic lower bound
for `Jcert`, provided the trial has that real logarithmic lower bound. -/
theorem eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLogLowerBound g c) :
    EventuallyLogLowerBound Jcert c := by
  unfold EventuallyLogLowerBound at *
  filter_upwards
    [eventually_nat_lower_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (Jcert := Jcert) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm,
     hg] with m hgm hglog
  exact le_trans hglog (by exact_mod_cast hgm)

/-- Linear lower production for the certified prefix transfers, through the
finite canonical-block layer, to the certified nonempty block count. -/
theorem eventuallyLinearLowerBound_certifiedBlockCountAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLinearLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedBlockCountAt a Jcert) c' :=
  eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLinearLowerBound_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (g := g) (kappa := kappa) (C0 := C0)
      (shift := shift) hcrit hadm hg)
    hc'

/-- Logarithmic lower production for the certified prefix transfers, through
the finite canonical-block layer, to the certified nonempty block count. -/
theorem eventuallyLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLogLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c' :=
  eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (g := g) (kappa := kappa) (C0 := C0)
      (shift := shift) hcrit hadm hg)
    hc'

/-! ## Reducing admissibility to denominator-growth upper bounds -/

/-- A global linear upper bound for the denominator-log model.  This is
stronger than an eventual bound, but convenient as a first formal interface. -/
def GlobalLinearQlogUpperBound (Qlog : ℕ → ℝ) (L C : ℝ) : Prop :=
  ∀ n : ℕ, Qlog n ≤ L * (n : ℝ) + C

/-- A global exponential upper bound for the denominator-log model, in exponent
form.  This is the interface for logarithmic-prefix theorems. -/
def GlobalExpQlogUpperBound (Qlog : ℕ → ℝ) (rho C : ℝ) : Prop :=
  ∀ n : ℕ, Qlog n ≤ Real.exp (rho * (n : ℝ) + C)

/-- If `Qlog` has a global linear upper bound, admissibility follows from the
corresponding elementary affine inequality for the chosen trial function. -/
theorem eventuallyPrefixAdmissible_of_globalLinearQlogUpperBound_aux
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 L C : ℝ} {shift : ℕ}
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hineq : ∀ᶠ m : ℕ in atTop,
      C0 + 2 * (L * ((g m + shift : ℕ) : ℝ) + C) ≤ kappa * (m : ℝ)) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  unfold EventuallyPrefixAdmissible at *
  filter_upwards [hineq] with m hm
  have hQm : Qlog (g m + shift) ≤
      L * ((g m + shift : ℕ) : ℝ) + C := hQ (g m + shift)
  nlinarith

/-- If `Qlog` has a global exponential upper bound, admissibility follows from
the corresponding elementary exponential inequality for the chosen trial. -/
theorem eventuallyPrefixAdmissible_of_globalExpQlogUpperBound_aux
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 rho C : ℝ} {shift : ℕ}
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hineq : ∀ᶠ m : ℕ in atTop,
      C0 + 2 * Real.exp (rho * ((g m + shift : ℕ) : ℝ) + C) ≤
        kappa * (m : ℝ)) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  unfold EventuallyPrefixAdmissible at *
  filter_upwards [hineq] with m hm
  have hQm : Qlog (g m + shift) ≤
      Real.exp (rho * ((g m + shift : ℕ) : ℝ) + C) := hQ (g m + shift)
  nlinarith

/-! ## One-over-pi block-count wrappers -/

/-- Natural-number transfer to the formal `B_oneOverPi` block count from an
abstract prefix criterion and an admissible trial. -/
theorem eventually_nat_lower_B_oneOverPi_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g) :
    ∀ᶠ m : ℕ in atTop, g m / 2 ≤ B_oneOverPi m := by
  simpa [B_oneOverPi] using
    eventually_nat_lower_certifiedBlockCountAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hadm

/-- Linear lower bound for `B_oneOverPi` from an abstract prefix criterion and
a linearly growing admissible trial. -/
theorem eventuallyLinearLowerBound_B_oneOverPi_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLinearLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLinearLowerBound_certifiedBlockCountAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift)
      (c := c) (c' := c') hcrit hadm hg hc'

/-- Logarithmic lower bound for `B_oneOverPi` from an abstract prefix criterion
and a logarithmically growing admissible trial. -/
theorem eventuallyLogLowerBound_B_oneOverPi_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLogLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift)
      (c := c) (c' := c') hcrit hadm hg hc'

/-! ## Actual extracted-set cardinality wrappers -/

/-- Natural-number transfer to the cardinality of the actual extracted finite
set. -/
theorem eventually_nat_lower_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g) :
    ∀ᶠ m : ℕ in atTop,
      g m / 2 - 1 ≤ certifiedOddBlocksCardAt a Jcert m :=
  eventually_nat_lower_certifiedOddBlocksCardAt_of_nat_lower_Jcert
    (a := a) hpos (Jcert := Jcert) (g := g)
    (eventually_nat_lower_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (Jcert := Jcert) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm)

/-- Linear lower bound for the cardinality of the actual extracted finite
set. -/
theorem eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLinearLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedOddBlocksCardAt a Jcert) c' :=
  eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLinearLowerBound_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (Jcert := Jcert) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm hg)
    hc'

/-- Logarithmic lower bound for the cardinality of the actual extracted finite
set. -/
theorem eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLogLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedOddBlocksCardAt a Jcert) c' :=
  eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
      (Qlog := Qlog) (Jcert := Jcert) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm hg)
    hc'

/-- Natural-number cardinality transfer specialized to `1 / π`. -/
theorem eventually_nat_lower_certifiedAOneOverPiCard_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g) :
    ∀ᶠ m : ℕ in atTop, g m / 2 - 1 ≤ certifiedAOneOverPiCard m := by
  simpa [certifiedAOneOverPiCard] using
    eventually_nat_lower_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift) hcrit hadm

/-- Linear cardinality transfer specialized to `1 / π`. -/
theorem eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLinearLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift)
      (c := c) (c' := c') hcrit hadm hg hc'

/-- Logarithmic cardinality transfer specialized to `1 / π`. -/
theorem eventuallyLogLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_of_admissible
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift g)
    (hg : EventuallyLogLowerBound g c)
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (g := g)
      (kappa := kappa) (C0 := C0) (shift := shift)
      (c := c) (c' := c') hcrit hadm hg hc'

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanGrowthCorollaries.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Growth corollaries for Ramanujan-certified extraction

This file turns the abstract prefix criterion into explicit linear-rate lower
bounds under a linear upper bound for the denominator-log model `Qlog`.

The key point is elementary: a trial index `g(m)` with slope at most `s`, a
denominator-log bound `Qlog n ≤ L*n + C`, and the strict slope inequality
`2*L*s < kappa` imply that `g` is admissible for the prefix criterion.
-/

/-- Eventually `(g m : ℝ) ≤ s*m + A`.  This is the upper-growth side of a
linear trial. -/
def EventuallyAffineUpperBound (g : ℕ → ℕ) (s A : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, (g m : ℝ) ≤ s * (m : ℝ) + A

/-- A positive multiple of `m` eventually dominates any real constant. -/
lemma eventually_const_le_pos_mul_natCast
    {A δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, A ≤ δ * (m : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (A / δ)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hm' : A / δ < (m : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hm)
  have hA : A = δ * (A / δ) := by
    field_simp [ne_of_gt hδ]
  calc
    A = δ * (A / δ) := hA
    _ ≤ δ * (m : ℝ) := by
      exact le_of_lt (mul_lt_mul_of_pos_left hm' hδ)

/-- Cast upper estimate for natural division. -/
lemma nat_div_cast_le (n D : ℕ) (hD : 0 < D) :
    ((n / D : ℕ) : ℝ) ≤ (n : ℝ) / (D : ℝ) := by
  have hmul : (n / D) * D ≤ n := Nat.div_mul_le_self n D
  have hmulR : ((n / D : ℕ) : ℝ) * (D : ℝ) ≤ (n : ℝ) := by
    have hmulR0 : (((n / D) * D : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmul
    simpa [Nat.cast_mul] using hmulR0
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  exact (le_div_iff₀ hDpos).mpr hmulR

/-- Cast lower estimate for natural division: `floor(n/D) ≥ n/D - 1`. -/
lemma nat_div_cast_lower (n D : ℕ) (hD : 0 < D) :
    (n : ℝ) / (D : ℝ) - 1 ≤ ((n / D : ℕ) : ℝ) := by
  have hmod : n % D < D := Nat.mod_lt n hD
  have hdecomp : D * (n / D) + n % D = n := Nat.div_add_mod n D
  have hnat : n ≤ D * (n / D + 1) := by
    calc
      n = D * (n / D) + n % D := hdecomp.symm
      _ ≤ D * (n / D) + D := by
        exact Nat.add_le_add_left (Nat.le_of_lt hmod) _
      _ = D * (n / D + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  have hreal : (n : ℝ) ≤ (D : ℝ) * (((n / D : ℕ) : ℝ) + 1) := by
    have hreal0 : (n : ℝ) ≤ ((D * (n / D + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_mul, Nat.cast_add] using hreal0
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hdiv : (n : ℝ) / (D : ℝ) ≤ ((n / D : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hDpos]
    nlinarith
  nlinarith

/-- Rational linear trial `m ↦ floor(K*m/D)`. -/
def rationalLinearTrial (K D : ℕ) : ℕ → ℕ :=
  fun m => (K * m) / D

/-- The rational linear trial is eventually linearly lower-bounded by every
fixed value strictly below `K/D`. -/
theorem eventuallyLinearLowerBound_rationalLinearTrial
    {K D : ℕ} (hD : 0 < D) {c : ℝ}
    (hc : c < (K : ℝ) / (D : ℝ)) :
    EventuallyLinearLowerBound (rationalLinearTrial K D) c := by
  unfold EventuallyLinearLowerBound rationalLinearTrial
  have hδ : 0 < (K : ℝ) / (D : ℝ) - c := by linarith
  filter_upwards [eventually_const_le_pos_mul_natCast (A := 1) hδ] with m hm
  have hfloor : ((K * m : ℕ) : ℝ) / (D : ℝ) - 1 ≤
      (((K * m) / D : ℕ) : ℝ) := nat_div_cast_lower (K * m) D hD
  have hmul : ((K * m : ℕ) : ℝ) / (D : ℝ) =
      ((K : ℝ) / (D : ℝ)) * (m : ℝ) := by
    have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
    rw [Nat.cast_mul]
    field_simp [hDne]
  nlinarith

/-- The rational linear trial has upper slope `K/D`, with no additive error. -/
theorem eventuallyAffineUpperBound_rationalLinearTrial
    {K D : ℕ} (hD : 0 < D) :
    EventuallyAffineUpperBound (rationalLinearTrial K D)
      ((K : ℝ) / (D : ℝ)) 0 := by
  unfold EventuallyAffineUpperBound rationalLinearTrial
  filter_upwards with m
  have hfloor : ((((K * m) / D : ℕ) : ℝ)) ≤
      ((K * m : ℕ) : ℝ) / (D : ℝ) := nat_div_cast_le (K * m) D hD
  have hmul : ((K * m : ℕ) : ℝ) / (D : ℝ) =
      ((K : ℝ) / (D : ℝ)) * (m : ℝ) := by
    have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
    rw [Nat.cast_mul]
    field_simp [hDne]
  rw [hmul] at hfloor
  simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor

/-- Linear `Qlog` growth plus an eventually affine upper bound for the trial
implies admissibility, provided the slope is strictly below the boundary slope. -/
theorem eventuallyPrefixAdmissible_of_globalLinearQlogUpperBound_of_affineUpper
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 L C s A : ℝ} {shift : ℕ}
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hg : EventuallyAffineUpperBound g s A)
    (hslope : 2 * L * s < kappa) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  unfold EventuallyPrefixAdmissible EventuallyAffineUpperBound at *
  have hδ : 0 < kappa - 2 * L * s := by linarith
  let M : ℝ := C0 + 2 * (L * (A + (shift : ℝ)) + C)
  filter_upwards [hg, eventually_const_le_pos_mul_natCast (A := M) hδ]
    with m hgm hM
  have hQm : Qlog (g m + shift) ≤
      L * ((g m + shift : ℕ) : ℝ) + C := hQ (g m + shift)
  have hcast : ((g m + shift : ℕ) : ℝ) = (g m : ℝ) + (shift : ℝ) := by
    norm_num
  have hmain : C0 + 2 * Qlog (g m + shift) ≤
      M + 2 * L * s * (m : ℝ) := by
    dsimp [M]
    nlinarith [hQm, hgm, hcast]
  have hfinish : M + 2 * L * s * (m : ℝ) ≤ kappa * (m : ℝ) := by
    nlinarith
  exact le_trans hmain hfinish

/-- Rational-linear specialization of the previous admissibility theorem. -/
theorem eventuallyPrefixAdmissible_rationalLinearTrial_of_globalLinearQlogUpperBound
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 L C : ℝ} {shift : ℕ}
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift (rationalLinearTrial K D) :=
  eventuallyPrefixAdmissible_of_globalLinearQlogUpperBound_of_affineUpper
    (Qlog := Qlog) (g := rationalLinearTrial K D)
    (kappa := kappa) (C0 := C0) (L := L) (C := C)
    (s := (K : ℝ) / (D : ℝ)) (A := 0) (shift := shift)
    hQ hL (eventuallyAffineUpperBound_rationalLinearTrial hD) hslope

/-! ## Consequences for `Jcert` -/

/-- Prefix criterion plus global linear `Qlog` growth gives a linear lower
bound for `Jcert`, using the rational trial `floor(K*m/D)`. -/
theorem eventuallyLinearLowerBound_Jcert_of_prefixCriterion_globalLinearQlog_rationalTrial
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 L C c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ)) :
    EventuallyLinearLowerBound Jcert c :=
  eventuallyLinearLowerBound_Jcert_of_prefixCriterion_of_admissible
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalLinearTrial K D)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit
    (eventuallyPrefixAdmissible_rationalLinearTrial_of_globalLinearQlogUpperBound
      (Qlog := Qlog) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (L := L) (C := C) (shift := shift)
      hD hQ hL hslope)
    (eventuallyLinearLowerBound_rationalLinearTrial hD hc)

/-! ## Consequences for canonical block count and extracted-set cardinality -/

/-- Linear lower bound for certified nonempty block count from global linear
`Qlog` growth and a rational admissible slope. -/
theorem eventuallyLinearLowerBound_certifiedBlockCountAt_of_prefixCriterion_globalLinearQlog_rationalTrial
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 L C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedBlockCountAt a Jcert) c' :=
  eventuallyLinearLowerBound_certifiedBlockCountAt_of_prefixCriterion_of_admissible
    (a := a) hpos
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalLinearTrial K D)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit
    (eventuallyPrefixAdmissible_rationalLinearTrial_of_globalLinearQlogUpperBound
      (Qlog := Qlog) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (L := L) (C := C) (shift := shift)
      hD hQ hL hslope)
    (eventuallyLinearLowerBound_rationalLinearTrial hD hc)
    hc'

/-- Linear lower bound for the cardinality of the actual extracted finite set
from global linear `Qlog` growth and a rational admissible slope. -/
theorem eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_globalLinearQlog_rationalTrial
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 L C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedOddBlocksCardAt a Jcert) c' :=
  eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_of_admissible
    (a := a) hpos
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalLinearTrial K D)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit
    (eventuallyPrefixAdmissible_rationalLinearTrial_of_globalLinearQlogUpperBound
      (Qlog := Qlog) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (L := L) (C := C) (shift := shift)
      hD hQ hL hslope)
    (eventuallyLinearLowerBound_rationalLinearTrial hD hc)
    hc'

/-! ## `1 / π` wrappers -/

/-- Linear lower bound for `J_oneOverPi` from a future prefix criterion and a
linear `Qlog` upper bound. -/
theorem eventuallyLinearLowerBound_J_oneOverPi_of_prefixCriterion_globalLinearQlog_rationalTrial
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 L C c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ)) :
    EventuallyLinearLowerBound J_oneOverPi c :=
  eventuallyLinearLowerBound_Jcert_of_prefixCriterion_globalLinearQlog_rationalTrial
    (Qlog := Qlog) (Jcert := J_oneOverPi) (K := K) (D := D)
    (kappa := kappa) (C0 := C0) (L := L) (C := C)
    (c := c) (shift := shift)
    hcrit hD hQ hL hslope hc

/-- Linear lower bound for `B_oneOverPi` from a future prefix criterion and a
linear `Qlog` upper bound. -/
theorem eventuallyLinearLowerBound_B_oneOverPi_of_prefixCriterion_globalLinearQlog_rationalTrial
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 L C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLinearLowerBound_certifiedBlockCountAt_of_prefixCriterion_globalLinearQlog_rationalTrial
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (L := L) (C := C)
      (c := c) (c' := c') (shift := shift)
      hcrit hD hQ hL hslope hc hc'

/-- Linear lower bound for the actual extracted finite subset cardinality for
`1 / π`, from a future prefix criterion and a linear `Qlog` upper bound. -/
theorem eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_globalLinearQlog_rationalTrial
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 L C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalLinearQlogUpperBound Qlog L C)
    (hL : 0 ≤ L)
    (hslope : 2 * L * ((K : ℝ) / (D : ℝ)) < kappa)
    (hc : c < (K : ℝ) / (D : ℝ))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_globalLinearQlog_rationalTrial
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (L := L) (C := C)
      (c := c) (c' := c') (shift := shift)
      hcrit hD hQ hL hslope hc hc'

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanLogGrowthCorollaries.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Logarithmic growth corollaries

This file packages the formally provable consequence

`Qlog n <= exp(rho*n + C)` plus the abstract certified-prefix criterion
implies logarithmic certified extraction.

The concrete trial is based on `Nat.log 2`, avoiding a real-to-nat floor.
-/

/-- Eventually `(g m : ℝ) ≤ s * log m + A`.
This is the upper-growth side of a logarithmic trial. -/
def EventuallyLogAffineUpperBound (g : ℕ → ℕ) (s A : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, (g m : ℝ) ≤ s * Real.log (m : ℝ) + A

/-- A positive multiple of `log m` eventually dominates any real constant. -/
lemma eventually_const_le_pos_mul_log_natCast
    {A δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, A ≤ δ * Real.log (m : ℝ) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun m : ℕ => δ * Real.log (m : ℝ)) atTop atTop := by
    exact hlog.const_mul_atTop hδ
  exact htend.eventually_ge_atTop A

/-- The logarithmic trial `m |-> floor(K * log_2(m) / D)`, implemented using
natural logarithm base two. Its real logarithmic rate is `(K/D) / log 2`. -/
def rationalNatLogTrial (K D : ℕ) : ℕ → ℕ :=
  fun m => (K * Nat.log 2 m) / D

/-- Upper estimate for `Nat.log 2 m` in terms of real logarithm. -/
lemma natLog_two_cast_le_real_log_div_log_two
    {m : ℕ} (_hm : 1 ≤ m) :
    ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  simpa [Real.log_div_log] using (Real.natLog_le_logb m 2)

/-- Lower estimate for `Nat.log 2 m` in terms of real logarithm. -/
lemma real_log_div_log_two_sub_one_le_natLog_two_cast
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log (m : ℝ) / Real.log 2 - 1 ≤ ((Nat.log 2 m : ℕ) : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := real_log_le_succ_natLog_mul_log_two (m := m) hm
  have hdiv :
      Real.log (m : ℝ) / Real.log 2 ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) := by
    exact (div_le_iff₀ hlog2).mpr h
  have hsucc :
      ((Nat.log 2 m + 1 : ℕ) : ℝ) =
        ((Nat.log 2 m : ℕ) : ℝ) + 1 := by
    norm_num
  nlinarith [hdiv, hsucc]

/-- The rational `Nat.log 2` trial has logarithmic upper slope
`(K/D)/log 2`, with zero additive error, eventually. -/
theorem eventuallyLogAffineUpperBound_rationalNatLogTrial
    {K D : ℕ} (hD : 0 < D) :
    EventuallyLogAffineUpperBound (rationalNatLogTrial K D)
      (((K : ℝ) / (D : ℝ)) / Real.log 2) 0 := by
  unfold EventuallyLogAffineUpperBound rationalNatLogTrial
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hfloor : (((K * Nat.log 2 m) / D : ℕ) : ℝ) ≤
      ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) :=
    nat_div_cast_le (K * Nat.log 2 m) D hD
  have hlog : ((Nat.log 2 m : ℕ) : ℝ) ≤
      Real.log (m : ℝ) / Real.log 2 :=
    natLog_two_cast_le_real_log_div_log_two (m := m) hm
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hKnonneg : 0 ≤ (K : ℝ) / (D : ℝ) := by positivity
  calc
    (((K * Nat.log 2 m) / D : ℕ) : ℝ)
        ≤ ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) := hfloor
    _ = ((K : ℝ) / (D : ℝ)) * ((Nat.log 2 m : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        field_simp [hDne]
    _ ≤ ((K : ℝ) / (D : ℝ)) * (Real.log (m : ℝ) / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hlog hKnonneg
    _ = (((K : ℝ) / (D : ℝ)) / Real.log 2) * Real.log (m : ℝ) + 0 := by
        ring

/-- The rational `Nat.log 2` trial is logarithmically lower-bounded by every
fixed value strictly below `(K/D)/log 2`. -/
theorem eventuallyLogLowerBound_rationalNatLogTrial
    {K D : ℕ} (hD : 0 < D) {c : ℝ}
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2)) :
    EventuallyLogLowerBound (rationalNatLogTrial K D) c := by
  unfold EventuallyLogLowerBound rationalNatLogTrial
  let s : ℝ := (((K : ℝ) / (D : ℝ)) / Real.log 2)
  have hs_gap : 0 < s - c := by
    dsimp [s]
    linarith
  let A : ℝ := ((K : ℝ) / (D : ℝ)) + 1
  filter_upwards
    [eventually_ge_atTop 1,
     eventually_const_le_pos_mul_log_natCast (A := A) (δ := s - c) hs_gap]
    with m hm hdom
  have hfloor : ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) - 1 ≤
      (((K * Nat.log 2 m) / D : ℕ) : ℝ) :=
    nat_div_cast_lower (K * Nat.log 2 m) D hD
  have hnatlog_lower :
      Real.log (m : ℝ) / Real.log 2 - 1 ≤
        ((Nat.log 2 m : ℕ) : ℝ) :=
    real_log_div_log_two_sub_one_le_natLog_two_cast (m := m) hm
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hKoverD_nonneg : 0 ≤ (K : ℝ) / (D : ℝ) := by positivity
  have hpre : s * Real.log (m : ℝ) - A ≤
      ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) - 1 := by
    dsimp [s, A]
    have hmul := mul_le_mul_of_nonneg_left hnatlog_lower hKoverD_nonneg
    have hcast : ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) =
        ((K : ℝ) / (D : ℝ)) * ((Nat.log 2 m : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      field_simp [hDne]
    calc
      ((K : ℝ) / (D : ℝ) / Real.log 2) * Real.log (m : ℝ) -
            ((K : ℝ) / (D : ℝ) + 1)
          = ((K : ℝ) / (D : ℝ)) *
              (Real.log (m : ℝ) / Real.log 2 - 1) - 1 := by
            ring
      _ ≤ ((K : ℝ) / (D : ℝ)) * ((Nat.log 2 m : ℕ) : ℝ) - 1 := by
            nlinarith [hmul]
      _ = ((K * Nat.log 2 m : ℕ) : ℝ) / (D : ℝ) - 1 := by
            rw [hcast]
  have htarget : c * Real.log (m : ℝ) ≤ s * Real.log (m : ℝ) - A := by
    dsimp [s] at hdom
    nlinarith
  exact le_trans htarget (le_trans hpre hfloor)

/-! ## A real-analysis domination lemma for exponential-in-log trials -/

private lemma exp_affine_log_div_natCast_tendsto_zero
    {A a : ℝ} (ha : a < 1) :
    Tendsto
      (fun m : ℕ => Real.exp (A + a * Real.log (m : ℝ)) / (m : ℝ))
      atTop (𝓝 0) := by
  have hb : 0 < 1 - a := by linarith
  have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(1 - a))) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
  have hmul :
      Tendsto (fun m : ℕ => Real.exp A * ((m : ℝ) ^ (-(1 - a)))) atTop (𝓝 0) := by
    simpa using hpow.const_mul (Real.exp A)
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hexp :
      Real.exp (A + a * Real.log (m : ℝ)) =
        Real.exp A * ((m : ℝ) ^ a) := by
    rw [Real.exp_add]
    rw [show a * Real.log (m : ℝ) = Real.log (m : ℝ) * a by ring]
    rw [← Real.rpow_def_of_pos hmpos a]
  have hpoweq : (m : ℝ) ^ (-(1 - a)) = (m : ℝ) ^ (a - 1) := by
    ring_nf
  calc
    Real.exp A * ((m : ℝ) ^ (-(1 - a)))
        = Real.exp A * ((m : ℝ) ^ (a - 1)) := by rw [hpoweq]
    _ = Real.exp A * (((m : ℝ) ^ a) / (m : ℝ)) := by
        rw [Real.rpow_sub hmpos a 1]
        rw [Real.rpow_one]
    _ = Real.exp (A + a * Real.log (m : ℝ)) / (m : ℝ) := by
        rw [hexp]
        field_simp [hne]

/-- If `a < 1`, then `C0 + 2*exp(A + a*log m)` is eventually bounded by
`kappa*m` for every positive `kappa`. -/
lemma eventually_const_add_two_exp_affine_log_le_linear
    {A a kappa C0 : ℝ}
    (ha : a < 1) (hkappa : 0 < kappa) :
    ∀ᶠ m : ℕ in atTop,
      C0 + 2 * Real.exp (A + a * Real.log (m : ℝ)) ≤
        kappa * (m : ℝ) := by
  have hratio :
      Tendsto
        (fun m : ℕ =>
          (C0 + 2 * Real.exp (A + a * Real.log (m : ℝ))) / (m : ℝ))
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun m : ℕ => C0 / (m : ℝ)) atTop (𝓝 0) := by
      have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      simpa [div_eq_mul_inv] using hnat.inv_tendsto_atTop.const_mul C0
    have hexp0 := exp_affine_log_div_natCast_tendsto_zero (A := A) (a := a) ha
    have htwo :
        Tendsto
          (fun m : ℕ => 2 * (Real.exp (A + a * Real.log (m : ℝ)) / (m : ℝ)))
          atTop (𝓝 0) := by
      simpa using hexp0.const_mul (2 : ℝ)
    have hsum :
        Tendsto
          (fun m : ℕ =>
            C0 / (m : ℝ) +
              2 * (Real.exp (A + a * Real.log (m : ℝ)) / (m : ℝ)))
          atTop (𝓝 0) := by
      simpa using hinv.add htwo
    refine hsum.congr' ?_
    exact Eventually.of_forall fun m => by
      by_cases hne : (m : ℝ) = 0
      · simp [hne]
      · field_simp [hne]
  have hevent :
      ∀ᶠ m : ℕ in atTop,
        (C0 + 2 * Real.exp (A + a * Real.log (m : ℝ))) / (m : ℝ) ≤ kappa := by
    exact ((tendsto_order.1 hratio).2 _ hkappa).mono fun _ hm => le_of_lt hm
  filter_upwards [hevent, eventually_ge_atTop 1] with m hm hge
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hge)
  have hmul := mul_le_mul_of_nonneg_right hm hmpos.le
  field_simp [ne_of_gt hmpos] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Exponential `Qlog` growth plus an eventually logarithmic upper bound for
the trial implies admissibility, provided the exponential-in-log slope is
strictly sublinear. -/
theorem eventuallyPrefixAdmissible_of_globalExpQlogUpperBound_of_logAffineUpper
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 rho C s A : ℝ} {shift : ℕ}
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hg : EventuallyLogAffineUpperBound g s A)
    (hslope : rho * s < 1) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  unfold EventuallyPrefixAdmissible EventuallyLogAffineUpperBound at *
  let M : ℝ := rho * (A + (shift : ℝ)) + C
  have hdom := eventually_const_add_two_exp_affine_log_le_linear
    (A := M) (a := rho * s) (kappa := kappa) (C0 := C0)
    hslope hkappa
  filter_upwards [hg, hdom] with m hgm hdom_m
  have hQm : Qlog (g m + shift) ≤
      Real.exp (rho * ((g m + shift : ℕ) : ℝ) + C) := hQ (g m + shift)
  have hcast : ((g m + shift : ℕ) : ℝ) = (g m : ℝ) + (shift : ℝ) := by
    norm_num
  have hexp_le :
      Real.exp (rho * ((g m + shift : ℕ) : ℝ) + C) ≤
        Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [M]
    nlinarith [hgm, hcast]
  have hmain : C0 + 2 * Qlog (g m + shift) ≤
      C0 + 2 * Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    nlinarith [hQm, hexp_le]
  exact le_trans hmain hdom_m

/-- Rational-logarithmic specialization of the exponential-growth admissibility
criterion. -/
theorem eventuallyPrefixAdmissible_rationalNatLogTrial_of_globalExpQlogUpperBound
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 rho C : ℝ} {shift : ℕ}
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift (rationalNatLogTrial K D) := by
  exact eventuallyPrefixAdmissible_of_globalExpQlogUpperBound_of_logAffineUpper
    (Qlog := Qlog) (g := rationalNatLogTrial K D)
    (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
    (s := (((K : ℝ) / (D : ℝ)) / Real.log 2)) (A := 0)
    (shift := shift) hQ hrho hkappa
    (eventuallyLogAffineUpperBound_rationalNatLogTrial (K := K) (D := D) hD)
    hslope

/-! ## Consequences for `Jcert` -/

/-- Prefix criterion plus global exponential `Qlog` growth gives a logarithmic
lower bound for `Jcert`, using the rational `Nat.log 2` trial. -/
theorem eventuallyLogLowerBound_Jcert_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 rho C c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2)) :
    EventuallyLogLowerBound Jcert c := by
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalNatLogTrial K D)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit
    (eventuallyPrefixAdmissible_rationalNatLogTrial_of_globalExpQlogUpperBound
      (Qlog := Qlog) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
      (shift := shift) hD hQ hrho hkappa hslope)
    (eventuallyLogLowerBound_rationalNatLogTrial hD hc)

/-! ## Consequences for canonical block count and extracted-set cardinality -/

/-- Exponential `Qlog` growth gives logarithmic lower bound for certified
nonempty block count. -/
theorem eventuallyLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 rho C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c' := by
  exact eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLogLowerBound_Jcert_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
      (Qlog := Qlog) (Jcert := Jcert) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
      (shift := shift) hcrit hD hQ hrho hkappa hslope hc)
    hc'

/-- Exponential `Qlog` growth gives logarithmic lower bound for the actual
certified extracted finite-set cardinality. -/
theorem eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 rho C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound (certifiedOddBlocksCardAt a Jcert) c' := by
  exact eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := c) (c' := c')
    (eventuallyLogLowerBound_Jcert_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
      (Qlog := Qlog) (Jcert := Jcert) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
      (shift := shift) hcrit hD hQ hrho hkappa hslope hc)
    hc'

/-! ## One-over-pi wrappers -/

/-- Exponential `Qlog` growth plus the abstract prefix criterion gives a
logarithmic lower bound for `B_oneOverPi`. -/
theorem eventuallyLogLowerBound_B_oneOverPi_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 rho C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound B_oneOverPi c' := by
  simpa [B_oneOverPi] using
    eventuallyLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
      (shift := shift) hcrit hD hQ hrho hkappa hslope hc hc'

/-- Exponential `Qlog` growth plus the abstract prefix criterion gives a
logarithmic lower bound for the actual certified `A_{1/pi}` finite subset
cardinality. -/
theorem eventuallyLogLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 rho C c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hQ : GlobalExpQlogUpperBound Qlog rho C)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound certifiedAOneOverPiCard c' := by
  simpa [certifiedAOneOverPiCard] using
    eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_globalExpQlog_rationalNatLogTrial
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi) (K := K) (D := D)
      (kappa := kappa) (C0 := C0) (rho := rho) (C := C)
      (shift := shift) hcrit hD hQ hrho hkappa hslope hc hc'

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanDenominatorGrowthBridge.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Denominator-growth bridge for Ramanujan-certified extraction

This file connects continued-fraction denominator growth to the abstract
`Qlog` interface used by the Ramanujan certified-prefix layer.
-/

/-- Logarithm of the `n`-th continuant denominator. -/
noncomputable def continuantQlog (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (continuantDen a n : ℝ)

/-- An eventual exponential upper bound for a denominator-log model, packaged
with the base `R` used by the denominator-ratio exponent. -/
def EventuallyStepQlogUpperBound (Qlog : ℕ → ℝ) (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    Qlog n ≤ Real.exp (Real.log R * (n : ℝ) + C)

private lemma eventuallyExpQlogUpperBound_of_eventuallyStepQlogUpperBound
    {Qlog : ℕ → ℝ} {R : ℝ}
    (hstep : EventuallyStepQlogUpperBound Qlog R) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Qlog n ≤ Real.exp (Real.log R * (n : ℝ) + C) :=
  hstep

theorem tendsto_atTop_of_eventuallyLogLowerBound
    {g : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hg : EventuallyLogLowerBound g c) :
    Tendsto g atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have hlog : Tendsto (fun m : ℕ => c * Real.log (m : ℝ)) atTop atTop := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hevent := (hlog.eventually_ge_atTop (b : ℝ)).and hg
  rw [Filter.eventually_atTop] at hevent
  rcases hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  rcases hN m hm with ⟨hb, hg_m⟩
  exact_mod_cast (le_trans hb hg_m)

private lemma tendsto_add_const_atTop_of_tendsto_atTop
    {g : ℕ → ℕ} (shift : ℕ)
    (hg : Tendsto g atTop atTop) :
    Tendsto (fun m : ℕ => g m + shift) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop] at hg ⊢
  intro b
  rcases hg b with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  exact le_trans (hN m hm) (Nat.le_add_right (g m) shift)

private theorem eventuallyPrefixAdmissible_of_eventuallyExpQlogUpperBound_of_logAffineUpper
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 rho C s A c : ℝ} {shift : ℕ}
    (hQ : ∀ᶠ n : ℕ in atTop,
      Qlog n ≤ Real.exp (rho * (n : ℝ) + C))
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hgUpper : EventuallyLogAffineUpperBound g s A)
    (hgLower : EventuallyLogLowerBound g c)
    (hc : 0 < c)
    (hslope : rho * s < 1) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  unfold EventuallyPrefixAdmissible EventuallyLogAffineUpperBound at *
  have hgTendsto : Tendsto (fun m : ℕ => g m + shift) atTop atTop :=
    tendsto_add_const_atTop_of_tendsto_atTop shift
      (tendsto_atTop_of_eventuallyLogLowerBound hc hgLower)
  let M : ℝ := rho * (A + (shift : ℝ)) + C
  have hdom := eventually_const_add_two_exp_affine_log_le_linear
    (A := M) (a := rho * s) (kappa := kappa) (C0 := C0)
    hslope hkappa
  filter_upwards [hgUpper, hgTendsto.eventually hQ, hdom] with m hgm hQm hdom_m
  have hcast : ((g m + shift : ℕ) : ℝ) = (g m : ℝ) + (shift : ℝ) := by
    norm_num
  have hexp_le :
      Real.exp (rho * ((g m + shift : ℕ) : ℝ) + C) ≤
        Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [M]
    nlinarith [hgm, hcast]
  have hmain : C0 + 2 * Qlog (g m + shift) ≤
      C0 + 2 * Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    nlinarith [hQm, hexp_le]
  exact le_trans hmain hdom_m

/-- Explicit logarithmic extraction from an eventual exponential bound on
`Qlog` with base `R`. -/
theorem eventuallyLogLowerBound_Jcert_of_prefixCriterion_eventuallyStepQlog_rationalNatLogTrial
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 R c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hD : 0 < D)
    (hR : 1 < R)
    (hstep : EventuallyStepQlogUpperBound Qlog R)
    (hkappa : 0 < kappa)
    (hspos : 0 < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hslope : Real.log R * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2)) :
    EventuallyLogLowerBound Jcert c := by
  rcases eventuallyExpQlogUpperBound_of_eventuallyStepQlogUpperBound hstep with ⟨C, hQ⟩
  have hlogR_nonneg : 0 ≤ Real.log R := Real.log_nonneg hR.le
  have htrialLowerPos :
      EventuallyLogLowerBound (rationalNatLogTrial K D)
        ((((K : ℝ) / (D : ℝ)) / Real.log 2) / 2) := by
    exact eventuallyLogLowerBound_rationalNatLogTrial
      (K := K) (D := D) hD (by nlinarith [hspos])
  have htrialUpper :
      EventuallyLogAffineUpperBound (rationalNatLogTrial K D)
        (((K : ℝ) / (D : ℝ)) / Real.log 2) 0 :=
    eventuallyLogAffineUpperBound_rationalNatLogTrial (K := K) (D := D) hD
  have hadm :
      EventuallyPrefixAdmissible Qlog kappa C0 shift
        (rationalNatLogTrial K D) := by
    exact eventuallyPrefixAdmissible_of_eventuallyExpQlogUpperBound_of_logAffineUpper
      (Qlog := Qlog) (g := rationalNatLogTrial K D)
      (kappa := kappa) (C0 := C0) (rho := Real.log R) (C := C)
      (s := (((K : ℝ) / (D : ℝ)) / Real.log 2)) (A := 0)
      (c := (((K : ℝ) / (D : ℝ)) / Real.log 2) / 2)
      (shift := shift) hQ hlogR_nonneg hkappa htrialUpper htrialLowerPos
      (by nlinarith [hspos]) hslope
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalNatLogTrial K D)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit hadm (eventuallyLogLowerBound_rationalNatLogTrial hD hc)

private lemma exp_log_mul_nat_add_log_eq_mul_pow
    {B R : ℝ} (hB : 0 < B) (hR : 0 < R) (n : ℕ) :
    Real.exp (Real.log R * (n : ℝ) + Real.log B) = B * R ^ n := by
  calc
    Real.exp (Real.log R * (n : ℝ) + Real.log B)
        = Real.exp (Real.log B + (n : ℝ) * Real.log R) := by
            ring_nf
    _ = Real.exp (Real.log B) * Real.exp ((n : ℝ) * Real.log R) := by
            rw [Real.exp_add]
    _ = B * R ^ n := by
            rw [Real.exp_log hB]
            rw [Real.exp_nat_mul]
            rw [Real.exp_log hR]

private lemma eventuallyExpQlogUpperBound_of_eventually_step_mul
    {Qlog : ℕ → ℝ} {R : ℝ}
    (hR : 1 < R)
    (hstep : ∀ᶠ n : ℕ in atTop, Qlog (n + 1) ≤ R * Qlog n) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      Qlog n ≤ Real.exp (Real.log R * (n : ℝ) + C) := by
  rw [Filter.eventually_atTop] at hstep
  rcases hstep with ⟨N0, hN0⟩
  let N : ℕ := max N0 1
  let B : ℝ := max 1 (Qlog N)
  have hN0N : N0 ≤ N := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have htail : ∀ k : ℕ, Qlog (N + k) ≤ B * R ^ k := by
    intro k
    induction k with
    | zero =>
        simp [B]
    | succ k ih =>
        have hstep_k : Qlog ((N + k) + 1) ≤ R * Qlog (N + k) :=
          hN0 (N + k) (le_trans hN0N (Nat.le_add_right N k))
        calc
          Qlog (N + (k + 1))
              = Qlog ((N + k) + 1) := by
                  simp [Nat.add_assoc]
          _ ≤ R * Qlog (N + k) := hstep_k
          _ ≤ R * (B * R ^ k) := by
                  exact mul_le_mul_of_nonneg_left ih hRnonneg
          _ = B * R ^ (k + 1) := by
                  rw [pow_succ]
                  ring
  refine ⟨Real.log B, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  let k : ℕ := n - N
  have hNk : N + k = n := Nat.add_sub_of_le hn
  have hkn : k ≤ n := Nat.sub_le n N
  have htail_n : Qlog n ≤ B * R ^ k := by
    simpa [hNk] using htail k
  have hpow_le : R ^ k ≤ R ^ n := pow_le_pow_right₀ hR.le hkn
  have hBR_le : B * R ^ k ≤ B * R ^ n :=
    mul_le_mul_of_nonneg_left hpow_le hBpos.le
  have hexp : Real.exp (Real.log R * (n : ℝ) + Real.log B) = B * R ^ n :=
    exp_log_mul_nat_add_log_eq_mul_pow hBpos hRpos n
  exact htail_n.trans (hBR_le.trans_eq hexp.symm)

/-- A strict denominator-ratio exponent bound gives eventual exponential
growth control for the continuant denominator logarithms. -/
theorem eventuallyStepQlogUpperBound_continuantQlog_of_denominatorRatioExponent_lt
    {a : ℕ → ℕ} {R : ℝ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hR : 1 < R)
    (hbdd :
      IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun n : ℕ =>
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ)))
    (hrho_lt : denominatorRatioExponent a < R) :
    EventuallyStepQlogUpperBound (continuantQlog a) R := by
  have hratio_lt :
      ∀ᶠ n : ℕ in atTop,
        continuantDenLogRatio a n < R :=
    eventually_lt_of_limsup_lt (by
      simpa [denominatorRatioExponent, continuantDenLogRatio] using hrho_lt) hbdd
  have hqR : Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hqgt1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  have hstep_mul : ∀ᶠ n : ℕ in atTop,
      continuantQlog a (n + 1) ≤ R * continuantQlog a n := by
    filter_upwards [hratio_lt, hqgt1] with n hlt hqn_gt1
    have hlogpos : 0 < Real.log (continuantDen a n : ℝ) :=
      Real.log_pos hqn_gt1
    have hle : continuantDenLogRatio a n ≤ R := le_of_lt hlt
    have hmul := mul_le_mul_of_nonneg_right hle hlogpos.le
    have hmul' :
        Real.log (continuantDen a (n + 1) : ℝ) ≤
          R * Real.log (continuantDen a n : ℝ) := by
      rw [continuantDenLogRatio] at hmul
      field_simp [ne_of_gt hlogpos] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [continuantQlog] using hmul'
  exact eventuallyExpQlogUpperBound_of_eventually_step_mul hR hstep_mul

/-- Strict denominator-ratio exponent bound gives explicit logarithmic
certified-prefix production. -/
theorem eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ} {K D : ℕ}
    {kappa C0 R c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion (continuantQlog a) Jcert kappa C0 shift)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hD : 0 < D)
    (hR : 1 < R)
    (hbdd :
      IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun n : ℕ =>
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ)))
    (hrho_lt : denominatorRatioExponent a < R)
    (hkappa : 0 < kappa)
    (hspos : 0 < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hslope : Real.log R * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2)) :
    EventuallyLogLowerBound Jcert c := by
  have hstep : EventuallyStepQlogUpperBound (continuantQlog a) R :=
    eventuallyStepQlogUpperBound_continuantQlog_of_denominatorRatioExponent_lt
      (a := a) (R := R) hpos hR hbdd hrho_lt
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_eventuallyStepQlog_rationalNatLogTrial
    (Qlog := continuantQlog a) (Jcert := Jcert)
    (K := K) (D := D) (kappa := kappa) (C0 := C0)
    (R := R) (c := c) (shift := shift)
    hcrit hD hR hstep hkappa hspos hslope hc

theorem eventuallyLogLowerBound_B_oneOverPi_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
    {K D : ℕ} {kappa C0 R c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hR : 1 < R)
    (hbdd : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun n : ℕ =>
        Real.log (continuantDen oneOverPiCF (n + 1) : ℝ) /
          Real.log (continuantDen oneOverPiCF n : ℝ)))
    (hrho : denominatorRatioExponent oneOverPiCF < R)
    (hkappa : 0 < kappa)
    (hspos : 0 < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hslope : Real.log R * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound B_oneOverPi c' := by
  have hJ :
      EventuallyLogLowerBound J_oneOverPi c :=
    eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
      (a := oneOverPiCF) (Jcert := J_oneOverPi)
      (K := K) (D := D) (kappa := kappa) (C0 := C0)
      (R := R) (c := c) (shift := shift)
      hcrit oneOverPiCF_partials_pos hD hR hbdd hrho hkappa hspos hslope hc
  exact eventuallyLogLowerBound_B_oneOverPi_of_J_oneOverPi hJ hc'

theorem eventuallyLogLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
    {K D : ℕ} {kappa C0 R c c' : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C0 shift)
    (hD : 0 < D)
    (hR : 1 < R)
    (hbdd : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun n : ℕ =>
        Real.log (continuantDen oneOverPiCF (n + 1) : ℝ) /
          Real.log (continuantDen oneOverPiCF n : ℝ)))
    (hrho : denominatorRatioExponent oneOverPiCF < R)
    (hkappa : 0 < kappa)
    (hspos : 0 < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hslope : Real.log R * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1)
    (hc : c < (((K : ℝ) / (D : ℝ)) / Real.log 2))
    (hc' : c' < c / 2) :
    EventuallyLogLowerBound certifiedAOneOverPiCard c' := by
  have hJ :
      EventuallyLogLowerBound J_oneOverPi c :=
    eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
      (a := oneOverPiCF) (Jcert := J_oneOverPi)
      (K := K) (D := D) (kappa := kappa) (C0 := C0)
      (R := R) (c := c) (shift := shift)
      hcrit oneOverPiCF_partials_pos hD hR hbdd hrho hkappa hspos hslope hc
  exact eventuallyLogLowerBound_certifiedAOneOverPiCard_of_J hJ hc'

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanCriticalRatioCorollaries.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Critical denominator-ratio corollaries

This file proves the clean conditional consequence of the critical denominator
log-ratio condition `denominatorRatioExponent a = 1`.

Under the abstract certified-prefix criterion, this gives super-logarithmic
certified production in the weak sense that every fixed multiple of `log m` is
eventually dominated.
-/

/-- A natural-valued function eventually dominates every positive multiple of
`log m`. -/
def EventuallySuperLogLowerBound (f : ℕ → ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → EventuallyLogLowerBound f c

/-! ## Small Archimedean helpers -/

/-- Choose a natural rational `K/D` strictly larger than a real number. -/
lemma exists_nat_ratio_gt (x : ℝ) :
    ∃ K D : ℕ, 0 < D ∧ x < (K : ℝ) / (D : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_gt x
  refine ⟨K, 1, by norm_num, ?_⟩
  simpa using hK

/-- For any positive trial slope `s`, choose `R > 1` so that
`log R * s < 1`. -/
lemma exists_R_gt_one_log_mul_lt_one {s : ℝ} (hs : 0 < s) :
    ∃ R : ℝ, 1 < R ∧ Real.log R * s < 1 := by
  refine ⟨Real.exp (1 / (2 * s)), ?_, ?_⟩
  · have hpos : 0 < 1 / (2 * s) := by positivity
    simpa using
      (Real.exp_lt_exp.mpr hpos : Real.exp 0 < Real.exp (1 / (2 * s)))
  · rw [Real.log_exp]
    have hsne : s ≠ 0 := ne_of_gt hs
    have htwos : 2 * s ≠ 0 := by positivity
    field_simp [hsne, htwos]
    nlinarith [hs]

/-- If `K/D > c log 2`, then `(K/D)/log 2 > c`. -/
lemma lt_div_log_two_of_mul_log_two_lt
    {K D : ℕ} {c : ℝ}
    (_hD : 0 < D)
    (hKD : c * Real.log 2 < (K : ℝ) / (D : ℝ)) :
    c < (((K : ℝ) / (D : ℝ)) / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := div_lt_div_of_pos_right hKD hlog2
  calc
    c = (c * Real.log 2) / Real.log 2 := by
      field_simp [ne_of_gt hlog2]
    _ < ((K : ℝ) / (D : ℝ)) / Real.log 2 := h

/-- Positivity of the rational log trial slope selected above. -/
lemma rational_log_trial_slope_pos_of_gt_pos
    {K D : ℕ} {x : ℝ}
    (_hD : 0 < D)
    (hx : 0 < x)
    (hKD : x < (K : ℝ) / (D : ℝ)) :
    0 < (((K : ℝ) / (D : ℝ)) / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (lt_trans hx hKD) hlog2

/-! ## Critical ratio gives arbitrary logarithmic prefix production -/

/-- Generic critical-ratio theorem for certified prefix length.

If the denominator log-ratio exponent is exactly `1`, then for every positive
constant `c`, the certified prefix function `Jcert` eventually dominates
`c * log m`, provided the abstract certified-prefix criterion is available. -/
theorem eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ}
    {kappa C0 c : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion (continuantQlog a) Jcert kappa C0 shift)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hrho : denominatorRatioExponent a = 1)
    (hkappa : 0 < kappa)
    (hc : 0 < c) :
    EventuallyLogLowerBound Jcert c := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases exists_nat_ratio_gt (c * Real.log 2) with ⟨K, D, hD, hKD⟩
  let s : ℝ := (((K : ℝ) / (D : ℝ)) / Real.log 2)
  have hc_lt_s : c < s := by
    dsimp [s]
    exact lt_div_log_two_of_mul_log_two_lt (K := K) (D := D) (c := c) hD hKD
  have hs_pos : 0 < s := by
    dsimp [s]
    exact rational_log_trial_slope_pos_of_gt_pos
      (K := K) (D := D) (x := c * Real.log 2)
      hD (mul_pos hc hlog2) hKD
  rcases exists_R_gt_one_log_mul_lt_one hs_pos with ⟨R, hR, hslopeR⟩
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun n : ℕ =>
        Real.log (continuantDen a (n + 1) : ℝ) /
          Real.log (continuantDen a n : ℝ)) :=
    denominatorRatioExponent_eq_one_isBoundedUnder (a := a) hrho
  have hrho_lt : denominatorRatioExponent a < R := by
    rw [hrho]
    exact hR
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_lt_rationalNatLogTrial
    (a := a) (Jcert := Jcert)
    (K := K) (D := D)
    (kappa := kappa) (C0 := C0) (R := R)
    (c := c) (shift := shift)
    hcrit hpos hD hR hbdd hrho_lt hkappa hs_pos
    (by simpa [s] using hslopeR) hc_lt_s

/-- Super-logarithmic prefix production in predicate form. -/
theorem eventuallySuperLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion (continuantQlog a) Jcert kappa C0 shift)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hrho : denominatorRatioExponent a = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound Jcert := by
  intro c hc
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
    (a := a) (Jcert := Jcert)
    (kappa := kappa) (C0 := C0) (c := c) (shift := shift)
    hcrit hpos hrho hkappa hc

/-! ## Transfer to block count and actual extracted cardinality -/

/-- Critical ratio gives super-logarithmic certified nonempty block production. -/
theorem eventuallySuperLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion (continuantQlog a) Jcert kappa C0 shift)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hrho : denominatorRatioExponent a = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound (certifiedBlockCountAt a Jcert) := by
  intro c hc
  have hJ : EventuallyLogLowerBound Jcert (3 * c) :=
    eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
      (a := a) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (c := 3 * c) (shift := shift)
      hcrit hpos hrho hkappa (by positivity)
  exact eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := 3 * c) (c' := c) hJ (by nlinarith)

/-- Critical ratio gives super-logarithmic actual certified extracted-cardinality
production. -/
theorem eventuallySuperLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion (continuantQlog a) Jcert kappa C0 shift)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hrho : denominatorRatioExponent a = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound (certifiedOddBlocksCardAt a Jcert) := by
  intro c hc
  have hJ : EventuallyLogLowerBound Jcert (3 * c) :=
    eventuallyLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
      (a := a) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (c := 3 * c) (shift := shift)
      hcrit hpos hrho hkappa (by positivity)
  exact eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := 3 * c) (c' := c) hJ (by nlinarith)

/-! ## One-over-pi wrappers -/

/-- Critical denominator-ratio condition for `oneOverPiCF` gives
super-logarithmic certified prefix production for `J_oneOverPi`. -/
theorem eventuallySuperLogLowerBound_J_oneOverPi_of_prefixCriterion_denominatorRatioExponent_eq_one
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C0 shift)
    (hrho : denominatorRatioExponent oneOverPiCF = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound J_oneOverPi :=
  eventuallySuperLogLowerBound_Jcert_of_prefixCriterion_denominatorRatioExponent_eq_one
    (a := oneOverPiCF) (Jcert := J_oneOverPi)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit oneOverPiCF_partials_pos hrho hkappa

/-- Critical denominator-ratio condition for `oneOverPiCF` gives
super-logarithmic production for the informal block count `B_oneOverPi`. -/
theorem eventuallySuperLogLowerBound_B_oneOverPi_of_prefixCriterion_denominatorRatioExponent_eq_one
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C0 shift)
    (hrho : denominatorRatioExponent oneOverPiCF = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound B_oneOverPi := by
  simpa [B_oneOverPi] using
    eventuallySuperLogLowerBound_certifiedBlockCountAt_of_prefixCriterion_denominatorRatioExponent_eq_one
      (a := oneOverPiCF) (Jcert := J_oneOverPi)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit oneOverPiCF_partials_pos hrho hkappa

/-- Critical denominator-ratio condition for `oneOverPiCF` gives
super-logarithmic production for the actual finite certified subset of
`A_{1/pi}`. -/
theorem eventuallySuperLogLowerBound_certifiedAOneOverPiCard_of_prefixCriterion_denominatorRatioExponent_eq_one
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C0 shift)
    (hrho : denominatorRatioExponent oneOverPiCF = 1)
    (hkappa : 0 < kappa) :
    EventuallySuperLogLowerBound certifiedAOneOverPiCard := by
  simpa [certifiedAOneOverPiCard] using
    eventuallySuperLogLowerBound_certifiedOddBlocksCardAt_of_prefixCriterion_denominatorRatioExponent_eq_one
      (a := oneOverPiCF) (Jcert := J_oneOverPi)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit oneOverPiCF_partials_pos hrho hkappa

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanReverseEquivalence.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Reverse certified-prefix interface

This file records the converse abstraction for Ramanujan-certified continued
fraction prefixes.  The forward files say that upper bounds for denominator
logs force certified-prefix lower bounds.  Here we isolate the reverse analytic
criterion saying that certifying `n` coefficients forces the relevant continued
fraction cylinder to fit inside the Ramanujan interval.

The pi-specific interval/cylinder theorem is not asserted here; it should later
instantiate `CertifiedPrefixReverseCriterion`.
-/

/-- Reverse certified-prefix criterion.

Interpretation: once `m` is large, if the `m`-th certificate reaches prefix
length `n`, then the corresponding denominator logarithm is at most the
Ramanujan precision scale.  The `shift` belongs to the denominator-log model,
matching the forward `CertifiedPrefixCriterion` interface. -/
def CertifiedPrefixReverseCriterion
    (Qlog : ℕ → ℝ) (Jcert : ℕ → ℕ)
    (kappa C : ℝ) (shift : ℕ) : Prop :=
  ∃ M : ℕ, ∀ m n : ℕ,
    M ≤ m → n ≤ Jcert m →
      2 * Qlog (n + shift) ≤ kappa * (m : ℝ) + C

/-- Eventually `J m ≥ (K/D) m`, written without real floors. -/
def EventuallyRationalLinearLowerBound
    (J : ℕ → ℕ) (K D : ℕ) : Prop :=
  0 < K ∧ 0 < D ∧
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → K * m ≤ D * J m

/-- Eventually `Qlog n ≤ L*n + O(1)`. -/
def EventuallyRealAffineUpperBound (Qlog : ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, Qlog n ≤ L * (n : ℝ) + A

/-- Eventually `Qlog n ≤ exp(rho*n + O(1))`. -/
def EventuallyRealExpUpperBound (Qlog : ℕ → ℝ) (rho : ℝ) : Prop :=
  ∃ A : ℝ, ∀ᶠ n : ℕ in atTop, Qlog n ≤ Real.exp (rho * (n : ℝ) + A)

/-- `Qlog` has subexponential growth in the coefficient index. -/
def EventuallySubexponentialUpperBound (Qlog : ℕ → ℝ) : Prop :=
  ∀ rho : ℝ, 0 < rho → EventuallyRealExpUpperBound Qlog rho

/-! ## Shift-removal helpers -/

/-- If a shifted sequence has an affine upper bound, then the original sequence
has the same eventual affine upper slope. -/
theorem eventuallyRealAffineUpperBound_of_shifted
    {Qlog : ℕ → ℝ} {L : ℝ} {shift : ℕ}
    (hL : 0 ≤ L)
    (h : EventuallyRealAffineUpperBound (fun n : ℕ => Qlog (n + shift)) L) :
    EventuallyRealAffineUpperBound Qlog L := by
  rcases h with ⟨A, hA⟩
  rw [eventually_atTop] at hA
  rcases hA with ⟨N, hN⟩
  refine ⟨A, ?_⟩
  rw [eventually_atTop]
  refine ⟨N + shift, ?_⟩
  intro n hn
  let t : ℕ := n - shift
  have htN : N ≤ t := by
    dsimp [t]
    omega
  have htadd : t + shift = n := by
    dsimp [t]
    exact Nat.sub_add_cancel (by omega : shift ≤ n)
  have ht_le_n : (t : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.sub_le n shift)
  have hbound : Qlog (t + shift) ≤ L * (t : ℝ) + A := hN t htN
  have hmono : L * (t : ℝ) + A ≤ L * (n : ℝ) + A := by
    nlinarith [mul_le_mul_of_nonneg_left ht_le_n hL]
  simpa [htadd] using hbound.trans hmono

/-- If a shifted sequence has an exponential upper bound, then the original
sequence has the same eventual exponential upper exponent. -/
theorem eventuallyRealExpUpperBound_of_shifted
    {Qlog : ℕ → ℝ} {rho : ℝ} {shift : ℕ}
    (hrho : 0 ≤ rho)
    (h : EventuallyRealExpUpperBound (fun n : ℕ => Qlog (n + shift)) rho) :
    EventuallyRealExpUpperBound Qlog rho := by
  rcases h with ⟨A, hA⟩
  rw [eventually_atTop] at hA
  rcases hA with ⟨N, hN⟩
  refine ⟨A, ?_⟩
  rw [eventually_atTop]
  refine ⟨N + shift, ?_⟩
  intro n hn
  let t : ℕ := n - shift
  have htN : N ≤ t := by
    dsimp [t]
    omega
  have htadd : t + shift = n := by
    dsimp [t]
    exact Nat.sub_add_cancel (by omega : shift ≤ n)
  have ht_le_n : (t : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.sub_le n shift)
  have hbound : Qlog (t + shift) ≤ Real.exp (rho * (t : ℝ) + A) := hN t htN
  have hexp_mono :
      Real.exp (rho * (t : ℝ) + A) ≤ Real.exp (rho * (n : ℝ) + A) := by
    exact Real.exp_monotone (by nlinarith [mul_le_mul_of_nonneg_left ht_le_n hrho])
  simpa [htadd] using hbound.trans hexp_mono

/-- Shifted subexponential growth is equivalent to unshifted subexponential
growth in the direction needed for reverse-prefix applications. -/
theorem eventuallySubexponentialUpperBound_of_shifted
    {Qlog : ℕ → ℝ} {shift : ℕ}
    (h : EventuallySubexponentialUpperBound
      (fun n : ℕ => Qlog (n + shift))) :
    EventuallySubexponentialUpperBound Qlog := by
  intro rho hrho
  exact eventuallyRealExpUpperBound_of_shifted (le_of_lt hrho) (h rho hrho)

/-! ## The finite selector used by the rational converse -/

/-- A rational lower bound from a fixed threshold lets every index `n` be
certified by a level `m` beyond that threshold and affine-linear in `n`.
This is the integer-arithmetic core of the reverse linear converse. -/
theorem exists_certificate_level_of_rationalLinearLower_from
    {J : ℕ → ℕ} {K D M : ℕ}
    (hKpos : 0 < K) (hDpos : 0 < D)
    (hM : ∀ m : ℕ, M ≤ m → K * m ≤ D * J m) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ m : ℕ,
      M ≤ m ∧ n ≤ J m ∧
        (m : ℝ) ≤ ((D : ℝ) / (K : ℝ)) * (n : ℝ) + B := by
  refine ⟨D * (M + 1), ?_⟩
  intro n
  let t : ℕ := n / K + M + 1
  let m : ℕ := D * t
  refine ⟨m, ?_, ?_, ?_⟩
  · have htM : M ≤ t := by
      dsimp [t]
      exact (Nat.le_add_left M (n / K)).trans (Nat.le_succ _)
    have ht_le_mul : t ≤ D * t := Nat.le_mul_of_pos_left t hDpos
    exact htM.trans ht_le_mul
  · have hMle : M ≤ m := by
      have htM : M ≤ t := by
        dsimp [t]
        exact (Nat.le_add_left M (n / K)).trans (Nat.le_succ _)
      have ht_le_mul : t ≤ D * t := Nat.le_mul_of_pos_left t hDpos
      exact htM.trans ht_le_mul
    have hnat := hM m hMle
    have hcast : (K : ℝ) * (m : ℝ) ≤ (D : ℝ) * (J m : ℝ) := by
      have hcast0 : ((K * m : ℕ) : ℝ) ≤ ((D * J m : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simpa [Nat.cast_mul] using hcast0
    have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpos
    have htbound : (n : ℝ) < (K : ℝ) * (t : ℝ) := by
      dsimp [t]
      have hmod : n % K < K := Nat.mod_lt n hKpos
      have hdecomp : K * (n / K) + n % K = n := Nat.div_add_mod n K
      have hstep : n < K * (n / K + 1) := by
        calc
          n = K * (n / K) + n % K := hdecomp.symm
          _ < K * (n / K) + K := by
            exact Nat.add_lt_add_left hmod _
          _ = K * (n / K + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
      have hstepR : (n : ℝ) < (K * (n / K + 1) : ℕ) := by
        exact_mod_cast hstep
      have hle : (K * (n / K + 1) : ℕ) ≤ K * t := by
        dsimp [t]
        exact Nat.mul_le_mul_left K (by omega)
      have hleR : ((K * (n / K + 1) : ℕ) : ℝ) ≤ (K * t : ℕ) := by
        exact_mod_cast hle
      have hKt : ((K * t : ℕ) : ℝ) = (K : ℝ) * (t : ℝ) := by
        norm_num
      have hleR' :
          ((K * (n / K + 1) : ℕ) : ℝ) ≤ (K : ℝ) * (t : ℝ) := by
        calc
          ((K * (n / K + 1) : ℕ) : ℝ) ≤ ((K * t : ℕ) : ℝ) := hleR
          _ = (K : ℝ) * (t : ℝ) := hKt
      exact hstepR.trans_le hleR'
    have hm_eq : (m : ℝ) = (D : ℝ) * (t : ℝ) := by
      dsimp [m]
      norm_num
    have hJge : (n : ℝ) ≤ (J m : ℝ) := by
      have hmain : (K : ℝ) * ((D : ℝ) * (t : ℝ)) ≤ (D : ℝ) * (J m : ℝ) := by
        simpa [hm_eq, mul_assoc, mul_left_comm, mul_comm] using hcast
      have htmain : (K : ℝ) * (t : ℝ) ≤ (J m : ℝ) := by
        nlinarith [hmain, hDreal]
      exact le_trans (le_of_lt htbound) htmain
    exact_mod_cast hJge
  · have hdiv : ((n / K : ℕ) : ℝ) ≤ (n : ℝ) / (K : ℝ) :=
      nat_div_cast_le n K hKpos
    have hDreal : 0 ≤ (D : ℝ) := by positivity
    dsimp [m, t]
    have hmain :
        (D : ℝ) * ((n / K : ℕ) : ℝ) +
            (D : ℝ) * ((M + 1 : ℕ) : ℝ)
          ≤
        (D : ℝ) * ((n : ℝ) / (K : ℝ)) +
            (D : ℝ) * ((M + 1 : ℕ) : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hdiv hDreal]
    have hKreal_ne : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hKpos
    have hrewrite :
        (D : ℝ) * ((n : ℝ) / (K : ℝ)) =
          ((D : ℝ) / (K : ℝ)) * (n : ℝ) := by
      field_simp [hKreal_ne]
    have hB :
        ((D * (M + 1) : ℕ) : ℝ) =
          (D : ℝ) * ((M + 1 : ℕ) : ℝ) := by norm_num
    have hcast :
        ((D * (n / K + M + 1) : ℕ) : ℝ) =
          (D : ℝ) * ((n / K : ℕ) : ℝ) +
            (D : ℝ) * ((M + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    calc
      (m : ℝ)
          = (D : ℝ) * ((n / K : ℕ) : ℝ) +
              (D : ℝ) * ((M + 1 : ℕ) : ℝ) := by
              simpa [m, t] using hcast
      _ ≤ (D : ℝ) * ((n : ℝ) / (K : ℝ)) +
              (D : ℝ) * ((M + 1 : ℕ) : ℝ) := hmain
      _ = ((D : ℝ) / (K : ℝ)) * (n : ℝ) +
              (D * (M + 1) : ℕ) := by
              simp [hrewrite, hB]

/-- A rational lower bound for `J` lets every large index `n` be certified by
some certificate level `m` whose size is affine-linear in `n`. -/
theorem exists_certificate_level_of_rationalLinearLower
    {J : ℕ → ℕ} {K D : ℕ}
    (hlin : EventuallyRationalLinearLowerBound J K D) :
    ∃ B M : ℕ, ∀ n : ℕ, ∃ m : ℕ,
      M ≤ m ∧ n ≤ J m ∧
        (m : ℝ) ≤ ((D : ℝ) / (K : ℝ)) * (n : ℝ) + B := by
  rcases hlin with ⟨hKpos, hDpos, M, hM⟩
  rcases exists_certificate_level_of_rationalLinearLower_from
      (J := J) (K := K) (D := D) (M := M) hKpos hDpos hM with
    ⟨B, hB⟩
  exact ⟨B, M, hB⟩

/-- Reverse criterion plus a rational linear lower bound for `Jcert` gives an
affine upper bound for the shifted denominator-log sequence. -/
theorem reverseCriterion_rationalLinearLower_implies_shifted_affineUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C L : ℝ} {shift K D : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hlin : EventuallyRationalLinearLowerBound Jcert K D)
    (hkappa_nonneg : 0 ≤ kappa)
    (hL : kappa * (D : ℝ) < 2 * L * (K : ℝ)) :
    EventuallyRealAffineUpperBound (fun n : ℕ => Qlog (n + shift)) L := by
  rcases hrev with ⟨Mrev, hrevM⟩
  rcases hlin with ⟨hKpos, hDpos, Mlin, hlinM⟩
  have hselector :
      ∃ B : ℕ, ∀ n : ℕ, ∃ m : ℕ,
        Mrev + Mlin + 1 ≤ m ∧ n ≤ Jcert m ∧
          (m : ℝ) ≤ ((D : ℝ) / (K : ℝ)) * (n : ℝ) + B :=
    exists_certificate_level_of_rationalLinearLower_from
      (J := Jcert) (K := K) (D := D)
      (M := Mrev + Mlin + 1) hKpos hDpos
      (by
        intro m hm
        exact hlinM m (by omega))
  rcases hselector with ⟨B, hB⟩
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hslope_lt : kappa * ((D : ℝ) / (K : ℝ)) / 2 < L := by
    have htmp : kappa * (D : ℝ) / (K : ℝ) < 2 * L := by
      rw [div_lt_iff₀ hKreal]
      nlinarith [hL]
    have htmp' : kappa * ((D : ℝ) / (K : ℝ)) < 2 * L := by
      simpa [mul_div_assoc] using htmp
    nlinarith
  let slope : ℝ := kappa * ((D : ℝ) / (K : ℝ)) / 2
  let A : ℝ := kappa * (B : ℝ) / 2 + C / 2
  refine ⟨A, ?_⟩
  filter_upwards with n
  rcases hB n with ⟨m, hmSel, hnm, hmB⟩
  have hm_large : Mrev ≤ m := by
    omega
  have hrevn : 2 * Qlog (n + shift) ≤ kappa * (m : ℝ) + C :=
    hrevM m n hm_large hnm
  have hslope_bound :
      kappa * (m : ℝ) + C ≤
        2 * (slope * (n : ℝ) + A) := by
    have hmB' := mul_le_mul_of_nonneg_left hmB hkappa_nonneg
    dsimp [slope, A]
    nlinarith
  have htwo : 2 * Qlog (n + shift) ≤
      2 * (slope * (n : ℝ) + A) := hrevn.trans hslope_bound
  have hq : Qlog (n + shift) ≤ slope * (n : ℝ) + A := by nlinarith
  have hslope_le : slope ≤ L := le_of_lt hslope_lt
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hLA : slope * (n : ℝ) + A ≤ L * (n : ℝ) + A := by
    nlinarith [mul_le_mul_of_nonneg_right hslope_le hnnonneg]
  exact hq.trans hLA

/-- Unshifted affine version of the rational linear converse. -/
theorem reverseCriterion_rationalLinearLower_implies_affineUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C L : ℝ} {shift K D : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hlin : EventuallyRationalLinearLowerBound Jcert K D)
    (hkappa_nonneg : 0 ≤ kappa)
    (hL_nonneg : 0 ≤ L)
    (hL : kappa * (D : ℝ) < 2 * L * (K : ℝ)) :
    EventuallyRealAffineUpperBound Qlog L :=
  eventuallyRealAffineUpperBound_of_shifted hL_nonneg
    (reverseCriterion_rationalLinearLower_implies_shifted_affineUpper
      hrev hlin hkappa_nonneg hL)

/-! ## oneOverPi wrappers with reverse criterion as an explicit hypothesis -/

/-- Converse obstruction for `1 / π`: rational-linear certified production
forces affine upper growth of the continued-fraction denominator logs. -/
theorem oneOverPi_affineUpper_of_rationalLinear_J
    {kappa C L : ℝ} {shift K D : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hJ : EventuallyRationalLinearLowerBound J_oneOverPi K D)
    (hkappa_nonneg : 0 ≤ kappa)
    (hL_nonneg : 0 ≤ L)
    (hL : kappa * (D : ℝ) < 2 * L * (K : ℝ)) :
    EventuallyRealAffineUpperBound (continuantQlog oneOverPiCF) L :=
  reverseCriterion_rationalLinearLower_implies_affineUpper
    hrev hJ hkappa_nonneg hL_nonneg hL

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanLogReverseSelection.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Logarithmic reverse-selection bridge

This file proves the ceiling-selection argument for the reverse Ramanujan
interface:

`EventuallyLogLowerBound Jcert c` lets us choose, for each large `n`, an integer
`m ≈ exp(rho₀ n)` with `n ≤ Jcert m`, whenever `1 / c < rho₀`.

Together with `CertifiedPrefixReverseCriterion`, this gives exponential upper
growth for the shifted denominator-log sequence.
-/

/-- Strong logarithmic selector.

For every fixed threshold `M0`, eventually in `n` there is a certificate level
`m` beyond that threshold which certifies `n` and remains below `exp(rho*n)`. -/
def EventuallyLogPrefixSelector (Jcert : ℕ → ℕ) (rho : ℝ) : Prop :=
  ∀ M0 : ℕ,
    ∀ᶠ n : ℕ in atTop,
      ∃ m : ℕ,
        M0 ≤ m ∧ n ≤ Jcert m ∧
          (m : ℝ) ≤ Real.exp (rho * (n : ℝ))

/-! ## Elementary ceiling/exponential helpers -/

/-- Exponentials with positive linear exponent eventually dominate any fixed
natural threshold. -/
lemma eventually_nat_le_exp_mul
    {rho : ℝ} (hrho : 0 < rho) (M0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (M0 : ℝ) ≤ Real.exp (rho * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log ((M0 + 1 : ℕ) : ℝ) / rho)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have harg_lt : Real.log ((M0 + 1 : ℕ) : ℝ) < rho * (n : ℝ) := by
    have hN' : Real.log ((M0 + 1 : ℕ) : ℝ) / rho < (N : ℝ) := hN
    have hNn : Real.log ((M0 + 1 : ℕ) : ℝ) / rho < (n : ℝ) :=
      hN'.trans_le hNle
    have hmul := mul_lt_mul_of_pos_left hNn hrho
    have hrhone : rho ≠ 0 := ne_of_gt hrho
    field_simp [hrhone] at hmul
    simpa [mul_comm] using hmul
  have hMpos : 0 < ((M0 + 1 : ℕ) : ℝ) := by positivity
  have hMexp :
      ((M0 + 1 : ℕ) : ℝ) < Real.exp (rho * (n : ℝ)) := by
    calc
      ((M0 + 1 : ℕ) : ℝ) = Real.exp (Real.log ((M0 + 1 : ℕ) : ℝ)) := by
          rw [Real.exp_log hMpos]
      _ < Real.exp (rho * (n : ℝ)) := Real.exp_lt_exp.mpr harg_lt
  have hMle : (M0 : ℝ) ≤ ((M0 + 1 : ℕ) : ℝ) := by norm_num
  exact hMle.trans (le_of_lt hMexp)

/-- `ceil(exp(rho0*n))` is eventually bounded by `exp(rho*n)` when
`rho0 < rho`. -/
lemma eventually_natCeil_exp_mul_le_exp_larger
    {rho0 rho : ℝ} (hrho0 : 0 < rho0) (hstrict : rho0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.ceil (Real.exp (rho0 * (n : ℝ))) : ℕ) : ℝ) ≤
        Real.exp (rho * (n : ℝ)) := by
  have hgap : 0 < rho - rho0 := by linarith
  filter_upwards [eventually_nat_le_exp_mul hgap 2] with n hgap_exp
  let x : ℝ := Real.exp (rho0 * (n : ℝ))
  have hxpos : 0 < x := Real.exp_pos _
  have hxone : 1 ≤ x := by
    dsimp [x]
    have h : Real.exp 0 ≤ Real.exp (rho0 * (n : ℝ)) := Real.exp_le_exp.mpr (by
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      nlinarith [hrho0, hnnonneg])
    simpa using h
  have hceil : ((Nat.ceil x : ℕ) : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hxpos.le
  have hceil_le_two : ((Nat.ceil x : ℕ) : ℝ) ≤ 2 * x := by
    nlinarith
  have htwo_le_gap : 2 ≤ Real.exp ((rho - rho0) * (n : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgap_exp
  have htwo_x_le :
      2 * x ≤ Real.exp (rho * (n : ℝ)) := by
    have hxnonneg : 0 ≤ x := le_of_lt hxpos
    have hmul := mul_le_mul_of_nonneg_right htwo_le_gap hxnonneg
    have hexp_eq :
        Real.exp ((rho - rho0) * (n : ℝ)) * x =
          Real.exp (rho * (n : ℝ)) := by
      dsimp [x]
      rw [← Real.exp_add]
      congr 1
      ring
    simpa [hexp_eq] using hmul
  exact hceil_le_two.trans htwo_x_le

/-- The selected ceiling eventually exceeds any fixed threshold. -/
lemma eventually_threshold_le_natCeil_exp_mul
    {rho0 : ℝ} (hrho0 : 0 < rho0) (M0 : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      M0 ≤ Nat.ceil (Real.exp (rho0 * (n : ℝ))) := by
  filter_upwards [eventually_nat_le_exp_mul hrho0 M0] with n hM
  have hreal :
      (M0 : ℝ) ≤
        ((Nat.ceil (Real.exp (rho0 * (n : ℝ))) : ℕ) : ℝ) :=
    hM.trans (Nat.le_ceil _)
  exact_mod_cast hreal

/-- The logarithm of the selected ceiling is at least the exponent used to
select it. -/
lemma le_log_natCeil_exp_mul
    {rho0 : ℝ} (_hrho0 : 0 < rho0) (n : ℕ) :
    rho0 * (n : ℝ) ≤
      Real.log ((Nat.ceil (Real.exp (rho0 * (n : ℝ))) : ℕ) : ℝ) := by
  let x : ℝ := Real.exp (rho0 * (n : ℝ))
  have hxpos : 0 < x := Real.exp_pos _
  have hxceil : x ≤ ((Nat.ceil x : ℕ) : ℝ) := Nat.le_ceil _
  have hlog := Real.log_le_log hxpos hxceil
  simpa [x, Real.log_exp] using hlog

/-- If `1/c < rho`, choose an intermediate positive exponent. -/
lemma exists_intermediate_inverse_lt
    {c rho : ℝ} (hc : 0 < c) (hrho : 1 / c < rho) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ 1 / c < rho0 ∧ rho0 < rho := by
  rcases exists_between hrho with ⟨rho0, hinv, hrho0⟩
  have hinv_pos : 0 < 1 / c := one_div_pos.mpr hc
  exact ⟨rho0, hinv_pos.trans hinv, hinv, hrho0⟩

/-! ## Selector theorem -/

/-- Logarithmic lower bound for `Jcert` gives the strong logarithmic selector. -/
theorem eventuallyLogPrefixSelector_of_eventuallyLogLowerBound
    {Jcert : ℕ → ℕ} {c rho : ℝ}
    (hJ : EventuallyLogLowerBound Jcert c)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyLogPrefixSelector Jcert rho := by
  unfold EventuallyLogPrefixSelector
  intro M0
  rcases exists_intermediate_inverse_lt (c := c) (rho := rho) hc hrho with
    ⟨rho0, hrho0_pos, hinv_lt, hrho0_lt⟩
  unfold EventuallyLogLowerBound at hJ
  rw [eventually_atTop] at hJ
  rcases hJ with ⟨MJ, hMJ⟩
  filter_upwards
    [eventually_threshold_le_natCeil_exp_mul hrho0_pos M0,
     eventually_threshold_le_natCeil_exp_mul hrho0_pos MJ,
     eventually_natCeil_exp_mul_le_exp_larger hrho0_pos hrho0_lt]
    with n hM0 hMJceil hupper
  let m : ℕ := Nat.ceil (Real.exp (rho0 * (n : ℝ)))
  refine ⟨m, hM0, ?_, hupper⟩
  have hJm : c * Real.log (m : ℝ) ≤ (Jcert m : ℝ) := hMJ m hMJceil
  have hlog :
      rho0 * (n : ℝ) ≤ Real.log (m : ℝ) := by
    dsimp [m]
    exact le_log_natCeil_exp_mul hrho0_pos n
  have hone : 1 < c * rho0 := by
    have hmul := mul_lt_mul_of_pos_left hinv_lt hc
    have hcinv : c * (1 / c) = 1 := by
      field_simp [ne_of_gt hc]
    nlinarith
  have hn_to_crho :
      (n : ℝ) ≤ c * (rho0 * (n : ℝ)) := by
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hone) hnnonneg]
  have hcrho_to_log :
      c * (rho0 * (n : ℝ)) ≤ c * Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hc)
  have hnJ : (n : ℝ) ≤ (Jcert m : ℝ) :=
    hn_to_crho.trans (hcrho_to_log.trans hJm)
  exact_mod_cast hnJ

/-! ## Reverse criterion plus selector gives exponential upper bound -/

/-- A selector plus the reverse criterion gives a shifted exponential upper
bound. -/
theorem reverseCriterion_logSelector_implies_shifted_expUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C rho : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hsel : EventuallyLogPrefixSelector Jcert rho)
    (hkappa_nonneg : 0 ≤ kappa)
    (hrho_pos : 0 < rho) :
    EventuallyRealExpUpperBound (fun n : ℕ => Qlog (n + shift)) rho := by
  rcases hrev with ⟨Mrev, hrevM⟩
  let B : ℝ := kappa / 2 + |C| / 2 + 1
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨Real.log B, ?_⟩
  filter_upwards [hsel Mrev] with n hseln
  rcases hseln with ⟨m, hmrev, hnm, hmexp⟩
  have hrevn : 2 * Qlog (n + shift) ≤ kappa * (m : ℝ) + C :=
    hrevM m n hmrev hnm
  have hexp_pos : 0 < Real.exp (rho * (n : ℝ)) := Real.exp_pos _
  have hexp_ge_one : 1 ≤ Real.exp (rho * (n : ℝ)) := by
    have h : Real.exp 0 ≤ Real.exp (rho * (n : ℝ)) := Real.exp_le_exp.mpr (by
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      nlinarith [hrho_pos, hnnonneg])
    simpa using h
  have hmterm :
      kappa * (m : ℝ) / 2 ≤
        (kappa / 2) * Real.exp (rho * (n : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hmexp hkappa_nonneg
    nlinarith
  have hCterm : C / 2 ≤ |C| / 2 := by
    nlinarith [le_abs_self C]
  have hCterm_exp :
      |C| / 2 ≤ (|C| / 2) * Real.exp (rho * (n : ℝ)) := by
    have hnonneg : 0 ≤ |C| / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp_ge_one hnonneg]
  have hQ_pre :
      Qlog (n + shift) ≤ kappa * (m : ℝ) / 2 + C / 2 := by
    nlinarith
  have hQ_B :
      Qlog (n + shift) ≤ B * Real.exp (rho * (n : ℝ)) := by
    dsimp [B]
    nlinarith [hQ_pre, hmterm, hCterm, hCterm_exp, hexp_ge_one]
  calc
    Qlog (n + shift) ≤ B * Real.exp (rho * (n : ℝ)) := hQ_B
    _ = Real.exp (rho * (n : ℝ) + Real.log B) := by
        rw [Real.exp_add, Real.exp_log hBpos]
        ring

/-- Main shifted logarithmic reverse theorem. -/
theorem reverseCriterion_logLower_implies_shifted_expUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C c rho : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hJ : EventuallyLogLowerBound Jcert c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound (fun n : ℕ => Qlog (n + shift)) rho := by
  have hsel : EventuallyLogPrefixSelector Jcert rho :=
    eventuallyLogPrefixSelector_of_eventuallyLogLowerBound
      (Jcert := Jcert) hJ hc hrho
  have hrho_pos : 0 < rho := by
    have hinv_pos : 0 < 1 / c := one_div_pos.mpr hc
    exact hinv_pos.trans hrho
  exact reverseCriterion_logSelector_implies_shifted_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev) (hsel := hsel)
    hkappa_nonneg hrho_pos

/-- Unshifted logarithmic reverse theorem. -/
theorem reverseCriterion_logLower_implies_expUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C c rho : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hJ : EventuallyLogLowerBound Jcert c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound Qlog rho := by
  have hshifted := reverseCriterion_logLower_implies_shifted_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev) (hJ := hJ)
    hkappa_nonneg hc hrho
  have hrho_nonneg : 0 ≤ rho := by
    have hinv_pos : 0 < 1 / c := one_div_pos.mpr hc
    exact le_of_lt (hinv_pos.trans hrho)
  exact eventuallyRealExpUpperBound_of_shifted
    (Qlog := Qlog) (rho := rho) (shift := shift)
    hrho_nonneg hshifted

/-! ## oneOverPi and super-log wrappers -/

/-- If the `1 / π` certified prefix function has a logarithmic lower bound,
then the `1 / π` continuant-log sequence has every exponential upper bound
with exponent larger than `1/c`, assuming the reverse criterion. -/
theorem oneOverPi_expUpper_of_logLower_J
    {kappa C c rho : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hJ : EventuallyLogLowerBound J_oneOverPi c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound (continuantQlog oneOverPiCF) rho :=
  reverseCriterion_logLower_implies_expUpper
    (Qlog := continuantQlog oneOverPiCF) (Jcert := J_oneOverPi)
    (hrev := hrev) (hJ := hJ)
    hkappa_nonneg hc hrho

/-- Super-logarithmic certified prefix production forces subexponential
continued-fraction denominator-log growth, under the reverse criterion. -/
theorem reverseCriterion_superLogLower_implies_subexponentialUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hJ : ∀ c : ℝ, 0 < c → EventuallyLogLowerBound Jcert c)
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound Qlog := by
  intro rho hrho
  let c : ℝ := 2 / rho
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hineq : 1 / c < rho := by
    dsimp [c]
    field_simp [ne_of_gt hrho]
    nlinarith [hrho]
  exact reverseCriterion_logLower_implies_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev) (hJ := hJ c hc)
    hkappa_nonneg hc hineq

/-- One-over-pi wrapper for the super-logarithmic reverse consequence. -/
theorem oneOverPi_subexponentialUpper_of_superLogLower_J
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hJ : ∀ c : ℝ, 0 < c → EventuallyLogLowerBound J_oneOverPi c)
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound (continuantQlog oneOverPiCF) :=
  reverseCriterion_superLogLower_implies_subexponentialUpper
    (Qlog := continuantQlog oneOverPiCF) (Jcert := J_oneOverPi)
    (hrev := hrev) (hJ := hJ) hkappa_nonneg

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanBlockCountReverse.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Block-count reverse wrappers

The reverse analytic interface is stated for the certified prefix length
`Jcert`.  This file adds the finite reverse transfer from certified nonempty
block count back to `Jcert`, using the elementary bound
`certifiedBlockCountAt a Jcert m ≤ Jcert m`.

Do not confuse this with the extracted-cardinality object: one long block can
make the extracted set large without forcing many certified blocks.
-/

/-! ## Pure finite reverse: block count is bounded by prefix length -/

/-- The certified nonempty block count at level `m` is bounded by the certified
prefix length at level `m`. -/
theorem certifiedBlockCountAt_le_Jcert
    (a : ℕ → ℕ) (Jcert : ℕ → ℕ) (m : ℕ) :
    certifiedBlockCountAt a Jcert m ≤ Jcert m := by
  rw [certifiedBlockCountAt_apply]
  exact certifiedBlockCount_le a (Jcert m)

/-! ## Lower-bound transfers from block count back to prefix length -/

/-- A linear lower bound for certified block count gives the same lower bound
for the certified prefix length. -/
theorem eventuallyLinearLowerBound_Jcert_of_certifiedBlockCountAt
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ} {c : ℝ}
    (hB : EventuallyLinearLowerBound (certifiedBlockCountAt a Jcert) c) :
    EventuallyLinearLowerBound Jcert c := by
  unfold EventuallyLinearLowerBound at *
  filter_upwards [hB] with m hm
  have hle_nat : certifiedBlockCountAt a Jcert m ≤ Jcert m :=
    certifiedBlockCountAt_le_Jcert a Jcert m
  have hle_real :
      ((certifiedBlockCountAt a Jcert m : ℕ) : ℝ) ≤ (Jcert m : ℝ) := by
    exact_mod_cast hle_nat
  exact hm.trans hle_real

/-- A logarithmic lower bound for certified block count gives the same lower
bound for the certified prefix length. -/
theorem eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ} {c : ℝ}
    (hB : EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c) :
    EventuallyLogLowerBound Jcert c := by
  unfold EventuallyLogLowerBound at *
  filter_upwards [hB] with m hm
  have hle_nat : certifiedBlockCountAt a Jcert m ≤ Jcert m :=
    certifiedBlockCountAt_le_Jcert a Jcert m
  have hle_real :
      ((certifiedBlockCountAt a Jcert m : ℕ) : ℝ) ≤ (Jcert m : ℝ) := by
    exact_mod_cast hle_nat
  exact hm.trans hle_real

/-- A super-logarithmic lower bound for certified block count gives the same
super-logarithmic lower bound for the certified prefix length. -/
theorem eventuallySuperLogLowerBound_Jcert_of_certifiedBlockCountAt
    {a : ℕ → ℕ} {Jcert : ℕ → ℕ}
    (hB : EventuallySuperLogLowerBound (certifiedBlockCountAt a Jcert)) :
    EventuallySuperLogLowerBound Jcert := by
  intro c hc
  exact eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
    (a := a) (Jcert := Jcert) (c := c) (hB c hc)

/-! ## One-over-pi wrappers for `B_oneOverPi` -/

/-- Linear lower bounds for the informal block count `B_oneOverPi` transfer
back to `J_oneOverPi`. -/
theorem eventuallyLinearLowerBound_J_oneOverPi_of_B_oneOverPi
    {c : ℝ}
    (hB : EventuallyLinearLowerBound B_oneOverPi c) :
    EventuallyLinearLowerBound J_oneOverPi c := by
  simpa [B_oneOverPi] using
    eventuallyLinearLowerBound_Jcert_of_certifiedBlockCountAt
      (a := oneOverPiCF) (Jcert := J_oneOverPi) (c := c) hB

/-- Logarithmic lower bounds for the informal block count `B_oneOverPi`
transfer back to `J_oneOverPi`. -/
theorem eventuallyLogLowerBound_J_oneOverPi_of_B_oneOverPi
    {c : ℝ}
    (hB : EventuallyLogLowerBound B_oneOverPi c) :
    EventuallyLogLowerBound J_oneOverPi c := by
  simpa [B_oneOverPi] using
    eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
      (a := oneOverPiCF) (Jcert := J_oneOverPi) (c := c) hB

/-- Super-logarithmic lower bounds for `B_oneOverPi` transfer back to
`J_oneOverPi`. -/
theorem eventuallySuperLogLowerBound_J_oneOverPi_of_B_oneOverPi
    (hB : EventuallySuperLogLowerBound B_oneOverPi) :
    EventuallySuperLogLowerBound J_oneOverPi := by
  intro c hc
  exact eventuallyLogLowerBound_J_oneOverPi_of_B_oneOverPi
    (c := c) (hB c hc)

/-! ## Feed block-count lower bounds into the reverse analytic theorem -/

/-- Generic shifted reverse theorem using a logarithmic lower bound for
certified block count instead of directly for `Jcert`. -/
theorem reverseCriterion_logLower_blockCountAt_implies_shifted_expUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {a : ℕ → ℕ}
    {kappa C rho c : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hB : EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound (fun n : ℕ => Qlog (n + shift)) rho :=
  reverseCriterion_logLower_implies_shifted_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev)
    (hJ := eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
      (a := a) (Jcert := Jcert) (c := c) hB)
    hkappa_nonneg hc hrho

/-- Generic unshifted reverse theorem using a logarithmic lower bound for
certified block count instead of directly for `Jcert`. -/
theorem reverseCriterion_logLower_blockCountAt_implies_expUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {a : ℕ → ℕ}
    {kappa C rho c : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hB : EventuallyLogLowerBound (certifiedBlockCountAt a Jcert) c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound Qlog rho :=
  reverseCriterion_logLower_implies_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev)
    (hJ := eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
      (a := a) (Jcert := Jcert) (c := c) hB)
    hkappa_nonneg hc hrho

/-- Generic shifted super-logarithmic reverse theorem from certified block
count. -/
theorem reverseCriterion_superLogLower_blockCountAt_implies_shifted_subexponentialUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {a : ℕ → ℕ}
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hB : EventuallySuperLogLowerBound (certifiedBlockCountAt a Jcert))
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound (fun n : ℕ => Qlog (n + shift)) := by
  intro rho hrho
  let c : ℝ := 2 / rho
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hineq : 1 / c < rho := by
    dsimp [c]
    field_simp [ne_of_gt hrho]
    nlinarith [hrho]
  exact reverseCriterion_logLower_blockCountAt_implies_shifted_expUpper
    (Qlog := Qlog) (Jcert := Jcert) (a := a)
    (hrev := hrev) (hB := hB c hc)
    hkappa_nonneg hc hineq

/-- Generic unshifted super-logarithmic reverse theorem from certified block
count. -/
theorem reverseCriterion_superLogLower_blockCountAt_implies_subexponentialUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ} {a : ℕ → ℕ}
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion Qlog Jcert kappa C shift)
    (hB : EventuallySuperLogLowerBound (certifiedBlockCountAt a Jcert))
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound Qlog :=
  reverseCriterion_superLogLower_implies_subexponentialUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hrev)
    (hJ := eventuallySuperLogLowerBound_Jcert_of_certifiedBlockCountAt
      (a := a) (Jcert := Jcert) hB)
    hkappa_nonneg

/-! ## One-over-pi reverse wrappers from `B_oneOverPi` -/

/-- A logarithmic lower bound for `B_oneOverPi` gives a shifted exponential
upper bound for the `1 / π` continuant-log sequence, assuming the reverse
criterion. -/
theorem oneOverPi_shifted_expUpper_of_logLower_B
    {kappa C rho c : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hB : EventuallyLogLowerBound B_oneOverPi c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound
      (fun n : ℕ => continuantQlog oneOverPiCF (n + shift)) rho := by
  simpa [B_oneOverPi] using
    reverseCriterion_logLower_blockCountAt_implies_shifted_expUpper
      (Qlog := continuantQlog oneOverPiCF) (Jcert := J_oneOverPi)
      (a := oneOverPiCF) (hrev := hrev) (hB := hB)
      hkappa_nonneg hc hrho

/-- A logarithmic lower bound for `B_oneOverPi` gives an unshifted exponential
upper bound for the `1 / π` continuant-log sequence, assuming the reverse
criterion. -/
theorem oneOverPi_expUpper_of_logLower_B
    {kappa C rho c : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hB : EventuallyLogLowerBound B_oneOverPi c)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc : 0 < c)
    (hrho : 1 / c < rho) :
    EventuallyRealExpUpperBound (continuantQlog oneOverPiCF) rho :=
  oneOverPi_expUpper_of_logLower_J
    (hrev := hrev)
    (hJ := eventuallyLogLowerBound_J_oneOverPi_of_B_oneOverPi
      (c := c) hB)
    hkappa_nonneg hc hrho

/-- A super-logarithmic lower bound for `B_oneOverPi` gives shifted
subexponential upper growth for the `1 / π` continuant-log sequence. -/
theorem oneOverPi_shifted_subexponentialUpper_of_superLogLower_B
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hB : EventuallySuperLogLowerBound B_oneOverPi)
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound
      (fun n : ℕ => continuantQlog oneOverPiCF (n + shift)) := by
  simpa [B_oneOverPi] using
    reverseCriterion_superLogLower_blockCountAt_implies_shifted_subexponentialUpper
      (Qlog := continuantQlog oneOverPiCF) (Jcert := J_oneOverPi)
      (a := oneOverPiCF) (hrev := hrev) (hB := hB)
      hkappa_nonneg

/-- A super-logarithmic lower bound for `B_oneOverPi` gives unshifted
subexponential upper growth for the `1 / π` continuant-log sequence. -/
theorem oneOverPi_subexponentialUpper_of_superLogLower_B
    {kappa C : ℝ} {shift : ℕ}
    (hrev : CertifiedPrefixReverseCriterion
      (continuantQlog oneOverPiCF) J_oneOverPi kappa C shift)
    (hB : EventuallySuperLogLowerBound B_oneOverPi)
    (hkappa_nonneg : 0 ≤ kappa) :
    EventuallySubexponentialUpperBound (continuantQlog oneOverPiCF) :=
  oneOverPi_subexponentialUpper_of_superLogLower_J
    (hrev := hrev)
    (hJ := eventuallySuperLogLowerBound_J_oneOverPi_of_B_oneOverPi hB)
    hkappa_nonneg

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanSubexponentialForward.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Forward subexponential-to-superlog bridge

This file proves the forward abstract implication:

`CertifiedPrefixCriterion Qlog Jcert kappa C0 shift`
plus shifted subexponential upper growth for `Qlog`
implies super-logarithmic certified-prefix production.

Combined with the reverse layer, this packages a two-sided abstract equivalence.
No pi-specific analytic criterion is asserted here.
-/

/-- Shifted eventual exponential upper bound:
`Qlog(n + shift) ≤ exp(rho*n + O(1))` eventually. -/
def EventuallyShiftedExpQlogUpperBound
    (Qlog : ℕ → ℝ) (shift : ℕ) (rho : ℝ) : Prop :=
  EventuallyRealExpUpperBound (fun n : ℕ => Qlog (n + shift)) rho

/-- Shifted subexponential upper bound:
`Qlog(n + shift) ≤ exp(o(n))`. -/
def EventuallyShiftedSubexponentialQlogUpperBound
    (Qlog : ℕ → ℝ) (shift : ℕ) : Prop :=
  EventuallySubexponentialUpperBound (fun n : ℕ => Qlog (n + shift))

/-- Local alias for the already compiled super-logarithmic lower-bound
predicate. -/
abbrev SuperLogLowerBound (J : ℕ → ℕ) : Prop :=
  EventuallySuperLogLowerBound J

theorem shiftedSubexp_iff_subexp_comp_shift
    {Qlog : ℕ → ℝ} {shift : ℕ} :
    EventuallyShiftedSubexponentialQlogUpperBound Qlog shift ↔
      EventuallySubexponentialUpperBound (fun n : ℕ => Qlog (n + shift)) := by
  rfl

/-! ## Tending-to-infinity helpers for logarithmic trials -/

/-- If `K,D > 0`, the rational `Nat.log 2` trial tends to infinity. -/
theorem tendsto_rationalNatLogTrial_atTop
    {K D : ℕ} (hK : 0 < K) (hD : 0 < D) :
    Tendsto (rationalNatLogTrial K D) atTop atTop := by
  let s : ℝ := (((K : ℝ) / (D : ℝ)) / Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hspos : 0 < s := by
    dsimp [s]
    exact div_pos (div_pos (by exact_mod_cast hK) (by exact_mod_cast hD)) hlog2
  have hhalf_pos : 0 < s / 2 := by positivity
  have hhalf_lt : s / 2 < s := by linarith
  exact tendsto_atTop_of_eventuallyLogLowerBound hhalf_pos
    (eventuallyLogLowerBound_rationalNatLogTrial
      (K := K) (D := D) hD hhalf_lt)

/-- Adding a fixed shift preserves divergence to infinity for the rational
logarithmic trial. -/
theorem tendsto_rationalNatLogTrial_add_shift_atTop
    {K D shift : ℕ} (hK : 0 < K) (hD : 0 < D) :
    Tendsto (fun m : ℕ => rationalNatLogTrial K D m + shift) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have ht := tendsto_rationalNatLogTrial_atTop (K := K) (D := D) hK hD
  rw [Filter.tendsto_atTop_atTop] at ht
  rcases ht b with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  exact (hN m hm).trans (Nat.le_add_right _ _)

/-! ## Shifted exponential upper bounds imply admissibility -/

/-- Eventual shifted exponential `Qlog` growth plus an eventually logarithmic
upper bound for the trial gives prefix admissibility, provided
`rho * s < 1`. -/
theorem eventuallyPrefixAdmissible_of_shiftedExpQlogUpperBound_of_logAffineUpper
    {Qlog : ℕ → ℝ} {g : ℕ → ℕ}
    {kappa C0 rho s A : ℝ} {shift : ℕ}
    (hg_tendsto : Tendsto g atTop atTop)
    (hQ : EventuallyShiftedExpQlogUpperBound Qlog shift rho)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hg_upper : EventuallyLogAffineUpperBound g s A)
    (hslope : rho * s < 1) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift g := by
  rcases hQ with ⟨C, hQevent⟩
  unfold EventuallyPrefixAdmissible EventuallyLogAffineUpperBound at *
  let M : ℝ := C + rho * A
  have hdom := eventually_const_add_two_exp_affine_log_le_linear
    (A := M) (a := rho * s) (kappa := kappa) (C0 := C0)
    hslope hkappa
  filter_upwards [hg_tendsto.eventually hQevent, hg_upper, hdom]
    with m hQm hgm hdom_m
  have hexp_le :
      Real.exp (rho * (g m : ℝ) + C) ≤
        Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [M]
    nlinarith [hgm, mul_le_mul_of_nonneg_left hgm hrho]
  have hmain : C0 + 2 * Qlog (g m + shift) ≤
      C0 + 2 * Real.exp (M + (rho * s) * Real.log (m : ℝ)) := by
    nlinarith [hQm, hexp_le]
  exact hmain.trans hdom_m

/-- Rational-logarithmic specialization of shifted exponential admissibility. -/
theorem eventuallyPrefixAdmissible_rationalNatLogTrial_of_shiftedExpQlogUpperBound
    {Qlog : ℕ → ℝ} {K D : ℕ}
    {kappa C0 rho : ℝ} {shift : ℕ}
    (hK : 0 < K) (hD : 0 < D)
    (hQ : EventuallyShiftedExpQlogUpperBound Qlog shift rho)
    (hrho : 0 ≤ rho)
    (hkappa : 0 < kappa)
    (hslope : rho * ((((K : ℝ) / (D : ℝ)) / Real.log 2)) < 1) :
    EventuallyPrefixAdmissible Qlog kappa C0 shift (rationalNatLogTrial K D) := by
  exact eventuallyPrefixAdmissible_of_shiftedExpQlogUpperBound_of_logAffineUpper
    (Qlog := Qlog) (g := rationalNatLogTrial K D)
    (kappa := kappa) (C0 := C0) (rho := rho)
    (s := (((K : ℝ) / (D : ℝ)) / Real.log 2)) (A := 0)
    (shift := shift)
    (tendsto_rationalNatLogTrial_atTop (K := K) (D := D) hK hD)
    hQ hrho hkappa
    (eventuallyLogAffineUpperBound_rationalNatLogTrial (K := K) (D := D) hD)
    hslope

/-! ## Rational rate selection -/

/-- Choose a positive integer whose base-two logarithmic trial rate exceeds any
given positive real constant. -/
lemma exists_nat_rate_gt
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 0 < K ∧ c < ((K : ℝ) / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (c * Real.log 2)
  have hKpos : 0 < K := by
    have hKposR : 0 < (K : ℝ) := by
      nlinarith [mul_pos hc hlog2, hK]
    exact_mod_cast hKposR
  refine ⟨K, hKpos, ?_⟩
  exact (lt_div_iff₀ hlog2).mpr hK

/-- For every positive slope, choose a positive exponent with product below
one. -/
lemma exists_pos_rho_mul_lt_one
    {s : ℝ} (hs : 0 < s) :
    ∃ rho : ℝ, 0 < rho ∧ rho * s < 1 := by
  refine ⟨1 / (2 * s), ?_, ?_⟩
  · positivity
  · have hsne : s ≠ 0 := ne_of_gt hs
    have htwos : 2 * s ≠ 0 := by positivity
    field_simp [hsne, htwos]
    nlinarith [hs]

/-! ## Main forward theorem -/

/-- Forward super-log theorem.  If the prefix criterion holds and the shifted
`Qlog` upper bound is subexponential, then the certified-prefix function is
super-logarithmic. -/
theorem prefixCriterion_shiftedSubexpUpper_implies_superLogLower_Jcert
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound Jcert := by
  intro c hc
  rcases exists_nat_rate_gt hc with ⟨K, hKpos, hcrate⟩
  let s : ℝ := (K : ℝ) / Real.log 2
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  rcases exists_pos_rho_mul_lt_one hspos with ⟨rho, hrho_pos, hslope'⟩
  have hQrho : EventuallyShiftedExpQlogUpperBound Qlog shift rho :=
    hsub rho hrho_pos
  have hslope :
      rho * ((((K : ℝ) / (((1 : ℕ) : ℝ))) / Real.log 2)) < 1 := by
    simpa [s] using hslope'
  have hadm : EventuallyPrefixAdmissible Qlog kappa C0 shift
      (rationalNatLogTrial K 1) :=
    eventuallyPrefixAdmissible_rationalNatLogTrial_of_shiftedExpQlogUpperBound
      (Qlog := Qlog) (K := K) (D := 1)
      (kappa := kappa) (C0 := C0) (rho := rho) (shift := shift)
      hKpos (by norm_num) hQrho (le_of_lt hrho_pos) hkappa hslope
  exact eventuallyLogLowerBound_Jcert_of_prefixCriterion_of_admissible
    (Qlog := Qlog) (Jcert := Jcert) (g := rationalNatLogTrial K 1)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hcrit hadm
    (eventuallyLogLowerBound_rationalNatLogTrial
      (K := K) (D := 1) (by norm_num) (by simpa using hcrate))

/-! ## Forward transfers to block count and extracted cardinality -/

theorem prefixCriterion_shiftedSubexpUpper_implies_superLogLower_certifiedBlockCountAt
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound (certifiedBlockCountAt a Jcert) := by
  intro c hc
  have hJ : SuperLogLowerBound Jcert :=
    prefixCriterion_shiftedSubexpUpper_implies_superLogLower_Jcert
      (Qlog := Qlog) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hkappa hsub
  have hJ3 : EventuallyLogLowerBound Jcert (3 * c) := hJ (3 * c) (by positivity)
  exact eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := 3 * c) (c' := c) hJ3 (by nlinarith)

theorem prefixCriterion_shiftedSubexpUpper_implies_superLogLower_certifiedOddBlocksCardAt
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound (certifiedOddBlocksCardAt a Jcert) := by
  intro c hc
  have hJ : SuperLogLowerBound Jcert :=
    prefixCriterion_shiftedSubexpUpper_implies_superLogLower_Jcert
      (Qlog := Qlog) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hkappa hsub
  have hJ3 : EventuallyLogLowerBound Jcert (3 * c) := hJ (3 * c) (by positivity)
  exact eventuallyLogLowerBound_certifiedOddBlocksCardAt_of_Jcert
    (a := a) hpos (Jcert := Jcert)
    (c := 3 * c) (c' := c) hJ3 (by nlinarith)

theorem oneOverPi_superLogLower_B_of_prefixCriterion_shiftedSubexpUpper
    {Qlog : ℕ → ℝ} {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound B_oneOverPi := by
  simpa [B_oneOverPi] using
    prefixCriterion_shiftedSubexpUpper_implies_superLogLower_certifiedBlockCountAt
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hkappa hsub

theorem oneOverPi_superLogLower_certifiedCard_of_prefixCriterion_shiftedSubexpUpper
    {Qlog : ℕ → ℝ} {kappa C0 : ℝ} {shift : ℕ}
    (hcrit : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound certifiedAOneOverPiCard := by
  simpa [certifiedAOneOverPiCard] using
    prefixCriterion_shiftedSubexpUpper_implies_superLogLower_certifiedOddBlocksCardAt
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hcrit hkappa hsub

/-! ## Two-sided packaging -/

/-- Reverse super-log theorem in shifted-subexponential vocabulary. -/
theorem reverseCriterion_superLogLower_implies_shiftedSubexpUpper
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hreverse : CertifiedPrefixReverseCriterion Qlog Jcert kappa C0 shift)
    (hkappa_nonneg : 0 ≤ kappa)
    (hJ : SuperLogLowerBound Jcert) :
    EventuallyShiftedSubexponentialQlogUpperBound Qlog shift := by
  intro rho hrho
  let c : ℝ := 2 / rho
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hineq : 1 / c < rho := by
    dsimp [c]
    field_simp [ne_of_gt hrho]
    nlinarith [hrho]
  exact reverseCriterion_logLower_implies_shifted_expUpper
    (Qlog := Qlog) (Jcert := Jcert)
    (hrev := hreverse) (hJ := hJ c hc)
    hkappa_nonneg hc hineq

/-- Under both abstract prefix criteria, super-logarithmic certified-prefix
production is equivalent to shifted subexponential `Qlog` growth. -/
theorem superLogLower_Jcert_iff_shiftedSubexpUpper_of_prefixCriteria
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hforward : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hreverse : CertifiedPrefixReverseCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa) :
    SuperLogLowerBound Jcert ↔
      EventuallyShiftedSubexponentialQlogUpperBound Qlog shift := by
  constructor
  · intro hJ
    exact reverseCriterion_superLogLower_implies_shiftedSubexpUpper
      (Qlog := Qlog) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hreverse (le_of_lt hkappa) hJ
  · intro hsub
    exact prefixCriterion_shiftedSubexpUpper_implies_superLogLower_Jcert
      (Qlog := Qlog) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hforward hkappa hsub

/-- Certified block count is super-logarithmic iff the certified prefix length
is super-logarithmic. -/
theorem superLogLower_certifiedBlockCountAt_iff_Jcert
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Jcert : ℕ → ℕ} :
    SuperLogLowerBound (certifiedBlockCountAt a Jcert) ↔
      SuperLogLowerBound Jcert := by
  constructor
  · intro hB c hc
    exact eventuallyLogLowerBound_Jcert_of_certifiedBlockCountAt
      (a := a) (Jcert := Jcert) (c := c) (hB c hc)
  · intro hJ c hc
    have hJ3 : EventuallyLogLowerBound Jcert (3 * c) := hJ (3 * c) (by positivity)
    exact eventuallyLogLowerBound_certifiedBlockCountAt_of_Jcert
      (a := a) hpos (Jcert := Jcert)
      (c := 3 * c) (c' := c) hJ3 (by nlinarith)

/-- Under both abstract prefix criteria, super-logarithmic certified block count
is equivalent to shifted subexponential `Qlog` growth. -/
theorem superLogLower_B_iff_shiftedSubexpUpper_of_prefixCriteria
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hforward : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hreverse : CertifiedPrefixReverseCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa) :
    SuperLogLowerBound (certifiedBlockCountAt a Jcert) ↔
      EventuallyShiftedSubexponentialQlogUpperBound Qlog shift := by
  constructor
  · intro hB
    have hJ : SuperLogLowerBound Jcert :=
      (superLogLower_certifiedBlockCountAt_iff_Jcert (a := a) hpos).mp hB
    exact (superLogLower_Jcert_iff_shiftedSubexpUpper_of_prefixCriteria
      (Qlog := Qlog) (Jcert := Jcert)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hforward hreverse hkappa).mp hJ
  · intro hsub
    have hJ : SuperLogLowerBound Jcert :=
      (superLogLower_Jcert_iff_shiftedSubexpUpper_of_prefixCriteria
        (Qlog := Qlog) (Jcert := Jcert)
        (kappa := kappa) (C0 := C0) (shift := shift)
        hforward hreverse hkappa).mpr hsub
    exact (superLogLower_certifiedBlockCountAt_iff_Jcert (a := a) hpos).mpr hJ

theorem superLogLower_B_oneOverPi_iff_shiftedSubexpUpper_of_prefixCriteria
    {Qlog : ℕ → ℝ} {kappa C0 : ℝ} {shift : ℕ}
    (hforward : CertifiedPrefixCriterion Qlog J_oneOverPi kappa C0 shift)
    (hreverse : CertifiedPrefixReverseCriterion Qlog J_oneOverPi kappa C0 shift)
    (hkappa : 0 < kappa) :
    SuperLogLowerBound B_oneOverPi ↔
      EventuallyShiftedSubexponentialQlogUpperBound Qlog shift := by
  simpa [B_oneOverPi] using
    superLogLower_B_iff_shiftedSubexpUpper_of_prefixCriteria
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      (Qlog := Qlog) (Jcert := J_oneOverPi)
      (kappa := kappa) (C0 := C0) (shift := shift)
      hforward hreverse hkappa

/-- Safe one-way result for extracted-cardinality production.  We intentionally
do not state a reverse equivalence for extracted cardinality: one long block can
make the extracted set large without forcing many certified blocks. -/
theorem shiftedSubexpUpper_implies_superLogLower_certifiedCard_of_prefixCriterion
    {a : ℕ → ℕ} (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Qlog : ℕ → ℝ} {Jcert : ℕ → ℕ}
    {kappa C0 : ℝ} {shift : ℕ}
    (hforward : CertifiedPrefixCriterion Qlog Jcert kappa C0 shift)
    (hkappa : 0 < kappa)
    (hsub : EventuallyShiftedSubexponentialQlogUpperBound Qlog shift) :
    SuperLogLowerBound (certifiedOddBlocksCardAt a Jcert) :=
  prefixCriterion_shiftedSubexpUpper_implies_superLogLower_certifiedOddBlocksCardAt
    (a := a) hpos (Qlog := Qlog) (Jcert := Jcert)
    (kappa := kappa) (C0 := C0) (shift := shift)
    hforward hkappa hsub

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanPartialPathCertification.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Partial Farey-path certification interface

This file isolates the finite Farey/Stern--Brocot layer suggested by the
Ramanujan bottleneck plan.  The point is deliberately modest: we formalize the
deterministic path state and the denominator-minimality facts that do not rely
on any unproved Ramanujan tail or Kummer estimates.

The heavy analytic inputs are intentionally not asserted here.
-/

/-! ## Rational intervals and least denominators -/

/-- The rational `p / q` lies in the closed real interval `[L, U]`. -/
def RatInClosedInterval (L U : ℝ) (p : ℤ) (q : ℕ) : Prop :=
  0 < q ∧ L ≤ (p : ℝ) / (q : ℝ) ∧ (p : ℝ) / (q : ℝ) ≤ U

/-- A rational in `[L, U]` whose denominator is minimal among all rationals in
that closed interval. -/
def LeastDenominatorInInterval (L U : ℝ) (p : ℤ) (q : ℕ) : Prop :=
  RatInClosedInterval L U p q ∧
    ∀ p' : ℤ, ∀ q' : ℕ, RatInClosedInterval L U p' q' → q ≤ q'

theorem LeastDenominatorInInterval.ratIn {L U : ℝ} {p : ℤ} {q : ℕ}
    (h : LeastDenominatorInInterval L U p q) :
    RatInClosedInterval L U p q :=
  h.1

theorem LeastDenominatorInInterval.den_pos {L U : ℝ} {p : ℤ} {q : ℕ}
    (h : LeastDenominatorInInterval L U p q) :
    0 < q :=
  h.1.1

theorem LeastDenominatorInInterval.den_le {L U : ℝ} {p p' : ℤ} {q q' : ℕ}
    (h : LeastDenominatorInInterval L U p q)
    (h' : RatInClosedInterval L U p' q') :
    q ≤ q' :=
  h.2 p' q' h'

theorem LeastDenominatorInInterval.den_eq_of_two_least
    {L U : ℝ} {p p' : ℤ} {q q' : ℕ}
    (h : LeastDenominatorInInterval L U p q)
    (h' : LeastDenominatorInInterval L U p' q') :
    q = q' :=
  le_antisymm (h.den_le h'.ratIn) (h'.den_le h.ratIn)

/-- A rational number, viewed directly as a point of `[L, U]`. -/
def RatInClosedIntervalQ (L U : ℝ) (r : ℚ) : Prop :=
  L ≤ (r : ℝ) ∧ (r : ℝ) ≤ U

theorem ratInClosedInterval_of_ratInClosedIntervalQ
    {L U : ℝ} {r : ℚ} (hr : RatInClosedIntervalQ L U r) :
    RatInClosedInterval L U r.num r.den := by
  refine ⟨r.den_pos, ?_, ?_⟩
  · simpa [RatInClosedIntervalQ, Rat.cast_def] using hr.1
  · simpa [RatInClosedIntervalQ, Rat.cast_def] using hr.2

theorem exists_ratInClosedInterval_of_lt {L U : ℝ} (hLU : L < U) :
    ∃ p : ℤ, ∃ q : ℕ, RatInClosedInterval L U p q := by
  rcases exists_rat_btwn hLU with ⟨r, hLr, hrU⟩
  exact ⟨r.num, r.den,
    ratInClosedInterval_of_ratInClosedIntervalQ
      (r := r) ⟨hLr.le, hrU.le⟩⟩

/-- A denominator occurs among rationals in `[L, U]`. -/
def DenominatorInInterval (L U : ℝ) (q : ℕ) : Prop :=
  ∃ p : ℤ, RatInClosedInterval L U p q

theorem exists_denominatorInInterval_of_lt {L U : ℝ} (hLU : L < U) :
    ∃ q : ℕ, DenominatorInInterval L U q := by
  rcases exists_ratInClosedInterval_of_lt hLU with ⟨p, q, hpq⟩
  exact ⟨q, p, hpq⟩

/-- The least denominator of a rational in a nontrivial interval. -/
noncomputable def leastDenominatorInInterval
    (L U : ℝ) (hLU : L < U) : ℕ := by
  classical
  exact Nat.find (exists_denominatorInInterval_of_lt hLU)

theorem leastDenominatorInInterval_spec {L U : ℝ} (hLU : L < U) :
    DenominatorInInterval L U (leastDenominatorInInterval L U hLU) := by
  classical
  unfold leastDenominatorInInterval
  exact Nat.find_spec (exists_denominatorInInterval_of_lt hLU)

theorem leastDenominatorInInterval_min
    {L U : ℝ} (hLU : L < U)
    {q : ℕ} (hq : DenominatorInInterval L U q) :
    leastDenominatorInInterval L U hLU ≤ q := by
  classical
  unfold leastDenominatorInInterval
  exact Nat.find_min' (exists_denominatorInInterval_of_lt hLU) hq

theorem exists_leastDenominatorInInterval {L U : ℝ} (hLU : L < U) :
    ∃ p : ℤ, ∃ q : ℕ, LeastDenominatorInInterval L U p q := by
  let q0 := leastDenominatorInInterval L U hLU
  have hq0 : DenominatorInInterval L U q0 :=
    leastDenominatorInInterval_spec hLU
  rcases hq0 with ⟨p0, hp0⟩
  refine ⟨p0, q0, hp0, ?_⟩
  intro p q hpq
  exact leastDenominatorInInterval_min hLU ⟨p, hpq⟩

theorem leastDenominatorInInterval_pos {L U : ℝ} (hLU : L < U) :
    0 < leastDenominatorInInterval L U hLU := by
  rcases leastDenominatorInInterval_spec hLU with ⟨p, hp⟩
  exact hp.1

theorem leastDenominatorInInterval_real_pos {L U : ℝ} (hLU : L < U) :
    0 < (leastDenominatorInInterval L U hLU : ℝ) := by
  exact_mod_cast leastDenominatorInInterval_pos hLU

/-! ## Farey frames -/

/-- A finite Farey/Stern--Brocot state.  It records two neighboring fractions
`lp / lq < rp / rq` via the determinant identity `lq * rp = lp * rq + 1`. -/
structure FareyFrame where
  lp : ℕ
  lq : ℕ
  rp : ℕ
  rq : ℕ
  lq_pos : 0 < lq
  rq_pos : 0 < rq
  det_one : lq * rp = lp * rq + 1

namespace FareyFrame

/-- Left endpoint value of a Farey frame. -/
noncomputable def leftValue (F : FareyFrame) : ℝ :=
  ratValue F.lp F.lq

/-- Right endpoint value of a Farey frame. -/
noncomputable def rightValue (F : FareyFrame) : ℝ :=
  ratValue F.rp F.rq

/-- Numerator of the frame mediant. -/
def medNum (F : FareyFrame) : ℕ :=
  F.lp + F.rp

/-- Denominator of the frame mediant. -/
def medDen (F : FareyFrame) : ℕ :=
  F.lq + F.rq

@[simp] theorem medNum_eq (F : FareyFrame) :
    F.medNum = F.lp + F.rp :=
  rfl

@[simp] theorem medDen_eq (F : FareyFrame) :
    F.medDen = F.lq + F.rq :=
  rfl

theorem medDen_pos (F : FareyFrame) :
    0 < F.medDen := by
  dsimp [medDen]
  exact lt_of_lt_of_le F.lq_pos (Nat.le_add_right F.lq F.rq)

theorem lq_lt_medDen (F : FareyFrame) :
    F.lq < F.medDen := by
  dsimp [medDen]
  exact Nat.lt_add_of_pos_right F.rq_pos

theorem rq_lt_medDen (F : FareyFrame) :
    F.rq < F.medDen := by
  dsimp [medDen]
  have h : F.rq < F.rq + F.lq := Nat.lt_add_of_pos_right F.lq_pos
  simpa [Nat.add_comm] using h

theorem left_mul_right_den_lt_right_mul_left_den (F : FareyFrame) :
    F.lp * F.rq < F.rp * F.lq := by
  have hlt : F.lp * F.rq < F.lq * F.rp := by
    rw [F.det_one]
    exact Nat.lt_succ_self (F.lp * F.rq)
  simpa [Nat.mul_comm] using hlt

theorem leftValue_lt_rightValue (F : FareyFrame) :
    F.leftValue < F.rightValue := by
  unfold leftValue rightValue ratValue
  have hlqR : (0 : ℝ) < F.lq := by exact_mod_cast F.lq_pos
  have hrqR : (0 : ℝ) < F.rq := by exact_mod_cast F.rq_pos
  rw [div_lt_div_iff₀ hlqR hrqR]
  have hnat := F.left_mul_right_den_lt_right_mul_left_den
  have hreal : (F.lp : ℝ) * (F.rq : ℝ) <
      (F.rp : ℝ) * (F.lq : ℝ) := by
    exact_mod_cast hnat
  simpa [mul_comm, mul_left_comm, mul_assoc] using hreal

theorem leftValue_lt_mediant (F : FareyFrame) :
    F.leftValue < ratValue F.medNum F.medDen := by
  unfold leftValue ratValue medNum medDen
  have hlqR : (0 : ℝ) < F.lq := by exact_mod_cast F.lq_pos
  have hmedR : (0 : ℝ) < F.lq + F.rq := by
    exact_mod_cast F.medDen_pos
  push_cast
  rw [div_lt_div_iff₀ hlqR hmedR]
  have hnat := F.left_mul_right_den_lt_right_mul_left_den
  have hreal : (F.lp : ℝ) * ((F.lq : ℝ) + (F.rq : ℝ)) <
      ((F.lp : ℝ) + (F.rp : ℝ)) * (F.lq : ℝ) := by
    nlinarith [show (F.lp : ℝ) * (F.rq : ℝ) <
        (F.rp : ℝ) * (F.lq : ℝ) by exact_mod_cast hnat]
  simpa [Nat.cast_add, mul_comm, mul_left_comm, mul_assoc] using hreal

theorem mediant_lt_rightValue (F : FareyFrame) :
    ratValue F.medNum F.medDen < F.rightValue := by
  unfold rightValue ratValue medNum medDen
  have hmedR : (0 : ℝ) < F.lq + F.rq := by
    exact_mod_cast F.medDen_pos
  have hrqR : (0 : ℝ) < F.rq := by exact_mod_cast F.rq_pos
  push_cast
  rw [div_lt_div_iff₀ hmedR hrqR]
  have hnat := F.left_mul_right_den_lt_right_mul_left_den
  have hreal : ((F.lp : ℝ) + (F.rp : ℝ)) * (F.rq : ℝ) <
      (F.rp : ℝ) * ((F.lq : ℝ) + (F.rq : ℝ)) := by
    nlinarith [show (F.lp : ℝ) * (F.rq : ℝ) <
        (F.rp : ℝ) * (F.lq : ℝ) by exact_mod_cast hnat]
  simpa [Nat.cast_add, mul_comm, mul_left_comm, mul_assoc] using hreal

theorem mediant_between (F : FareyFrame) :
    F.leftValue < ratValue F.medNum F.medDen ∧
      ratValue F.medNum F.medDen < F.rightValue :=
  ⟨F.leftValue_lt_mediant, F.mediant_lt_rightValue⟩

theorem medNum_coprime_medDen (F : FareyFrame) :
    Nat.Coprime F.medNum F.medDen := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g : ℕ := Nat.gcd F.medNum F.medDen
  have hg_num : g ∣ F.medNum := Nat.gcd_dvd_left _ _
  have hg_den : g ∣ F.medDen := Nat.gcd_dvd_right _ _
  have hg_numZ : (g : ℤ) ∣ (F.medNum : ℤ) := by
    exact_mod_cast hg_num
  have hg_denZ : (g : ℤ) ∣ (F.medDen : ℤ) := by
    exact_mod_cast hg_den
  have hfareyZ :
      (F.lq : ℤ) * (F.rp : ℤ) - (F.lp : ℤ) * (F.rq : ℤ) = 1 := by
    have h : (F.lq : ℤ) * (F.rp : ℤ) =
        (F.lp : ℤ) * (F.rq : ℤ) + 1 := by
      exact_mod_cast F.det_one
    omega
  have hmedZ :
      (F.medDen : ℤ) * (F.rp : ℤ) -
        (F.medNum : ℤ) * (F.rq : ℤ) = 1 := by
    calc
      (F.medDen : ℤ) * (F.rp : ℤ) -
          (F.medNum : ℤ) * (F.rq : ℤ)
          = (F.lq : ℤ) * (F.rp : ℤ) -
              (F.lp : ℤ) * (F.rq : ℤ) := by
              simp [medDen, medNum]
              ring
      _ = 1 := hfareyZ
  have hg_oneZ : (g : ℤ) ∣ (1 : ℤ) := by
    rw [← hmedZ]
    exact dvd_sub
      (dvd_mul_of_dvd_left hg_denZ _)
      (dvd_mul_of_dvd_left hg_numZ _)
  have hg_one : g ∣ 1 := by
    exact_mod_cast hg_oneZ
  exact Nat.dvd_one.mp hg_one

theorem mediant_reduced (F : FareyFrame) :
    ReducedFraction F.medNum F.medDen :=
  ⟨F.medDen_pos, F.medNum_coprime_medDen⟩

/-- Replace the left endpoint by the mediant. -/
def updateLeft (F : FareyFrame) : FareyFrame where
  lp := F.medNum
  lq := F.medDen
  rp := F.rp
  rq := F.rq
  lq_pos := F.medDen_pos
  rq_pos := F.rq_pos
  det_one := by
    dsimp [medNum, medDen]
    calc
      (F.lq + F.rq) * F.rp = F.lq * F.rp + F.rq * F.rp := by
        rw [Nat.add_mul]
      _ = (F.lp * F.rq + 1) + F.rq * F.rp := by
        rw [F.det_one]
      _ = (F.lp + F.rp) * F.rq + 1 := by
        ring

/-- Replace the right endpoint by the mediant. -/
def updateRight (F : FareyFrame) : FareyFrame where
  lp := F.lp
  lq := F.lq
  rp := F.medNum
  rq := F.medDen
  lq_pos := F.lq_pos
  rq_pos := F.medDen_pos
  det_one := by
    dsimp [medNum, medDen]
    calc
      F.lq * (F.lp + F.rp) = F.lq * F.lp + F.lq * F.rp := by
        rw [Nat.mul_add]
      _ = F.lq * F.lp + (F.lp * F.rq + 1) := by
        rw [F.det_one]
      _ = F.lp * (F.lq + F.rq) + 1 := by
        ring

@[simp] theorem updateLeft_lp (F : FareyFrame) :
    F.updateLeft.lp = F.medNum :=
  rfl

@[simp] theorem updateLeft_lq (F : FareyFrame) :
    F.updateLeft.lq = F.medDen :=
  rfl

@[simp] theorem updateLeft_rp (F : FareyFrame) :
    F.updateLeft.rp = F.rp :=
  rfl

@[simp] theorem updateLeft_rq (F : FareyFrame) :
    F.updateLeft.rq = F.rq :=
  rfl

@[simp] theorem updateRight_lp (F : FareyFrame) :
    F.updateRight.lp = F.lp :=
  rfl

@[simp] theorem updateRight_lq (F : FareyFrame) :
    F.updateRight.lq = F.lq :=
  rfl

@[simp] theorem updateRight_rp (F : FareyFrame) :
    F.updateRight.rp = F.medNum :=
  rfl

@[simp] theorem updateRight_rq (F : FareyFrame) :
    F.updateRight.rq = F.medDen :=
  rfl

/-- Any positive-denominator rational strictly between the frame endpoints has
denominator at least the mediant denominator. -/
theorem medDen_le_of_between {F : FareyFrame} {x y : ℕ}
    (hy : 0 < y)
    (hbetween :
      F.leftValue < ratValue x y ∧ ratValue x y < F.rightValue) :
    F.medDen ≤ y := by
  simpa [medDen, leftValue, rightValue] using
    farey_neighbor_denominator_lower_bound
      F.lq_pos F.rq_pos hy F.det_one hbetween

/-- Any natural rational lying in an interval strictly inside the Farey frame
has denominator at least the frame mediant denominator.  This is the finite
denominator-minimality statement used before moving to signed/reduced
rational endpoints. -/
theorem medDen_le_of_natRatInClosedInterval
    {F : FareyFrame} {L U : ℝ} {p q : ℕ}
    (hleft : F.leftValue < L)
    (hright : U < F.rightValue)
    (hpq : RatInClosedInterval L U (p : ℤ) q) :
    F.medDen ≤ q := by
  have hqpos : 0 < q := hpq.1
  have hbetween :
      F.leftValue < ratValue p q ∧ ratValue p q < F.rightValue := by
    unfold ratValue
    constructor
    · have hL : F.leftValue < ((p : ℤ) : ℝ) / (q : ℝ) :=
        lt_of_lt_of_le hleft hpq.2.1
      simpa using hL
    · have hU : ((p : ℤ) : ℝ) / (q : ℝ) < F.rightValue :=
        lt_of_le_of_lt hpq.2.2 hright
      simpa using hU
  exact F.medDen_le_of_between hqpos hbetween

/-- The initial frame `0/1 < 1/1`, used for numbers in `(0,1)`. -/
def initialUnit : FareyFrame where
  lp := 0
  lq := 1
  rp := 1
  rq := 1
  lq_pos := by norm_num
  rq_pos := by norm_num
  det_one := by norm_num

/-- A single Stern--Brocot step.  `left` means replace the left endpoint by
the mediant; `right` means replace the right endpoint by the mediant. -/
inductive Step where
  | left
  | right
  deriving DecidableEq, Repr

/-- Apply one Stern--Brocot update to a frame. -/
def step (F : FareyFrame) : Step → FareyFrame
  | Step.left => F.updateLeft
  | Step.right => F.updateRight

/-- The finite list of mediants visited while following a list of updates. -/
def visitedMediants : FareyFrame → List Step → List (ℕ × ℕ)
  | F, [] => [(F.medNum, F.medDen)]
  | F, s :: ss => (F.medNum, F.medDen) :: visitedMediants (F.step s) ss

theorem visitedMediants_nil (F : FareyFrame) :
    visitedMediants F [] = [(F.medNum, F.medDen)] :=
  rfl

theorem visitedMediants_cons (F : FareyFrame) (s : Step) (ss : List Step) :
    visitedMediants F (s :: ss) =
      (F.medNum, F.medDen) :: visitedMediants (F.step s) ss :=
  rfl

theorem visitedMediants_reduced
    {F : FareyFrame} {steps : List Step} {pair : ℕ × ℕ}
    (hpair : pair ∈ visitedMediants F steps) :
    ReducedFraction pair.1 pair.2 := by
  induction steps generalizing F with
  | nil =>
      simp [visitedMediants] at hpair
      rcases hpair with rfl
      exact F.mediant_reduced
  | cons s ss ih =>
      simp [visitedMediants] at hpair
      rcases hpair with hpair | hpair
      · rcases hpair with rfl
        exact F.mediant_reduced
      · exact ih (F := F.step s) hpair

/-! ## Fibonacci denominator bounds for finite Stern--Brocot paths -/

/-- A loose Fibonacci upper bound for the two endpoint denominators of a frame.
The shift is chosen to make the initial `0/1, 1/1` frame start at `k = 0`. -/
def FibDenBound (F : FareyFrame) (k : ℕ) : Prop :=
  Nat.min F.lq F.rq ≤ Nat.fib (k + 2) ∧
    Nat.max F.lq F.rq ≤ Nat.fib (k + 3)

theorem initialUnit_fibDenBound :
    initialUnit.FibDenBound 0 := by
  norm_num [FibDenBound, initialUnit, Nat.fib]

theorem add_le_min_max_bound {a b A B : ℕ}
    (hmin : Nat.min a b ≤ A)
    (hmax : Nat.max a b ≤ B) :
    a + b ≤ A + B := by
  by_cases h : a ≤ b
  · have ha : a ≤ A := by simpa [min_eq_left h] using hmin
    have hb : b ≤ B := by simpa [max_eq_right h] using hmax
    exact Nat.add_le_add ha hb
  · have hba : b ≤ a := le_of_lt (Nat.lt_of_not_ge h)
    have hb : b ≤ A := by simpa [min_eq_right hba] using hmin
    have ha : a ≤ B := by simpa [max_eq_left hba] using hmax
    simpa [Nat.add_comm] using Nat.add_le_add hb ha

private theorem fib_succ_pair_add (k : ℕ) :
    Nat.fib (k + 2) + Nat.fib (k + 3) = Nat.fib (k + 4) := by
  have h := (Nat.fib_add_two (n := k + 2))
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

theorem FibDenBound.updateLeft {F : FareyFrame} {k : ℕ}
    (hF : F.FibDenBound k) :
    F.updateLeft.FibDenBound (k + 1) := by
  constructor
  · have hmin :
        Nat.min F.updateLeft.lq F.updateLeft.rq ≤ Nat.max F.lq F.rq := by
      exact (Nat.min_le_right _ _).trans (le_max_right _ _)
    have hmax : Nat.max F.lq F.rq ≤ Nat.fib ((k + 1) + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF.2
    exact hmin.trans hmax
  · have hnew :
        Nat.max F.updateLeft.lq F.updateLeft.rq ≤ F.lq + F.rq := by
      apply max_le
      · rfl
      · exact Nat.le_add_left F.rq F.lq
    have hsum : F.lq + F.rq ≤ Nat.fib (k + 2) + Nat.fib (k + 3) :=
      add_le_min_max_bound hF.1 hF.2
    exact hnew.trans (hsum.trans (by rw [fib_succ_pair_add k]))

theorem FibDenBound.updateRight {F : FareyFrame} {k : ℕ}
    (hF : F.FibDenBound k) :
    F.updateRight.FibDenBound (k + 1) := by
  constructor
  · have hmin :
        Nat.min F.updateRight.lq F.updateRight.rq ≤ Nat.max F.lq F.rq := by
      exact (Nat.min_le_left _ _).trans (le_max_left _ _)
    have hmax : Nat.max F.lq F.rq ≤ Nat.fib ((k + 1) + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF.2
    exact hmin.trans hmax
  · have hnew :
        Nat.max F.updateRight.lq F.updateRight.rq ≤ F.lq + F.rq := by
      apply max_le
      · exact Nat.le_add_right F.lq F.rq
      · rfl
    have hsum : F.lq + F.rq ≤ Nat.fib (k + 2) + Nat.fib (k + 3) :=
      add_le_min_max_bound hF.1 hF.2
    exact hnew.trans (hsum.trans (by rw [fib_succ_pair_add k]))

theorem medDen_le_fib_of_fibDenBound {F : FareyFrame} {k : ℕ}
    (hF : F.FibDenBound k) :
    F.medDen ≤ Nat.fib (k + 4) := by
  have hsum : F.lq + F.rq ≤ Nat.fib (k + 2) + Nat.fib (k + 3) :=
    add_le_min_max_bound hF.1 hF.2
  dsimp [medDen]
  exact hsum.trans (by rw [fib_succ_pair_add k])

/-- The frame obtained after a finite list of Stern--Brocot moves. -/
def afterMoves : FareyFrame → List Step → FareyFrame
  | F, [] => F
  | F, s :: ss => afterMoves (F.step s) ss

@[simp] theorem afterMoves_nil (F : FareyFrame) :
    F.afterMoves [] = F :=
  rfl

@[simp] theorem afterMoves_cons (F : FareyFrame) (s : Step) (ss : List Step) :
    F.afterMoves (s :: ss) = (F.step s).afterMoves ss :=
  rfl

theorem FibDenBound.afterMoves
    {F : FareyFrame} {moves : List Step} {k : ℕ}
    (hF : F.FibDenBound k) :
    (F.afterMoves moves).FibDenBound (k + moves.length) := by
  induction moves generalizing F k with
  | nil =>
      simpa using hF
  | cons s ss ih =>
      cases s
      · simpa [afterMoves, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (F := F.updateLeft) (k := k + 1) hF.updateLeft
      · simpa [afterMoves, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (F := F.updateRight) (k := k + 1) hF.updateRight

theorem medDen_afterMoves_le_fib (moves : List Step) :
    (initialUnit.afterMoves moves).medDen ≤ Nat.fib (moves.length + 4) := by
  have hbound :
      (initialUnit.afterMoves moves).FibDenBound (0 + moves.length) :=
    initialUnit_fibDenBound.afterMoves (moves := moves)
  have hmed := medDen_le_fib_of_fibDenBound hbound
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmed

/-! ## Least denominator versus a finite path hit -/

/-- The mediant of a frame lies in the interval `[L, U]`. -/
def MediantInInterval (F : FareyFrame) (L U : ℝ) : Prop :=
  L ≤ ratValue F.medNum F.medDen ∧ ratValue F.medNum F.medDen ≤ U

theorem leastDenominatorInInterval_le_hitMedDen
    {L U : ℝ} (hLU : L < U) {moves : List Step}
    (hhit : (initialUnit.afterMoves moves).MediantInInterval L U) :
    leastDenominatorInInterval L U hLU ≤
      (initialUnit.afterMoves moves).medDen := by
  apply leastDenominatorInInterval_min hLU
  refine ⟨((initialUnit.afterMoves moves).medNum : ℤ), ?_⟩
  refine ⟨(initialUnit.afterMoves moves).medDen_pos, ?_, ?_⟩
  · simpa [MediantInInterval, ratValue] using hhit.1
  · simpa [MediantInInterval, ratValue] using hhit.2

theorem leastDenominatorInInterval_le_fib_of_mediantHit
    {L U : ℝ} (hLU : L < U) {moves : List Step}
    (hhit : (initialUnit.afterMoves moves).MediantInInterval L U) :
    leastDenominatorInInterval L U hLU ≤ Nat.fib (moves.length + 4) :=
  (leastDenominatorInInterval_le_hitMedDen hLU hhit).trans
    (medDen_afterMoves_le_fib moves)

private theorem fib_le_two_pow : ∀ n : ℕ, Nat.fib n ≤ 2 ^ n
  | 0 => by simp [Nat.fib]
  | 1 => by simp [Nat.fib]
  | n + 2 => by
      rw [Nat.fib_add_two]
      have hn : Nat.fib n ≤ 2 ^ n := fib_le_two_pow n
      have hn1 : Nat.fib (n + 1) ≤ 2 ^ (n + 1) :=
        fib_le_two_pow (n + 1)
      calc
        Nat.fib n + Nat.fib (n + 1)
            ≤ 2 ^ n + 2 ^ (n + 1) := Nat.add_le_add hn hn1
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by
          exact Nat.add_le_add_right
            (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_succ n))
            (2 ^ (n + 1))
        _ = 2 ^ (n + 2) := by
          rw [← two_mul, pow_succ']
          ring

/-- Fibonacci numbers are bounded by powers of the golden ratio.  This avoids
Binet's formula and only uses the recurrence plus `φ² = φ + 1`. -/
theorem natFib_le_goldenRatio_pow : ∀ n : ℕ,
    (Nat.fib n : ℝ) ≤ Real.goldenRatio ^ n
  | 0 => by simp [Nat.fib]
  | 1 => by
      simpa [Nat.fib] using (le_of_lt Real.one_lt_goldenRatio)
  | n + 2 => by
      rw [Nat.fib_add_two]
      have hn : (Nat.fib n : ℝ) ≤ Real.goldenRatio ^ n :=
        natFib_le_goldenRatio_pow n
      have hn1 : (Nat.fib (n + 1) : ℝ) ≤ Real.goldenRatio ^ (n + 1) :=
        natFib_le_goldenRatio_pow (n + 1)
      have hpow :
          Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n =
            Real.goldenRatio ^ (n + 2) := by
        calc
          Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n
              = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by
                  rw [pow_succ]
                  ring
          _ = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by
                  rw [Real.goldenRatio_sq]
          _ = Real.goldenRatio ^ (n + 2) := by
                   rw [pow_add]
      calc
        ((Nat.fib n + Nat.fib (n + 1) : ℕ) : ℝ)
            = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by norm_num
        _ ≤ Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) :=
            add_le_add hn hn1
        _ = Real.goldenRatio ^ (n + 2) := by
            rw [add_comm, hpow]

theorem log_le_of_le_fib_hit_two
    {L U : ℝ} (hLU : L < U) {moves : List Step}
    (hhit : (initialUnit.afterMoves moves).MediantInInterval L U) :
    Real.log (leastDenominatorInInterval L U hLU : ℝ)
      ≤ (moves.length + 4 : ℝ) * Real.log 2 := by
  have hleast_pos : 0 < leastDenominatorInInterval L U hLU := by
    rcases leastDenominatorInInterval_spec hLU with ⟨p, hp⟩
    exact hp.1
  have hleNat :
      leastDenominatorInInterval L U hLU ≤ 2 ^ (moves.length + 4) :=
    (leastDenominatorInInterval_le_fib_of_mediantHit hLU hhit).trans
      (fib_le_two_pow (moves.length + 4))
  have hleR :
      (leastDenominatorInInterval L U hLU : ℝ) ≤
        ((2 ^ (moves.length + 4) : ℕ) : ℝ) := by
    exact_mod_cast hleNat
  have hlog :
      Real.log (leastDenominatorInInterval L U hLU : ℝ) ≤
        Real.log (((2 ^ (moves.length + 4) : ℕ) : ℝ)) :=
    Real.log_le_log (leastDenominatorInInterval_real_pos hLU) hleR
  simpa [Nat.cast_pow, Real.log_pow] using hlog

theorem log_le_of_le_fib_hit_phi
    {L U : ℝ} (hLU : L < U) {moves : List Step}
    (hhit : (initialUnit.afterMoves moves).MediantInInterval L U) :
    Real.log (leastDenominatorInInterval L U hLU : ℝ)
      ≤ (moves.length : ℝ) * Real.log Real.goldenRatio +
          4 * Real.log Real.goldenRatio := by
  have hq_fib_nat :
      leastDenominatorInInterval L U hLU ≤ Nat.fib (moves.length + 4) :=
    leastDenominatorInInterval_le_fib_of_mediantHit hLU hhit
  have hq_fib :
      (leastDenominatorInInterval L U hLU : ℝ) ≤
        (Nat.fib (moves.length + 4) : ℝ) := by
    exact_mod_cast hq_fib_nat
  have hfib_phi :
      (Nat.fib (moves.length + 4) : ℝ) ≤
        Real.goldenRatio ^ (moves.length + 4) :=
    natFib_le_goldenRatio_pow (moves.length + 4)
  have hq_phi :
      (leastDenominatorInInterval L U hLU : ℝ) ≤
        Real.goldenRatio ^ (moves.length + 4) :=
    hq_fib.trans hfib_phi
  have hlog :
      Real.log (leastDenominatorInInterval L U hLU : ℝ) ≤
        Real.log (Real.goldenRatio ^ (moves.length + 4)) :=
    Real.log_le_log (leastDenominatorInInterval_real_pos hLU) hq_phi
  calc
    Real.log (leastDenominatorInInterval L U hLU : ℝ)
        ≤ Real.log (Real.goldenRatio ^ (moves.length + 4)) := hlog
    _ = ((moves.length + 4 : ℕ) : ℝ) * Real.log Real.goldenRatio := by
        rw [Real.log_pow]
    _ = (moves.length : ℝ) * Real.log Real.goldenRatio +
          4 * Real.log Real.goldenRatio := by
        norm_num [Nat.cast_add, add_mul]

theorem exists_C_log_le_of_le_fib_hit_phi
    {L U : ℝ} (hLU : L < U) {moves : List Step}
    (hhit : (initialUnit.afterMoves moves).MediantInInterval L U) :
    ∃ C : ℝ,
      Real.log (leastDenominatorInInterval L U hLU : ℝ)
        ≤ (moves.length : ℝ) * Real.log Real.goldenRatio + C := by
  refine ⟨4 * Real.log Real.goldenRatio, ?_⟩
  exact log_le_of_le_fib_hit_phi hLU hhit

end FareyFrame

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanMeasureWidthBridge.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Measure/width bridge for partial Farey paths

This file connects a certified interval width bound with the upper-failure
clause in the literal irrationality-measure predicate.  The small-denominator
exclusion is kept as an explicit hypothesis; proving it from shrinking
irrational intervals is a separate finite compactness step.
-/

/-- Least denominator in the `m`-th certified interval. -/
noncomputable def leastDenominatorInIntervalSeq
    (L U : ℕ → ℝ) (hLU : ∀ m : ℕ, L m < U m) (m : ℕ) : ℕ :=
  leastDenominatorInInterval (L m) (U m) (hLU m)

@[simp] theorem leastDenominatorInIntervalSeq_def
    (L U : ℕ → ℝ) (hLU : ∀ m : ℕ, L m < U m) (m : ℕ) :
    leastDenominatorInIntervalSeq L U hLU m =
      leastDenominatorInInterval (L m) (U m) (hLU m) :=
  rfl

theorem leastDenominatorInIntervalSeq_pos
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m} (m : ℕ) :
    0 < leastDenominatorInIntervalSeq L U hLU m := by
  simpa [leastDenominatorInIntervalSeq] using
    leastDenominatorInInterval_pos (L := L m) (U := U m) (hLU m)

theorem leastDenominatorInIntervalSeq_real_pos
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m} (m : ℕ) :
    (0 : ℝ) < (leastDenominatorInIntervalSeq L U hLU m : ℝ) := by
  exact_mod_cast leastDenominatorInIntervalSeq_pos
    (L := L) (U := U) (hLU := hLU) m

/-- Eventually the interval `[L m, U m]` contains `α`. -/
def EventuallyAlphaInInterval (α : ℝ) (L U : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, L m ≤ α ∧ α ≤ U m

/-- Eventually the interval width has exponential upper bound
`U_m - L_m ≤ exp(-κ m + C)`. -/
def EventuallyExpWidthUpper (L U : ℕ → ℝ) (κ C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    U m - L m ≤ Real.exp (-(κ * (m : ℝ)) + C)

/-- Eventually the least denominator in `[L m, U m]` is at least `Q0`. -/
def EventuallyLeastDenominatorGe
    (L U : ℕ → ℝ) (hLU : ∀ m : ℕ, L m < U m) (Q0 : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    Q0 ≤ leastDenominatorInIntervalSeq L U hLU m

/-- The certified intervals shrink to `α`; the containment predicate is kept
because later width-only applications often already prove it separately. -/
def EventuallyIntervalShrinksTo (α : ℝ) (L U : ℕ → ℝ) : Prop :=
  Tendsto L atTop (𝓝 α) ∧ Tendsto U atTop (𝓝 α) ∧
    EventuallyAlphaInInterval α L U

theorem eventually_interval_subset_Ioo_of_intervalShrinksTo
    {α a b : ℝ} {L U : ℕ → ℝ}
    (hshrink : EventuallyIntervalShrinksTo α L U)
    (ha : a < α) (hb : α < b) :
    ∀ᶠ m : ℕ in atTop, a < L m ∧ U m < b := by
  rcases hshrink with ⟨hL, hU, _hcontains⟩
  filter_upwards
      [hL.eventually (eventually_gt_nhds ha),
        hU.eventually (eventually_lt_nhds hb)]
      with m hmL hmU
  exact ⟨hmL, hmU⟩

private theorem eventually_excludes_fixed_denominator
    {α : ℝ} {L U : ℕ → ℝ}
    (hirr : IsIrrational α)
    (hshrink : EventuallyIntervalShrinksTo α L U)
    {q : ℕ} (hq : 0 < q) :
    ∀ᶠ m : ℕ in atTop,
      ∀ p : ℤ,
        ¬ (L m ≤ (p : ℝ) / (q : ℝ) ∧
           (p : ℝ) / (q : ℝ) ≤ U m) := by
  let z : ℤ := Int.floor ((q : ℝ) * α)
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hlo :
      (z : ℝ) / (q : ℝ) < α := by
    rw [div_lt_iff₀ hqR]
    dsimp [z]
    simpa [mul_comm] using
      floor_lt_of_not_int (mul_irrational_not_int hirr hq)
  have hhi :
      α < ((z + 1 : ℤ) : ℝ) / (q : ℝ) := by
    rw [lt_div_iff₀ hqR]
    dsimp [z]
    calc
      α * (q : ℝ) = (q : ℝ) * α := by ring
      _ < (Int.floor ((q : ℝ) * α) : ℝ) + 1 :=
        Int.lt_floor_add_one ((q : ℝ) * α)
      _ = ((Int.floor ((q : ℝ) * α) + 1 : ℤ) : ℝ) := by
        norm_num
  have hinside :
      ∀ᶠ m : ℕ in atTop,
        (z : ℝ) / (q : ℝ) < L m ∧
        U m < ((z + 1 : ℤ) : ℝ) / (q : ℝ) :=
    eventually_interval_subset_Ioo_of_intervalShrinksTo hshrink hlo hhi
  filter_upwards [hinside] with m hm
  intro p hp
  have hp_lower :
      (z : ℝ) < (p : ℝ) := by
    have hdiv :
        (z : ℝ) / (q : ℝ) <
          (p : ℝ) / (q : ℝ) :=
      lt_of_lt_of_le hm.1 hp.1
    exact (div_lt_div_iff_of_pos_right hqR).mp hdiv
  have hp_upper :
      (p : ℝ) < ((z + 1 : ℤ) : ℝ) := by
    have hdiv :
        (p : ℝ) / (q : ℝ) <
          ((z + 1 : ℤ) : ℝ) / (q : ℝ) :=
      lt_of_le_of_lt hp.2 hm.2
    exact (div_lt_div_iff_of_pos_right hqR).mp hdiv
  have hp_lower_int : z < p := by
    exact_mod_cast hp_lower
  have hp_upper_int : p < z + 1 := by
    exact_mod_cast hp_upper
  omega

private theorem eventually_forall_finset
    {ι β : Type*} {l : Filter β}
    (s : Finset ι) (P : β → ι → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x : β in l, P x i) :
    ∀ᶠ x : β in l, ∀ i ∈ s, P x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha_eventually : ∀ᶠ x : β in l, P x a :=
        hP a (by simp)
      have hs_eventually : ∀ᶠ x : β in l, ∀ i ∈ s, P x i :=
        ih (fun i hi => hP i (by simp [hi]))
      filter_upwards [ha_eventually, hs_eventually] with x hax hsx
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hax
      · exact hsx i hi

private theorem eventually_excludes_small_denominators
    {α : ℝ} {L U : ℕ → ℝ}
    (hirr : IsIrrational α)
    (hshrink : EventuallyIntervalShrinksTo α L U)
    (Q0 : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ q : ℕ, 0 < q → q < Q0 →
        ∀ p : ℤ,
          ¬ (L m ≤ (p : ℝ) / (q : ℝ) ∧
             (p : ℝ) / (q : ℝ) ≤ U m) := by
  classical
  have hfinite :
      ∀ᶠ m : ℕ in atTop,
        ∀ q ∈ Finset.Ico 1 Q0,
          ∀ p : ℤ,
            ¬ (L m ≤ (p : ℝ) / (q : ℝ) ∧
               (p : ℝ) / (q : ℝ) ≤ U m) := by
    apply eventually_forall_finset
    intro q hqmem
    have hqIco : 1 ≤ q ∧ q < Q0 := by
      simpa [Finset.mem_Ico] using hqmem
    have hqpos : 0 < q := by omega
    exact eventually_excludes_fixed_denominator hirr hshrink hqpos
  filter_upwards [hfinite] with m hm
  intro q hqpos hqQ0 p
  have hqone : 1 ≤ q := Nat.succ_le_iff.mpr hqpos
  exact hm q (by simp [Finset.mem_Ico, hqone, hqQ0]) p

theorem leastDenominatorInInterval_ge_of_no_smaller_denominator
    {L U : ℝ} {hLU : L < U} {Q0 : ℕ}
    (hno : ∀ q : ℕ, 0 < q → q < Q0 →
        ∀ p : ℤ,
          ¬ (L ≤ (p : ℝ) / (q : ℝ) ∧
             (p : ℝ) / (q : ℝ) ≤ U)) :
    Q0 ≤ leastDenominatorInInterval L U hLU := by
  by_contra hnot
  have hlt : leastDenominatorInInterval L U hLU < Q0 :=
    Nat.lt_of_not_ge hnot
  rcases leastDenominatorInInterval_spec hLU with ⟨p, hp⟩
  exact hno _ hp.1 hlt p hp.2

theorem eventuallyLeastDenominatorGe_of_intervalShrinksTo_irrational
    {α : ℝ} {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    (hirr : IsIrrational α)
    (hshrink : EventuallyIntervalShrinksTo α L U)
    (Q0 : ℕ) :
    EventuallyLeastDenominatorGe L U hLU Q0 := by
  unfold EventuallyLeastDenominatorGe
  have hsmall := eventually_excludes_small_denominators hirr hshrink Q0
  filter_upwards [hsmall] with m hm
  exact leastDenominatorInInterval_ge_of_no_smaller_denominator
    (hLU := hLU m)
    (by
      intro q hqpos hqQ0 p hp
      exact hm q hqpos hqQ0 p hp)

/-- A thresholded rational-approximation lower bound. -/
def RationalApproxLowerFrom (α ν : ℝ) (Q0 : ℕ) : Prop :=
  ∀ q : ℕ, Q0 ≤ q → ∀ p : ℤ, 0 < q →
    (q : ℝ) ^ (-ν) ≤ |α - (p : ℝ) / (q : ℝ)|

theorem eventually_measure_lower_bound_for_rationals
    {α μ ν : ℝ}
    (hμ : HasIrrationalityMeasure α μ)
    (hν : μ < ν) :
    ∀ᶠ q : ℕ in atTop,
      ∀ p : ℤ, 0 < q →
        (q : ℝ) ^ (-ν) ≤ |α - (p : ℝ) / (q : ℝ)| := by
  rcases hμ with ⟨_, hupper⟩
  have h := hupper ν hν
  filter_upwards [h] with q hq p hqpos
  exact le_of_not_gt (hq p hqpos)

theorem exists_rationalApproxLowerFrom_of_measure
    {α μ ν : ℝ}
    (hμ : HasIrrationalityMeasure α μ)
    (hν : μ < ν) :
    ∃ Q0 : ℕ, RationalApproxLowerFrom α ν Q0 := by
  have hEv := eventually_measure_lower_bound_for_rationals hμ hν
  rw [eventually_atTop] at hEv
  rcases hEv with ⟨Q0, hQ0⟩
  refine ⟨Q0, ?_⟩
  intro q hq p hqpos
  exact hQ0 q hq p hqpos

lemma abs_sub_le_width_of_two_points_in_interval
    {x y L U : ℝ}
    (hxL : L ≤ x) (hxU : x ≤ U)
    (hyL : L ≤ y) (hyU : y ≤ U) :
    |x - y| ≤ U - L := by
  have h1 : x - y ≤ U - L := by linarith
  have h2 : -(U - L) ≤ x - y := by linarith
  exact abs_le.mpr ⟨h2, h1⟩

theorem exists_int_num_for_leastDenominatorInInterval
    {L U : ℝ} (hLU : L < U) :
    ∃ p : ℤ,
      let q : ℕ := leastDenominatorInInterval L U hLU
      0 < q ∧ L ≤ (p : ℝ) / (q : ℝ) ∧
        (p : ℝ) / (q : ℝ) ≤ U := by
  rcases leastDenominatorInInterval_spec hLU with ⟨p, hp⟩
  exact ⟨p, hp⟩

theorem abs_alpha_sub_le_width_of_leastDenominator_spec
    {α L U : ℝ} {hLU : L < U}
    (hα : L ≤ α ∧ α ≤ U) :
    ∃ p : ℤ,
      let q : ℕ := leastDenominatorInInterval L U hLU
      0 < q ∧ |α - (p : ℝ) / (q : ℝ)| ≤ U - L := by
  rcases exists_int_num_for_leastDenominatorInInterval hLU with
    ⟨p, hqpos, hpL, hpU⟩
  refine ⟨p, hqpos, ?_⟩
  exact abs_sub_le_width_of_two_points_in_interval
    hα.1 hα.2 hpL hpU

lemma log_lower_of_rpow_neg_le_exp
    {q ν A : ℝ}
    (hq : 0 < q)
    (hν : 0 < ν)
    (h : q ^ (-ν) ≤ Real.exp A) :
    (-A) / ν ≤ Real.log q := by
  have hpowpos : 0 < q ^ (-ν) := Real.rpow_pos_of_pos hq _
  have hlog : Real.log (q ^ (-ν)) ≤ Real.log (Real.exp A) :=
    Real.log_le_log hpowpos h
  rw [Real.log_rpow hq, Real.log_exp] at hlog
  have hmain : -A ≤ ν * Real.log q := by
    nlinarith
  exact (div_le_iff₀ hν).mpr (by simpa [mul_comm] using hmain)

lemma log_q_lower_of_width_exp
    {q ν κ C m : ℝ}
    (hq : 0 < q) (hν : 0 < ν)
    (h : q ^ (-ν) ≤ Real.exp (-(κ * m) + C)) :
    (κ * m - C) / ν ≤ Real.log q := by
  have h0 := log_lower_of_rpow_neg_le_exp
    (q := q) (ν := ν) (A := -(κ * m) + C) hq hν h
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h0

theorem eventually_log_leastDenominator_lower_of_measure_width_from
    {α ν κ C : ℝ} {L U : ℕ → ℝ}
    {hLU : ∀ m : ℕ, L m < U m}
    {Q0 : ℕ}
    (hνpos : 0 < ν)
    (hApprox : RationalApproxLowerFrom α ν Q0)
    (hαI : EventuallyAlphaInInterval α L U)
    (hwidth : EventuallyExpWidthUpper L U κ C)
    (hqmin : EventuallyLeastDenominatorGe L U hLU Q0) :
    ∀ᶠ m : ℕ in atTop,
      (κ * (m : ℝ) - C) / ν ≤
        Real.log (leastDenominatorInIntervalSeq L U hLU m : ℝ) := by
  unfold EventuallyAlphaInInterval EventuallyExpWidthUpper
    EventuallyLeastDenominatorGe at *
  filter_upwards [hαI, hwidth, hqmin] with m hαm hwm hqge
  rcases abs_alpha_sub_le_width_of_leastDenominator_spec
      (α := α) (L := L m) (U := U m) (hLU := hLU m) hαm with
    ⟨p, hqpos, hclose⟩
  let q : ℕ := leastDenominatorInIntervalSeq L U hLU m
  have hqpos_seq : 0 < q := by
    simpa [q, leastDenominatorInIntervalSeq] using hqpos
  have hclose_seq :
      |α - (p : ℝ) / (q : ℝ)| ≤ U m - L m := by
    simpa [q, leastDenominatorInIntervalSeq] using hclose
  have happrox : (q : ℝ) ^ (-ν) ≤ |α - (p : ℝ) / (q : ℝ)| :=
    hApprox q hqge p hqpos_seq
  have hq_to_exp : (q : ℝ) ^ (-ν) ≤ Real.exp (-(κ * (m : ℝ)) + C) :=
    happrox.trans (hclose_seq.trans hwm)
  have hqrealpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos_seq
  simpa [q, leastDenominatorInIntervalSeq] using
    log_q_lower_of_width_exp
      (q := (q : ℝ)) (ν := ν) (κ := κ) (C := C) (m := (m : ℝ))
      hqrealpos hνpos hq_to_exp

theorem eventually_log_leastDenominator_lower_of_measure_width
    {α μ ν κ C : ℝ} {L U : ℕ → ℝ}
    {hLU : ∀ m : ℕ, L m < U m}
    (hμ : HasIrrationalityMeasure α μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hαI : EventuallyAlphaInInterval α L U)
    (hwidth : EventuallyExpWidthUpper L U κ C)
    (hNoSmall : ∀ Q0 : ℕ, EventuallyLeastDenominatorGe L U hLU Q0) :
    ∀ᶠ m : ℕ in atTop,
      (κ * (m : ℝ) - C) / ν ≤
        Real.log (leastDenominatorInIntervalSeq L U hLU m : ℝ) := by
  rcases exists_rationalApproxLowerFrom_of_measure hμ hν with ⟨Q0, hApprox⟩
  exact eventually_log_leastDenominator_lower_of_measure_width_from
    (hνpos := hνpos) hApprox hαI hwidth (hNoSmall Q0)

/-- Abstract path-length upper bound supplied by the finite `φ` theorem. -/
def EventuallyPhiUpperFromPathLength
    (qmin : ℕ → ℕ) (K : ℕ → ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    Real.log (qmin m : ℝ) ≤
      (K m : ℝ) * Real.log Real.goldenRatio +
        4 * Real.log Real.goldenRatio

theorem log_goldenRatio_pos : 0 < Real.log Real.goldenRatio :=
  Real.log_pos Real.one_lt_goldenRatio

/-- If `log qmin(m)` grows at least linearly and the finite Farey-frame
argument bounds it above by `K(m) log φ + O(1)`, then every strict slope below
the quotient is eventually a lower bound for `K`. -/
theorem eventuallyLinearLowerBound_pathLength_of_logQmin_lower_phiUpper
    {qmin K : ℕ → ℕ} {κ ν C c : ℝ}
    (hνpos : 0 < ν)
    (hφpos : 0 < Real.log Real.goldenRatio)
    (hlower : ∀ᶠ m : ℕ in atTop,
      (κ * (m : ℝ) - C) / ν ≤ Real.log (qmin m : ℝ))
    (hupper : EventuallyPhiUpperFromPathLength qmin K)
    (hc : c < κ / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  unfold EventuallyPhiUpperFromPathLength EventuallyLinearLowerBound at *
  let φlog : ℝ := Real.log Real.goldenRatio
  have hνne : ν ≠ 0 := ne_of_gt hνpos
  have hφne : φlog ≠ 0 := ne_of_gt (by simpa [φlog] using hφpos)
  have hdenpos : 0 < ν * φlog := mul_pos hνpos (by simpa [φlog] using hφpos)
  have hgap : 0 < κ / ν - c * φlog := by
    have hcφ :
        c * φlog < (κ / (ν * φlog)) * φlog :=
      mul_lt_mul_of_pos_right (by simpa [φlog] using hc)
        (by simpa [φlog] using hφpos)
    have hright : (κ / (ν * φlog)) * φlog = κ / ν := by
      field_simp [hνne, hφne]
    exact sub_pos.mpr (by simpa [hright] using hcφ)
  filter_upwards
      [hlower, hupper,
        eventually_const_le_pos_mul_natCast
          (A := C / ν + 4 * φlog) (δ := κ / ν - c * φlog) hgap]
      with m hlo hup hconst
  have hmain :
      (κ * (m : ℝ) - C) / ν ≤
        (K m : ℝ) * φlog + 4 * φlog := by
    simpa [φlog] using hlo.trans hup
  have hrewrite :
      (κ * (m : ℝ) - C) / ν =
        (κ / ν) * (m : ℝ) - C / ν := by
    field_simp [hνne]
  have hmain' :
      (κ / ν) * (m : ℝ) - C / ν ≤
        (K m : ℝ) * φlog + 4 * φlog := by
    simpa [hrewrite] using hmain
  have hmul :
      (c * (m : ℝ)) * φlog ≤ (K m : ℝ) * φlog := by
    nlinarith
  by_contra hnot
  have hlt : (K m : ℝ) < c * (m : ℝ) := lt_of_not_ge hnot
  have hlt_mul :
      (K m : ℝ) * φlog < (c * (m : ℝ)) * φlog :=
    mul_lt_mul_of_pos_right hlt (by simpa [φlog] using hφpos)
  exact not_lt_of_ge hmul hlt_mul

/-- Composed measure-width/path-length bridge.

The hypotheses are deliberately non-circular: an available irrationality-measure
upper exponent, a certified exponential interval-width bound, small-denominator
exclusion inside those intervals, and the finite `φ` path upper bound together
force a linear lower bound for the certified partial path length. -/
theorem eventuallyLinearLowerBound_pathLength_of_measure_width_phiUpper
    {α μ ν κ C c : ℝ} {L U : ℕ → ℝ}
    {hLU : ∀ m : ℕ, L m < U m}
    {K : ℕ → ℕ}
    (hμ : HasIrrationalityMeasure α μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hαI : EventuallyAlphaInInterval α L U)
    (hwidth : EventuallyExpWidthUpper L U κ C)
    (hNoSmall : ∀ Q0 : ℕ, EventuallyLeastDenominatorGe L U hLU Q0)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq L U hLU) K)
    (hc : c < κ / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  have hlower :
      ∀ᶠ m : ℕ in atTop,
        (κ * (m : ℝ) - C) / ν ≤
          Real.log (leastDenominatorInIntervalSeq L U hLU m : ℝ) :=
    eventually_log_leastDenominator_lower_of_measure_width
      (hμ := hμ) (hν := hν) (hνpos := hνpos)
      hαI hwidth hNoSmall
  exact eventuallyLinearLowerBound_pathLength_of_logQmin_lower_phiUpper
    (hνpos := hνpos) (hφpos := log_goldenRatio_pos)
    hlower hphi hc

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanPi.lean -/


namespace IrrationalityAr

namespace RamanujanPi

noncomputable section

/-!
# A finite Ramanujan--Farey certificate for `A (1 / π)`

This module proves a concrete finite certificate:

`687 + 710*s ∈ A (1 / Real.pi)` for every `s ≤ 146`.

The proof uses only:

* the project Farey-certificate API;
* Mathlib's certified 20-decimal bounds for `π`;
* Mathlib's irrationality of `π`.

It does not depend on a formal proof of the infinite Ramanujan series.
-/

noncomputable def invPi : ℝ := 1 / Real.pi

noncomputable def ramanujanLow : ℝ := ratValue 113 355

noncomputable def ramanujanHigh : ℝ := ratValue 33102 103993

noncomputable def ramanujanS3 : ℝ := ratValue 5468521975 17179869184

noncomputable def ramanujanU3 : ℝ := ratValue 25198950320425 79164837199872

lemma invPi_pos : 0 < invPi := by
  simpa [invPi] using one_div_pos.mpr Real.pi_pos

lemma ramanujanS3_pos : 0 < ramanujanS3 := by
  norm_num [ramanujanS3, ratValue]

lemma ramanujanU3_pos : 0 < ramanujanU3 := by
  norm_num [ramanujanU3, ratValue]

lemma ramanujanLow_pos : 0 < ramanujanLow := by
  norm_num [ramanujanLow, ratValue]

lemma ramanujanHigh_pos : 0 < ramanujanHigh := by
  norm_num [ramanujanHigh, ratValue]

lemma invPi_isIrrational : IsIrrational invPi := by
  simpa [invPi, one_div] using isIrrational_of_irrational irrational_pi.inv

lemma ne_ratValue_of_isIrrational
    {α : ℝ} (hαirr : IsIrrational α)
    (p q : ℕ) :
    α ≠ ratValue p q := by
  intro h
  apply hαirr
  refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
  simpa [ratValue] using h.symm

lemma low_lt_S3 :
    ramanujanLow < ramanujanS3 := by
  norm_num [ramanujanLow, ramanujanS3, ratValue]

lemma U3_lt_high :
    ramanujanU3 < ramanujanHigh := by
  norm_num [ramanujanU3, ramanujanHigh, ratValue]

lemma S3_lt_invPi :
    ramanujanS3 < invPi := by
  have hmul : ramanujanS3 * Real.pi < 1 := by
    calc
      ramanujanS3 * Real.pi
          < ramanujanS3 *
              (3.14159265358979323847 : ℝ) := by
            exact mul_lt_mul_of_pos_left Real.pi_lt_d20 ramanujanS3_pos
      _ < 1 := by
            norm_num [ramanujanS3, ratValue]
  have hdiv := (lt_div_iff₀ Real.pi_pos).2 hmul
  simpa [invPi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

lemma invPi_lt_U3 :
    invPi < ramanujanU3 := by
  have hmul : 1 < ramanujanU3 * Real.pi := by
    calc
      1 < ramanujanU3 *
            (3.14159265358979323846 : ℝ) := by
            norm_num [ramanujanU3, ratValue]
      _ < ramanujanU3 * Real.pi := by
            exact mul_lt_mul_of_pos_left Real.pi_gt_d20 ramanujanU3_pos
  have hdiv := (div_lt_iff₀ Real.pi_pos).2 hmul
  simpa [invPi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

theorem low_invPi_high :
    ramanujanLow < invPi ∧ invPi < ramanujanHigh := by
  exact ⟨low_lt_S3.trans S3_lt_invPi, invPi_lt_U3.trans U3_lt_high⟩

lemma low_invPi_high_ratValue :
    ratValue 113 355 < invPi ∧
      invPi < ratValue 33102 103993 := by
  simpa [ramanujanLow, ramanujanHigh] using low_invPi_high

def ramanujanP (t : ℕ) : ℕ := 106 + 113 * t

def ramanujanQ (t : ℕ) : ℕ := 333 + 355 * t

lemma ramanujanP_292 : ramanujanP 292 = 33102 := by
  norm_num [ramanujanP]

lemma ramanujanQ_292 : ramanujanQ 292 = 103993 := by
  norm_num [ramanujanQ]

lemma ramanujanP_293 : ramanujanP 293 = 33215 := by
  norm_num [ramanujanP]

lemma ramanujanQ_293 : ramanujanQ 293 = 104348 := by
  norm_num [ramanujanQ]

lemma ramanujanQ_pos (t : ℕ) :
    0 < ramanujanQ t := by
  unfold ramanujanQ
  omega

lemma two_le_ramanujanQ (t : ℕ) :
    2 ≤ ramanujanQ t := by
  unfold ramanujanQ
  omega

lemma low_path_farey (t : ℕ) :
    355 * ramanujanP t =
      113 * ramanujanQ t + 1 := by
  unfold ramanujanP ramanujanQ
  omega

lemma ramanujan_path_cross (t u : ℕ) :
    (ramanujanP t : ℤ) * (ramanujanQ u : ℤ) -
      (ramanujanP u : ℤ) * (ramanujanQ t : ℤ) =
        (u : ℤ) - (t : ℤ) := by
  simp [ramanujanP, ramanujanQ]
  ring

lemma ramanujan_path_antitone
    {t u : ℕ} (htu : t ≤ u) :
    ratValue (ramanujanP u) (ramanujanQ u) ≤
      ratValue (ramanujanP t) (ramanujanQ t) := by
  have hQt : (0 : ℝ) < ramanujanQ t := by
    exact_mod_cast ramanujanQ_pos t
  have hQu : (0 : ℝ) < ramanujanQ u := by
    exact_mod_cast ramanujanQ_pos u
  unfold ratValue
  rw [div_le_div_iff₀ hQu hQt]
  have hcross := ramanujan_path_cross t u
  have hprodZ :
      (ramanujanP u : ℤ) * (ramanujanQ t : ℤ) ≤
        (ramanujanP t : ℤ) * (ramanujanQ u : ℤ) := by
    have htuZ : (t : ℤ) ≤ (u : ℤ) := by exact_mod_cast htu
    omega
  exact_mod_cast hprodZ

lemma high_eq_path_292 :
    ratValue 33102 103993 =
      ratValue (ramanujanP 292) (ramanujanQ 292) := by
  simp [ramanujanP_292, ramanujanQ_292]

lemma invPi_lt_path_of_le_292
    {t : ℕ} (ht : t ≤ 292) :
    invPi < ratValue (ramanujanP t) (ramanujanQ t) := by
  have hHpath :
      ratValue 33102 103993 ≤
        ratValue (ramanujanP t) (ramanujanQ t) := by
    rw [high_eq_path_292]
    exact ramanujan_path_antitone ht
  exact low_invPi_high_ratValue.2.trans_le hHpath

lemma path293_high_farey :
    ramanujanQ 293 * 33102 =
      ramanujanP 293 * 103993 + 1 := by
  norm_num [ramanujanP, ramanujanQ]

lemma invPi_ne_path_293 :
    invPi ≠ ratValue (ramanujanP 293) (ramanujanQ 293) := by
  exact ne_ratValue_of_isIrrational invPi_isIrrational _ _

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


lemma ramanujan_path_reduced (t : ℕ) :
    ReducedFraction (ramanujanP t) (ramanujanQ t) := by
  exact reducedFraction_right_of_fareyDet
    (ramanujanQ_pos t) (low_path_farey t)

lemma ramanujanP_odd_of_odd
    {t : ℕ} (ht : Odd t) :
    Odd (ramanujanP t) := by
  rcases ht with ⟨s, hs⟩
  subst t
  refine ⟨113 * s + 109, ?_⟩
  unfold ramanujanP
  omega

lemma ramanujan_path_best_of_le_292
    {t : ℕ} (ht : t ≤ 292) :
    NoSmallDenominatorBetween invPi
      (ramanujanP t) (ramanujanQ t) := by
  exact noSmallDenominatorBetween_right_of_fareyBracket
    (p := 113) (q := 355)
    (r := ramanujanP t) (s := ramanujanQ t)
    (by norm_num)
    (ramanujanQ_pos t)
    (low_path_farey t)
    ⟨low_invPi_high_ratValue.1,
      invPi_lt_path_of_le_292 ht⟩

lemma ramanujan_path_best_293 :
    NoSmallDenominatorBetween invPi
      (ramanujanP 293) (ramanujanQ 293) := by
  rcases lt_or_gt_of_ne invPi_ne_path_293 with hαM | hMα
  · exact noSmallDenominatorBetween_right_of_fareyBracket
      (p := 113) (q := 355)
      (r := ramanujanP 293) (s := ramanujanQ 293)
      (by norm_num)
      (ramanujanQ_pos 293)
      (low_path_farey 293)
      ⟨low_invPi_high_ratValue.1, hαM⟩
  · exact noSmallDenominatorBetween_left_of_fareyBracket
      (p := ramanujanP 293) (q := ramanujanQ 293)
      (r := 33102) (s := 103993)
      (ramanujanQ_pos 293)
      (by norm_num)
      path293_high_farey
      ⟨hMα, low_invPi_high_ratValue.2⟩

theorem ramanujan_path_best
    {t : ℕ} (_ht1 : 1 ≤ t) (ht293 : t ≤ 293) :
    NoSmallDenominatorBetween invPi
      (ramanujanP t) (ramanujanQ t) := by
  by_cases ht292 : t ≤ 292
  · exact ramanujan_path_best_of_le_292 ht292
  · have ht : t = 293 := by omega
    subst t
    exact ramanujan_path_best_293

theorem ramanujan_path_convergent_or_semiconvergent
    {t : ℕ} (ht293 : t ≤ 293) :
    IsConvergentOrSemiconvergent invPi
      (ramanujanP t) (ramanujanQ t) := by
  apply (no_small_denominator_iff_convergent_or_semiconvergent
    invPi_pos invPi_isIrrational
    (two_le_ramanujanQ t)
    (ramanujan_path_reduced t)).1
  by_cases ht292 : t ≤ 292
  · exact ramanujan_path_best_of_le_292 ht292
  · have ht : t = 293 := by omega
    subst t
    exact ramanujan_path_best_293

theorem ramanujan_path_mem_A_of_odd
    {t : ℕ}
    (ht1 : 1 ≤ t)
    (ht293 : t ≤ 293)
    (htodd : Odd t) :
    ramanujanQ t - 1 ∈ A invPi := by
  have hbest :
      NoSmallDenominatorBetween invPi
        (ramanujanP t) (ramanujanQ t) :=
    ramanujan_path_best ht1 ht293
  have hcf :
      IsConvergentOrSemiconvergent invPi
        (ramanujanP t) (ramanujanQ t) :=
    (no_small_denominator_iff_convergent_or_semiconvergent
      invPi_pos invPi_isIrrational
      (two_le_ramanujanQ t)
      (ramanujan_path_reduced t)).1 hbest
  exact mem_A_of_odd_convergent_or_semiconvergent
    invPi_pos invPi_isIrrational
    (two_le_ramanujanQ t)
    (ramanujan_path_reduced t)
    hcf
    (ramanujanP_odd_of_odd htodd)

lemma odd_path_index_pos (s : ℕ) :
    1 ≤ 2 * s + 1 := by
  omega

lemma odd_path_index_le_293
    {s : ℕ} (hs : s ≤ 146) :
    2 * s + 1 ≤ 293 := by
  omega

lemma odd_path_index (s : ℕ) :
    Odd (2 * s + 1) := by
  exact ⟨s, rfl⟩

lemma ramanujanQ_odd_index_sub_one (s : ℕ) :
    ramanujanQ (2 * s + 1) - 1 =
      687 + 710 * s := by
  unfold ramanujanQ
  omega

theorem ramanujan_progression_mem_A_invPi
    {s : ℕ} (hs : s ≤ 146) :
    687 + 710 * s ∈ A invPi := by
  have hmem :
      ramanujanQ (2 * s + 1) - 1 ∈ A invPi :=
    ramanujan_path_mem_A_of_odd
      (odd_path_index_pos s)
      (odd_path_index_le_293 hs)
      (odd_path_index s)
  rwa [ramanujanQ_odd_index_sub_one] at hmem

end

end RamanujanPi

/-- A 147-term arithmetic progression certified inside `A (1 / π)`. -/
theorem ramanujan_progression_mem_A
    {s : ℕ} (hs : s ≤ 146) :
    687 + 710 * s ∈ A (1 / Real.pi) := by
  simpa [RamanujanPi.invPi] using
    RamanujanPi.ramanujan_progression_mem_A_invPi hs

def ramanujanAP : Finset ℕ :=
  finiteArithmeticBlock 687 710 147

theorem ramanujanAP_subset_A :
    ∀ n ∈ ramanujanAP, n ∈ A (1 / Real.pi) := by
  intro n hn
  rw [ramanujanAP, mem_finiteArithmeticBlock_iff] at hn
  rcases hn with ⟨s, hs, rfl⟩
  have hs146 : s ≤ 146 := by omega
  simpa [Nat.mul_comm] using
    ramanujan_progression_mem_A hs146

theorem ramanujanAP_card :
    ramanujanAP.card = 147 := by
  unfold ramanujanAP
  exact finiteArithmeticBlock_card
    (s := 687) (d := 710) (m := 147)
    (by norm_num)

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanPiIntervals.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Concrete Ramanujan intervals around `1 / π`

This file introduces the elementary interval data for the Ramanujan
`42 n + 5` series.  The actual Ramanujan summation identity and optimized tail
estimates are left as explicit inputs, so downstream denominator-exclusion and
path-length consequences can already be stated against concrete intervals.
-/

/-- The positive Ramanujan summand

`choose (2n) n^3 * (42n + 5) / 2^(12n+4)`.
-/
noncomputable def ramanujanPiTerm (n : ℕ) : ℝ :=
  ((Nat.choose (2 * n) n : ℝ) ^ 3 * (42 * (n : ℝ) + 5)) /
    (2 : ℝ) ^ (12 * n + 4)

/-- The partial sum through index `m`. -/
noncomputable def ramanujanPiPartial (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), ramanujanPiTerm n

/-- Safe geometric-tail placeholder using the ratio `1/4`. -/
noncomputable def ramanujanPiTailBound (m : ℕ) : ℝ :=
  (4 / 3 : ℝ) * ramanujanPiTerm (m + 1)

noncomputable def ramanujanPiL (m : ℕ) : ℝ :=
  ramanujanPiPartial m

noncomputable def ramanujanPiU (m : ℕ) : ℝ :=
  ramanujanPiPartial m + ramanujanPiTailBound m

theorem ramanujanPiTerm_pos (n : ℕ) :
    0 < ramanujanPiTerm n := by
  unfold ramanujanPiTerm
  have hchooseNat : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hchoose : 0 < (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast hchooseNat
  have hlin : 0 < 42 * (n : ℝ) + 5 := by
    positivity
  have hnum :
      0 < (Nat.choose (2 * n) n : ℝ) ^ 3 *
        (42 * (n : ℝ) + 5) :=
    mul_pos (pow_pos hchoose 3) hlin
  have hden : 0 < (2 : ℝ) ^ (12 * n + 4) :=
    pow_pos (by norm_num) _
  exact div_pos hnum hden

private lemma central_choose_succ_le_four (n : ℕ) :
    (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) ≤
      4 * (Nat.choose (2 * n) n : ℝ) := by
  let Cn : ℝ := (Nat.choose (2 * n) n : ℝ)
  let Cnext : ℝ := (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
  have hrecNat :
      (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) =
        2 * (2 * n + 1) * Nat.choose (2 * n) n := by
    simpa [Nat.centralBinom] using Nat.succ_mul_centralBinom_succ n
  have hcoefNat : 2 * (2 * n + 1) ≤ 4 * (n + 1) := by
    omega
  have hmulNat :
      (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) ≤
        (n + 1) * (4 * Nat.choose (2 * n) n) := by
    calc
      (n + 1) * Nat.choose (2 * (n + 1)) (n + 1)
          = 2 * (2 * n + 1) * Nat.choose (2 * n) n := hrecNat
      _ ≤ (4 * (n + 1)) * Nat.choose (2 * n) n := by
          exact Nat.mul_le_mul_right _ hcoefNat
      _ = (n + 1) * (4 * Nat.choose (2 * n) n) := by
          ring
  have hmulR :
      ((n + 1 : ℕ) : ℝ) * Cnext ≤
        ((n + 1 : ℕ) : ℝ) * (4 * Cn) := by
    dsimp [Cn, Cnext]
    exact_mod_cast hmulNat
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by
    positivity
  by_contra hnot
  have hlt : 4 * Cn < Cnext := lt_of_not_ge hnot
  have hltmul :
      ((n + 1 : ℕ) : ℝ) * (4 * Cn) <
        ((n + 1 : ℕ) : ℝ) * Cnext :=
    mul_lt_mul_of_pos_left hlt hnpos
  exact not_lt_of_ge hmulR hltmul

private lemma central_choose_succ_eq_ratio (n : ℕ) :
    (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) =
      ((2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1)) *
        (Nat.choose (2 * n) n : ℝ) := by
  let Cn : ℝ := (Nat.choose (2 * n) n : ℝ)
  let Cnext : ℝ := (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
  have hrecNat :
      (n + 1) * Nat.choose (2 * (n + 1)) (n + 1) =
        2 * (2 * n + 1) * Nat.choose (2 * n) n := by
    simpa [Nat.centralBinom] using Nat.succ_mul_centralBinom_succ n
  have hrecR :
      ((n : ℝ) + 1) * Cnext =
        (2 * (2 * (n : ℝ) + 1)) * Cn := by
    dsimp [Cn, Cnext]
    norm_num [Nat.cast_add, Nat.cast_one] at hrecNat ⊢
    exact_mod_cast hrecNat
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  calc
    Cnext = (((n : ℝ) + 1) * Cnext) / ((n : ℝ) + 1) := by
      field_simp [hn]
    _ = ((2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1)) * Cn := by
      rw [hrecR]
      ring

private lemma ramanujanPi_linearFactor_succ_le (n : ℕ) :
    42 * ((n + 1 : ℕ) : ℝ) + 5
      ≤ (47 / 5 : ℝ) * (42 * (n : ℝ) + 5) := by
  norm_num [Nat.cast_add, Nat.cast_one]
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.zero_le n]

private lemma ramanujanPi_den_succ_eq (n : ℕ) :
    (2 : ℝ) ^ (12 * (n + 1) + 4)
      = 4096 * (2 : ℝ) ^ (12 * n + 4) := by
  have h :
      12 * (n + 1) + 4 = 12 + (12 * n + 4) := by
    omega
  rw [h, pow_add]
  norm_num

theorem ramanujanPiTerm_ratio_eq (n : ℕ) :
    ramanujanPiTerm (n + 1) / ramanujanPiTerm n =
      (((2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1)) ^ 3 *
          ((42 * (n : ℝ) + 47) / (42 * (n : ℝ) + 5))) /
        4096 := by
  let Cn : ℝ := (Nat.choose (2 * n) n : ℝ)
  let Rn : ℝ := (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1)
  let An : ℝ := 42 * (n : ℝ) + 5
  let Dn : ℝ := (2 : ℝ) ^ (12 * n + 4)
  have hC : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) = Rn * Cn := by
    dsimp [Rn, Cn]
    exact central_choose_succ_eq_ratio n
  have hA : 42 * ((n + 1 : ℕ) : ℝ) + 5 = An + 42 := by
    dsimp [An]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hD : (2 : ℝ) ^ (12 * (n + 1) + 4) = 4096 * Dn := by
    dsimp [Dn]
    exact ramanujanPi_den_succ_eq n
  have hCn_pos : 0 < Cn := by
    dsimp [Cn]
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  have hAn_pos : 0 < An := by
    dsimp [An]
    positivity
  have hDn_pos : 0 < Dn := by
    dsimp [Dn]
    positivity
  have hRn_den : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold ramanujanPiTerm
  dsimp [Cn, Rn, An, Dn] at *
  rw [hC, hA, hD]
  field_simp [hCn_pos.ne', hAn_pos.ne', hDn_pos.ne', hRn_den]
  ring

theorem ramanujanPiTerm_ratio_tendsto_one_div_64 :
    Tendsto
      (fun n : ℕ => ramanujanPiTerm (n + 1) / ramanujanPiTerm n)
      atTop
      (𝓝 (1 / 64 : ℝ)) := by
  have hcentral :
      Tendsto
        (fun n : ℕ =>
          (2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1))
        atTop (𝓝 (4 : ℝ)) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (a := (2 : ℝ)) (b := (1 : ℝ))
        (c := (4 : ℝ)) (d := (1 : ℝ))
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa [mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc,
      show (2 : ℝ) * 2 = 4 by norm_num] using h
  have hlinear :
      Tendsto
        (fun n : ℕ =>
          (42 * (n : ℝ) + 47) / (42 * (n : ℝ) + 5))
        atTop (𝓝 (1 : ℝ)) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (a := (47 : ℝ)) (b := (5 : ℝ))
        (c := (42 : ℝ)) (d := (42 : ℝ))
        (by norm_num : (42 : ℝ) ≠ 0)
    simpa [add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (((2 * (2 * (n : ℝ) + 1)) / ((n : ℝ) + 1)) ^ 3 *
            ((42 * (n : ℝ) + 47) / (42 * (n : ℝ) + 5))) /
            4096)
        atTop (𝓝 (1 / 64 : ℝ)) := by
    have hmain := (hcentral.pow 3).mul hlinear
    have hdiv := hmain.div_const (4096 : ℝ)
    simpa [show (4 : ℝ) ^ 3 / 4096 = (1 / 64 : ℝ) by norm_num] using hdiv
  simpa [ramanujanPiTerm_ratio_eq] using hratio

private theorem one_div_64_eq_exp_neg_six_log_two :
    (1 / 64 : ℝ) = Real.exp (-(6 * Real.log 2)) := by
  rw [Real.exp_neg]
  have h : Real.exp (6 * Real.log 2) = (64 : ℝ) := by
    calc
      Real.exp (6 * Real.log 2)
          = Real.exp ((6 : ℕ) * Real.log 2) := by norm_num
      _ = Real.exp (Real.log 2) ^ 6 := by
            rw [Real.exp_nat_mul]
      _ = (2 : ℝ) ^ 6 := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = 64 := by norm_num
  rw [h]
  norm_num

theorem ramanujanPiTerm_succ_le_exp_of_lt_six_log_two
    {c : ℝ} (hc : c < 6 * Real.log 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ramanujanPiTerm (n + 1)
        ≤ Real.exp (-c) * ramanujanPiTerm n := by
  have hlim_lt : (1 / 64 : ℝ) < Real.exp (-c) := by
    calc
      (1 / 64 : ℝ) = Real.exp (-(6 * Real.log 2)) :=
        one_div_64_eq_exp_neg_six_log_two
      _ < Real.exp (-c) := by
        exact Real.exp_lt_exp.mpr (by linarith)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ramanujanPiTerm (n + 1) / ramanujanPiTerm n < Real.exp (-c) :=
    ramanujanPiTerm_ratio_tendsto_one_div_64.eventually
      (eventually_lt_nhds hlim_lt)
  filter_upwards [hevent] with n hn
  have hpos := ramanujanPiTerm_pos n
  exact le_of_lt ((div_lt_iff₀ hpos).mp hn)

theorem ramanujanPiTerm_succ_ge_exp_neg_of_gt_six_log_two
    {c : ℝ} (hc : 6 * Real.log 2 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-c) * ramanujanPiTerm n ≤
        ramanujanPiTerm (n + 1) := by
  have hexp_lt : Real.exp (-c) < (1 / 64 : ℝ) := by
    calc
      Real.exp (-c) < Real.exp (-(6 * Real.log 2)) := by
        exact Real.exp_lt_exp.mpr (by linarith)
      _ = (1 / 64 : ℝ) := one_div_64_eq_exp_neg_six_log_two.symm
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-c) <
          ramanujanPiTerm (n + 1) / ramanujanPiTerm n :=
    ramanujanPiTerm_ratio_tendsto_one_div_64.eventually
      (eventually_gt_nhds hexp_lt)
  filter_upwards [hevent] with n hn
  have hpos := ramanujanPiTerm_pos n
  exact le_of_lt ((lt_div_iff₀ hpos).mp hn)

private theorem ramanujanPiTerm_eventually_exp_lower_bound_of_step
    {c : ℝ}
    (hstep : ∀ᶠ n : ℕ in atTop,
      Real.exp (-c) * ramanujanPiTerm n ≤
        ramanujanPiTerm (n + 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        C * Real.exp (-(c * (n : ℝ))) ≤ ramanujanPiTerm n := by
  rw [eventually_atTop] at hstep
  rcases hstep with ⟨N, hN⟩
  let r : ℝ := Real.exp (-c)
  let C : ℝ := ramanujanPiTerm N * Real.exp (c * (N : ℝ))
  have hr_nonneg : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have htermNpos : 0 < ramanujanPiTerm N := ramanujanPiTerm_pos N
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos htermNpos (Real.exp_pos _)
  have hiter :
      ∀ k : ℕ, r ^ k * ramanujanPiTerm N ≤ ramanujanPiTerm (N + k) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hstepNk :
            r * ramanujanPiTerm (N + k) ≤
              ramanujanPiTerm (N + k + 1) := by
          simpa [r, Nat.add_assoc] using hN (N + k) (Nat.le_add_right N k)
        calc
          r ^ (k + 1) * ramanujanPiTerm N
              = r * (r ^ k * ramanujanPiTerm N) := by
                rw [pow_succ']
                ring
          _ ≤ r * ramanujanPiTerm (N + k) := by
                exact mul_le_mul_of_nonneg_left ih hr_nonneg
          _ ≤ ramanujanPiTerm (N + k + 1) := hstepNk
          _ = ramanujanPiTerm (N + (k + 1)) := by
                simp [Nat.add_assoc]
  refine ⟨C, hCpos, ?_⟩
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  let k : ℕ := n - N
  have hNk : N + k = n := Nat.add_sub_of_le hn
  have hle : r ^ k * ramanujanPiTerm N ≤ ramanujanPiTerm n := by
    simpa [hNk] using hiter k
  have hexp :
      C * Real.exp (-(c * (n : ℝ))) =
        r ^ k * ramanujanPiTerm N := by
    calc
      C * Real.exp (-(c * (n : ℝ)))
          =
        ramanujanPiTerm N *
          Real.exp (c * (N : ℝ) + -(c * (n : ℝ))) := by
            dsimp [C]
            rw [mul_assoc, ← Real.exp_add]
      _ = ramanujanPiTerm N * Real.exp ((k : ℝ) * (-c)) := by
            rw [← hNk]
            congr 1
            norm_num [Nat.cast_add]
            ring
      _ = ramanujanPiTerm N * r ^ k := by
            dsimp [r]
            rw [Real.exp_nat_mul]
      _ = r ^ k * ramanujanPiTerm N := by
            ring
  exact hexp.trans_le hle

private theorem const_mul_exp_lower_absorb
    {C c₀ c : ℝ}
    (hC : 0 < C) (hc₀c : c₀ < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(c * (n : ℝ))) ≤
        C * Real.exp (-(c₀ * (n : ℝ))) := by
  have hgap : 0 < c - c₀ := sub_pos.mpr hc₀c
  have hlarge :=
    eventually_const_le_pos_mul_natCast
      (A := -Real.log C) (δ := c - c₀) hgap
  filter_upwards [hlarge] with n hn
  have hlogle : -((c - c₀) * (n : ℝ)) ≤ Real.log C := by
    linarith
  have hsmall :
      Real.exp (-((c - c₀) * (n : ℝ))) ≤ C := by
    calc
      Real.exp (-((c - c₀) * (n : ℝ)))
          ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr hlogle
      _ = C := Real.exp_log hC
  calc
    Real.exp (-(c * (n : ℝ)))
        =
      Real.exp (-(c₀ * (n : ℝ))) *
        Real.exp (-((c - c₀) * (n : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-(c₀ * (n : ℝ))) * C := by
          exact mul_le_mul_of_nonneg_left hsmall (le_of_lt (Real.exp_pos _))
    _ = C * Real.exp (-(c₀ * (n : ℝ))) := by
          ring

theorem ramanujanPiTerm_exp_lower_of_gt_six_log_two
    {c : ℝ} (hc : 6 * Real.log 2 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-(c * (n : ℝ))) ≤ ramanujanPiTerm n := by
  let c₀ : ℝ := (6 * Real.log 2 + c) / 2
  have hc₀_lower : 6 * Real.log 2 < c₀ := by
    dsimp [c₀]
    linarith
  have hc₀c : c₀ < c := by
    dsimp [c₀]
    linarith
  rcases
      ramanujanPiTerm_eventually_exp_lower_bound_of_step
        (ramanujanPiTerm_succ_ge_exp_neg_of_gt_six_log_two hc₀_lower)
      with ⟨C, hCpos, hC⟩
  have habsorb := const_mul_exp_lower_absorb hCpos hc₀c
  filter_upwards [habsorb, hC] with n habs hlower
  exact habs.trans hlower

private theorem ramanujanPiTerm_eventually_exp_bound_of_step
    {c : ℝ}
    (hstep : ∀ᶠ n : ℕ in atTop,
      ramanujanPiTerm (n + 1) ≤ Real.exp (-c) * ramanujanPiTerm n) :
    ∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop,
        ramanujanPiTerm n ≤ Real.exp (-(c * (n : ℝ)) + C) := by
  rw [eventually_atTop] at hstep
  rcases hstep with ⟨N, hN⟩
  let r : ℝ := Real.exp (-c)
  let C : ℝ := Real.log (ramanujanPiTerm N) + c * (N : ℝ)
  have hr_nonneg : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have htermNpos : 0 < ramanujanPiTerm N := ramanujanPiTerm_pos N
  have hiter :
      ∀ k : ℕ, ramanujanPiTerm (N + k) ≤ r ^ k * ramanujanPiTerm N := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hstepNk :
            ramanujanPiTerm (N + k + 1)
              ≤ r * ramanujanPiTerm (N + k) := by
          simpa [r, Nat.add_assoc] using hN (N + k) (Nat.le_add_right N k)
        calc
          ramanujanPiTerm (N + (k + 1))
              = ramanujanPiTerm (N + k + 1) := by
                simp [Nat.add_assoc]
          _ ≤ r * ramanujanPiTerm (N + k) := hstepNk
          _ ≤ r * (r ^ k * ramanujanPiTerm N) := by
                exact mul_le_mul_of_nonneg_left ih hr_nonneg
          _ = r ^ (k + 1) * ramanujanPiTerm N := by
                rw [pow_succ']
                ring
  refine ⟨C, ?_⟩
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  let k : ℕ := n - N
  have hNk : N + k = n := Nat.add_sub_of_le hn
  have hle : ramanujanPiTerm n ≤ r ^ k * ramanujanPiTerm N := by
    simpa [hNk] using hiter k
  have hexp :
      r ^ k * ramanujanPiTerm N =
        Real.exp (-(c * (n : ℝ)) + C) := by
    calc
      r ^ k * ramanujanPiTerm N
          = Real.exp ((k : ℝ) * (-c)) * ramanujanPiTerm N := by
            dsimp [r]
            rw [← Real.exp_nat_mul]
      _ = Real.exp ((k : ℝ) * (-c)) *
            Real.exp (Real.log (ramanujanPiTerm N)) := by
            rw [Real.exp_log htermNpos]
      _ = Real.exp (((k : ℝ) * (-c)) +
            Real.log (ramanujanPiTerm N)) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(c * (n : ℝ)) + C) := by
            dsimp [C]
            rw [← hNk]
            congr 1
            norm_num [Nat.cast_add]
            ring
  exact hle.trans_eq hexp

theorem ramanujanPiTerm_succ_le_47_div_320 (n : ℕ) :
    ramanujanPiTerm (n + 1)
      ≤ (47 / 320 : ℝ) * ramanujanPiTerm n := by
  let Cn : ℝ := (Nat.choose (2 * n) n : ℝ)
  let Cnext : ℝ := (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
  let An : ℝ := 42 * (n : ℝ) + 5
  let Anext : ℝ := 42 * ((n + 1 : ℕ) : ℝ) + 5
  let Dn : ℝ := (2 : ℝ) ^ (12 * n + 4)
  let Dnext : ℝ := (2 : ℝ) ^ (12 * (n + 1) + 4)
  have hC : Cnext ≤ 4 * Cn := by
    dsimp [Cnext, Cn]
    exact central_choose_succ_le_four n
  have hC3 : Cnext ^ 3 ≤ 64 * Cn ^ 3 := by
    have hCnext_nonneg : 0 ≤ Cnext := by
      dsimp [Cnext]
      positivity
    calc
      Cnext ^ 3 ≤ (4 * Cn) ^ 3 := by
        gcongr
      _ = 64 * Cn ^ 3 := by ring
  have hA : Anext ≤ (47 / 5 : ℝ) * An := by
    dsimp [Anext, An]
    exact ramanujanPi_linearFactor_succ_le n
  have hnum :
      Cnext ^ 3 * Anext
        ≤ (64 * Cn ^ 3) * ((47 / 5 : ℝ) * An) := by
    have hC3_nonneg : 0 ≤ Cnext ^ 3 := by positivity
    calc
      Cnext ^ 3 * Anext
          ≤ Cnext ^ 3 * ((47 / 5 : ℝ) * An) := by
            gcongr
      _ ≤ (64 * Cn ^ 3) * ((47 / 5 : ℝ) * An) := by
            gcongr
  have hD : Dnext = 4096 * Dn := by
    dsimp [Dnext, Dn]
    exact ramanujanPi_den_succ_eq n
  have hD_nonneg : 0 ≤ 4096 * Dn := by
    dsimp [Dn]
    positivity
  unfold ramanujanPiTerm
  dsimp [Cn, Cnext, An, Anext, Dn, Dnext] at *
  calc
    ((Nat.choose (2 * (n + 1)) (n + 1) : ℝ) ^ 3
        * (42 * ((n + 1 : ℕ) : ℝ) + 5))
        / (2 : ℝ) ^ (12 * (n + 1) + 4)
        =
      (Cnext ^ 3 * Anext) / Dnext := by rfl
    _ =
      (Cnext ^ 3 * Anext) / (4096 * Dn) := by
        dsimp [Dnext, Dn]
        rw [hD]
    _ ≤
      ((64 * Cn ^ 3) * ((47 / 5 : ℝ) * An)) / (4096 * Dn) := by
        exact div_le_div_of_nonneg_right hnum hD_nonneg
    _ =
      (47 / 320 : ℝ) * (Cn ^ 3 * An / Dn) := by
        field_simp [Dn]
        ring
    _ =
      (47 / 320 : ℝ) *
        (((Nat.choose (2 * n) n : ℝ) ^ 3 * (42 * (n : ℝ) + 5))
          / (2 : ℝ) ^ (12 * n + 4)) := by
        rfl

theorem ramanujanPiTerm_succ_le_quarter (n : ℕ) :
    ramanujanPiTerm (n + 1) ≤ (1 / 4 : ℝ) * ramanujanPiTerm n := by
  have h := ramanujanPiTerm_succ_le_47_div_320 n
  have hcoef : (47 / 320 : ℝ) ≤ 1 / 4 := by norm_num
  calc
    ramanujanPiTerm (n + 1)
        ≤ (47 / 320 : ℝ) * ramanujanPiTerm n := h
    _ ≤ (1 / 4 : ℝ) * ramanujanPiTerm n := by
        gcongr
        exact le_of_lt (ramanujanPiTerm_pos n)

theorem ramanujanPiTerm_le_geometric (n : ℕ) :
    ramanujanPiTerm n ≤ ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ramanujanPiTerm (n + 1)
            ≤ (1 / 4 : ℝ) * ramanujanPiTerm n :=
              ramanujanPiTerm_succ_le_quarter n
        _ ≤ (1 / 4 : ℝ) *
              (ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ n) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ (n + 1) := by
              ring

private theorem quarter_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)

private theorem ramanujanPi_geometric_tendsto_zero :
    Tendsto
      (fun n : ℕ => ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ n)
      atTop (𝓝 0) := by
  simpa using
    (tendsto_const_nhds.mul quarter_pow_tendsto_zero : Tendsto
      (fun n : ℕ => ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ n)
      atTop (𝓝 (ramanujanPiTerm 0 * 0)))

theorem ramanujanPiTerm_tendsto_zero :
    Tendsto ramanujanPiTerm atTop (𝓝 0) := by
  exact squeeze_zero
    (fun n => le_of_lt (ramanujanPiTerm_pos n))
    ramanujanPiTerm_le_geometric
    ramanujanPi_geometric_tendsto_zero

theorem ramanujanPiTailBound_tendsto_zero :
    Tendsto ramanujanPiTailBound atTop (𝓝 0) := by
  unfold ramanujanPiTailBound
  have hshift :
      Tendsto (fun m : ℕ => ramanujanPiTerm (m + 1)) atTop (𝓝 0) :=
    ramanujanPiTerm_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  simpa using
    (tendsto_const_nhds.mul hshift : Tendsto
      (fun m : ℕ => (4 / 3 : ℝ) * ramanujanPiTerm (m + 1))
      atTop (𝓝 ((4 / 3 : ℝ) * 0)))

private theorem quarter_pow_eq_exp_neg_log_four_mul (m : ℕ) :
    (1 / 4 : ℝ) ^ m = Real.exp (-(Real.log 4 * (m : ℝ))) := by
  calc
    (1 / 4 : ℝ) ^ m = (Real.exp (-Real.log 4)) ^ m := by
      congr 1
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    _ = Real.exp ((m : ℝ) * (-Real.log 4)) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (-(Real.log 4 * (m : ℝ))) := by
      ring_nf

theorem ramanujanPiTailBound_le_exp_log4 (m : ℕ) :
    ramanujanPiTailBound m ≤
      Real.exp
        (-(Real.log 4 * (m : ℝ)) +
          Real.log ((4 / 3 : ℝ) * ramanujanPiTerm 0)) := by
  let C0 : ℝ := (4 / 3 : ℝ) * ramanujanPiTerm 0
  have hC0pos : 0 < C0 := by
    dsimp [C0]
    exact mul_pos (by norm_num) (ramanujanPiTerm_pos 0)
  have hterm := ramanujanPiTerm_le_geometric (m + 1)
  have htail_le :
      ramanujanPiTailBound m ≤ C0 * (1 / 4 : ℝ) ^ (m + 1) := by
    unfold ramanujanPiTailBound
    dsimp [C0]
    calc
      (4 / 3 : ℝ) * ramanujanPiTerm (m + 1)
          ≤ (4 / 3 : ℝ) *
              (ramanujanPiTerm 0 * (1 / 4 : ℝ) ^ (m + 1)) := by
            exact mul_le_mul_of_nonneg_left hterm (by norm_num)
      _ = ((4 / 3 : ℝ) * ramanujanPiTerm 0) *
            (1 / 4 : ℝ) ^ (m + 1) := by
            ring
  have hpow_mono : (1 / 4 : ℝ) ^ (m + 1) ≤ (1 / 4 : ℝ) ^ m := by
    calc
      (1 / 4 : ℝ) ^ (m + 1)
          = (1 / 4 : ℝ) ^ m * (1 / 4 : ℝ) := by
            rw [pow_succ]
      _ ≤ (1 / 4 : ℝ) ^ m * 1 := by
            exact mul_le_mul_of_nonneg_left (by norm_num : (1 / 4 : ℝ) ≤ 1)
              (by positivity)
      _ = (1 / 4 : ℝ) ^ m := by ring
  have htail_le' :
      ramanujanPiTailBound m ≤ C0 * (1 / 4 : ℝ) ^ m :=
    htail_le.trans (mul_le_mul_of_nonneg_left hpow_mono hC0pos.le)
  have hexp :
      C0 * (1 / 4 : ℝ) ^ m =
        Real.exp (-(Real.log 4 * (m : ℝ)) + Real.log C0) := by
    calc
      C0 * (1 / 4 : ℝ) ^ m
          = C0 * Real.exp (-(Real.log 4 * (m : ℝ))) := by
            rw [quarter_pow_eq_exp_neg_log_four_mul]
      _ = Real.exp (Real.log C0) *
            Real.exp (-(Real.log 4 * (m : ℝ))) := by
            rw [Real.exp_log hC0pos]
      _ = Real.exp (Real.log C0 + -(Real.log 4 * (m : ℝ))) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(Real.log 4 * (m : ℝ)) + Real.log C0) := by
            ring_nf
  dsimp [C0] at htail_le' hexp
  exact htail_le'.trans_eq hexp

theorem ramanujanPiTerm_tail_le_geometric (m k : ℕ) :
    ramanujanPiTerm (m + 1 + k)
      ≤ (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :
          ramanujanPiTerm (m + 1 + k + 1)
            ≤ (1 / 4 : ℝ) * ramanujanPiTerm (m + 1 + k) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ramanujanPiTerm_succ_le_quarter (m + 1 + k)
      calc
        ramanujanPiTerm (m + 1 + (k + 1))
            = ramanujanPiTerm (m + 1 + k + 1) := by
              simp [Nat.add_assoc]
        _ ≤ (1 / 4 : ℝ) * ramanujanPiTerm (m + 1 + k) := hstep
        _ ≤ (1 / 4 : ℝ) *
              ((1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 4 : ℝ) ^ (k + 1) * ramanujanPiTerm (m + 1) := by
              rw [pow_succ']
              ring

private theorem summable_ramanujanPiTerm_tail (m : ℕ) :
    Summable (fun k : ℕ => ramanujanPiTerm (m + 1 + k)) := by
  have hpow : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hgeom :
      Summable
        (fun k : ℕ => (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.mul_right (ramanujanPiTerm (m + 1))
  exact Summable.of_nonneg_of_le
    (fun k => le_of_lt (ramanujanPiTerm_pos (m + 1 + k)))
    (fun k => ramanujanPiTerm_tail_le_geometric m k)
    hgeom

theorem ramanujanPi_tsum_tail_le_tailBound (m : ℕ) :
    (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
      ≤ ramanujanPiTailBound m := by
  have hpow : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hgeom :
      Summable
        (fun k : ℕ => (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.mul_right (ramanujanPiTerm (m + 1))
  have hgeom_tsum :
      (∑' k : ℕ, (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1))
        = ramanujanPiTailBound m := by
    unfold ramanujanPiTailBound
    calc
      (∑' k : ℕ, (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1))
          =
        (∑' k : ℕ, (1 / 4 : ℝ) ^ k) *
          ramanujanPiTerm (m + 1) := by
            rw [tsum_mul_right]
      _ = (4 / 3 : ℝ) * ramanujanPiTerm (m + 1) := by
            rw [tsum_geometric_of_norm_lt_one
              (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
            norm_num
  have hle :
      (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
        ≤
      (∑' k : ℕ, (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1)) :=
    (summable_ramanujanPiTerm_tail m).tsum_le_tsum
      (fun k => ramanujanPiTerm_tail_le_geometric m k) hgeom
  exact hle.trans_eq hgeom_tsum

theorem ramanujanPi_tsum_tail_eq
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi)) (m : ℕ) :
    (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
      = 1 / Real.pi - ramanujanPiPartial m := by
  have hsum_eq : (∑' n : ℕ, ramanujanPiTerm n) = 1 / Real.pi :=
    hRam.tsum_eq
  have hdecomp :
      ramanujanPiPartial m +
          (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
        = 1 / Real.pi := by
    calc
      ramanujanPiPartial m +
          (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
          = (∑' n : ℕ, ramanujanPiTerm n) := by
              simpa [ramanujanPiPartial, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using
                (hRam.summable.sum_add_tsum_nat_add (m + 1))
      _ = 1 / Real.pi := hsum_eq
  linarith

theorem ramanujanPi_interval_contains_inv_pi_of_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi)) :
    ∀ m : ℕ,
      ramanujanPiL m ≤ 1 / Real.pi ∧
      1 / Real.pi ≤ ramanujanPiU m := by
  intro m
  have htail_eq := ramanujanPi_tsum_tail_eq hRam m
  have htail_nonneg :
      0 ≤ (∑' k : ℕ, ramanujanPiTerm (m + 1 + k)) :=
    tsum_nonneg fun k => le_of_lt (ramanujanPiTerm_pos (m + 1 + k))
  have htail_bound :
      (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
        ≤ ramanujanPiTailBound m :=
    ramanujanPi_tsum_tail_le_tailBound m
  constructor
  · unfold ramanujanPiL
    rw [htail_eq] at htail_nonneg
    linarith
  · unfold ramanujanPiU
    rw [htail_eq] at htail_bound
    linarith

theorem ramanujanPiTailBound_pos (m : ℕ) :
    0 < ramanujanPiTailBound m := by
  unfold ramanujanPiTailBound
  exact mul_pos (by norm_num) (ramanujanPiTerm_pos (m + 1))

theorem ramanujanPi_hLU (m : ℕ) :
    ramanujanPiL m < ramanujanPiU m := by
  unfold ramanujanPiL ramanujanPiU
  have htail := ramanujanPiTailBound_pos m
  linarith

theorem ramanujanPi_width (m : ℕ) :
    ramanujanPiU m - ramanujanPiL m = ramanujanPiTailBound m := by
  unfold ramanujanPiL ramanujanPiU
  ring

theorem ramanujanPiTailBound_exp_lower_of_gt_six_log_two
    {c : ℝ} (hc : 6 * Real.log 2 < c) :
    ∀ᶠ m : ℕ in Filter.atTop,
      Real.exp (-(c * (m : ℝ))) ≤ ramanujanPiTailBound m := by
  let c₀ : ℝ := (6 * Real.log 2 + c) / 2
  have hc₀_lower : 6 * Real.log 2 < c₀ := by
    dsimp [c₀]
    linarith
  have hc₀c : c₀ < c := by
    dsimp [c₀]
    linarith
  have hterm := ramanujanPiTerm_exp_lower_of_gt_six_log_two hc₀_lower
  rw [eventually_atTop] at hterm
  rcases hterm with ⟨N, hN⟩
  let C : ℝ := (4 / 3 : ℝ) * Real.exp (-c₀)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (by norm_num) (Real.exp_pos _)
  have habsorb := const_mul_exp_lower_absorb hCpos hc₀c
  filter_upwards [habsorb, eventually_ge_atTop N] with m habs hm
  have hterm_shift :
      Real.exp (-(c₀ * ((m + 1 : ℕ) : ℝ))) ≤ ramanujanPiTerm (m + 1) :=
    hN (m + 1) (by omega)
  calc
    Real.exp (-(c * (m : ℝ)))
        ≤ C * Real.exp (-(c₀ * (m : ℝ))) := habs
    _ = (4 / 3 : ℝ) *
          Real.exp (-(c₀ * ((m + 1 : ℕ) : ℝ))) := by
          dsimp [C]
          calc
            (4 / 3 : ℝ) * Real.exp (-c₀) *
                Real.exp (-(c₀ * (m : ℝ)))
                =
              (4 / 3 : ℝ) *
                (Real.exp (-c₀) * Real.exp (-(c₀ * (m : ℝ)))) := by
                ring
            _ = (4 / 3 : ℝ) *
                Real.exp (-c₀ + -(c₀ * (m : ℝ))) := by
                rw [← Real.exp_add]
            _ = (4 / 3 : ℝ) *
                Real.exp (-(c₀ * ((m + 1 : ℕ) : ℝ))) := by
                congr 1
                norm_num [Nat.cast_add, Nat.cast_one]
                ring
    _ ≤ (4 / 3 : ℝ) * ramanujanPiTerm (m + 1) := by
          exact mul_le_mul_of_nonneg_left hterm_shift (by norm_num)
    _ = ramanujanPiTailBound m := by
          rfl

/-- The partial sums converge to the Ramanujan value, assuming the summation
identity as an external analytic input. -/
theorem ramanujanPiPartial_tendsto_of_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi)) :
    Tendsto ramanujanPiPartial atTop (𝓝 (1 / Real.pi)) := by
  have ht := hRam.tendsto_sum_nat
  have hshift : Tendsto (fun m : ℕ => m + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  simpa [ramanujanPiPartial, Function.comp_def] using ht.comp hshift

theorem ramanujanPiU_tendsto_of_hasSum_tail_tendsto
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (htail : Tendsto ramanujanPiTailBound atTop (𝓝 0)) :
    Tendsto ramanujanPiU atTop (𝓝 (1 / Real.pi)) := by
  have hpartial := ramanujanPiPartial_tendsto_of_hasSum hRam
  have hadd := hpartial.add htail
  simpa [ramanujanPiU, ramanujanPiL] using hadd

theorem ramanujanPi_eventuallyAlphaInInterval_of_forall
    (hcontains : ∀ m : ℕ,
      ramanujanPiL m ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ ramanujanPiU m) :
    EventuallyAlphaInInterval (1 / Real.pi) ramanujanPiL ramanujanPiU := by
  unfold EventuallyAlphaInInterval
  exact Eventually.of_forall hcontains

/-- Concrete shrink-to-`1/π` certificate from the Ramanujan identity, a tail
tending to zero, and pointwise interval containment. -/
theorem ramanujanPi_intervalShrinksTo_inv_pi
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (htail : Tendsto ramanujanPiTailBound atTop (𝓝 0))
    (hcontains : ∀ m : ℕ,
      ramanujanPiL m ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ ramanujanPiU m) :
    EventuallyIntervalShrinksTo (1 / Real.pi) ramanujanPiL ramanujanPiU := by
  exact ⟨ramanujanPiPartial_tendsto_of_hasSum hRam,
    ramanujanPiU_tendsto_of_hasSum_tail_tendsto hRam htail,
    ramanujanPi_eventuallyAlphaInInterval_of_forall hcontains⟩

/-- Concrete shrink-to-`1/π` wrapper using the proved geometric tail decay. -/
theorem ramanujanPi_intervalShrinksTo_inv_pi_of_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hcontains : ∀ m : ℕ,
      ramanujanPiL m ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ ramanujanPiU m) :
    EventuallyIntervalShrinksTo (1 / Real.pi) ramanujanPiL ramanujanPiU :=
  ramanujanPi_intervalShrinksTo_inv_pi
    hRam ramanujanPiTailBound_tendsto_zero hcontains

theorem ramanujanPi_eventuallyExpWidthUpper_of_tailBound
    {κ C : ℝ}
    (htail : ∀ᶠ m : ℕ in atTop,
      ramanujanPiTailBound m ≤ Real.exp (-(κ * (m : ℝ)) + C)) :
    EventuallyExpWidthUpper ramanujanPiL ramanujanPiU κ C := by
  unfold EventuallyExpWidthUpper
  filter_upwards [htail] with m hm
  rw [ramanujanPi_width]
  exact hm

theorem ramanujanPi_eventuallyExpWidthUpper_log4 :
    EventuallyExpWidthUpper
      ramanujanPiL ramanujanPiU
      (Real.log 4)
      (Real.log ((4 / 3 : ℝ) * ramanujanPiTerm 0)) := by
  exact ramanujanPi_eventuallyExpWidthUpper_of_tailBound
    (Eventually.of_forall ramanujanPiTailBound_le_exp_log4)

theorem ramanujanPi_eventuallyExpWidthUpper_log4_from_hasSum
    (_hRam : HasSum ramanujanPiTerm (1 / Real.pi)) :
    EventuallyExpWidthUpper
      ramanujanPiL ramanujanPiU
      (Real.log 4)
      (Real.log ((4 / 3 : ℝ) * ramanujanPiTerm 0)) :=
  ramanujanPi_eventuallyExpWidthUpper_log4

theorem ramanujanPi_eventuallyExpWidthUpper_with_const_of_pos_lt_six_log_two
    {c : ℝ} (_hcpos : 0 < c) (hc : c < 6 * Real.log 2) :
    ∃ C : ℝ, EventuallyExpWidthUpper ramanujanPiL ramanujanPiU c C := by
  rcases ramanujanPiTerm_eventually_exp_bound_of_step
      (ramanujanPiTerm_succ_le_exp_of_lt_six_log_two hc) with
    ⟨C, hC⟩
  refine ⟨C + Real.log (4 / 3 : ℝ) - c, ?_⟩
  unfold EventuallyExpWidthUpper
  rw [eventually_atTop] at hC ⊢
  rcases hC with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  rw [ramanujanPi_width]
  have hterm :
      ramanujanPiTerm (m + 1)
        ≤ Real.exp (-(c * ((m + 1 : ℕ) : ℝ)) + C) :=
    hN (m + 1) (by omega)
  calc
    ramanujanPiTailBound m
        = (4 / 3 : ℝ) * ramanujanPiTerm (m + 1) := by
          rfl
    _ ≤ (4 / 3 : ℝ) *
          Real.exp (-(c * ((m + 1 : ℕ) : ℝ)) + C) := by
          exact mul_le_mul_of_nonneg_left hterm (by norm_num)
    _ = Real.exp (-(c * (m : ℝ)) +
          (C + Real.log (4 / 3 : ℝ) - c)) := by
          calc
            (4 / 3 : ℝ) *
                Real.exp (-(c * ((m + 1 : ℕ) : ℝ)) + C)
                =
              Real.exp (Real.log (4 / 3 : ℝ)) *
                Real.exp (-(c * ((m + 1 : ℕ) : ℝ)) + C) := by
                  rw [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
            _ = Real.exp (Real.log (4 / 3 : ℝ) +
                  (-(c * ((m + 1 : ℕ) : ℝ)) + C)) := by
                  rw [← Real.exp_add]
            _ = Real.exp (-(c * (m : ℝ)) +
                  (C + Real.log (4 / 3 : ℝ) - c)) := by
                  norm_num [Nat.cast_add, Nat.cast_one]
                  ring

theorem ramanujanPi_eventuallyExpWidthUpper_of_lt_six_log_two
    {c : ℝ} (hc : c < 6 * Real.log 2) :
    EventuallyExpWidthUpper ramanujanPiL ramanujanPiU c 0 := by
  rcases le_or_gt c 0 with hc_nonpos | hcpos
  · unfold EventuallyExpWidthUpper
    have hsmall :
        ∀ᶠ m : ℕ in atTop, ramanujanPiTailBound m < 1 :=
      ramanujanPiTailBound_tendsto_zero.eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with m hm
    rw [ramanujanPi_width]
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (-(c * (m : ℝ)) + 0) := by
      calc
        (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (-(c * (m : ℝ)) + 0) := by
          exact Real.exp_le_exp.mpr (by
            have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
            nlinarith)
    exact (le_of_lt hm).trans hexp_ge_one
  · let c' : ℝ := (c + 6 * Real.log 2) / 2
    have hc_lt_c' : c < c' := by
      dsimp [c']
      linarith
    have hc'_lt : c' < 6 * Real.log 2 := by
      dsimp [c']
      linarith
    have hc'pos : 0 < c' := lt_trans hcpos hc_lt_c'
    rcases
        ramanujanPi_eventuallyExpWidthUpper_with_const_of_pos_lt_six_log_two
          hc'pos hc'_lt with
      ⟨C, hC⟩
    unfold EventuallyExpWidthUpper at hC ⊢
    rw [eventually_atTop] at hC ⊢
    rcases hC with ⟨N, hN⟩
    have hgap : 0 < c' - c := sub_pos.mpr hc_lt_c'
    have habsorb :=
      eventually_const_le_pos_mul_natCast (A := C) (δ := c' - c) hgap
    rw [eventually_atTop] at habsorb
    rcases habsorb with ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    intro m hm
    have hmN : N ≤ m := le_trans (Nat.le_max_left N M) hm
    have hmM : M ≤ m := le_trans (Nat.le_max_right N M) hm
    have hw := hN m hmN
    have hconst := hM m hmM
    have hexp_le :
        Real.exp (-(c' * (m : ℝ)) + C) ≤
          Real.exp (-(c * (m : ℝ)) + 0) := by
      exact Real.exp_le_exp.mpr (by
        nlinarith)
    exact hw.trans hexp_le

theorem invPi_isIrrational : IsIrrational (1 / Real.pi) := by
  simpa [one_div] using isIrrational_of_irrational irrational_pi.inv

theorem eventuallyLeastDenominatorGe_ramanujanPi
    (hshrink :
      EventuallyIntervalShrinksTo (1 / Real.pi) ramanujanPiL ramanujanPiU)
    (Q0 : ℕ) :
    EventuallyLeastDenominatorGe ramanujanPiL ramanujanPiU ramanujanPi_hLU Q0 :=
  eventuallyLeastDenominatorGe_of_intervalShrinksTo_irrational
    invPi_isIrrational hshrink Q0

theorem eventuallyLeastDenominatorGe_ramanujanPi_of_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hcontains : ∀ m : ℕ,
      ramanujanPiL m ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ ramanujanPiU m)
    (Q0 : ℕ) :
    EventuallyLeastDenominatorGe ramanujanPiL ramanujanPiU ramanujanPi_hLU Q0 :=
  eventuallyLeastDenominatorGe_ramanujanPi
    (ramanujanPi_intervalShrinksTo_inv_pi_of_hasSum hRam hcontains) Q0

theorem ramanujanPi_intervalShrinksTo_inv_pi_from_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi)) :
    EventuallyIntervalShrinksTo (1 / Real.pi) ramanujanPiL ramanujanPiU :=
  ramanujanPi_intervalShrinksTo_inv_pi_of_hasSum
    hRam (ramanujanPi_interval_contains_inv_pi_of_hasSum hRam)

theorem eventuallyLeastDenominatorGe_ramanujanPi_from_hasSum
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (Q0 : ℕ) :
    EventuallyLeastDenominatorGe ramanujanPiL ramanujanPiU ramanujanPi_hLU Q0 :=
  eventuallyLeastDenominatorGe_ramanujanPi_of_hasSum
    hRam (ramanujanPi_interval_contains_inv_pi_of_hasSum hRam) Q0

/-- Concrete Ramanujan interval wrapper for the generic measure-width/φ bridge.

The analytic work is isolated in `hμ`, `hshrink`, `hwidth`, and `hphi`; this
theorem supplies the concrete `1 / π` irrationality and small-denominator
exclusion automatically. -/
theorem eventuallyLinearLowerBound_pathLength_ramanujanPi
    {μ ν κ C c : ℝ} {K : ℕ → ℕ}
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hshrink :
      EventuallyIntervalShrinksTo (1 / Real.pi) ramanujanPiL ramanujanPiU)
    (hwidth : EventuallyExpWidthUpper ramanujanPiL ramanujanPiU κ C)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU) K)
    (hc : c < κ / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  exact eventuallyLinearLowerBound_pathLength_of_measure_width_phiUpper
    (hLU := ramanujanPi_hLU)
    (hμ := hμ) (hν := hν) (hνpos := hνpos)
    (hαI := hshrink.2.2) (hwidth := hwidth)
    (hNoSmall := fun Q0 =>
      eventuallyLeastDenominatorGe_ramanujanPi hshrink Q0)
    (hphi := hphi) (hc := hc)

theorem eventuallyLinearLowerBound_pathLength_ramanujanPi_from_hasSum
    {μ ν c : ℝ} {K : ℕ → ℕ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU) K)
    (hc : c < (Real.log 4) / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  exact eventuallyLinearLowerBound_pathLength_ramanujanPi
    (hμ := hμ) (hν := hν) (hνpos := hνpos)
    (hshrink := ramanujanPi_intervalShrinksTo_inv_pi_from_hasSum hRam)
    (hwidth := ramanujanPi_eventuallyExpWidthUpper_log4_from_hasSum hRam)
    (hphi := hphi) (hc := hc)

theorem eventuallyLinearLowerBound_pathLength_ramanujanPi_of_lt_six_log_two
    {μ ν κ c : ℝ} {K : ℕ → ℕ}
    (hκ : κ < 6 * Real.log 2)
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU) K)
    (hc : c < κ / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  exact eventuallyLinearLowerBound_pathLength_ramanujanPi
    (hμ := hμ) (hν := hν) (hνpos := hνpos)
    (hshrink := ramanujanPi_intervalShrinksTo_inv_pi_from_hasSum hRam)
    (hwidth := ramanujanPi_eventuallyExpWidthUpper_of_lt_six_log_two hκ)
    (hphi := hphi) (hc := hc)

theorem eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp
    {μ ν c : ℝ} {K : ℕ → ℕ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU) K)
    (hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound K c := by
  let D : ℝ := ν * Real.log Real.goldenRatio
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos hνpos log_goldenRatio_pos
  have hmul : c * D < 6 * Real.log 2 := by
    exact (lt_div_iff₀ hDpos).mp hc
  let κ : ℝ := (c * D + 6 * Real.log 2) / 2
  have hκ_lt : κ < 6 * Real.log 2 := by
    dsimp [κ]
    linarith
  have hc_κ : c < κ / (ν * Real.log Real.goldenRatio) := by
    rw [show ν * Real.log Real.goldenRatio = D by rfl]
    rw [lt_div_iff₀ hDpos]
    dsimp [κ]
    linarith
  exact eventuallyLinearLowerBound_pathLength_ramanujanPi_of_lt_six_log_two
    (κ := κ) (c := c)
    hκ_lt hRam hμ hν hνpos hphi hc_κ

theorem eventually_endpointDen_oneOverPi_le_exp_of_cylinder_width
    {Λ : ℝ}
    (hΛ : 3 * Real.log 2 < Λ)
    (hcyl :
      ∀ᶠ m : ℕ in atTop,
        ((continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ^ 2) *
          (ramanujanPiU m - ramanujanPiL m) ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)) := by
  let c : ℝ := (6 * Real.log 2 + 2 * Λ) / 2
  have hc_lower : 6 * Real.log 2 < c := by
    dsimp [c]
    linarith
  have hc_half : c / 2 < Λ := by
    dsimp [c]
    linarith
  have hwidth := ramanujanPiTailBound_exp_lower_of_gt_six_log_two hc_lower
  filter_upwards [hwidth, hcyl] with m hwidth_m hcyl_m
  rw [ramanujanPi_width] at hcyl_m
  let q : ℝ := (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ)
  have hq_nonneg : 0 ≤ q := by
    positivity
  have hq_sq_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hq_width :
      q ^ 2 * Real.exp (-(c * (m : ℝ))) ≤ 1 := by
    calc
      q ^ 2 * Real.exp (-(c * (m : ℝ)))
          ≤ q ^ 2 * ramanujanPiTailBound m := by
          exact mul_le_mul_of_nonneg_left hwidth_m hq_sq_nonneg
      _ ≤ 1 := by
          simpa [q] using hcyl_m
  have hq_sq_le_exp :
      q ^ 2 ≤ Real.exp (c * (m : ℝ)) := by
    have hmul :
        (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
            Real.exp (c * (m : ℝ)) ≤
          1 * Real.exp (c * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hq_width
        (le_of_lt (Real.exp_pos _))
    calc
      q ^ 2
          =
        (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
          Real.exp (c * (m : ℝ)) := by
          calc
            q ^ 2 = q ^ 2 * 1 := by
                ring
            _ = q ^ 2 *
                Real.exp (-(c * (m : ℝ)) + c * (m : ℝ)) := by
                rw [show -(c * (m : ℝ)) + c * (m : ℝ) = 0 by ring]
                rw [Real.exp_zero]
            _ = q ^ 2 *
                (Real.exp (-(c * (m : ℝ))) *
                  Real.exp (c * (m : ℝ))) := by
                rw [← Real.exp_add]
            _ =
              (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
                Real.exp (c * (m : ℝ)) := by
                ring
      _ ≤ 1 * Real.exp (c * (m : ℝ)) := hmul
      _ = Real.exp (c * (m : ℝ)) := by
          ring
  have hq_sq_le_half_exp_sq :
      q ^ 2 ≤ (Real.exp ((c / 2) * (m : ℝ))) ^ 2 := by
    calc
      q ^ 2 ≤ Real.exp (c * (m : ℝ)) := hq_sq_le_exp
      _ = (Real.exp ((c / 2) * (m : ℝ))) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
  have hq_le_half :
      q ≤ Real.exp ((c / 2) * (m : ℝ)) :=
    (sq_le_sq₀ hq_nonneg (le_of_lt (Real.exp_pos _))).mp
      hq_sq_le_half_exp_sq
  have hhalf_le :
      Real.exp ((c / 2) * (m : ℝ)) ≤
        Real.exp (Λ * (m : ℝ)) := by
    exact Real.exp_le_exp.mpr (by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (le_of_lt hc_half) hm_nonneg)
  exact hq_le_half.trans hhalf_le

theorem eventuallyLinearLowerBound_B_oneOverPi_of_ramanujanPi_sharp
    {μ ν c c' : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound B_oneOverPi c' := by
  have hJ : EventuallyLinearLowerBound J_oneOverPi c :=
    eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp
      (K := J_oneOverPi)
      hRam hμ hν hνpos hphi hc
  exact eventuallyLinearLowerBound_B_oneOverPi_of_J_oneOverPi hJ hc'

theorem eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_ramanujanPi_sharp
    {μ ν c c' : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio))
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound certifiedAOneOverPiCard c' := by
  have hJ : EventuallyLinearLowerBound J_oneOverPi c :=
    eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp
      (K := J_oneOverPi)
      hRam hμ hν hνpos hphi hc
  exact eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_J hJ hc'

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_slope
    {μ ν c ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio))
    (hρ : ρ < c / 2)
    (hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExp m Λ).card : ℝ) := by
  have hcard :
      EventuallyLinearLowerBound certifiedAOneOverPiCard ρ :=
    eventuallyLinearLowerBound_certifiedAOneOverPiCard_of_ramanujanPi_sharp
      hRam hμ hν hνpos hphi hc hρ
  exact
    eventuallyManyCertifiedAOneOverPiBelowExp_of_card_lower_and_endpoint_bound
      hcard hden

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp
    {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hρ :
      ρ <
        ((6 * Real.log 2) / (ν * Real.log Real.goldenRatio)) / 2)
    (hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExp m Λ).card : ℝ) := by
  let C : ℝ := (6 * Real.log 2) / (ν * Real.log Real.goldenRatio)
  let c : ℝ := (2 * ρ + C) / 2
  have hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio) := by
    dsimp [c, C]
    linarith
  have hρc : ρ < c / 2 := by
    dsimp [c, C] at *
    linarith
  exact
    eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_slope
      (c := c) hRam hμ hν hνpos hphi hc hρc hden

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_cylinder
    {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hρ :
      ρ <
        ((6 * Real.log 2) / (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ)
    (hcyl :
      ∀ᶠ m : ℕ in atTop,
        ((continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ^ 2) *
          (ramanujanPiU m - ramanujanPiL m) ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExp m Λ).card : ℝ) := by
  exact
    eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp
      hRam hμ hν hνpos hphi hρ
      (eventually_endpointDen_oneOverPi_le_exp_of_cylinder_width hΛ hcyl)

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanCFCylinderWidth.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Continued-fraction cylinder width for Ramanujan intervals

This file isolates the geometric part of the endpoint-height bridge.  It proves
that interval containment in a continued-fraction cylinder gives the square
denominator/width certificate used by the Ramanujan `1 / π` wrappers.
-/

noncomputable def cfCylinderEndpoint0 (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  (continuantNum a j : ℝ) / (continuantDen a j : ℝ)

noncomputable def cfCylinderEndpoint1 (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  ((continuantNum a j + continuantNumPrev a j : ℕ) : ℝ) /
    ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ)

def IntervalInCFCylinder
    (a : ℕ → ℕ) (j : ℕ) (L U : ℝ) : Prop :=
  min (cfCylinderEndpoint0 a j) (cfCylinderEndpoint1 a j) ≤ L ∧
    U ≤ max (cfCylinderEndpoint0 a j) (cfCylinderEndpoint1 a j)

def EventuallyIntervalInCFCylinder
    (a : ℕ → ℕ) (J : ℕ → ℕ) (L U : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, IntervalInCFCylinder a (J m) (L m) (U m)

theorem cfCylinder_endpoint_abs_sub
    (a : ℕ → ℕ) (j : ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    |cfCylinderEndpoint0 a j - cfCylinderEndpoint1 a j| =
      1 / ((continuantDen a j : ℝ) *
        ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ)) := by
  unfold cfCylinderEndpoint0 cfCylinderEndpoint1
  let p : ℝ := continuantNum a j
  let pp : ℝ := continuantNumPrev a j
  let q : ℝ := continuantDen a j
  let qq : ℝ := continuantDenPrev a j
  have hqpos_nat : 1 ≤ continuantDen a j :=
    one_le_continuantDen_of_partials_pos_global a hpos j
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hqpos_nat
  have hqsumpos : 0 < q + qq := by
    dsimp [q, qq]
    positivity
  have hprodpos : 0 < q * (q + qq) := mul_pos hqpos hqsumpos
  have hdetR : |p * qq - pp * q| = (1 : ℝ) := by
    dsimp [p, pp, q, qq]
    exact_mod_cast continuant_det_abs_one a j
  calc
    |(continuantNum a j : ℝ) / (continuantDen a j : ℝ) -
        ((continuantNum a j + continuantNumPrev a j : ℕ) : ℝ) /
          ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ)|
        = |p / q - (p + pp) / (q + qq)| := by
        simp [p, pp, q, qq, Nat.cast_add]
    _ = |(p * qq - pp * q) / (q * (q + qq))| := by
        field_simp [ne_of_gt hqpos, ne_of_gt hqsumpos]
        ring_nf
    _ = |p * qq - pp * q| / |q * (q + qq)| := by
        rw [abs_div]
    _ = 1 / (q * (q + qq)) := by
        rw [hdetR, abs_of_pos hprodpos]
    _ = 1 / ((continuantDen a j : ℝ) *
          ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ)) := by
        simp [q, qq, Nat.cast_add]

theorem cfCylinder_width_le_inv_sq_den
    (a : ℕ → ℕ) (j : ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    |cfCylinderEndpoint0 a j - cfCylinderEndpoint1 a j|
      ≤ 1 / ((continuantDen a j : ℝ) ^ 2) := by
  rw [cfCylinder_endpoint_abs_sub a j hpos]
  have hqpos_nat : 1 ≤ continuantDen a j :=
    one_le_continuantDen_of_partials_pos_global a hpos j
  have hqpos : 0 < (continuantDen a j : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hqpos_nat
  have hprodpos :
      0 <
        (continuantDen a j : ℝ) *
          ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ) := by
    positivity
  have hsqpos : 0 < (continuantDen a j : ℝ) ^ 2 := by
    positivity
  have hden_le :
      (continuantDen a j : ℝ) ^ 2 ≤
        (continuantDen a j : ℝ) *
          ((continuantDen a j + continuantDenPrev a j : ℕ) : ℝ) := by
    rw [pow_two]
    norm_num [Nat.cast_add]
    nlinarith [show (0 : ℝ) ≤ (continuantDenPrev a j : ℝ) by positivity]
  exact one_div_le_one_div_of_le hsqpos hden_le

theorem interval_width_le_abs_endpoint_diff
    {L U A B : ℝ}
    (hsub : min A B ≤ L ∧ U ≤ max A B) :
    U - L ≤ |A - B| := by
  have hwidth : U - L ≤ max A B - min A B := by
    linarith [hsub.1, hsub.2]
  have hmaxmin : max A B - min A B = |A - B| := by
    by_cases hAB : A ≤ B
    · have hmin : min A B = A := min_eq_left hAB
      have hmax : max A B = B := max_eq_right hAB
      rw [hmin, hmax, abs_sub_comm]
      exact (abs_of_nonneg (sub_nonneg.mpr hAB)).symm
    · have hBA : B ≤ A := le_of_not_ge hAB
      have hmin : min A B = B := min_eq_right hBA
      have hmax : max A B = A := max_eq_left hBA
      rw [hmin, hmax]
      exact (abs_of_nonneg (sub_nonneg.mpr hBA)).symm
  exact hwidth.trans_eq hmaxmin

theorem interval_width_mul_sq_den_le_one_of_mem_cfCylinder
    {a : ℕ → ℕ} {j : ℕ} {L U : ℝ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hsub : IntervalInCFCylinder a j L U) :
    ((continuantDen a j : ℝ) ^ 2) * (U - L) ≤ 1 := by
  let A : ℝ := cfCylinderEndpoint0 a j
  let B : ℝ := cfCylinderEndpoint1 a j
  have hwidth1 : U - L ≤ |A - B| := by
    exact interval_width_le_abs_endpoint_diff hsub
  have hwidth2 : |A - B| ≤ 1 / ((continuantDen a j : ℝ) ^ 2) := by
    dsimp [A, B]
    exact cfCylinder_width_le_inv_sq_den a j hpos
  have hwidth : U - L ≤ 1 / ((continuantDen a j : ℝ) ^ 2) :=
    hwidth1.trans hwidth2
  have hqpos_nat : 1 ≤ continuantDen a j :=
    one_le_continuantDen_of_partials_pos_global a hpos j
  have hqpos : 0 < (continuantDen a j : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hqpos_nat
  have hsqpos : 0 < (continuantDen a j : ℝ) ^ 2 := by
    positivity
  calc
    ((continuantDen a j : ℝ) ^ 2) * (U - L)
        ≤ ((continuantDen a j : ℝ) ^ 2) *
            (1 / ((continuantDen a j : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hwidth (le_of_lt hsqpos)
    _ = 1 := by
          rw [pow_two]
          field_simp [ne_of_gt hqpos]

theorem eventually_cylinder_width_certificate_oneOverPi
    (hcyl :
      EventuallyIntervalInCFCylinder oneOverPiCF J_oneOverPi
        ramanujanPiL ramanujanPiU) :
    ∀ᶠ m : ℕ in atTop,
      ((continuantDen oneOverPiCF (J_oneOverPi m) : ℝ) ^ 2) *
        (ramanujanPiU m - ramanujanPiL m) ≤ 1 := by
  filter_upwards [hcyl] with m hm
  exact interval_width_mul_sq_den_le_one_of_mem_cfCylinder
    (a := oneOverPiCF)
    (j := J_oneOverPi m)
    (L := ramanujanPiL m)
    (U := ramanujanPiU m)
    oneOverPiCF_partials_pos
    hm

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_cylinderContain
    {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi : EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      J_oneOverPi)
    (hρ :
      ρ <
        ((6 * Real.log 2) / (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ)
    (hcyl :
      EventuallyIntervalInCFCylinder oneOverPiCF J_oneOverPi
        ramanujanPiL ramanujanPiU) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExp m Λ).card : ℝ) := by
  exact
    eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_cylinder
      hRam hμ hν hνpos hphi hρ hΛ
      (eventually_cylinder_width_certificate_oneOverPi hcyl)

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanCertifiedSubsequenceAt.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Parameterized certified subsequences for `A_{1 / π}`

This file removes the serious theorem layer from the placeholder
`J_oneOverPi`.  A certified-prefix function is now an explicit parameter.
-/

noncomputable def B_oneOverPiAt (Jcert : ℕ → ℕ) (m : ℕ) : ℕ :=
  certifiedBlockCountAt oneOverPiCF Jcert m

noncomputable def certifiedAOneOverPiSubsetAt
    (Jcert : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  certifiedOddBlocks oneOverPiCF (Jcert m)

noncomputable def certifiedAOneOverPiCardAt
    (Jcert : ℕ → ℕ) (m : ℕ) : ℕ :=
  (certifiedAOneOverPiSubsetAt Jcert m).card

noncomputable def certifiedAOneOverPiSubsetBelowExpAt
    (Jcert : ℕ → ℕ) (m : ℕ) (Λ : ℝ) : Finset ℕ := by
  classical
  exact (certifiedAOneOverPiSubsetAt Jcert m).filter
    (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))

@[simp] theorem certifiedAOneOverPiSubsetAt_apply
    (Jcert : ℕ → ℕ) (m : ℕ) :
    certifiedAOneOverPiSubsetAt Jcert m =
      certifiedOddBlocks oneOverPiCF (Jcert m) := rfl

theorem certifiedAOneOverPiCardAt_eq_card
    (Jcert : ℕ → ℕ) (m : ℕ) :
    certifiedAOneOverPiCardAt Jcert m =
      (certifiedAOneOverPiSubsetAt Jcert m).card := rfl

@[simp] theorem mem_certifiedAOneOverPiSubsetBelowExpAt_iff
    {Jcert : ℕ → ℕ} {m x : ℕ} {Λ : ℝ} :
    x ∈ certifiedAOneOverPiSubsetBelowExpAt Jcert m Λ ↔
      x ∈ certifiedAOneOverPiSubsetAt Jcert m ∧
        (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  classical
  unfold certifiedAOneOverPiSubsetBelowExpAt
  simp

theorem certifiedAOneOverPiSubsetAt_mem_A
    (Jcert : ℕ → ℕ)
    (hpos : 0 < oneOverPi)
    (hirr : IsIrrational oneOverPi)
    (hcf : IsSimpleCFExpansion oneOverPi oneOverPiCF)
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubsetAt Jcert m) :
    x ∈ A oneOverPi := by
  unfold certifiedAOneOverPiSubsetAt at hx
  exact certifiedOddBlocks_subset_A_of_IsSimpleCFExpansion hpos hirr hcf hx

theorem certifiedAOneOverPiSubsetAt_mem_A_from_A_eq
    (Jcert : ℕ → ℕ)
    (hA : A oneOverPi = oddBlockASet oneOverPiCF)
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubsetAt Jcert m) :
    x ∈ A oneOverPi := by
  unfold certifiedAOneOverPiSubsetAt at hx
  exact certifiedOddBlocks_subset_A_of_A_eq_oddBlockASet hA hx

theorem certifiedAOneOverPiSubsetAt_le_endpoint_denominator
    {Jcert : ℕ → ℕ} {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiSubsetAt Jcert m) :
    x ≤ continuantDen oneOverPiCF (Jcert m) := by
  unfold certifiedAOneOverPiSubsetAt at hx
  rw [mem_certifiedOddBlocks_iff] at hx
  rcases hx with ⟨_hx0, j, hj, hxblock⟩
  have hx_endpoint :
      x ≤ continuantDen oneOverPiCF (j + 1) :=
    canonicalOddDenominatorBlock_le_endpoint
      (a := oneOverPiCF) oneOverPiCF_partials_pos hxblock
  have hmono :
      continuantDen oneOverPiCF (j + 1) ≤
        continuantDen oneOverPiCF (Jcert m) :=
    continuantDen_mono_of_partials_pos_le
      oneOverPiCF oneOverPiCF_partials_pos (by omega)
  exact hx_endpoint.trans hmono

theorem certifiedAOneOverPiSubsetAt_bound_of_endpoint_denominator_le_exp
    {Jcert : ℕ → ℕ} {m x : ℕ} {Λ : ℝ}
    (hden :
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)))
    (hx : x ∈ certifiedAOneOverPiSubsetAt Jcert m) :
    (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  have hxden_nat :=
    certifiedAOneOverPiSubsetAt_le_endpoint_denominator
      (Jcert := Jcert) hx
  have hxden_real :
      (x : ℝ) ≤
        (continuantDen oneOverPiCF (Jcert m) : ℝ) := by
    exact_mod_cast hxden_nat
  exact hxden_real.trans hden

theorem certifiedAOneOverPiSubsetBelowExpAt_eq_self_of_endpoint_denominator_le_exp
    {Jcert : ℕ → ℕ} {m : ℕ} {Λ : ℝ}
    (hden :
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ))) :
    certifiedAOneOverPiSubsetBelowExpAt Jcert m Λ =
      certifiedAOneOverPiSubsetAt Jcert m := by
  classical
  ext x
  rw [mem_certifiedAOneOverPiSubsetBelowExpAt_iff]
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx,
      certifiedAOneOverPiSubsetAt_bound_of_endpoint_denominator_le_exp
        (Jcert := Jcert) hden hx⟩

theorem eventuallyManyCertifiedAOneOverPiBelowExpAt_of_card_lower_and_endpoint_bound
    {Jcert : ℕ → ℕ} {ρ Λ : ℝ}
    (hcard : EventuallyLinearLowerBound (certifiedAOneOverPiCardAt Jcert) ρ)
    (hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExpAt Jcert m Λ).card : ℝ) := by
  unfold EventuallyLinearLowerBound at hcard
  filter_upwards [hcard, hden] with m hcardm hdenm
  rw [certifiedAOneOverPiSubsetBelowExpAt_eq_self_of_endpoint_denominator_le_exp
    (Jcert := Jcert) hdenm]
  simpa [certifiedAOneOverPiCardAt_eq_card] using hcardm

theorem eventuallyLinearLowerBound_B_oneOverPiAt_of_Jcert
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (B_oneOverPiAt Jcert) c' := by
  simpa [B_oneOverPiAt] using
    eventuallyLinearLowerBound_certifiedBlockCountAt_of_Jcert
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      (Jcert := Jcert)
      (c := c) (c' := c') hJ hc'

theorem eventuallyLinearLowerBound_certifiedAOneOverPiCardAt_of_Jcert
    {Jcert : ℕ → ℕ} {c c' : ℝ}
    (hJ : EventuallyLinearLowerBound Jcert c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound (certifiedAOneOverPiCardAt Jcert) c' := by
  simpa [certifiedAOneOverPiCardAt, certifiedAOneOverPiSubsetAt] using
    eventuallyLinearLowerBound_certifiedOddBlocksCardAt_of_Jcert
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      (Jcert := Jcert)
      (c := c) (c' := c') hJ hc'

theorem eventually_cylinder_width_certificate_oneOverPiAt
    {Jcert : ℕ → ℕ}
    (hcyl :
      EventuallyIntervalInCFCylinder oneOverPiCF Jcert
        ramanujanPiL ramanujanPiU) :
    ∀ᶠ m : ℕ in atTop,
      ((continuantDen oneOverPiCF (Jcert m) : ℝ) ^ 2) *
        (ramanujanPiU m - ramanujanPiL m) ≤ 1 := by
  filter_upwards [hcyl] with m hm
  exact interval_width_mul_sq_den_le_one_of_mem_cfCylinder
    (a := oneOverPiCF)
    (j := Jcert m)
    (L := ramanujanPiL m)
    (U := ramanujanPiU m)
    oneOverPiCF_partials_pos
    hm

theorem eventually_endpointDen_oneOverPiAt_le_exp_of_cylinder_width
    {Jcert : ℕ → ℕ} {Λ : ℝ}
    (hΛ : 3 * Real.log 2 < Λ)
    (hcyl :
      ∀ᶠ m : ℕ in atTop,
        ((continuantDen oneOverPiCF (Jcert m) : ℝ) ^ 2) *
          (ramanujanPiU m - ramanujanPiL m) ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)) := by
  let c : ℝ := (6 * Real.log 2 + 2 * Λ) / 2
  have hc_lower : 6 * Real.log 2 < c := by
    dsimp [c]
    linarith
  have hc_half : c / 2 < Λ := by
    dsimp [c]
    linarith
  have hwidth := ramanujanPiTailBound_exp_lower_of_gt_six_log_two hc_lower
  filter_upwards [hwidth, hcyl] with m hwidth_m hcyl_m
  rw [ramanujanPi_width] at hcyl_m
  let q : ℝ := (continuantDen oneOverPiCF (Jcert m) : ℝ)
  have hq_nonneg : 0 ≤ q := by
    positivity
  have hq_sq_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hq_width :
      q ^ 2 * Real.exp (-(c * (m : ℝ))) ≤ 1 := by
    calc
      q ^ 2 * Real.exp (-(c * (m : ℝ)))
          ≤ q ^ 2 * ramanujanPiTailBound m := by
          exact mul_le_mul_of_nonneg_left hwidth_m hq_sq_nonneg
      _ ≤ 1 := by
          simpa [q] using hcyl_m
  have hq_sq_le_exp :
      q ^ 2 ≤ Real.exp (c * (m : ℝ)) := by
    have hmul :
        (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
            Real.exp (c * (m : ℝ)) ≤
          1 * Real.exp (c * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hq_width
        (le_of_lt (Real.exp_pos _))
    calc
      q ^ 2
          =
        (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
          Real.exp (c * (m : ℝ)) := by
          calc
            q ^ 2 = q ^ 2 * 1 := by
                ring
            _ = q ^ 2 *
                Real.exp (-(c * (m : ℝ)) + c * (m : ℝ)) := by
                rw [show -(c * (m : ℝ)) + c * (m : ℝ) = 0 by ring]
                rw [Real.exp_zero]
            _ = q ^ 2 *
                (Real.exp (-(c * (m : ℝ))) *
                  Real.exp (c * (m : ℝ))) := by
                rw [← Real.exp_add]
            _ =
              (q ^ 2 * Real.exp (-(c * (m : ℝ)))) *
                Real.exp (c * (m : ℝ)) := by
                ring
      _ ≤ 1 * Real.exp (c * (m : ℝ)) := hmul
      _ = Real.exp (c * (m : ℝ)) := by
          ring
  have hq_sq_le_half_exp_sq :
      q ^ 2 ≤ (Real.exp ((c / 2) * (m : ℝ))) ^ 2 := by
    calc
      q ^ 2 ≤ Real.exp (c * (m : ℝ)) := hq_sq_le_exp
      _ = (Real.exp ((c / 2) * (m : ℝ))) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
  have hq_le_half :
      q ≤ Real.exp ((c / 2) * (m : ℝ)) :=
    (sq_le_sq₀ hq_nonneg (le_of_lt (Real.exp_pos _))).mp
      hq_sq_le_half_exp_sq
  have hhalf_le :
      Real.exp ((c / 2) * (m : ℝ)) ≤
        Real.exp (Λ * (m : ℝ)) := by
    exact Real.exp_le_exp.mpr (by
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (le_of_lt hc_half) hm_nonneg)
  exact hq_le_half.trans hhalf_le

theorem eventually_endpointDen_oneOverPiAt_le_exp_of_cylinderContain
    {Jcert : ℕ → ℕ} {Λ : ℝ}
    (hΛ : 3 * Real.log 2 < Λ)
    (hcyl :
      EventuallyIntervalInCFCylinder oneOverPiCF Jcert
        ramanujanPiL ramanujanPiU) :
    ∀ᶠ m : ℕ in atTop,
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)) := by
  exact eventually_endpointDen_oneOverPiAt_le_exp_of_cylinder_width
    (Jcert := Jcert) hΛ
    (eventually_cylinder_width_certificate_oneOverPiAt
      (Jcert := Jcert) hcyl)

theorem eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp_at
    {Jcert : ℕ → ℕ} {μ ν c : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi :
      EventuallyPhiUpperFromPathLength
        (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
        Jcert)
    (hc : c < (6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) :
    EventuallyLinearLowerBound Jcert c :=
  eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp
    (K := Jcert) hRam hμ hν hνpos hphi hc

theorem eventuallyLinearLowerBound_B_oneOverPiAt_of_ramanujanPi_sharp
    {Jcert : ℕ → ℕ} {μ ν ρ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi :
      EventuallyPhiUpperFromPathLength
        (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
        Jcert)
    (hρ :
      ρ < ((6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) / 2) :
    EventuallyLinearLowerBound (B_oneOverPiAt Jcert) ρ := by
  let C : ℝ := (6 * Real.log 2) / (ν * Real.log Real.goldenRatio)
  let c : ℝ := (2 * ρ + C) / 2
  have hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio) := by
    dsimp [c, C]
    linarith
  have hρc : ρ < c / 2 := by
    dsimp [c, C] at *
    linarith
  have hJ : EventuallyLinearLowerBound Jcert c :=
    eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp_at
      (Jcert := Jcert)
      hRam hμ hν hνpos hphi hc
  exact eventuallyLinearLowerBound_B_oneOverPiAt_of_Jcert hJ hρc

theorem eventuallyLinearLowerBound_certifiedAOneOverPiCardAt_of_ramanujanPi_sharp
    {Jcert : ℕ → ℕ} {μ ν ρ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi :
      EventuallyPhiUpperFromPathLength
        (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
        Jcert)
    (hρ :
      ρ < ((6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) / 2) :
    EventuallyLinearLowerBound (certifiedAOneOverPiCardAt Jcert) ρ := by
  let C : ℝ := (6 * Real.log 2) / (ν * Real.log Real.goldenRatio)
  let c : ℝ := (2 * ρ + C) / 2
  have hc : c < (6 * Real.log 2) / (ν * Real.log Real.goldenRatio) := by
    dsimp [c, C]
    linarith
  have hρc : ρ < c / 2 := by
    dsimp [c, C] at *
    linarith
  have hJ : EventuallyLinearLowerBound Jcert c :=
    eventuallyLinearLowerBound_pathLength_ramanujanPi_sharp_at
      (Jcert := Jcert)
      hRam hμ hν hνpos hphi hc
  exact eventuallyLinearLowerBound_certifiedAOneOverPiCardAt_of_Jcert hJ hρc

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_cylinderContain_at
    {Jcert : ℕ → ℕ} {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi :
      EventuallyPhiUpperFromPathLength
        (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
        Jcert)
    (hcyl :
      EventuallyIntervalInCFCylinder oneOverPiCF Jcert
        ramanujanPiL ramanujanPiU)
    (hρ :
      ρ < ((6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExpAt Jcert m Λ).card : ℝ) := by
  have hcard :
      EventuallyLinearLowerBound (certifiedAOneOverPiCardAt Jcert) ρ :=
    eventuallyLinearLowerBound_certifiedAOneOverPiCardAt_of_ramanujanPi_sharp
      (Jcert := Jcert)
      hRam hμ hν hνpos hphi hρ
  have hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ)) :=
    eventually_endpointDen_oneOverPiAt_le_exp_of_cylinderContain
      (Jcert := Jcert) hΛ hcyl
  exact
    eventuallyManyCertifiedAOneOverPiBelowExpAt_of_card_lower_and_endpoint_bound
      (Jcert := Jcert) hcard hden

theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_twoFunctions
    {Jcert Kprod : ℕ → ℕ} {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hphi :
      EventuallyPhiUpperFromPathLength
        (leastDenominatorInIntervalSeq ramanujanPiL ramanujanPiU ramanujanPi_hLU)
        Kprod)
    (hKleJ : ∀ᶠ m : ℕ in atTop, Kprod m ≤ Jcert m)
    (hcylJ :
      EventuallyIntervalInCFCylinder oneOverPiCF Jcert
        ramanujanPiL ramanujanPiU)
    (hρ :
      ρ < ((6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExpAt Kprod m Λ).card : ℝ) := by
  have hcard :
      EventuallyLinearLowerBound (certifiedAOneOverPiCardAt Kprod) ρ :=
    eventuallyLinearLowerBound_certifiedAOneOverPiCardAt_of_ramanujanPi_sharp
      (Jcert := Kprod)
      hRam hμ hν hνpos hphi hρ
  have hdenJ :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ)) :=
    eventually_endpointDen_oneOverPiAt_le_exp_of_cylinderContain
      (Jcert := Jcert) hΛ hcylJ
  have hdenK :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (Kprod m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ)) := by
    filter_upwards [hKleJ, hdenJ] with m hKJ hdenm
    have hmono_nat :
        continuantDen oneOverPiCF (Kprod m) ≤
          continuantDen oneOverPiCF (Jcert m) :=
      continuantDen_mono_of_partials_pos_le
        oneOverPiCF oneOverPiCF_partials_pos hKJ
    have hmono_real :
        (continuantDen oneOverPiCF (Kprod m) : ℝ) ≤
          (continuantDen oneOverPiCF (Jcert m) : ℝ) := by
      exact_mod_cast hmono_nat
    exact hmono_real.trans hdenm
  exact
    eventuallyManyCertifiedAOneOverPiBelowExpAt_of_card_lower_and_endpoint_bound
      (Jcert := Kprod) hcard hdenK

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanCertifiedPrefixSystem.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Proof-carrying certified-prefix systems for `1 / π`

The current production theorem uses `certifiedAOneOverPiSubsetAt Kprod`, so
`Kprod` should be read as a certified continued-fraction block-prefix length.
The separate function `Jcert` records a cylinder-contained endpoint depth used
to control the height of all produced elements.

This file deliberately keeps the system proof-carrying: constructing such a
system is the next mathematical step, not hidden inside a placeholder
definition.
-/

/-- A proof-carrying certified-prefix system for the Ramanujan intervals around
`1 / π`.

`Kprod` is the usable prefix length whose certified blocks are produced.
`Jcert` is a cylinder-contained prefix depth whose endpoint denominator controls
the height.  The hypothesis `K_le_J` transfers that height control back to the
usable prefix. -/
structure OneOverPiCertifiedPrefixSystem where
  Kprod : ℕ → ℕ
  Jcert : ℕ → ℕ
  phiUpper :
    EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq
        ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      Kprod
  K_le_J :
    ∀ᶠ m : ℕ in atTop, Kprod m ≤ Jcert m
  cylinder :
    EventuallyIntervalInCFCylinder oneOverPiCF Jcert
      ramanujanPiL ramanujanPiU

/-- Final certified-subsequence theorem packaged through a proof-carrying
prefix system.

This is the honest project-level form of the current Ramanujan pipeline:
Ramanujan summation, an irrationality-measure input, and a certified-prefix
system imply linearly many certified elements of `A_{1 / π}` below
`exp(Λ m)` for every `Λ > 3 log 2`. -/
theorem eventuallyManyCertifiedAOneOverPiBelowExp_of_prefixSystem
    (S : OneOverPiCertifiedPrefixSystem)
    {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hρ :
      ρ < ((6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiSubsetBelowExpAt S.Kprod m Λ).card : ℝ) := by
  exact
    eventuallyManyCertifiedAOneOverPiBelowExp_of_ramanujanPi_sharp_twoFunctions
      (Kprod := S.Kprod)
      (Jcert := S.Jcert)
      hRam hμ hν hνpos
      S.phiUpper
      S.K_le_J
      S.cylinder
      hρ hΛ

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanCertifiedIntermediatePath.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

/-!
# Certified intermediate-path production for `A_{1 / π}`

This file starts the path-level replacement for principal-block production.
Path positions are flattened pairs `(j,t)` with `1 ≤ t ≤ a (j+1)`,
corresponding to the principal/intermediate denominator
`CFBlockDenominator a j t`.

The parity/counting theorem for the path prefix is intentionally kept as a
hypothesis in the final wrapper below; that theorem is the next finite
combinatorial bottleneck.
-/

def pathIndexStart (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  (Finset.range j).sum fun i => a (i + 1)

def flattenedPathIndex (a : ℕ → ℕ) (j t : ℕ) : ℕ :=
  pathIndexStart a j + (t - 1)

def ValidPathPair (a : ℕ → ℕ) (j t : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ a (j + 1)

noncomputable def canonicalPathPrefixIndices
    (a : ℕ → ℕ) (K : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range K).product (Finset.range (K + 1))).filter
    (fun jt : ℕ × ℕ =>
      1 ≤ jt.2 ∧ jt.2 ≤ a (jt.1 + 1) ∧
        flattenedPathIndex a jt.1 jt.2 < K)

theorem mem_canonicalPathPrefixIndices_iff
    {a : ℕ → ℕ} {K j t : ℕ} :
    (j, t) ∈ canonicalPathPrefixIndices a K ↔
      j < K ∧ 1 ≤ t ∧ t ≤ a (j + 1) ∧
        flattenedPathIndex a j t < K := by
  classical
  unfold canonicalPathPrefixIndices
  rw [Finset.mem_filter]
  change ((j, t) ∈ (Finset.range K) ×ˢ (Finset.range (K + 1)) ∧
      1 ≤ t ∧ t ≤ a (j + 1) ∧ flattenedPathIndex a j t < K) ↔
    j < K ∧ 1 ≤ t ∧ t ≤ a (j + 1) ∧
      flattenedPathIndex a j t < K
  rw [Finset.mem_product]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨⟨hj, _htK⟩, ht1, htle, hflat⟩
    exact ⟨hj, ht1, htle, hflat⟩
  · rintro ⟨hj, ht1, htle, hflat⟩
    have htK : t < K + 1 := by
      unfold flattenedPathIndex at hflat
      omega
    exact ⟨⟨hj, htK⟩, ht1, htle, hflat⟩

noncomputable def canonicalOddPathPrefixIndices
    (a : ℕ → ℕ) (K : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (canonicalPathPrefixIndices a K).filter
    (fun jt : ℕ × ℕ =>
      Odd (CFBlockNumerator a jt.1 jt.2) ∧
        2 ≤ CFBlockDenominator a jt.1 jt.2)

theorem mem_canonicalOddPathPrefixIndices_iff
    {a : ℕ → ℕ} {K j t : ℕ} :
    (j, t) ∈ canonicalOddPathPrefixIndices a K ↔
      j < K ∧ 1 ≤ t ∧ t ≤ a (j + 1) ∧
        flattenedPathIndex a j t < K ∧
        Odd (CFBlockNumerator a j t) ∧
        2 ≤ CFBlockDenominator a j t := by
  classical
  unfold canonicalOddPathPrefixIndices
  rw [Finset.mem_filter, mem_canonicalPathPrefixIndices_iff]
  constructor
  · rintro ⟨⟨hj, ht1, htle, hflat⟩, hodd, hden⟩
    exact ⟨hj, ht1, htle, hflat, hodd, hden⟩
  · rintro ⟨hj, ht1, htle, hflat, hodd, hden⟩
    exact ⟨⟨hj, ht1, htle, hflat⟩, hodd, hden⟩

noncomputable def certifiedOddPathPrefix
    (a : ℕ → ℕ) (K : ℕ) : Finset ℕ := by
  classical
  exact (canonicalOddPathPrefixIndices a K).image
    (fun jt : ℕ × ℕ => CFBlockDenominator a jt.1 jt.2 - 1)

theorem mem_oddBlockASet_of_valid_odd_path_pair
    {a : ℕ → ℕ} {j t : ℕ}
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1))
    (hodd : Odd (CFBlockNumerator a j t))
    (hden : 2 ≤ CFBlockDenominator a j t) :
    CFBlockDenominator a j t - 1 ∈ oddBlockASet a := by
  exact ⟨j, t, ht1, htle, hodd, hden, rfl⟩

theorem certifiedOddPathPrefix_subset_oddBlockASet
    (a : ℕ → ℕ) (K : ℕ) :
    ↑(certifiedOddPathPrefix a K) ⊆ oddBlockASet a := by
  intro x hx
  unfold certifiedOddPathPrefix at hx
  rcases Finset.mem_image.mp hx with ⟨jt, hjt, rfl⟩
  rcases jt with ⟨j, t⟩
  rw [mem_canonicalOddPathPrefixIndices_iff] at hjt
  exact mem_oddBlockASet_of_valid_odd_path_pair
    hjt.2.1 hjt.2.2.1 hjt.2.2.2.2.1 hjt.2.2.2.2.2

theorem certifiedOddPathPrefix_subset_A_of_IsSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ} {K : ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a) :
    ↑(certifiedOddPathPrefix a K) ⊆ A α := by
  have hA : A α = oddBlockASet a :=
    A_eq_oddBlockASet_of_IsSimpleCFExpansion hαpos hαirr hcf
  intro x hx
  rw [hA]
  exact certifiedOddPathPrefix_subset_oddBlockASet a K hx

theorem CFBlockIndexLt_total_of_ne
    {j t k s : ℕ}
    (hne : (j, t) ≠ (k, s)) :
    CFBlockIndexLt j t k s ∨ CFBlockIndexLt k s j t := by
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact Or.inl (Or.inl hjk)
  · subst k
    rcases lt_trichotomy t s with hts | hts | hst
    · exact Or.inl (Or.inr ⟨rfl, hts⟩)
    · subst s
      exact False.elim (hne rfl)
    · exact Or.inr (Or.inr ⟨rfl, hst⟩)
  · exact Or.inr (Or.inl hkj)

theorem one_le_CFBlockDenominator_of_valid
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t : ℕ}
    (hjt : ValidPathPair a j t) :
    1 ≤ CFBlockDenominator a j t := by
  unfold CFBlockDenominator
  have htpos : 0 < t := hjt.1
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hmulpos : 0 < t * continuantDen a j :=
    Nat.mul_pos htpos hqpos
  omega

theorem CFBlockDenominator_injective_of_valid
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t k s : ℕ}
    (hjt : ValidPathPair a j t)
    (hks : ValidPathPair a k s)
    (hQ :
      CFBlockDenominator a j t =
        CFBlockDenominator a k s) :
    (j, t) = (k, s) := by
  by_contra hne
  rcases CFBlockIndexLt_total_of_ne hne with hlt | hlt
  · have hden_lt :
        CFBlockDenominator a j t <
          CFBlockDenominator a k s :=
      (CFBlockIndexLt_iff_CFBlockDenominator_lt
        (a := a) hpos hjt hks).1 hlt
    omega
  · have hden_lt :
        CFBlockDenominator a k s <
          CFBlockDenominator a j t :=
      (CFBlockIndexLt_iff_CFBlockDenominator_lt
        (a := a) hpos hks hjt).1 hlt
    omega

theorem CFBlockDenominator_sub_one_injective_on_valid_pairs
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    Set.InjOn
      (fun jt : ℕ × ℕ =>
        CFBlockDenominator a jt.1 jt.2 - 1)
      {jt : ℕ × ℕ | ValidPathPair a jt.1 jt.2} := by
  intro jt hjt kt hkt heq
  rcases jt with ⟨j, t⟩
  rcases kt with ⟨k, s⟩
  have hQj : 1 ≤ CFBlockDenominator a j t :=
    one_le_CFBlockDenominator_of_valid hpos hjt
  have hQk : 1 ≤ CFBlockDenominator a k s :=
    one_le_CFBlockDenominator_of_valid hpos hkt
  have hQ :
      CFBlockDenominator a j t =
        CFBlockDenominator a k s := by
    have heq' :
        CFBlockDenominator a j t - 1 =
          CFBlockDenominator a k s - 1 := by
      simpa using heq
    calc
      CFBlockDenominator a j t
          = (CFBlockDenominator a j t - 1) + 1 := by
            omega
      _ = (CFBlockDenominator a k s - 1) + 1 := by
            rw [heq']
      _ = CFBlockDenominator a k s := by
            omega
  exact CFBlockDenominator_injective_of_valid hpos hjt hkt hQ

theorem certifiedOddPathPrefix_card_eq_indices_card
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (K : ℕ) :
    (certifiedOddPathPrefix a K).card =
      (canonicalOddPathPrefixIndices a K).card := by
  classical
  unfold certifiedOddPathPrefix
  exact Finset.card_image_of_injOn (by
    intro jt hjt kt hkt heq
    apply CFBlockDenominator_sub_one_injective_on_valid_pairs hpos
    · rcases jt with ⟨j, t⟩
      have hjt' : (j, t) ∈ canonicalOddPathPrefixIndices a K := by
        simpa using hjt
      rw [mem_canonicalOddPathPrefixIndices_iff] at hjt'
      exact ⟨hjt'.2.1, hjt'.2.2.1⟩
    · rcases kt with ⟨k, s⟩
      have hkt' : (k, s) ∈ canonicalOddPathPrefixIndices a K := by
        simpa using hkt
      rw [mem_canonicalOddPathPrefixIndices_iff] at hkt'
      exact ⟨hkt'.2.1, hkt'.2.2.1⟩
    · exact heq)

noncomputable def certifiedAOneOverPiPathSubsetAt
    (Kpath : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  certifiedOddPathPrefix oneOverPiCF (Kpath m)

noncomputable def certifiedAOneOverPiPathSubsetBelowExpAt
    (Kpath : ℕ → ℕ) (m : ℕ) (Λ : ℝ) : Finset ℕ := by
  classical
  exact (certifiedAOneOverPiPathSubsetAt Kpath m).filter
    (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))

@[simp] theorem mem_certifiedAOneOverPiPathSubsetBelowExpAt_iff
    {Kpath : ℕ → ℕ} {m x : ℕ} {Λ : ℝ} :
    x ∈ certifiedAOneOverPiPathSubsetBelowExpAt Kpath m Λ ↔
      x ∈ certifiedAOneOverPiPathSubsetAt Kpath m ∧
        (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  classical
  unfold certifiedAOneOverPiPathSubsetBelowExpAt
  simp

theorem certifiedAOneOverPiPathSubsetAt_mem_A
    (Kpath : ℕ → ℕ)
    (hpos : 0 < oneOverPi)
    (hirr : IsIrrational oneOverPi)
    (hcf : IsSimpleCFExpansion oneOverPi oneOverPiCF)
    {m x : ℕ}
    (hx : x ∈ certifiedAOneOverPiPathSubsetAt Kpath m) :
    x ∈ A oneOverPi := by
  unfold certifiedAOneOverPiPathSubsetAt at hx
  exact certifiedOddPathPrefix_subset_A_of_IsSimpleCFExpansion
    hpos hirr hcf hx

theorem pathIndexStart_succ (a : ℕ → ℕ) (j : ℕ) :
    pathIndexStart a (j + 1) = pathIndexStart a j + a (j + 1) := by
  unfold pathIndexStart
  exact Finset.sum_range_succ (fun i => a (i + 1)) j

@[simp] theorem pathIndexStart_zero (a : ℕ → ℕ) :
    pathIndexStart a 0 = 0 := by
  simp [pathIndexStart]

theorem pathIndexStart_lt_succ
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (j : ℕ) :
    pathIndexStart a j < pathIndexStart a (j + 1) := by
  rw [pathIndexStart_succ]
  exact Nat.lt_add_of_pos_right (hpos j)

theorem self_le_pathIndexStart
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    ∀ j : ℕ, j ≤ pathIndexStart a j := by
  intro j
  induction j with
  | zero =>
      simp
  | succ j ih =>
      rw [pathIndexStart_succ]
      have hblock : 1 ≤ a (j + 1) := hpos j
      omega

theorem pathIndexStart_mono (a : ℕ → ℕ) :
    Monotone (pathIndexStart a) := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step n _ ih =>
      exact ih.trans (by rw [pathIndexStart_succ]; omega)

theorem pathIndexStart_le_flattenedPathIndex
    (a : ℕ → ℕ) (j t : ℕ) :
    pathIndexStart a j ≤ flattenedPathIndex a j t := by
  unfold flattenedPathIndex
  omega

noncomputable def pathPairOfIndex (a : ℕ → ℕ) (r : ℕ) : ℕ × ℕ :=
  let j := Nat.findGreatest (fun j : ℕ => pathIndexStart a j ≤ r) r
  (j, r - pathIndexStart a j + 1)

theorem pathPairOfIndex_start_le
    (a : ℕ → ℕ) (r : ℕ) :
    pathIndexStart a (pathPairOfIndex a r).1 ≤ r := by
  unfold pathPairOfIndex
  exact Nat.findGreatest_spec
    (P := fun j : ℕ => pathIndexStart a j ≤ r)
    (m := 0) (n := r) (Nat.zero_le r) (by simp)

theorem pathPairOfIndex_lt_next_start
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (r : ℕ) :
    r < pathIndexStart a ((pathPairOfIndex a r).1 + 1) := by
  unfold pathPairOfIndex
  let j := Nat.findGreatest (fun j : ℕ => pathIndexStart a j ≤ r) r
  change r < pathIndexStart a (j + 1)
  by_contra hnot
  have hnext_le : pathIndexStart a (j + 1) ≤ r := Nat.le_of_not_gt hnot
  have hnext_cap : j + 1 ≤ r :=
    (self_le_pathIndexStart hpos (j + 1)).trans hnext_le
  have hmax :
      ¬ pathIndexStart a (j + 1) ≤ r :=
    Nat.findGreatest_is_greatest
      (P := fun j : ℕ => pathIndexStart a j ≤ r)
      (n := r)
      (by simp [j])
      hnext_cap
  exact hmax hnext_le

theorem pathPairOfIndex_second_eq
    (a : ℕ → ℕ) (r : ℕ) :
    (pathPairOfIndex a r).2 =
      r - pathIndexStart a (pathPairOfIndex a r).1 + 1 := by
  unfold pathPairOfIndex
  rfl

theorem pathPairOfIndex_valid
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (r : ℕ) :
    ValidPathPair a (pathPairOfIndex a r).1 (pathPairOfIndex a r).2 := by
  constructor
  · rw [pathPairOfIndex_second_eq]
    omega
  · have hstart := pathPairOfIndex_start_le a r
    have hnext := pathPairOfIndex_lt_next_start hpos r
    rw [pathPairOfIndex_second_eq]
    rw [pathIndexStart_succ] at hnext
    omega

theorem flattenedPathIndex_pathPairOfIndex
    {a : ℕ → ℕ}
    (_hpos : ∀ j : ℕ, 0 < a (j + 1)) (r : ℕ) :
    flattenedPathIndex a (pathPairOfIndex a r).1
      (pathPairOfIndex a r).2 = r := by
  have hstart := pathPairOfIndex_start_le a r
  rw [pathPairOfIndex_second_eq]
  unfold flattenedPathIndex
  omega

theorem pathPairOfIndex_mem_prefix
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) {K r : ℕ}
    (hr : r < K) :
    pathPairOfIndex a r ∈ canonicalPathPrefixIndices a K := by
  rw [mem_canonicalPathPrefixIndices_iff]
  have hvalid := pathPairOfIndex_valid hpos r
  have hflat := flattenedPathIndex_pathPairOfIndex hpos r
  have hstart := pathPairOfIndex_start_le a r
  have hjle : (pathPairOfIndex a r).1 ≤ r :=
    (self_le_pathIndexStart hpos (pathPairOfIndex a r).1).trans hstart
  exact ⟨lt_of_le_of_lt hjle hr, hvalid.1, hvalid.2, by
    simpa [hflat] using hr⟩

theorem pathPairOfIndex_injective
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    Function.Injective (pathPairOfIndex a) := by
  intro r s hrs
  have hrflat := flattenedPathIndex_pathPairOfIndex hpos r
  have hsflat := flattenedPathIndex_pathPairOfIndex hpos s
  rw [hrs] at hrflat
  omega

theorem flattenedPathIndex_lt_next_start_of_valid
    {a : ℕ → ℕ} {j t : ℕ}
    (ht : ValidPathPair a j t) :
    flattenedPathIndex a j t < pathIndexStart a (j + 1) := by
  rcases ht with ⟨ht1, htle⟩
  rw [pathIndexStart_succ]
  unfold flattenedPathIndex
  cases t with
  | zero =>
      omega
  | succ t =>
      simp
      omega

theorem pathPairOfIndex_eq_of_valid_flat
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {r j t : ℕ}
    (ht : ValidPathPair a j t)
    (hflat : flattenedPathIndex a j t = r) :
    pathPairOfIndex a r = (j, t) := by
  have hstart_le_r : pathIndexStart a j ≤ r := by
    rw [← hflat]
    exact pathIndexStart_le_flattenedPathIndex a j t
  have hflat_lt_next :
      r < pathIndexStart a (j + 1) := by
    rw [← hflat]
    exact flattenedPathIndex_lt_next_start_of_valid ht
  have hfind :
      Nat.findGreatest (fun k : ℕ => pathIndexStart a k ≤ r) r = j := by
    rw [Nat.findGreatest_eq_iff]
    refine ⟨?_, ?_, ?_⟩
    · exact (self_le_pathIndexStart hpos j).trans hstart_le_r
    · intro _hj0
      exact hstart_le_r
    · intro n hjn _hnr hnstart
      have hsucc_le_n : j + 1 ≤ n := Nat.succ_le_of_lt hjn
      have hnext_le :
          pathIndexStart a (j + 1) ≤ pathIndexStart a n :=
        pathIndexStart_mono a hsucc_le_n
      exact (not_le_of_gt hflat_lt_next) (hnext_le.trans hnstart)
  unfold pathPairOfIndex
  simp [hfind]
  unfold flattenedPathIndex at hflat
  rcases ht with ⟨ht1, _htle⟩
  cases t with
  | zero =>
      omega
  | succ t =>
      simp at hflat ⊢
      omega

noncomputable def pathNumeratorAt (a : ℕ → ℕ) (r : ℕ) : ℕ :=
  CFBlockNumerator a (pathPairOfIndex a r).1 (pathPairOfIndex a r).2

noncomputable def pathDenominatorAt (a : ℕ → ℕ) (r : ℕ) : ℕ :=
  CFBlockDenominator a (pathPairOfIndex a r).1 (pathPairOfIndex a r).2

theorem CFBlockNumerator_succ (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockNumerator a j (t + 1) =
      CFBlockNumerator a j t + continuantNum a j := by
  unfold CFBlockNumerator
  ring

theorem pathPairOfIndex_succ_same_of_lt
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) {r : ℕ}
    (ht : (pathPairOfIndex a r).2 <
      a ((pathPairOfIndex a r).1 + 1)) :
    pathPairOfIndex a (r + 1) =
      ((pathPairOfIndex a r).1, (pathPairOfIndex a r).2 + 1) := by
  rcases hpair : pathPairOfIndex a r with ⟨j, t⟩
  simp [hpair] at ht ⊢
  have hvalid_current : ValidPathPair a j t := by
    simpa [hpair] using pathPairOfIndex_valid hpos r
  have hvalid : ValidPathPair a j (t + 1) := by
    exact ⟨by omega, Nat.succ_le_of_lt ht⟩
  have hflat : flattenedPathIndex a j (t + 1) = r + 1 := by
    have hcurr := flattenedPathIndex_pathPairOfIndex hpos r
    simp [hpair] at hcurr
    unfold flattenedPathIndex at hcurr ⊢
    rcases hvalid_current with ⟨ht1, _htle⟩
    cases t with
    | zero =>
        omega
    | succ t =>
        simp at hcurr ⊢
        omega
  exact pathPairOfIndex_eq_of_valid_flat hpos hvalid hflat

theorem pathPairOfIndex_succ_next_of_not_lt
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) {r : ℕ}
    (ht : ¬ (pathPairOfIndex a r).2 <
      a ((pathPairOfIndex a r).1 + 1)) :
    pathPairOfIndex a (r + 1) =
      ((pathPairOfIndex a r).1 + 1, 1) := by
  rcases hpair : pathPairOfIndex a r with ⟨j, t⟩
  simp [hpair] at ht ⊢
  have hvalid_current : ValidPathPair a j t := by
    simpa [hpair] using pathPairOfIndex_valid hpos r
  have hteq : t = a (j + 1) := by
    exact le_antisymm hvalid_current.2 ht
  have hvalid : ValidPathPair a (j + 1) 1 := by
    exact ⟨by norm_num, hpos (j + 1)⟩
  have hflat : flattenedPathIndex a (j + 1) 1 = r + 1 := by
    have hcurr := flattenedPathIndex_pathPairOfIndex hpos r
    simp [hpair] at hcurr
    unfold flattenedPathIndex at hcurr ⊢
    rw [pathIndexStart_succ]
    have htpos : 1 ≤ t := hvalid_current.1
    cases t with
    | zero =>
        omega
    | succ t =>
        simp at hcurr ⊢
        omega
  exact pathPairOfIndex_eq_of_valid_flat hpos hvalid hflat

theorem not_even_pathNumeratorAt_and_succ
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (r : ℕ) :
    ¬ (Even (pathNumeratorAt a r) ∧
        Even (pathNumeratorAt a (r + 1))) := by
  intro hboth
  let jt := pathPairOfIndex a r
  let j := jt.1
  let t := jt.2
  by_cases ht : t < a (j + 1)
  · have hsucc := pathPairOfIndex_succ_same_of_lt
      (a := a) hpos (r := r) ht
    have hP : Even (CFBlockNumerator a j t) := by
      simpa [pathNumeratorAt, jt, j, t] using hboth.1
    have hPs : Even (CFBlockNumerator a j (t + 1)) := by
      simpa [pathNumeratorAt, jt, j, t, hsucc] using hboth.2
    have hcurrEven : Even (continuantNum a j) := by
      rw [CFBlockNumerator_succ] at hPs
      rcases Nat.even_or_odd (continuantNum a j) with hcurrEven | hcurrOdd
      · exact hcurrEven
      · have hodd_sum :
            Odd (CFBlockNumerator a j t + continuantNum a j) :=
          hP.add_odd hcurrOdd
        exact False.elim ((Nat.not_even_iff_odd.mpr hodd_sum) hPs)
    have hprevEven : Even (continuantNumPrev a j) := by
      unfold CFBlockNumerator at hP
      rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
      · exact hprevEven
      · have hmulEven : Even (t * continuantNum a j) :=
          hcurrEven.mul_left t
        have hodd_sum :
            Odd (continuantNumPrev a j + t * continuantNum a j) :=
          hprevOdd.add_even hmulEven
        exact False.elim ((Nat.not_even_iff_odd.mpr hodd_sum) hP)
    exact continuantNumPrev_not_even_and_even a j ⟨hprevEven, hcurrEven⟩
  · have hsucc := pathPairOfIndex_succ_next_of_not_lt
      (a := a) hpos (r := r) ht
    have hvalid_current : ValidPathPair a j t :=
      pathPairOfIndex_valid hpos r
    have hteq : t = a (j + 1) := by
      exact le_antisymm hvalid_current.2 (Nat.le_of_not_gt ht)
    have hP : Even (CFBlockNumerator a j t) := by
      simpa [pathNumeratorAt, jt, j, t] using hboth.1
    have hPs : Even (CFBlockNumerator a (j + 1) 1) := by
      simpa [pathNumeratorAt, jt, j, t, hsucc] using hboth.2
    have hcurrSuccEven : Even (continuantNum a (j + 1)) := by
      simpa [hteq, CFBlockNumerator_endpoint] using hP
    have hprevSuccEven : Even (continuantNumPrev a (j + 1)) := by
      unfold CFBlockNumerator at hPs
      rcases Nat.even_or_odd (continuantNumPrev a (j + 1)) with hprevEven | hprevOdd
      · exact hprevEven
      · have hsumOdd :
            Odd (continuantNumPrev a (j + 1) +
              1 * continuantNum a (j + 1)) := by
          exact hprevOdd.add_even (hcurrSuccEven.mul_left 1)
        exact False.elim ((Nat.not_even_iff_odd.mpr hsumOdd) hPs)
    exact continuantNumPrev_not_even_and_even a (j + 1)
      ⟨hprevSuccEven, hcurrSuccEven⟩

theorem odd_pathNumeratorAt_or_succ
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (r : ℕ) :
    Odd (pathNumeratorAt a r) ∨
      Odd (pathNumeratorAt a (r + 1)) := by
  rcases Nat.even_or_odd (pathNumeratorAt a r) with hrEven | hrOdd
  · rcases Nat.even_or_odd (pathNumeratorAt a (r + 1)) with hsEven | hsOdd
    · exact False.elim
        (not_even_pathNumeratorAt_and_succ hpos r ⟨hrEven, hsEven⟩)
    · exact Or.inr hsOdd
  · exact Or.inl hrOdd

private theorem half_le_card_filter_range_of_pair_path
    (P : ℕ → Prop) [DecidablePred P] :
    ∀ K : ℕ,
      (∀ r : ℕ, r + 1 < K → P r ∨ P (r + 1)) →
        K / 2 ≤ ((Finset.range K).filter P).card := by
  intro K
  refine Nat.strong_induction_on K ?_
  intro K ih hpair
  cases K with
  | zero =>
      simp
  | succ K1 =>
      cases K1 with
      | zero =>
          simp
      | succ K =>
          have hpairK :
              ∀ r : ℕ, r + 1 < K → P r ∨ P (r + 1) := by
            intro r hr
            exact hpair r (by omega)
          have ihK : K / 2 ≤ ((Finset.range K).filter P).card :=
            ih K (by omega) hpairK
          have hnew : P K ∨ P (K + 1) :=
            hpair K (by omega)
          have hif :
              1 ≤ (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
            rcases hnew with hK | hK1
            · by_cases hK1 : P (K + 1) <;> simp [hK, hK1]
            · by_cases hK : P K <;> simp [hK, hK1]
          have hstep :
              ((Finset.range (K + 2)).filter P).card =
                ((Finset.range K).filter P).card +
                  (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
            have h1 := card_filter_range_succ (P := P) (K + 1)
            have h0 := card_filter_range_succ (P := P) K
            calc
              ((Finset.range (K + 2)).filter P).card =
                  ((Finset.range (K + 1)).filter P).card +
                    (if P (K + 1) then 1 else 0) := by
                    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
              _ = (((Finset.range K).filter P).card +
                    (if P K then 1 else 0)) +
                    (if P (K + 1) then 1 else 0) := by
                    rw [h0]
              _ = ((Finset.range K).filter P).card +
                    (if P K then 1 else 0) +
                    (if P (K + 1) then 1 else 0) := by
                    omega
          rw [hstep]
          omega

theorem half_le_flatOddPathPrefix_card
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (K : ℕ) :
    K / 2 ≤
      ((Finset.range K).filter fun r : ℕ =>
        Odd (pathNumeratorAt a r)).card := by
  classical
  exact half_le_card_filter_range_of_pair_path
    (P := fun r : ℕ => Odd (pathNumeratorAt a r))
    K
    (by
      intro r _hr
      exact odd_pathNumeratorAt_or_succ hpos r)

theorem two_le_pathDenominatorAt_of_pos_index
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) {r : ℕ}
    (hrpos : 0 < r) :
    2 ≤ pathDenominatorAt a r := by
  unfold pathDenominatorAt
  rcases hpair : pathPairOfIndex a r with ⟨j, t⟩
  have hvalid : ValidPathPair a j t := by
    simpa [hpair] using pathPairOfIndex_valid hpos r
  cases j with
  | zero =>
      have hflat := flattenedPathIndex_pathPairOfIndex hpos r
      simp [hpair, flattenedPathIndex, pathIndexStart,
        CFBlockDenominator, continuantDen, continuantDenPrev] at hflat ⊢
      omega
  | succ j =>
      exact two_le_CFBlockDenominator_of_one_le_index hpos
        (by omega) hvalid.1

theorem flatOddPathPrefix_without_zero_card_le_indices_card_add_zero
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (K : ℕ) :
    (((Finset.range K).filter fun r : ℕ =>
        Odd (pathNumeratorAt a r)).erase 0).card ≤
      (canonicalOddPathPrefixIndices a K).card := by
  classical
  let S : Finset ℕ :=
    (((Finset.range K).filter fun r : ℕ =>
      Odd (pathNumeratorAt a r)).erase 0)
  have himage_subset :
      S.image (pathPairOfIndex a) ⊆ canonicalOddPathPrefixIndices a K := by
    intro jt hjt
    rw [Finset.mem_image] at hjt
    rcases hjt with ⟨r, hrS, rfl⟩
    have hrS' : r ∈ S := hrS
    unfold S at hrS'
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hrS'
    rcases hrS' with ⟨hrne, ⟨hrK, hodd⟩⟩
    have hprefix := pathPairOfIndex_mem_prefix hpos (K := K) hrK
    rw [mem_canonicalPathPrefixIndices_iff] at hprefix
    rw [mem_canonicalOddPathPrefixIndices_iff]
    exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2.1,
      hprefix.2.2.2, by simpa [pathNumeratorAt] using hodd,
      by
        have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
        simpa [pathDenominatorAt] using
          two_le_pathDenominatorAt_of_pos_index hpos hrpos⟩
  have hcard_image :
      (S.image (pathPairOfIndex a)).card = S.card := by
    rw [Finset.card_image_of_injOn]
    intro r hr s hs hrs
    exact pathPairOfIndex_injective hpos hrs
  rw [← hcard_image]
  exact Finset.card_le_card himage_subset

theorem card_canonicalOddPathPrefixIndices_ge_half
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (K : ℕ) :
    K / 2 ≤ (canonicalOddPathPrefixIndices a K).card + 2 := by
  classical
  let O : Finset ℕ :=
    (Finset.range K).filter fun r : ℕ => Odd (pathNumeratorAt a r)
  have hhalf : K / 2 ≤ O.card := by
    unfold O
    exact half_le_flatOddPathPrefix_card hpos K
  have herase_le :
      (O.erase 0).card ≤ (canonicalOddPathPrefixIndices a K).card := by
    unfold O
    exact flatOddPathPrefix_without_zero_card_le_indices_card_add_zero hpos K
  have hO_le : O.card ≤ (O.erase 0).card + 1 := by
    by_cases h0 : 0 ∈ O
    · have hcard := Finset.card_erase_add_one h0
      omega
    · have herase : O.erase 0 = O := Finset.erase_eq_of_notMem h0
      rw [herase]
      omega
  omega

theorem card_certifiedOddPathPrefix_ge_half
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (K : ℕ) :
    K / 2 ≤ (certifiedOddPathPrefix a K).card + 2 := by
  have hidx := card_canonicalOddPathPrefixIndices_ge_half hpos K
  have hcard := certifiedOddPathPrefix_card_eq_indices_card hpos K
  omega

theorem eventuallyLinearLowerBound_certifiedOddPathPrefix_card_of_Kpath_aux
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Kpath : ℕ → ℕ} {c c' : ℝ}
    (hK : EventuallyLinearLowerBound Kpath c)
    (hlarge : ∀ᶠ m : ℕ in atTop, 3 ≤ (c / 2 - c') * (m : ℝ)) :
    EventuallyLinearLowerBound
      (fun m : ℕ => (certifiedOddPathPrefix a (Kpath m)).card) c' := by
  unfold EventuallyLinearLowerBound at *
  filter_upwards [hK, hlarge] with m hKm hlarge_m
  have hhalf_nat :
      Kpath m / 2 ≤
        (certifiedOddPathPrefix a (Kpath m)).card + 2 :=
    card_certifiedOddPathPrefix_ge_half hpos (Kpath m)
  have hhalf_real :
      ((Kpath m / 2 : ℕ) : ℝ) ≤
        ((certifiedOddPathPrefix a (Kpath m)).card : ℝ) + 2 := by
    exact_mod_cast hhalf_nat
  have hfloor :
      (Kpath m : ℝ) / 2 - 1 ≤ ((Kpath m / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower (Kpath m)
  have hcard_lower :
      (Kpath m : ℝ) / 2 - 3 ≤
        ((certifiedOddPathPrefix a (Kpath m)).card : ℝ) := by
    nlinarith
  have htarget :
      c' * (m : ℝ) ≤ (Kpath m : ℝ) / 2 - 3 := by
    nlinarith
  exact htarget.trans hcard_lower

theorem eventuallyLinearLowerBound_certifiedOddPathPrefix_card_of_Kpath
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {Kpath : ℕ → ℕ} {c c' : ℝ}
    (hK : EventuallyLinearLowerBound Kpath c)
    (hc' : c' < c / 2) :
    EventuallyLinearLowerBound
      (fun m : ℕ => (certifiedOddPathPrefix a (Kpath m)).card) c' := by
  have hδ : 0 < c / 2 - c' := by linarith
  have hlarge :
      ∀ᶠ m : ℕ in atTop, 3 ≤ (c / 2 - c') * (m : ℝ) := by
    have hδ3 : 0 < (c / 2 - c') / 3 := by positivity
    filter_upwards [eventually_one_le_pos_mul_natCast hδ3] with m hm
    nlinarith
  exact eventuallyLinearLowerBound_certifiedOddPathPrefix_card_of_Kpath_aux
    (a := a) hpos (Kpath := Kpath) (c := c) (c' := c') hK hlarge

theorem path_block_index_lt_of_flattened_lt_start
    {a : ℕ → ℕ} {K J j t : ℕ}
    (hflat : flattenedPathIndex a j t < K)
    (hKJ : K ≤ pathIndexStart a J) :
    j < J := by
  by_contra hnot
  have hJle : J ≤ j := Nat.le_of_not_gt hnot
  have hstart_le : pathIndexStart a J ≤ pathIndexStart a j :=
    pathIndexStart_mono a hJle
  have hstart_flat : pathIndexStart a j ≤ flattenedPathIndex a j t :=
    pathIndexStart_le_flattenedPathIndex a j t
  omega

theorem certifiedOddPathPrefix_den_le_endpoint
    {a : ℕ → ℕ} {K J x : ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (hKlePathStart : K ≤ pathIndexStart a J)
    (hx : x ∈ certifiedOddPathPrefix a K) :
    x + 1 ≤ continuantDen a J := by
  unfold certifiedOddPathPrefix at hx
  rcases Finset.mem_image.mp hx with ⟨jt, hjt, rfl⟩
  rcases jt with ⟨j, t⟩
  rw [mem_canonicalOddPathPrefixIndices_iff] at hjt
  have hjlt : j < J :=
    path_block_index_lt_of_flattened_lt_start
      hjt.2.2.2.1 hKlePathStart
  have hblock_le :
      CFBlockDenominator a j t ≤ continuantDen a (j + 1) :=
    CFBlockDenominator_le_endpoint a hjt.2.2.1
  have hmono :
      continuantDen a (j + 1) ≤ continuantDen a J :=
    continuantDen_mono_of_partials_pos_le a hpos
      (Nat.succ_le_of_lt hjlt)
  have hQle :
      CFBlockDenominator a j t ≤ continuantDen a J :=
    hblock_le.trans hmono
  change CFBlockDenominator a j t - 1 + 1 ≤ continuantDen a J
  omega

theorem certifiedAOneOverPiPathSubsetAt_bound_of_pathStart_endpoint_denominator_le_exp
    {Kpath Jcert : ℕ → ℕ} {m x : ℕ} {Λ : ℝ}
    (hKlePathStart : Kpath m ≤ pathIndexStart oneOverPiCF (Jcert m))
    (hden :
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ)))
    (hx : x ∈ certifiedAOneOverPiPathSubsetAt Kpath m) :
    (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)) := by
  have hxden_succ :
      x + 1 ≤ continuantDen oneOverPiCF (Jcert m) :=
    certifiedOddPathPrefix_den_le_endpoint
      (a := oneOverPiCF) oneOverPiCF_partials_pos
      hKlePathStart hx
  have hxden_nat : x ≤ continuantDen oneOverPiCF (Jcert m) := by
    omega
  have hxden_real :
      (x : ℝ) ≤ (continuantDen oneOverPiCF (Jcert m) : ℝ) := by
    exact_mod_cast hxden_nat
  exact hxden_real.trans hden

theorem certifiedAOneOverPiPathSubsetBelowExpAt_eq_self_of_pathStart_endpoint_denominator_le_exp
    {Kpath Jcert : ℕ → ℕ} {m : ℕ} {Λ : ℝ}
    (hKlePathStart : Kpath m ≤ pathIndexStart oneOverPiCF (Jcert m))
    (hden :
      (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
        Real.exp (Λ * (m : ℝ))) :
    certifiedAOneOverPiPathSubsetBelowExpAt Kpath m Λ =
      certifiedAOneOverPiPathSubsetAt Kpath m := by
  classical
  ext x
  rw [mem_certifiedAOneOverPiPathSubsetBelowExpAt_iff]
  constructor
  · exact fun hx => hx.1
  · intro hx
    exact ⟨hx,
      certifiedAOneOverPiPathSubsetAt_bound_of_pathStart_endpoint_denominator_le_exp
        (Kpath := Kpath) (Jcert := Jcert) hKlePathStart hden hx⟩

theorem eventuallyManyCertifiedAOneOverPiPathBelowExpAt_of_card_lower_and_endpoint_bound
    {Kpath Jcert : ℕ → ℕ} {ρ Λ : ℝ}
    (hcard :
      EventuallyLinearLowerBound
        (fun m : ℕ => (certifiedAOneOverPiPathSubsetAt Kpath m).card) ρ)
    (hKlePathStart :
      ∀ᶠ m : ℕ in atTop,
        Kpath m ≤ pathIndexStart oneOverPiCF (Jcert m))
    (hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (Jcert m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiPathSubsetBelowExpAt Kpath m Λ).card : ℝ) := by
  unfold EventuallyLinearLowerBound at hcard
  filter_upwards [hcard, hKlePathStart, hden] with m hcardm hKlem hdenm
  rw [certifiedAOneOverPiPathSubsetBelowExpAt_eq_self_of_pathStart_endpoint_denominator_le_exp
    (Kpath := Kpath) (Jcert := Jcert) hKlem hdenm]
  exact hcardm

/-- Proof-carrying system for the intermediate-path production route.

The `pathCardLower` field is the finite parity/injectivity counting input still
to be proved generically from the flattened path.  Keeping it explicit prevents
confusing Stern--Brocot path length with principal-block count. -/
structure OneOverPiCertifiedIntermediatePathSystem where
  Kpath : ℕ → ℕ
  Jcert : ℕ → ℕ
  phiUpper :
    EventuallyPhiUpperFromPathLength
      (leastDenominatorInIntervalSeq
        ramanujanPiL ramanujanPiU ramanujanPi_hLU)
      Kpath
  K_le_pathStart :
    ∀ᶠ m : ℕ in atTop,
      Kpath m ≤ pathIndexStart oneOverPiCF (Jcert m)
  cylinder :
    EventuallyIntervalInCFCylinder oneOverPiCF Jcert
      ramanujanPiL ramanujanPiU

theorem eventuallyManyCertifiedAOneOverPiPathBelowExp_of_pathSystem_and_cardLower
    (S : OneOverPiCertifiedIntermediatePathSystem)
    {ρ Λ : ℝ}
    (hcard :
      EventuallyLinearLowerBound
        (fun m : ℕ => (certifiedAOneOverPiPathSubsetAt S.Kpath m).card) ρ)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        ((certifiedAOneOverPiPathSubsetBelowExpAt S.Kpath m Λ).card : ℝ) := by
  have hden :
      ∀ᶠ m : ℕ in atTop,
        (continuantDen oneOverPiCF (S.Jcert m) : ℝ) ≤
          Real.exp (Λ * (m : ℝ)) :=
    eventually_endpointDen_oneOverPiAt_le_exp_of_cylinderContain
      (Jcert := S.Jcert) hΛ S.cylinder
  exact
    eventuallyManyCertifiedAOneOverPiPathBelowExpAt_of_card_lower_and_endpoint_bound
      (Kpath := S.Kpath) (Jcert := S.Jcert)
      hcard S.K_le_pathStart hden

theorem eventuallyManyCertifiedAOneOverPiPathBelowExp_of_pathSystem_and_pathLengthLower
    (S : OneOverPiCertifiedIntermediatePathSystem)
    {ρ ρ' Λ : ℝ}
    (hpath : EventuallyLinearLowerBound S.Kpath ρ)
    (hρ' : ρ' < ρ / 2)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ' * (m : ℝ) ≤
        ((certifiedAOneOverPiPathSubsetBelowExpAt S.Kpath m Λ).card : ℝ) := by
  exact
    eventuallyManyCertifiedAOneOverPiPathBelowExp_of_pathSystem_and_cardLower
      S
      (eventuallyLinearLowerBound_certifiedOddPathPrefix_card_of_Kpath
        (a := oneOverPiCF) oneOverPiCF_partials_pos hpath hρ')
      hΛ

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanIntermediatePathConcrete.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Concrete height bounds for intermediate-path production

This file packages the universal part of the intermediate-path strategy.  The
finite parity theorem in `RamanujanCertifiedIntermediatePath` gives many
odd-numerator path elements; here we prove that the first `K` flattened
intermediate denominators have universal Fibonacci/golden-ratio height.
-/

private lemma fib_add_mul_le_fib_add (n : ℕ) :
    ∀ t : ℕ,
      Nat.fib n + t * Nat.fib (n + 1) ≤ Nat.fib (n + t + 1)
  | 0 => by
      simpa using Nat.fib_le_fib_succ (n := n)
  | 1 => by
      exact le_of_eq (by
        rw [Nat.fib_add_two]
        ring_nf)
  | t + 2 => by
      have ih :
          Nat.fib n + (t + 1) * Nat.fib (n + 1) ≤
            Nat.fib (n + (t + 1) + 1) :=
        fib_add_mul_le_fib_add n (t + 1)
      have hmono :
          Nat.fib (n + 1) ≤ Nat.fib (n + t + 1) :=
        Nat.fib_mono (by omega)
      calc
        Nat.fib n + (t + 2) * Nat.fib (n + 1)
            = Nat.fib n + (t + 1) * Nat.fib (n + 1) +
                Nat.fib (n + 1) := by ring
        _ ≤ Nat.fib (n + (t + 1) + 1) + Nat.fib (n + 1) :=
            Nat.add_le_add_right ih _
        _ ≤ Nat.fib (n + t + 2) + Nat.fib (n + t + 1) :=
            Nat.add_le_add_left hmono _
        _ = Nat.fib (n + t + 3) := by
            rw [add_comm, ← Nat.fib_add_two (n := n + t + 1)]
        _ = Nat.fib (n + (t + 2) + 1) := by
            congr 1

theorem continuantDenPrev_den_le_fib_pathIndexStart
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) :
    ∀ j : ℕ,
      continuantDenPrev a j ≤ Nat.fib (pathIndexStart a j + 1) ∧
        continuantDen a j ≤ Nat.fib (pathIndexStart a j + 2) := by
  intro j
  induction j with
  | zero =>
      simp [pathIndexStart, continuantDenPrev, continuantDen, Nat.fib]
  | succ j ih =>
      constructor
      · have hmono :
            Nat.fib (pathIndexStart a j + 2) ≤
              Nat.fib (pathIndexStart a (j + 1) + 1) :=
          Nat.fib_mono (by
            rw [pathIndexStart_succ]
            have hblock : 1 ≤ a (j + 1) := hpos j
            omega)
        simpa [continuantDenPrev] using ih.2.trans hmono
      · rw [continuantDen_succ_eq, pathIndexStart_succ]
        have hmul :
            a (j + 1) * continuantDen a j ≤
              a (j + 1) * Nat.fib (pathIndexStart a j + 2) :=
          Nat.mul_le_mul_left _ ih.2
        have hsum :
            a (j + 1) * continuantDen a j + continuantDenPrev a j ≤
              a (j + 1) * Nat.fib (pathIndexStart a j + 2) +
                Nat.fib (pathIndexStart a j + 1) :=
          Nat.add_le_add hmul ih.1
        have hfib :
            Nat.fib (pathIndexStart a j + 1) +
                a (j + 1) * Nat.fib (pathIndexStart a j + 2) ≤
              Nat.fib (pathIndexStart a j + a (j + 1) + 2) := by
          exact
            (fib_add_mul_le_fib_add
              (pathIndexStart a j + 1) (a (j + 1))).trans_eq
              (by
                congr 1
                omega)
        calc
          a (j + 1) * continuantDen a j + continuantDenPrev a j
              ≤ a (j + 1) * Nat.fib (pathIndexStart a j + 2) +
                  Nat.fib (pathIndexStart a j + 1) := hsum
          _ = Nat.fib (pathIndexStart a j + 1) +
                a (j + 1) * Nat.fib (pathIndexStart a j + 2) := by
                omega
          _ ≤ Nat.fib (pathIndexStart a j + a (j + 1) + 2) := hfib

theorem continuantDenPrev_le_fib_pathIndexStart_add_one
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (j : ℕ) :
    continuantDenPrev a j ≤ Nat.fib (pathIndexStart a j + 1) :=
  (continuantDenPrev_den_le_fib_pathIndexStart hpos j).1

theorem continuantDen_le_fib_pathIndexStart_add_two
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1)) (j : ℕ) :
    continuantDen a j ≤ Nat.fib (pathIndexStart a j + 2) :=
  (continuantDenPrev_den_le_fib_pathIndexStart hpos j).2

theorem CFBlockDenominator_le_fib_of_flattened_lt
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K j t : ℕ}
    (hmem : (j, t) ∈ canonicalPathPrefixIndices a K) :
    CFBlockDenominator a j t ≤ Nat.fib (K + 3) := by
  rw [mem_canonicalPathPrefixIndices_iff] at hmem
  rcases hmem with ⟨_hjK, ht1, _htle, hflat⟩
  have hprev :
      continuantDenPrev a j ≤ Nat.fib (pathIndexStart a j + 1) :=
    continuantDenPrev_le_fib_pathIndexStart_add_one hpos j
  have hcurr :
      continuantDen a j ≤ Nat.fib (pathIndexStart a j + 2) :=
    continuantDen_le_fib_pathIndexStart_add_two hpos j
  have hlin :
      CFBlockDenominator a j t ≤
        Nat.fib (pathIndexStart a j + 1) +
          t * Nat.fib (pathIndexStart a j + 2) := by
    unfold CFBlockDenominator
    exact Nat.add_le_add hprev (Nat.mul_le_mul_left t hcurr)
  have hfib :
      Nat.fib (pathIndexStart a j + 1) +
          t * Nat.fib (pathIndexStart a j + 2) ≤
        Nat.fib (pathIndexStart a j + t + 2) := by
    exact
      (fib_add_mul_le_fib_add (pathIndexStart a j + 1) t).trans_eq
        (by
          congr 1
          omega)
  have hflat_eq :
      pathIndexStart a j + t + 2 =
        flattenedPathIndex a j t + 3 := by
    unfold flattenedPathIndex
    cases t with
    | zero =>
        omega
    | succ t =>
        simp
        omega
  have hmono :
      Nat.fib (pathIndexStart a j + t + 2) ≤ Nat.fib (K + 3) := by
    rw [hflat_eq]
    exact Nat.fib_mono (by omega)
  exact hlin.trans (hfib.trans hmono)

theorem pathDenominatorAt_le_fib
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (r : ℕ) :
    pathDenominatorAt a r ≤ Nat.fib (r + 4) := by
  have hmem :
      pathPairOfIndex a r ∈ canonicalPathPrefixIndices a (r + 1) :=
    pathPairOfIndex_mem_prefix hpos (K := r + 1) (by omega)
  rcases hpair : pathPairOfIndex a r with ⟨j, t⟩
  have hden :
      CFBlockDenominator a j t ≤ Nat.fib ((r + 1) + 3) := by
    exact CFBlockDenominator_le_fib_of_flattened_lt
      (a := a) hpos (K := r + 1) (j := j) (t := t) (by
        simpa [hpair] using hmem)
  simpa [pathDenominatorAt, hpair, Nat.add_assoc] using hden

theorem CFBlockDenominator_le_exp_phi_of_flattened_lt
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K j t : ℕ}
    (hmem : (j, t) ∈ canonicalPathPrefixIndices a K) :
    (CFBlockDenominator a j t : ℝ) ≤
      Real.exp ((K + 4 : ℝ) * Real.log Real.goldenRatio) := by
  have hfibNat :
      CFBlockDenominator a j t ≤ Nat.fib (K + 3) :=
    CFBlockDenominator_le_fib_of_flattened_lt hpos hmem
  have hfibReal :
      (CFBlockDenominator a j t : ℝ) ≤ (Nat.fib (K + 3) : ℝ) := by
    exact_mod_cast hfibNat
  have hφfib :
      (Nat.fib (K + 3) : ℝ) ≤ Real.goldenRatio ^ (K + 3) :=
    FareyFrame.natFib_le_goldenRatio_pow (K + 3)
  have hpowmono :
      Real.goldenRatio ^ (K + 3) ≤ Real.goldenRatio ^ (K + 4) :=
    pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) (by omega)
  have hpowexp :
      Real.goldenRatio ^ (K + 4) =
        Real.exp ((K + 4 : ℝ) * Real.log Real.goldenRatio) := by
    symm
    calc
      Real.exp ((K + 4 : ℝ) * Real.log Real.goldenRatio)
          = Real.exp (Real.log Real.goldenRatio * ((K + 4 : ℕ) : ℝ)) := by
              congr 1
              have hcast : (((K + 4 : ℕ) : ℝ)) = (K : ℝ) + 4 := by
                norm_num
              rw [hcast]
              ring
      _ = (Real.exp (Real.log Real.goldenRatio)) ^
            ((K + 4 : ℕ) : ℝ) := by
              rw [Real.exp_mul]
      _ = Real.goldenRatio ^ ((K + 4 : ℕ) : ℝ) := by
              rw [Real.exp_log Real.goldenRatio_pos]
      _ = Real.goldenRatio ^ (K + 4) := by
              rw [Real.rpow_natCast]
  exact hfibReal.trans (hφfib.trans (hpowmono.trans_eq hpowexp))

theorem certifiedOddPathPrefix_subset_below_exp
    {a : ℕ → ℕ} {K : ℕ} {Λ M : ℝ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (hK : (K + 4 : ℝ) * Real.log Real.goldenRatio ≤ Λ * M)
    {x : ℕ}
    (hx : x ∈ certifiedOddPathPrefix a K) :
    (x : ℝ) ≤ Real.exp (Λ * M) := by
  unfold certifiedOddPathPrefix at hx
  rcases Finset.mem_image.mp hx with ⟨jt, hjt, rfl⟩
  rcases jt with ⟨j, t⟩
  rw [mem_canonicalOddPathPrefixIndices_iff] at hjt
  have hpath :
      (j, t) ∈ canonicalPathPrefixIndices a K := by
    rw [mem_canonicalPathPrefixIndices_iff]
    exact ⟨hjt.1, hjt.2.1, hjt.2.2.1, hjt.2.2.2.1⟩
  have hden :
      (CFBlockDenominator a j t : ℝ) ≤
        Real.exp ((K + 4 : ℝ) * Real.log Real.goldenRatio) :=
    CFBlockDenominator_le_exp_phi_of_flattened_lt hpos hpath
  have hheight :
      Real.exp ((K + 4 : ℝ) * Real.log Real.goldenRatio) ≤
        Real.exp (Λ * M) :=
    Real.exp_le_exp.mpr hK
  have hxden :
      ((CFBlockDenominator a j t - 1 : ℕ) : ℝ) ≤
        (CFBlockDenominator a j t : ℝ) := by
    exact_mod_cast Nat.sub_le (CFBlockDenominator a j t) 1
  exact hxden.trans (hden.trans hheight)

theorem card_A_intermediate_prefix_below_exp
    {α : ℝ} {a : ℕ → ℕ}
    (_hαpos : 0 < α)
    (_hαirr : IsIrrational α)
    (_hcf : IsSimpleCFExpansion α a)
    (hapos : ∀ j : ℕ, 0 < a (j + 1))
    {K : ℕ} {Λ M : ℝ}
    (hKheight :
      (K + 4 : ℝ) * Real.log Real.goldenRatio ≤ Λ * M) :
    K / 2 ≤
      ((certifiedOddPathPrefix a K).filter
        (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * M))).card + 2 := by
  classical
  have hfilter :
      (certifiedOddPathPrefix a K).filter
          (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * M)) =
        certifiedOddPathPrefix a K := by
    apply Finset.filter_true_of_mem
    intro x hx
    exact certifiedOddPathPrefix_subset_below_exp hapos hKheight hx
  rw [hfilter]
  exact card_certifiedOddPathPrefix_ge_half hapos K

noncomputable def linearPathTrial (c : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (c * (m : ℝ))

private lemma natFloor_cast_lower (x : ℝ) :
    x - 1 ≤ (Nat.floor x : ℝ) := by
  have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

theorem linearPathTrial_cast_le
    {c : ℝ} (hc_nonneg : 0 ≤ c) (m : ℕ) :
    (linearPathTrial c m : ℝ) ≤ c * (m : ℝ) := by
  unfold linearPathTrial
  exact Nat.floor_le (mul_nonneg hc_nonneg (Nat.cast_nonneg m))

theorem linearPathTrial_cast_lower
    (c : ℝ) (m : ℕ) :
    c * (m : ℝ) - 1 ≤ (linearPathTrial c m : ℝ) := by
  unfold linearPathTrial
  exact natFloor_cast_lower (c * (m : ℝ))

theorem eventuallyManyCertifiedOddPathBelowExp_linearTrial
    {a : ℕ → ℕ} {c ρ Λ : ℝ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (hcpos : 0 < c)
    (hρ : ρ < c / 2)
    (hheight : c * Real.log Real.goldenRatio < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤
        (((certifiedOddPathPrefix a (linearPathTrial c m)).filter
          (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) := by
  let φlog : ℝ := Real.log Real.goldenRatio
  have hφpos : 0 < φlog := by
    dsimp [φlog]
    exact log_goldenRatio_pos
  have hheight_gap : 0 < Λ - c * φlog := by
    linarith
  have hcard_gap : 0 < c / 2 - ρ := by linarith
  have hlarge_height :
      ∀ᶠ m : ℕ in atTop,
        4 * φlog ≤ (Λ - c * φlog) * (m : ℝ) :=
    eventually_const_le_pos_mul_natCast
      (A := 4 * φlog) hheight_gap
  have hlarge_card :
      ∀ᶠ m : ℕ in atTop,
        4 ≤ (c / 2 - ρ) * (m : ℝ) :=
    eventually_const_le_pos_mul_natCast
      (A := 4) hcard_gap
  filter_upwards [hlarge_height, hlarge_card] with m hlargeH hlargeC
  let K : ℕ := linearPathTrial c m
  have hKle : (K : ℝ) ≤ c * (m : ℝ) := by
    dsimp [K]
    exact linearPathTrial_cast_le (le_of_lt hcpos) m
  have hKheight :
      (K + 4 : ℝ) * Real.log Real.goldenRatio ≤ Λ * (m : ℝ) := by
    change ((K : ℝ) + 4) * φlog ≤ Λ * (m : ℝ)
    have hKφ : (K : ℝ) * φlog ≤ (c * (m : ℝ)) * φlog :=
      mul_le_mul_of_nonneg_right hKle (le_of_lt hφpos)
    nlinarith
  have hfilter :
      (certifiedOddPathPrefix a K).filter
          (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ))) =
        certifiedOddPathPrefix a K := by
    apply Finset.filter_true_of_mem
    intro x hx
    exact certifiedOddPathPrefix_subset_below_exp hpos hKheight hx
  have hhalf_nat :
      K / 2 ≤ (certifiedOddPathPrefix a K).card + 2 :=
    card_certifiedOddPathPrefix_ge_half hpos K
  have hhalf_real :
      ((K / 2 : ℕ) : ℝ) ≤
        ((certifiedOddPathPrefix a K).card : ℝ) + 2 := by
    exact_mod_cast hhalf_nat
  have hfloor_half :
      (K : ℝ) / 2 - 1 ≤ ((K / 2 : ℕ) : ℝ) :=
    nat_div_two_cast_lower K
  have hKlower : c * (m : ℝ) - 1 ≤ (K : ℝ) := by
    dsimp [K]
    exact linearPathTrial_cast_lower c m
  have hcard_lower :
      c / 2 * (m : ℝ) - 4 ≤
        ((certifiedOddPathPrefix a K).card : ℝ) := by
    nlinarith
  have htarget :
      ρ * (m : ℝ) ≤ c / 2 * (m : ℝ) - 4 := by
    nlinarith
  rw [show linearPathTrial c m = K by rfl, hfilter]
  exact htarget.trans hcard_lower

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanIntermediatePathCertification.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Concrete Ramanujan certification of intermediate-path prefixes

The universal path-production layer proves that the first `K` intermediate
continued-fraction path positions contain many odd-numerator denominators and
that their heights are bounded by `exp((log φ + o(1)) K)`.

This file adds the concrete Ramanujan interval certification layer: if every
early boundary rational has denominator below the least denominator occurring
inside the Ramanujan interval, then the interval cannot cross any of those
boundaries.  Since the interval contains `1 / π`, it certifies the same side of
each early boundary as `1 / π`.
-/

/-! ## Boundary rationals for flattened intermediate-path positions -/

noncomputable def pathBoundaryNum (a : ℕ → ℕ) (r : ℕ) : ℕ :=
  pathNumeratorAt a r

noncomputable def pathBoundaryDen (a : ℕ → ℕ) (r : ℕ) : ℕ :=
  pathDenominatorAt a r

noncomputable def pathBoundaryValue (a : ℕ → ℕ) (r : ℕ) : ℝ :=
  (pathBoundaryNum a r : ℝ) / (pathBoundaryDen a r : ℝ)

@[simp] theorem pathBoundaryNum_eq (a : ℕ → ℕ) (r : ℕ) :
    pathBoundaryNum a r =
      CFBlockNumerator a (pathPairOfIndex a r).1
        (pathPairOfIndex a r).2 :=
  rfl

@[simp] theorem pathBoundaryDen_eq (a : ℕ → ℕ) (r : ℕ) :
    pathBoundaryDen a r =
      CFBlockDenominator a (pathPairOfIndex a r).1
        (pathPairOfIndex a r).2 :=
  rfl

@[simp] theorem pathBoundaryValue_eq (a : ℕ → ℕ) (r : ℕ) :
    pathBoundaryValue a r =
      (pathBoundaryNum a r : ℝ) / (pathBoundaryDen a r : ℝ) :=
  rfl

theorem pathBoundaryDen_pos
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    (r : ℕ) :
    0 < pathBoundaryDen a r := by
  have hvalid :
      ValidPathPair a (pathPairOfIndex a r).1 (pathPairOfIndex a r).2 :=
    pathPairOfIndex_valid hpos r
  exact lt_of_lt_of_le Nat.zero_lt_one
    (one_le_CFBlockDenominator_of_valid hpos hvalid)

theorem pathBoundaryDen_le_exp_phi
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K r : ℕ}
    (hr : r < K) :
    (pathBoundaryDen a r : ℝ)
      ≤ Real.exp (((K : ℝ) + 4) *
          Real.log Real.goldenRatio) := by
  have hmem :
      pathPairOfIndex a r ∈ canonicalPathPrefixIndices a K :=
    pathPairOfIndex_mem_prefix hpos hr
  rcases hpair : pathPairOfIndex a r with ⟨j, t⟩
  have hden :
      (CFBlockDenominator a j t : ℝ) ≤
        Real.exp (((K : ℝ) + 4) *
          Real.log Real.goldenRatio) :=
    CFBlockDenominator_le_exp_phi_of_flattened_lt
      (a := a) hpos (by simpa [hpair] using hmem)
  simpa [pathBoundaryDen, pathDenominatorAt, hpair] using hden

theorem log_pathBoundaryDen_le_phi
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K r : ℕ}
    (hr : r < K) :
    Real.log (pathBoundaryDen a r : ℝ)
      ≤ ((K : ℝ) + 4) * Real.log Real.goldenRatio := by
  have hdenpos : 0 < (pathBoundaryDen a r : ℝ) := by
    exact_mod_cast pathBoundaryDen_pos (a := a) hpos r
  have hle := pathBoundaryDen_le_exp_phi (a := a) hpos hr
  have hlog := Real.log_le_log hdenpos hle
  simpa using hlog

/-! ## Least-denominator exclusion for boundary rationals -/

theorem leastDenominatorInIntervalSeq_le_pathBoundaryDen_of_mem
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    {a : ℕ → ℕ} {m r : ℕ}
    (_hdenpos : 0 < pathBoundaryDen a r)
    (hmem :
      RatInClosedInterval (L m) (U m)
        (pathBoundaryNum a r : ℤ)
        (pathBoundaryDen a r)) :
    leastDenominatorInIntervalSeq L U hLU m ≤
      pathBoundaryDen a r := by
  unfold leastDenominatorInIntervalSeq
  exact leastDenominatorInInterval_min (hLU m)
    ⟨(pathBoundaryNum a r : ℤ), hmem⟩

theorem not_ratInClosedInterval_pathBoundary_of_den_lt_qmin
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    {a : ℕ → ℕ} {m r : ℕ}
    (hdenpos : 0 < pathBoundaryDen a r)
    (hlt :
      pathBoundaryDen a r <
        leastDenominatorInIntervalSeq L U hLU m) :
    ¬ RatInClosedInterval (L m) (U m)
        (pathBoundaryNum a r : ℤ)
        (pathBoundaryDen a r) := by
  intro hmem
  have hle :=
    leastDenominatorInIntervalSeq_le_pathBoundaryDen_of_mem
      (L := L) (U := U) (hLU := hLU)
      (a := a) (m := m) (r := r)
      hdenpos hmem
  omega

theorem not_mem_Icc_pathBoundaryValue_of_den_lt_qmin
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    {a : ℕ → ℕ} {m r : ℕ}
    (hdenpos : 0 < pathBoundaryDen a r)
    (hlt :
      pathBoundaryDen a r <
        leastDenominatorInIntervalSeq L U hLU m) :
    ¬ (L m ≤ pathBoundaryValue a r ∧
        pathBoundaryValue a r ≤ U m) := by
  intro hI
  have hRat :
      RatInClosedInterval (L m) (U m)
        (pathBoundaryNum a r : ℤ)
        (pathBoundaryDen a r) := by
    refine ⟨hdenpos, ?_, ?_⟩
    · simpa [pathBoundaryValue] using hI.1
    · simpa [pathBoundaryValue] using hI.2
  exact
    not_ratInClosedInterval_pathBoundary_of_den_lt_qmin
      (L := L) (U := U) (hLU := hLU)
      (a := a) (m := m) (r := r)
      hdenpos hlt hRat

/-! ## Ramanujan least-denominator lower bound and boundary comparison -/

theorem eventually_log_qmin_ramanujanPi_lower_of_lt_six_log_two
    {μ ν κ : ℝ}
    (hκ : κ < 6 * Real.log 2)
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν) :
    ∀ᶠ m : ℕ in atTop,
      (κ * (m : ℝ)) / ν ≤
        Real.log
          (leastDenominatorInIntervalSeq
            ramanujanPiL ramanujanPiU ramanujanPi_hLU m : ℝ) := by
  have hshrink :=
    ramanujanPi_intervalShrinksTo_inv_pi_from_hasSum hRam
  have hwidth :
      EventuallyExpWidthUpper ramanujanPiL ramanujanPiU κ 0 :=
    ramanujanPi_eventuallyExpWidthUpper_of_lt_six_log_two hκ
  have hNoSmall :
      ∀ Q0 : ℕ,
        EventuallyLeastDenominatorGe
          ramanujanPiL ramanujanPiU ramanujanPi_hLU Q0 :=
    eventuallyLeastDenominatorGe_ramanujanPi_from_hasSum hRam
  have h :=
    eventually_log_leastDenominator_lower_of_measure_width
      (α := 1 / Real.pi)
      (μ := μ) (ν := ν) (κ := κ) (C := 0)
      (L := ramanujanPiL) (U := ramanujanPiU)
      (hLU := ramanujanPi_hLU)
      hμ hν hνpos hshrink.2.2 hwidth hNoSmall
  filter_upwards [h] with m hm
  simpa using hm

theorem eventually_linearTrial_phi_bound_lt
    {c κ ν : ℝ}
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hcgap :
      c * Real.log Real.goldenRatio < κ / ν) :
    ∀ᶠ m : ℕ in atTop,
      ((linearPathTrial c m : ℝ) + 4) *
          Real.log Real.goldenRatio
        < (κ * (m : ℝ)) / ν := by
  let φlog : ℝ := Real.log Real.goldenRatio
  have hφpos : 0 < φlog := by
    dsimp [φlog]
    exact log_goldenRatio_pos
  have hgap : 0 < κ / ν - c * φlog := by
    simpa [φlog] using sub_pos.mpr hcgap
  have hlarge :
      ∀ᶠ m : ℕ in atTop,
        4 * φlog < (κ / ν - c * φlog) * (m : ℝ) :=
    (eventually_const_le_pos_mul_natCast
      (A := 4 * φlog + 1) hgap).mono (by
        intro m hm
        nlinarith)
  filter_upwards [hlarge] with m hm
  have hKle : (linearPathTrial c m : ℝ) ≤ c * (m : ℝ) :=
    linearPathTrial_cast_le (le_of_lt hcpos) m
  have hKφ :
      (linearPathTrial c m : ℝ) * φlog ≤
        (c * (m : ℝ)) * φlog :=
    mul_le_mul_of_nonneg_right hKle (le_of_lt hφpos)
  have hνne : ν ≠ 0 := ne_of_gt hνpos
  have hrewrite :
      (κ * (m : ℝ)) / ν = (κ / ν) * (m : ℝ) := by
    field_simp [hνne]
  change (((linearPathTrial c m : ℝ) + 4) * φlog) <
    (κ * (m : ℝ)) / ν
  rw [hrewrite]
  nlinarith

theorem eventually_pathBoundaryDen_lt_qmin_linearTrial
    {μ ν c κ : ℝ}
    (hκ : κ < 6 * Real.log 2)
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hcgap :
      c * Real.log Real.goldenRatio < κ / ν) :
    ∀ᶠ m : ℕ in atTop,
      ∀ r : ℕ,
        r < linearPathTrial c m →
          pathBoundaryDen oneOverPiCF r <
            leastDenominatorInIntervalSeq
              ramanujanPiL ramanujanPiU ramanujanPi_hLU m := by
  have hqminLower :=
    eventually_log_qmin_ramanujanPi_lower_of_lt_six_log_two
      hκ hRam hμ hν hνpos
  have htrial :=
    eventually_linearTrial_phi_bound_lt
      (c := c) (κ := κ) (ν := ν) hνpos hcpos hcgap
  filter_upwards [hqminLower, htrial] with m hqmin htrialm
  intro r hr
  have hlogDen :
      Real.log (pathBoundaryDen oneOverPiCF r : ℝ)
        ≤ ((linearPathTrial c m : ℝ) + 4) *
          Real.log Real.goldenRatio :=
    log_pathBoundaryDen_le_phi
      (a := oneOverPiCF) oneOverPiCF_partials_pos hr
  have hlog_lt :
      Real.log (pathBoundaryDen oneOverPiCF r : ℝ) <
        Real.log
          (leastDenominatorInIntervalSeq
            ramanujanPiL ramanujanPiU ramanujanPi_hLU m : ℝ) :=
    lt_of_le_of_lt hlogDen (lt_of_lt_of_le htrialm hqmin)
  have hdenpos : 0 < (pathBoundaryDen oneOverPiCF r : ℝ) := by
    exact_mod_cast pathBoundaryDen_pos
      (a := oneOverPiCF) oneOverPiCF_partials_pos r
  have hqpos :
      0 <
        (leastDenominatorInIntervalSeq
          ramanujanPiL ramanujanPiU ramanujanPi_hLU m : ℝ) :=
    leastDenominatorInIntervalSeq_real_pos m
  have hreal :
      (pathBoundaryDen oneOverPiCF r : ℝ) <
        (leastDenominatorInIntervalSeq
          ramanujanPiL ramanujanPiU ramanujanPi_hLU m : ℝ) :=
    (Real.log_lt_log_iff hdenpos hqpos).mp hlog_lt
  exact_mod_cast hreal

/-! ## Boundary-avoidance and certification predicates -/

def IntervalAvoidsIntermediatePathBoundaries
    (a : ℕ → ℕ) (L U : ℕ → ℝ) (K m : ℕ) : Prop :=
  ∀ r : ℕ,
    r < K →
      ¬ RatInClosedInterval (L m) (U m)
        (pathBoundaryNum a r : ℤ)
        (pathBoundaryDen a r)

theorem intervalAvoidsIntermediatePathBoundaries_of_den_lt_qmin
    {a : ℕ → ℕ} {L U : ℕ → ℝ}
    {hLU : ∀ m : ℕ, L m < U m}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K m : ℕ}
    (hdenlt :
      ∀ r : ℕ,
        r < K →
          pathBoundaryDen a r <
            leastDenominatorInIntervalSeq L U hLU m) :
    IntervalAvoidsIntermediatePathBoundaries a L U K m := by
  intro r hr
  exact not_ratInClosedInterval_pathBoundary_of_den_lt_qmin
    (L := L) (U := U) (hLU := hLU)
    (a := a) (m := m) (r := r)
    (pathBoundaryDen_pos (a := a) hpos r)
    (hdenlt r hr)

theorem eventually_intervalAvoidsIntermediatePathBoundaries_linearTrial
    {μ ν c κ : ℝ}
    (hκ : κ < 6 * Real.log 2)
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hcgap :
      c * Real.log Real.goldenRatio < κ / ν) :
    ∀ᶠ m : ℕ in atTop,
      IntervalAvoidsIntermediatePathBoundaries oneOverPiCF
        ramanujanPiL ramanujanPiU
        (linearPathTrial c m) m := by
  have hdenlt :=
    eventually_pathBoundaryDen_lt_qmin_linearTrial
      hκ hRam hμ hν hνpos hcpos hcgap
  filter_upwards [hdenlt] with m hm
  exact intervalAvoidsIntermediatePathBoundaries_of_den_lt_qmin
    (a := oneOverPiCF)
    (L := ramanujanPiL) (U := ramanujanPiU)
    (hLU := ramanujanPi_hLU)
    oneOverPiCF_partials_pos hm

def BoundaryOnSameSideAsInterval
    (α L U b : ℝ) : Prop :=
  (b < α → b < L) ∧ (α < b → U < b)

def IntervalCertifiesIntermediatePathPrefix
    (α : ℝ) (a : ℕ → ℕ) (L U : ℕ → ℝ)
    (K m : ℕ) : Prop :=
  ∀ r : ℕ,
    r < K →
      BoundaryOnSameSideAsInterval α (L m) (U m)
        (pathBoundaryValue a r)

theorem boundarySameSide_of_contains_alpha_and_not_mem
    {α L U b : ℝ}
    (hcontains : L ≤ α ∧ α ≤ U)
    (hnot : ¬ (L ≤ b ∧ b ≤ U)) :
    BoundaryOnSameSideAsInterval α L U b := by
  constructor
  · intro hbα
    by_contra hnot_lt
    have hLle : L ≤ b := le_of_not_gt hnot_lt
    have hbU : b ≤ U := le_trans hbα.le hcontains.2
    exact hnot ⟨hLle, hbU⟩
  · intro hαb
    by_contra hnot_lt
    have hLb : L ≤ b := le_trans hcontains.1 hαb.le
    have hbU : b ≤ U := le_of_not_gt hnot_lt
    exact hnot ⟨hLb, hbU⟩

theorem intervalCertifiesIntermediatePathPrefix_of_contains_and_avoids
    {α : ℝ} {a : ℕ → ℕ} {L U : ℕ → ℝ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {K m : ℕ}
    (hcontains : L m ≤ α ∧ α ≤ U m)
    (havoid :
      IntervalAvoidsIntermediatePathBoundaries a L U K m) :
    IntervalCertifiesIntermediatePathPrefix α a L U K m := by
  intro r hr
  have hnotRat := havoid r hr
  apply boundarySameSide_of_contains_alpha_and_not_mem hcontains
  intro hI
  have hdenpos : 0 < pathBoundaryDen a r :=
    pathBoundaryDen_pos (a := a) hpos r
  have hRat :
      RatInClosedInterval (L m) (U m)
        (pathBoundaryNum a r : ℤ)
        (pathBoundaryDen a r) := by
    refine ⟨hdenpos, ?_, ?_⟩
    · simpa [pathBoundaryValue] using hI.1
    · simpa [pathBoundaryValue] using hI.2
  exact hnotRat hRat

theorem eventually_intervalCertifiesIntermediatePathPrefix_linearTrial
    {μ ν c κ : ℝ}
    (hκ : κ < 6 * Real.log 2)
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hcgap :
      c * Real.log Real.goldenRatio < κ / ν) :
    ∀ᶠ m : ℕ in atTop,
      IntervalCertifiesIntermediatePathPrefix
        (1 / Real.pi) oneOverPiCF
        ramanujanPiL ramanujanPiU
        (linearPathTrial c m) m := by
  have hcontains := ramanujanPi_interval_contains_inv_pi_of_hasSum hRam
  have havoid :=
    eventually_intervalAvoidsIntermediatePathBoundaries_linearTrial
      hκ hRam hμ hν hνpos hcpos hcgap
  filter_upwards [havoid] with m hm_avoid
  exact intervalCertifiesIntermediatePathPrefix_of_contains_and_avoids
    (α := 1 / Real.pi)
    (a := oneOverPiCF)
    (L := ramanujanPiL) (U := ramanujanPiU)
    oneOverPiCF_partials_pos
    (hcontains m) hm_avoid

/-! ## Concrete Ramanujan intermediate-path production -/

theorem eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete_boundary_slope
    {μ ν c ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hc :
      c < (6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio))
    (hρ : ρ < c / 2)
    (hΛ : c * Real.log Real.goldenRatio < Λ) :
    ∀ᶠ m : ℕ in atTop,
      IntervalCertifiesIntermediatePathPrefix
        (1 / Real.pi) oneOverPiCF
        ramanujanPiL ramanujanPiU
        (linearPathTrial c m) m
      ∧
      ρ * (m : ℝ) ≤
        (((certifiedOddPathPrefix oneOverPiCF
            (linearPathTrial c m)).filter
          (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) := by
  let φlog : ℝ := Real.log Real.goldenRatio
  let κ : ℝ := (c * ν * φlog + 6 * Real.log 2) / 2
  have hφpos : 0 < φlog := by
    dsimp [φlog]
    exact log_goldenRatio_pos
  have hdenpos : 0 < ν * φlog := mul_pos hνpos hφpos
  have hmul : c * (ν * φlog) < 6 * Real.log 2 := by
    exact (lt_div_iff₀ hdenpos).mp (by simpa [φlog] using hc)
  have hmul' : c * ν * φlog < 6 * Real.log 2 := by
    nlinarith
  have hκ_lt : κ < 6 * Real.log 2 := by
    dsimp [κ]
    linarith
  have hcgap : c * Real.log Real.goldenRatio < κ / ν := by
    rw [show Real.log Real.goldenRatio = φlog by rfl]
    rw [lt_div_iff₀ hνpos]
    dsimp [κ]
    nlinarith
  have hcert :
      ∀ᶠ m : ℕ in atTop,
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m :=
    eventually_intervalCertifiesIntermediatePathPrefix_linearTrial
      (κ := κ) hκ_lt hRam hμ hν hνpos hcpos hcgap
  have hcard :
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) :=
    eventuallyManyCertifiedOddPathBelowExp_linearTrial
      (a := oneOverPiCF)
      oneOverPiCF_partials_pos
      hcpos hρ hΛ
  filter_upwards [hcert, hcard] with m hmcert hmcard
  exact ⟨hmcert, hmcard⟩

theorem eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete_boundary
    {μ ν ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hνtwo : 2 < ν)
    (hρpos : 0 < ρ)
    (hρ :
      ρ <
        ((6 * Real.log 2) /
          (ν * Real.log Real.goldenRatio)) / 2)
    (hΛ : 3 * Real.log 2 < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ c : ℝ,
        0 < c ∧
        c < (6 * Real.log 2) /
              (ν * Real.log Real.goldenRatio) ∧
        ρ < c / 2 ∧
        c * Real.log Real.goldenRatio < Λ ∧
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m ∧
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) := by
  let Cmax : ℝ :=
    (6 * Real.log 2) / (ν * Real.log Real.goldenRatio)
  let c : ℝ := (2 * ρ + Cmax) / 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hφpos : 0 < Real.log Real.goldenRatio := log_goldenRatio_pos
  have hdenpos : 0 < ν * Real.log Real.goldenRatio :=
    mul_pos hνpos hφpos
  have hCmaxpos : 0 < Cmax := by
    dsimp [Cmax]
    positivity
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hcCmax : c < Cmax := by
    dsimp [c, Cmax] at *
    linarith
  have hρc : ρ < c / 2 := by
    dsimp [c, Cmax] at *
    linarith
  have hCmax_log :
      Cmax * Real.log Real.goldenRatio = (6 * Real.log 2) / ν := by
    dsimp [Cmax]
    field_simp [ne_of_gt hνpos, ne_of_gt hφpos]
  have hcΛ : c * Real.log Real.goldenRatio < Λ := by
    have hc_log :
        c * Real.log Real.goldenRatio <
          Cmax * Real.log Real.goldenRatio :=
      mul_lt_mul_of_pos_right hcCmax hφpos
    have hC_lt_three : (6 * Real.log 2) / ν < 3 * Real.log 2 := by
      rw [div_lt_iff₀ hνpos]
      have hthreeLogPos : 0 < 3 * Real.log 2 := by positivity
      have hmul :
          2 * (3 * Real.log 2) < ν * (3 * Real.log 2) :=
        mul_lt_mul_of_pos_right hνtwo hthreeLogPos
      nlinarith
    calc
      c * Real.log Real.goldenRatio
          < Cmax * Real.log Real.goldenRatio := hc_log
      _ = (6 * Real.log 2) / ν := hCmax_log
      _ < 3 * Real.log 2 := hC_lt_three
      _ < Λ := hΛ
  have hmain :
      ∀ᶠ m : ℕ in atTop,
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m
        ∧
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) :=
    eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete_boundary_slope
      (μ := μ) (ν := ν) (c := c) (ρ := ρ) (Λ := Λ)
      hRam hμ hν hνpos hcpos (by simpa [Cmax] using hcCmax)
      hρc hcΛ
  filter_upwards [hmain] with m hm
  exact ⟨c, hcpos, by simpa [Cmax] using hcCmax, hρc, hcΛ, hm.1, hm.2⟩

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanConcreteCorollaries.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Concrete corollaries from Ramanujan intermediate-path certification

This file packages the concrete boundary-certification theorem into cleaner
interfaces:

* finite irrationality measure gives some positive certified production slope;
* the certified intermediate-path set injects into the actual floor-sum set
  `A (1 / π)`;
* therefore the actual truncation below `exp(Λ m)` has linearly many elements.

The analytic Bauer/Ramanujan identity remains a named input, not an axiom.
-/

/-- The remaining Ramanujan summation identity, isolated as a named interface. -/
def BauerRamanujanIdentity : Prop :=
  HasSum ramanujanPiTerm (1 / Real.pi)

/-- A real number has finite irrationality measure in the project's predicate
if it has some finite exponent witness. -/
def HasFiniteIrrationalityMeasure (α : ℝ) : Prop :=
  ∃ μ : ℝ, HasIrrationalityMeasure α μ

private theorem oneOverPi_pos : 0 < oneOverPi := by
  unfold oneOverPi
  exact one_div_pos.mpr Real.pi_pos

private theorem oneOverPi_irrational : IsIrrational oneOverPi := by
  unfold oneOverPi
  simpa [one_div] using invPi_isIrrational

private theorem oneOverPiCF_isSimpleCFExpansion :
    IsSimpleCFExpansion oneOverPi oneOverPiCF := by
  unfold oneOverPiCF
  exact simplePartialQuotient_isSimpleCFExpansion
    oneOverPi_pos oneOverPi_irrational

/-- Every certified odd intermediate-path denominator for the canonical CF of
`1 / π` is an actual member of the floor-sum divisibility set `A (1 / π)`. -/
theorem certifiedOddPathPrefix_oneOverPi_subset_A
    (K : ℕ) :
    ↑(certifiedOddPathPrefix oneOverPiCF K) ⊆ A oneOverPi := by
  exact certifiedOddPathPrefix_subset_A_of_IsSimpleCFExpansion
    oneOverPi_pos oneOverPi_irrational oneOverPiCF_isSimpleCFExpansion

/-- A finite truncation of the actual set `A (1 / π)` below
`exp(Λ m)`. -/
noncomputable def AOneOverPiBelowExp (Λ : ℝ) (m : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range (Nat.floor (Real.exp (Λ * (m : ℝ))) + 1)).filter
      (fun x : ℕ => x ∈ A oneOverPi)

@[simp] theorem mem_AOneOverPiBelowExp_iff
    {Λ : ℝ} {m x : ℕ} :
    x ∈ AOneOverPiBelowExp Λ m ↔
      x < Nat.floor (Real.exp (Λ * (m : ℝ))) + 1 ∧
        x ∈ A oneOverPi := by
  classical
  unfold AOneOverPiBelowExp
  simp

theorem certifiedOddPathPrefix_filter_subset_AOneOverPiBelowExp
    {c Λ : ℝ} {m : ℕ} :
    ((certifiedOddPathPrefix oneOverPiCF (linearPathTrial c m)).filter
      (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ))))
      ⊆ AOneOverPiBelowExp Λ m := by
  classical
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [mem_AOneOverPiBelowExp_iff]
  refine ⟨?_, certifiedOddPathPrefix_oneOverPi_subset_A
    (linearPathTrial c m) hx.1⟩
  have hlt_real :
      (x : ℝ) <
        (Nat.floor (Real.exp (Λ * (m : ℝ))) : ℝ) + 1 :=
    lt_of_le_of_lt hx.2
      (Nat.lt_floor_add_one (Real.exp (Λ * (m : ℝ))))
  exact_mod_cast hlt_real

/-- If the concrete certification theorem supplies a lower bound for the
certified height-filtered path set, then the actual truncation of `A (1 / π)`
has the same lower bound. -/
theorem eventually_AOneOverPiBelowExp_card_lower_of_certified
    {c ρ Λ : ℝ}
    (hcert :
      ∀ᶠ m : ℕ in atTop,
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m
        ∧
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤ ((AOneOverPiBelowExp Λ m).card : ℝ) := by
  filter_upwards [hcert] with m hm
  have hsubset :
      ((certifiedOddPathPrefix oneOverPiCF (linearPathTrial c m)).filter
        (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ))))
        ⊆ AOneOverPiBelowExp Λ m :=
    certifiedOddPathPrefix_filter_subset_AOneOverPiBelowExp
      (c := c) (Λ := Λ) (m := m)
  have hcard_nat :
      (((certifiedOddPathPrefix oneOverPiCF (linearPathTrial c m)).filter
        (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card)
        ≤ (AOneOverPiBelowExp Λ m).card :=
    Finset.card_le_card hsubset
  have hcard_real :
      ((((certifiedOddPathPrefix oneOverPiCF (linearPathTrial c m)).filter
        (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℕ) : ℝ)
        ≤ ((AOneOverPiBelowExp Λ m).card : ℝ) := by
    exact_mod_cast hcard_nat
  exact hm.2.trans hcard_real

/-- Under any finite irrationality-measure witness for `1 / π`, Bauer's
Ramanujan identity gives some positive certified production slope. -/
theorem exists_eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    {μ : ℝ}
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ) :
    ∃ c ρ Λ : ℝ,
      0 < c ∧ 0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m
        ∧
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) := by
  let ν0 : ℝ := max (μ + 1) 3
  let c0 : ℝ :=
    Real.log 2 / (ν0 * Real.log Real.goldenRatio)
  let ρ0 : ℝ := c0 / 4
  let Λ0 : ℝ := 4 * Real.log 2
  have hlog2pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hφpos : 0 < Real.log Real.goldenRatio :=
    log_goldenRatio_pos
  have hμν : μ < ν0 := by
    dsimp [ν0]
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have htwoν : 2 < ν0 := by
    dsimp [ν0]
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 3) (le_max_right _ _)
  have hνpos : 0 < ν0 := by linarith
  have hdenpos : 0 < ν0 * Real.log Real.goldenRatio :=
    mul_pos hνpos hφpos
  have hcpos : 0 < c0 := by
    dsimp [c0]
    exact div_pos hlog2pos hdenpos
  have hρpos : 0 < ρ0 := by
    dsimp [ρ0]
    positivity
  have hΛpos : 3 * Real.log 2 < Λ0 := by
    dsimp [Λ0]
    nlinarith
  have hcUpper :
      c0 < (6 * Real.log 2) /
        (ν0 * Real.log Real.goldenRatio) := by
    dsimp [c0]
    exact div_lt_div_of_pos_right (by nlinarith) hdenpos
  have hρUpper : ρ0 < c0 / 2 := by
    dsimp [ρ0]
    nlinarith
  have hcHeight : c0 * Real.log Real.goldenRatio < Λ0 := by
    have hνne : ν0 ≠ 0 := ne_of_gt hνpos
    have hφne : Real.log Real.goldenRatio ≠ 0 := ne_of_gt hφpos
    have hc_eq :
        c0 * Real.log Real.goldenRatio = Real.log 2 / ν0 := by
      dsimp [c0]
      field_simp [hνne, hφne]
    have hsmall : Real.log 2 / ν0 < 4 * Real.log 2 := by
      rw [div_lt_iff₀ hνpos]
      nlinarith
    calc
      c0 * Real.log Real.goldenRatio
          = Real.log 2 / ν0 := hc_eq
      _ < 4 * Real.log 2 := hsmall
      _ = Λ0 := by rfl
  refine ⟨c0, ρ0, Λ0, hcpos, hρpos, hΛpos, ?_⟩
  exact
    eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete_boundary_slope
      (μ := μ) (ν := ν0) (c := c0) (ρ := ρ0) (Λ := Λ0)
      hRam hμ hμν hνpos hcpos hcUpper hρUpper hcHeight

theorem exists_eventuallyManyCertifiedAOneOverPiPathBelowExp_of_finiteMeasure
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ c ρ Λ : ℝ,
      0 < c ∧ 0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        IntervalCertifiesIntermediatePathPrefix
          (1 / Real.pi) oneOverPiCF
          ramanujanPiL ramanujanPiU
          (linearPathTrial c m) m
        ∧
        ρ * (m : ℝ) ≤
          (((certifiedOddPathPrefix oneOverPiCF
              (linearPathTrial c m)).filter
            (fun x : ℕ => (x : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).card : ℝ) := by
  rcases hfin with ⟨μ, hμ⟩
  exact exists_eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete hRam hμ

/-- Slope-specific actual `A (1 / π)` counting theorem below exponential
height. -/
theorem eventually_AOneOverPiBelowExp_card_lower_concrete
    {μ ν c ρ Λ : ℝ}
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : μ < ν)
    (hνpos : 0 < ν)
    (hcpos : 0 < c)
    (hc :
      c < (6 * Real.log 2) /
            (ν * Real.log Real.goldenRatio))
    (hρ : ρ < c / 2)
    (hΛ : c * Real.log Real.goldenRatio < Λ) :
    ∀ᶠ m : ℕ in atTop,
      ρ * (m : ℝ) ≤ ((AOneOverPiBelowExp Λ m).card : ℝ) := by
  exact eventually_AOneOverPiBelowExp_card_lower_of_certified
    (c := c) (ρ := ρ) (Λ := Λ)
    (eventuallyManyCertifiedAOneOverPiPathBelowExp_concrete_boundary_slope
      (μ := μ) (ν := ν) (c := c) (ρ := ρ) (Λ := Λ)
      hRam hμ hν hνpos hcpos hc hρ hΛ)

/-- Finite-measure wrapper for the actual `A (1 / π)` count. -/
theorem exists_eventually_AOneOverPiBelowExp_card_lower_of_finiteMeasure
    (hRam : HasSum ramanujanPiTerm (1 / Real.pi))
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤ ((AOneOverPiBelowExp Λ m).card : ℝ) := by
  rcases exists_eventuallyManyCertifiedAOneOverPiPathBelowExp_of_finiteMeasure
      hRam hfin with
    ⟨c, ρ, Λ, _hcpos, hρpos, hΛ, hprod⟩
  refine ⟨ρ, Λ, hρpos, hΛ, ?_⟩
  exact eventually_AOneOverPiBelowExp_card_lower_of_certified
    (c := c) (ρ := ρ) (Λ := Λ) hprod

/-- Bauer-interface version of the finite-measure counting theorem. -/
theorem exists_eventually_AOneOverPiBelowExp_card_lower_of_Bauer_finiteMeasure
    (hBauer : BauerRamanujanIdentity)
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤ ((AOneOverPiBelowExp Λ m).card : ℝ) :=
  exists_eventually_AOneOverPiBelowExp_card_lower_of_finiteMeasure
    hBauer hfin

end IrrationalityAr

/-! ## Merged from IrrationalityAr/RamanujanLimsupEntropy.lean -/


open Filter
open scoped BigOperators Topology

namespace IrrationalityAr

noncomputable section

/-!
# Limsup-completeness for bounded-jump depth subsequences

This file isolates the abstract part of the Ramanujan-certified-depth
argument.  A monotone, cofinal sequence of indices with bounded additive jumps
is limsup-complete for normalized monotone nonnegative cumulative quantities.

The intended applications are continued-fraction entropy and canonical block
entropy.  The Ramanujan-specific precision construction can later feed this
file by producing a depth sequence `J` satisfying the three hypotheses:
monotone, tending to infinity, and bounded jumps.
-/

/-- Normalized density of a cumulative real-valued quantity. -/
noncomputable def density (E : ℕ → ℝ) (n : ℕ) : ℝ :=
  E n / (((n + 1 : ℕ) : ℝ))

/-- Eventual upper-bound form of `limsup F ≤ C` at `atTop`.

This avoids boundedness side conditions for `Filter.limsup`; it is exactly the
form needed for transferring entropy-density bounds. -/
def LimsupLeAtTop (F : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, F n ≤ C + ε

lemma exists_hit_index
    {J : ℕ → ℕ}
    (hJtop : Tendsto J atTop atTop)
    (n : ℕ) :
    ∃ m : ℕ, n ≤ J m := by
  rw [tendsto_atTop] at hJtop
  have h := hJtop n
  rw [eventually_atTop] at h
  rcases h with ⟨m, hm⟩
  exact ⟨m, hm m le_rfl⟩

/-- First index at which a cofinal sequence `J` reaches the target `n`. -/
noncomputable def firstHit
    (J : ℕ → ℕ)
    (hJtop : Tendsto J atTop atTop)
    (n : ℕ) : ℕ :=
  Nat.find (exists_hit_index hJtop n)

lemma le_J_firstHit
    {J : ℕ → ℕ} (hJtop : Tendsto J atTop atTop) (n : ℕ) :
    n ≤ J (firstHit J hJtop n) := by
  exact Nat.find_spec (exists_hit_index hJtop n)

lemma firstHit_minimal
    {J : ℕ → ℕ} (hJtop : Tendsto J atTop atTop)
    {n m : ℕ} (hm : m < firstHit J hJtop n) :
    ¬ n ≤ J m := by
  exact Nat.find_min (exists_hit_index hJtop n) hm

lemma firstHit_tendsto_atTop
    {J : ℕ → ℕ}
    (hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop) :
    Tendsto (firstHit J hJtop) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  rw [eventually_atTop]
  refine ⟨J M + 1, ?_⟩
  intro n hn
  by_contra hnot
  have hlt : firstHit J hJtop n < M := Nat.lt_of_not_ge hnot
  have hJle : J (firstHit J hJtop n) ≤ J M :=
    hJmono (Nat.le_of_lt hlt)
  have hnle : n ≤ J (firstHit J hJtop n) := le_J_firstHit hJtop n
  omega

lemma J_firstHit_le_add_gap_eventually
    {J : ℕ → ℕ}
    (_hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop)
    {D : ℕ}
    (hJgap : ∀ m : ℕ, J (m + 1) ≤ J m + D) :
    ∀ᶠ n : ℕ in atTop,
      J (firstHit J hJtop n) ≤ n + D := by
  rw [eventually_atTop]
  refine ⟨J 0 + 1, ?_⟩
  intro n hn
  have hmne : firstHit J hJtop n ≠ 0 := by
    intro hm
    have hnle : n ≤ J (firstHit J hJtop n) := le_J_firstHit hJtop n
    rw [hm] at hnle
    omega
  rcases Nat.exists_eq_succ_of_ne_zero hmne with ⟨m, hm⟩
  have hm_lt : m < firstHit J hJtop n := by omega
  have hnot : ¬ n ≤ J m := firstHit_minimal hJtop hm_lt
  have hprev_lt : J m < n := Nat.lt_of_not_ge hnot
  have hgap : J (m + 1) ≤ J m + D := hJgap m
  calc
    J (firstHit J hJtop n) = J (m + 1) := by rw [hm]
    _ ≤ J m + D := hgap
    _ ≤ n + D := Nat.add_le_add_right (Nat.le_of_lt hprev_lt) D

private lemma density_nonneg
    {E : ℕ → ℝ}
    (hEnonneg : ∀ n : ℕ, 0 ≤ E n)
    (n : ℕ) :
    0 ≤ density E n := by
  unfold density
  exact div_nonneg (hEnonneg n) (by positivity)

lemma density_le_of_index_le_and_le_add
    {E : ℕ → ℝ}
    (hEmono : Monotone E)
    (_hEnonneg : ∀ n : ℕ, 0 ≤ E n)
    {n k D : ℕ}
    (hnk : n ≤ k)
    (_hkd : k ≤ n + D) :
    density E n ≤
      ((((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) * density E k) := by
  have hEk : E n ≤ E k := hEmono hnk
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  unfold density
  calc
    E n / (((n + 1 : ℕ) : ℝ))
        ≤ E k / (((n + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right hEk (le_of_lt hnpos)
    _ = (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) *
          (E k / (((k + 1 : ℕ) : ℝ))) := by
          field_simp [ne_of_gt hnpos, ne_of_gt hkpos]

lemma overshoot_factor_eventually_le
    (D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (((n + D + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) ≤ 1 + η := by
  rcases exists_nat_gt ((D : ℝ) / η) with ⟨N, hN⟩
  rw [eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : (D : ℝ) / η < ((n + 1 : ℕ) : ℝ) := by
    have hnle : (N : ℝ) ≤ (n : ℝ) := hNle
    norm_num
    linarith
  have hDlt : (D : ℝ) < (((n + 1 : ℕ) : ℝ)) * η :=
    (div_lt_iff₀ hη).mp hlt
  have hDdiv : (D : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤ η := by
    rw [div_le_iff₀ hnpos]
    linarith
  have hratio :
      (((n + D + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) =
        1 + (D : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
    field_simp [ne_of_gt hnpos]
    norm_num
    ring
  rw [hratio]
  linarith

theorem LimsupLeAtTop.comp_of_tendsto
    {F : ℕ → ℝ} {J : ℕ → ℕ} {C : ℝ}
    (hF : LimsupLeAtTop F C)
    (hJtop : Tendsto J atTop atTop) :
    LimsupLeAtTop (fun m => F (J m)) C := by
  intro ε hε
  exact hJtop.eventually (hF ε hε)

theorem LimsupLeAtTop.of_comp_bounded_jumps
    {E : ℕ → ℝ} {J : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hEmono : Monotone E)
    (hEnonneg : ∀ n : ℕ, 0 ≤ E n)
    (hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop)
    (hJgap : ∃ D : ℕ, ∀ m : ℕ, J (m + 1) ≤ J m + D)
    (hcomp : LimsupLeAtTop (fun m => density E (J m)) C) :
    LimsupLeAtTop (density E) C := by
  intro ε hε
  rcases hJgap with ⟨D, hD⟩
  let B : ℝ := C + ε / 2
  have hBpos : 0 < B := by
    dsimp [B]
    linarith
  let η : ℝ := (ε / 2) / B
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos (by linarith) hBpos
  have hhit_top : Tendsto (firstHit J hJtop) atTop atTop :=
    firstHit_tendsto_atTop hJmono hJtop
  have hsubseq :
      ∀ᶠ n : ℕ in atTop,
        density E (J (firstHit J hJtop n)) ≤ B := by
    have hcomp' :
        ∀ᶠ m : ℕ in atTop,
          density E (J m) ≤ C + ε / 2 :=
      hcomp (ε / 2) (by linarith)
    simpa [B] using hhit_top.eventually hcomp'
  have hovershoot :
      ∀ᶠ n : ℕ in atTop,
        J (firstHit J hJtop n) ≤ n + D :=
    J_firstHit_le_add_gap_eventually hJmono hJtop hD
  have hfactor :
      ∀ᶠ n : ℕ in atTop,
        (((n + D + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) ≤ 1 + η :=
    overshoot_factor_eventually_le D hηpos
  filter_upwards [hsubseq, hovershoot, hfactor] with n hnsub hnov hnfactor
  let k : ℕ := J (firstHit J hJtop n)
  have hnk : n ≤ k := by
    dsimp [k]
    exact le_J_firstHit hJtop n
  have hkD : k ≤ n + D := by
    dsimp [k]
    exact hnov
  have hdens :
      density E n ≤
        ((((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) * density E k) :=
    density_le_of_index_le_and_le_add hEmono hEnonneg hnk hkD
  have hknat : k + 1 ≤ n + D + 1 := by omega
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hfactor_k :
      (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) ≤
        (((n + D + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hknat) (le_of_lt hnpos)
  have hfactor_k' :
      (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) ≤ 1 + η :=
    hfactor_k.trans hnfactor
  have hdens_nonneg : 0 ≤ density E k := density_nonneg hEnonneg k
  have hfactor_nonneg :
      0 ≤ (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) := by
    positivity
  have hBnonneg : 0 ≤ B := le_of_lt hBpos
  have hmul :
      (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) * density E k ≤
        (1 + η) * B := by
    exact mul_le_mul hfactor_k' hnsub hdens_nonneg (by linarith)
  have hηmul : η * B = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt hBpos]
  have htarget : (1 + η) * B = C + ε := by
    calc
      (1 + η) * B = B + η * B := by ring
      _ = C + ε := by
        rw [hηmul]
        dsimp [B]
        ring
  calc
    density E n
        ≤ (((k + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ))) * density E k := hdens
    _ ≤ (1 + η) * B := hmul
    _ = C + ε := htarget

theorem LimsupLeAtTop_comp_iff_of_bounded_jumps
    {E : ℕ → ℝ} {J : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hEmono : Monotone E)
    (hEnonneg : ∀ n : ℕ, 0 ≤ E n)
    (hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop)
    (hJgap : ∃ D : ℕ, ∀ m : ℕ, J (m + 1) ≤ J m + D) :
    LimsupLeAtTop (fun m => density E (J m)) C ↔
      LimsupLeAtTop (density E) C := by
  constructor
  · exact LimsupLeAtTop.of_comp_bounded_jumps
      hC hEmono hEnonneg hJmono hJtop hJgap
  · intro hfull
    exact LimsupLeAtTop.comp_of_tendsto hfull hJtop

/-! ## Entropy applications -/

/-- Continued-fraction coefficient entropy. -/
noncomputable def cfEntropy (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    Real.log (((a (i + 1) + 1 : ℕ) : ℝ))

lemma cfEntropy_summand_nonneg (a : ℕ → ℕ) (i : ℕ) :
    0 ≤ Real.log (((a (i + 1) + 1 : ℕ) : ℝ)) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le (a (i + 1)))

lemma cfEntropy_nonneg (a : ℕ → ℕ) (n : ℕ) :
    0 ≤ cfEntropy a n := by
  unfold cfEntropy
  exact Finset.sum_nonneg fun i _hi => cfEntropy_summand_nonneg a i

lemma cfEntropy_mono (a : ℕ → ℕ) :
    Monotone (cfEntropy a) := by
  intro n m hnm
  unfold cfEntropy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro i hi
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) hnm))
    (by
      intro i _him _hin
      exact cfEntropy_summand_nonneg a i)

/-- Entropy of canonical safe block lengths. -/
noncomputable def blockEntropy (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    Real.log ((canonicalSafeBlockLength a j : ℕ) : ℝ)

lemma blockEntropy_summand_nonneg (a : ℕ → ℕ) (j : ℕ) :
    0 ≤ Real.log ((canonicalSafeBlockLength a j : ℕ) : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast one_le_canonicalSafeBlockLength a j

lemma blockEntropy_nonneg (a : ℕ → ℕ) (n : ℕ) :
    0 ≤ blockEntropy a n := by
  unfold blockEntropy
  exact Finset.sum_nonneg fun j _hj => blockEntropy_summand_nonneg a j

lemma blockEntropy_mono (a : ℕ → ℕ) :
    Monotone (blockEntropy a) := by
  intro n m hnm
  unfold blockEntropy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro j hj
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) hnm))
    (by
      intro j _hjm _hjn
      exact blockEntropy_summand_nonneg a j)

theorem cfEntropy_LimsupLeAtTop_comp_iff_of_depth
    {a : ℕ → ℕ} {J : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop)
    (hJgap : ∃ D : ℕ, ∀ m : ℕ, J (m + 1) ≤ J m + D) :
    LimsupLeAtTop (fun m => density (cfEntropy a) (J m)) C ↔
      LimsupLeAtTop (density (cfEntropy a)) C := by
  exact LimsupLeAtTop_comp_iff_of_bounded_jumps
    hC (cfEntropy_mono a) (cfEntropy_nonneg a) hJmono hJtop hJgap

theorem blockEntropy_LimsupLeAtTop_comp_iff_of_depth
    {a : ℕ → ℕ} {J : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hJmono : Monotone J)
    (hJtop : Tendsto J atTop atTop)
    (hJgap : ∃ D : ℕ, ∀ m : ℕ, J (m + 1) ≤ J m + D) :
    LimsupLeAtTop (fun m => density (blockEntropy a) (J m)) C ↔
      LimsupLeAtTop (density (blockEntropy a)) C := by
  exact LimsupLeAtTop_comp_iff_of_bounded_jumps
    hC (blockEntropy_mono a) (blockEntropy_nonneg a) hJmono hJtop hJgap

end

end IrrationalityAr
