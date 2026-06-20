import IrrationalityAr.ContinuedFractions

namespace IrrationalityAr

/-!
# Basic canonical continued-fraction block definitions

This module contains the coefficient-side block objects used by the
block-growth, gap-monotonicity, and Euler-specialization layers.
-/

/-- Numerator in the `j`-th principal/intermediate continued-fraction block:
`P_{j,t} = p_{j-1} + t p_j`. -/
def CFBlockNumerator (a : ℕ → ℕ) (j t : ℕ) : ℕ :=
  continuantNumPrev a j + t * continuantNum a j

/-- Denominator in the `j`-th principal/intermediate continued-fraction block:
`Q_{j,t} = q_{j-1} + t q_j`. -/
def CFBlockDenominator (a : ℕ → ℕ) (j t : ℕ) : ℕ :=
  continuantDenPrev a j + t * continuantDen a j

/-- The `A`-set described by odd-numerator principal/intermediate
continued-fraction block denominators attached to a chosen coefficient
sequence. -/
def oddBlockASet (a : ℕ → ℕ) : Set ℕ :=
  {n : ℕ |
    ∃ j t : ℕ,
      1 ≤ t ∧ t ≤ a (j + 1) ∧
        Odd (CFBlockNumerator a j t) ∧
        2 ≤ CFBlockDenominator a j t ∧
        n = CFBlockDenominator a j t - 1}

/-- The same selected continued-fraction block denominators as
`oddBlockASet`, before shifting each denominator down by one. -/
def oddBlockDenominatorSet (a : ℕ → ℕ) : Set ℕ :=
  {Q : ℕ |
    ∃ j t : ℕ,
      1 ≤ t ∧ t ≤ a (j + 1) ∧
        Odd (CFBlockNumerator a j t) ∧
        2 ≤ CFBlockDenominator a j t ∧
        Q = CFBlockDenominator a j t}

theorem mem_oddBlockASet_iff_succ_mem_oddBlockDenominatorSet
    (a : ℕ → ℕ) (n : ℕ) :
    n ∈ oddBlockASet a ↔ n + 1 ∈ oddBlockDenominatorSet a := by
  constructor
  · rintro ⟨j, t, ht1, htle, hodd, hQ2, hn⟩
    refine ⟨j, t, ht1, htle, hodd, hQ2, ?_⟩
    omega
  · rintro ⟨j, t, ht1, htle, hodd, hQ2, hn⟩
    refine ⟨j, t, ht1, htle, hodd, hQ2, ?_⟩
    omega

lemma zero_not_mem_oddBlockASet (a : ℕ → ℕ) :
    0 ∉ oddBlockASet a := by
  rintro ⟨j, t, _ht1, _htle, _hodd, hQ2, h0⟩
  omega

/-- A set of natural numbers has nondecreasing gaps between consecutive
members. This avoids choosing an explicit increasing enumeration
`s = {a₁ < a₂ < ...}`. -/
def SetConsecutiveGapsNondecreasing (s : Set ℕ) : Prop :=
  ∀ a b c : ℕ,
    a ∈ s → b ∈ s → c ∈ s →
      a < b → b < c →
        (∀ x : ℕ, x ∈ s → a < x → x < b → False) →
          (∀ x : ℕ, x ∈ s → b < x → x < c → False) →
            b - a ≤ c - b

/-- Shifting every element of a set down by one preserves consecutive gaps.

The hypothesis `n ∈ S ↔ n + 1 ∈ D` packages the shift without choosing an
enumeration of either set. -/
lemma SetConsecutiveGapsNondecreasing_shift_sub_one
    {D S : Set ℕ}
    (hS : ∀ n : ℕ, n ∈ S ↔ n + 1 ∈ D)
    (hD : SetConsecutiveGapsNondecreasing D) :
    SetConsecutiveGapsNondecreasing S := by
  intro a b c ha hb hc hab hbc hnone_ab hnone_bc
  have hDa : a + 1 ∈ D := (hS a).1 ha
  have hDb : b + 1 ∈ D := (hS b).1 hb
  have hDc : c + 1 ∈ D := (hS c).1 hc
  have hnoneD_ab :
      ∀ x : ℕ, x ∈ D → a + 1 < x → x < b + 1 → False := by
    intro x hx hax hxb
    have hxS : x - 1 ∈ S := by
      rw [hS]
      have hxsucc : x - 1 + 1 = x := by omega
      simpa [hxsucc] using hx
    exact hnone_ab (x - 1) hxS (by omega) (by omega)
  have hnoneD_bc :
      ∀ x : ℕ, x ∈ D → b + 1 < x → x < c + 1 → False := by
    intro x hx hbx hxc
    have hxS : x - 1 ∈ S := by
      rw [hS]
      have hxsucc : x - 1 + 1 = x := by omega
      simpa [hxsucc] using hx
    exact hnone_bc (x - 1) hxS (by omega) (by omega)
  have hgap :=
    hD (a + 1) (b + 1) (c + 1)
      hDa hDb hDc (by omega) (by omega) hnoneD_ab hnoneD_bc
  omega

/-- Gap-monotonicity target for `A_r`. -/
def AGapsNondecreasing (r : ℝ) : Prop :=
  SetConsecutiveGapsNondecreasing (A r)

/-- Gap-monotonicity for the coefficient-side shifted denominator set. -/
def OddBlockASetGapsNondecreasing (a : ℕ → ℕ) : Prop :=
  SetConsecutiveGapsNondecreasing (oddBlockASet a)

/-- Gap-monotonicity for the selected continued-fraction denominators before
the final `-1` shift. -/
def OddBlockDenominatorSetGapsNondecreasing (a : ℕ → ℕ) : Prop :=
  SetConsecutiveGapsNondecreasing (oddBlockDenominatorSet a)

theorem oddBlockASet_gaps_nondecreasing_of_denominatorSet
    {a : ℕ → ℕ}
    (hD : OddBlockDenominatorSetGapsNondecreasing a) :
    OddBlockASetGapsNondecreasing a := by
  unfold OddBlockASetGapsNondecreasing
    OddBlockDenominatorSetGapsNondecreasing at *
  exact SetConsecutiveGapsNondecreasing_shift_sub_one
    (D := oddBlockDenominatorSet a)
    (S := oddBlockASet a)
    (mem_oddBlockASet_iff_succ_mem_oddBlockDenominatorSet a)
    hD

/-- A valid parity-selected index in the canonical continued-fraction
principal/intermediate path. -/
def CanonicalOddCFIndex (a : ℕ → ℕ) (j t : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ a (j + 1) ∧ Odd (CFBlockNumerator a j t)

/-- Lexicographic order on block indices `(j,t)`, matching the natural order
of the unfiltered denominator path when partial quotients are positive. -/
def CFBlockIndexLt (j t k s : ℕ) : Prop :=
  j < k ∨ (j = k ∧ t < s)

/-- Consecutive parity-selected indices in the canonical denominator path. -/
def ConsecutiveCanonicalOddCFIndices
    (a : ℕ → ℕ) (j t k s : ℕ) : Prop :=
  CanonicalOddCFIndex a j t ∧
    CanonicalOddCFIndex a k s ∧
      CFBlockIndexLt j t k s ∧
        ∀ l u : ℕ,
          CanonicalOddCFIndex a l u →
            CFBlockIndexLt j t l u →
              CFBlockIndexLt l u k s →
                False

/-- Short alias for consecutive selected continued-fraction path indices. -/
abbrev ConsecutiveSelected :=
  ConsecutiveCanonicalOddCFIndices

/-- `s` is the first parity-selected index in block `k`. -/
def IsFirstSelectedInBlock (a : ℕ → ℕ) (k s : ℕ) : Prop :=
  CanonicalOddCFIndex a k s ∧
    ∀ u : ℕ, CanonicalOddCFIndex a k u → u < s → False

/-- Gap between two canonical continued-fraction block denominators. -/
def CanonicalOddCFGap (a : ℕ → ℕ) (j t k s : ℕ) : ℕ :=
  CFBlockDenominator a k s - CFBlockDenominator a j t

/-- The finite combinatorial core of the pasted proof: consecutive gaps in
the parity-selected denominator path are nondecreasing. -/
def CanonicalOddDenominatorGapsNondecreasing (a : ℕ → ℕ) : Prop :=
  ∀ j t k s l u : ℕ,
    ConsecutiveCanonicalOddCFIndices a j t k s →
      ConsecutiveCanonicalOddCFIndices a k s l u →
        CanonicalOddCFGap a j t k s ≤ CanonicalOddCFGap a k s l u

/-- The parity-selected part of the `j`-th denominator block. -/
def canonicalOddBlock (a : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (a (j + 1))).filter fun t : ℕ =>
    Odd (CFBlockNumerator a j t)

/-- Number of parity-selected denominators in the `j`-th block. -/
def canonicalBlockLength (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  (canonicalOddBlock a j).card

/-- Safe block length `M_j = max(1, L_j)`.

This is the length scale naturally compatible with `canonicalBlockGrowth`,
which is also capped below by `1`. -/
def canonicalSafeBlockLength (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  max 1 (canonicalBlockLength a j)

/-- Finite maximum of the safe block lengths over the prefix `j < J`. -/
def finiteSafeBlockMax (a : ℕ → ℕ) (J : ℕ) : ℕ :=
  max 1 ((Finset.range J).sup fun j : ℕ => canonicalSafeBlockLength a j)

end IrrationalityAr
