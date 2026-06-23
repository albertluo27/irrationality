import IrrationalityAr.ContinuedFractions
import IrrationalityAr.AdditiveBlockBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! ## Merged from IrrationalityAr/Blocks/BlockCore.lean -/


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

/-! ## Merged from IrrationalityAr/Blocks/ContinuantBounds.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Continuant and block-denominator bounds

This module contains the generic recurrence, growth, and endpoint lemmas for
continued-fraction continuants and their principal/intermediate blocks.  It is
kept independent of the Euler-specific and parity/gap-monotonicity layers.
-/

lemma continuantNum_succ_eq (a : ℕ → ℕ) (n : ℕ) :
    continuantNum a (n + 1) =
      a (n + 1) * continuantNum a n + continuantNumPrev a n := by
  cases n <;> rfl

lemma continuantDen_succ_eq (a : ℕ → ℕ) (n : ℕ) :
    continuantDen a (n + 1) =
      a (n + 1) * continuantDen a n + continuantDenPrev a n := by
  cases n <;> simp [continuantDen, continuantDenPrev]

lemma continuantNumPrev_coprime (a : ℕ → ℕ) (n : ℕ) :
    Nat.Coprime (continuantNumPrev a n) (continuantNum a n) := by
  induction n with
  | zero =>
      simp [continuantNumPrev, continuantNum]
  | succ n ih =>
      rw [continuantNumPrev]
      rw [continuantNum_succ_eq]
      rw [Nat.coprime_mul_right_add_right]
      exact ih.symm

lemma continuantNumPrev_not_even_and_even (a : ℕ → ℕ) (n : ℕ) :
    ¬ (Even (continuantNumPrev a n) ∧ Even (continuantNum a n)) := by
  intro h
  have h2gcd : 2 ∣ Nat.gcd (continuantNumPrev a n) (continuantNum a n) :=
    Nat.dvd_gcd h.1.two_dvd h.2.two_dvd
  have hgcd : Nat.gcd (continuantNumPrev a n) (continuantNum a n) = 1 :=
    (continuantNumPrev_coprime a n).gcd_eq_one
  rw [hgcd] at h2gcd
  norm_num at h2gcd

lemma fib_le_continuantDen_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ n : ℕ, Nat.fib (n + 1) ≤ continuantDen a n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [continuantDen]
  | one =>
      simpa [continuantDen] using hpos 0
  | more n ih0 ih1 =>
      rw [continuantDen]
      rw [Nat.fib_add_two]
      have hmul :
          continuantDen a (n + 1) ≤
            a (n + 2) * continuantDen a (n + 1) := by
        exact Nat.le_mul_of_pos_left (continuantDen a (n + 1)) (hpos (n + 1))
      omega

lemma continuantDen_mono_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ n : ℕ, continuantDen a n ≤ continuantDen a (n + 1) := by
  intro n
  cases n with
  | zero =>
      simpa [continuantDen] using hpos 0
  | succ n =>
      rw [continuantDen]
      have hmul :
          continuantDen a (n + 1) ≤
            a (n + 2) * continuantDen a (n + 1) := by
        exact Nat.le_mul_of_pos_left (continuantDen a (n + 1)) (hpos (n + 1))
      exact hmul.trans (Nat.le_add_right _ _)

lemma two_mul_continuantDen_le_two_step_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (n : ℕ) :
    2 * continuantDen a n ≤ continuantDen a (n + 2) := by
  cases n with
  | zero =>
      rw [continuantDen]
      simp [continuantDen]
      exact Nat.mul_pos (hpos 1) (hpos 0)
  | succ n =>
      rw [continuantDen]
      have hmono : continuantDen a (n + 1) ≤ continuantDen a (n + 2) :=
        continuantDen_mono_of_partials_pos a hpos (n + 1)
      have hmul :
          continuantDen a (n + 1) ≤
            a (n + 3) * continuantDen a (n + 2) := by
        exact hmono.trans
          (Nat.le_mul_of_pos_left (continuantDen a (n + 2)) (hpos (n + 2)))
      have hmul' :
          continuantDen a (n + 1) ≤
            a (n + 1 + 2) * continuantDen a (n + 1 + 1) := by
        simpa [Nat.add_assoc] using hmul
      calc
        2 * continuantDen a (n + 1) =
            continuantDen a (n + 1) + continuantDen a (n + 1) := by
          omega
        _ ≤
            a (n + 1 + 2) * continuantDen a (n + 1 + 1) +
              continuantDen a (n + 1) :=
          Nat.add_le_add_right hmul' _

lemma continuantDen_mono_of_partials_pos_le
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {m n : ℕ} (hmn : m ≤ n) :
    continuantDen a m ≤ continuantDen a n := by
  induction hmn with
  | refl => exact le_rfl
  | step _ ih =>
      exact le_trans ih (continuantDen_mono_of_partials_pos a hpos _)

lemma succ_le_continuantDen_two_mul
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ k : ℕ, k + 1 ≤ continuantDen a (2 * k)
  | 0 => by
      simp [continuantDen]
  | k + 1 => by
      have ih := succ_le_continuantDen_two_mul hpos k
      have hdenpos : 0 < continuantDen a (2 * k + 1) := by
        have hmono := continuantDen_mono_of_partials_pos a hpos (2 * k)
        omega
      have hprod_pos :
          0 < a (2 * k + 2) * continuantDen a (2 * k + 1) :=
        Nat.mul_pos (hpos (2 * k + 1)) hdenpos
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, continuantDen]
      omega

lemma continuantDen_tendsto_atTop_of_partials_pos
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto (continuantDen a) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b, ?_⟩
  intro n hn
  have hmono : continuantDen a (2 * b) ≤ continuantDen a n :=
    continuantDen_mono_of_partials_pos_le a hpos hn
  have hlower : b + 1 ≤ continuantDen a (2 * b) :=
    succ_le_continuantDen_two_mul hpos b
  exact le_trans (Nat.le_succ b) (le_trans hlower hmono)

lemma exists_convergent_interval_for_large_q
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ q : ℕ in atTop,
      ∃ n : ℕ,
        continuantDen a n ≤ q ∧
          q < continuantDen a (n + 1) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro q hqge1
  have htend := continuantDen_tendsto_atTop_of_partials_pos (a := a) hpos
  have hbound := (tendsto_atTop_atTop.mp htend) (q + 1)
  rcases hbound with ⟨M, hM⟩
  have hex : ∃ m : ℕ, q < continuantDen a m := by
    refine ⟨M, ?_⟩
    have hle : q + 1 ≤ continuantDen a M := hM M le_rfl
    omega
  let m : ℕ := Nat.find hex
  have hm_spec : q < continuantDen a m := by
    dsimp [m]
    exact Nat.find_spec hex
  have hm_pos : 0 < m := by
    rw [Nat.find_pos]
    simp [continuantDen]
    omega
  refine ⟨m - 1, ?_, ?_⟩
  · have hnot : ¬ q < continuantDen a (m - 1) := by
      dsimp [m]
      exact Nat.find_min hex (Nat.pred_lt (Nat.ne_of_gt hm_pos))
    exact le_of_not_gt hnot
  · simpa [Nat.sub_one_add_one_eq_of_pos hm_pos] using hm_spec

lemma eventually_exists_convergent_interval_of_eventually
    {a : ℕ → ℕ} {P : ℕ → Prop}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∀ᶠ q : ℕ in atTop,
      ∃ n : ℕ,
        P n ∧
          continuantDen a n ≤ q ∧
            q < continuantDen a (n + 1) := by
  rcases eventually_atTop.1 hP with ⟨N, hN⟩
  filter_upwards
    [exists_convergent_interval_for_large_q hpos,
      eventually_ge_atTop (continuantDen a N)] with q hloc hqN
  rcases hloc with ⟨n, hnlo, hnhi⟩
  have hnN : N ≤ n := by
    by_contra hnot
    have hnlt : n < N := Nat.lt_of_not_ge hnot
    have hsucc : n + 1 ≤ N := by omega
    have hden_le : continuantDen a (n + 1) ≤ continuantDen a N :=
      continuantDen_mono_of_partials_pos_le a hpos hsucc
    omega
  exact ⟨n, hN n hnN, hnlo, hnhi⟩

lemma log_const_over_log_continuantDen_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (C : ℝ) :
    Tendsto
      (fun n : ℕ => C / Real.log (continuantDen a n : ℝ))
      atTop (𝓝 0) := by
  have hqR : Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hlog :
      Tendsto (fun n : ℕ => Real.log (continuantDen a n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hqR
  exact hlog.const_div_atTop C

lemma log_const_over_log_nat_tendsto_zero (C : ℝ) :
    Tendsto
      (fun N : ℕ => C / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hlog.const_div_atTop C

lemma log_const_over_log_continuantDen_succ_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (C : ℝ) :
    Tendsto
      (fun j : ℕ => C / Real.log (continuantDen a (j + 1) : ℝ))
      atTop (𝓝 0) := by
  exact (Filter.tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => C / Real.log (continuantDen a n : ℝ)) 1).2
    (log_const_over_log_continuantDen_tendsto_zero hpos C)

lemma continuantDenPrev_le_continuantDen_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    continuantDenPrev a n ≤ continuantDen a n := by
  cases n with
  | zero => simp [continuantDenPrev, continuantDen]
  | succ n =>
      simp [continuantDenPrev]
      exact continuantDen_mono_of_partials_pos a hpos n

lemma continuantDen_succ_mul_bounds
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    a (n + 1) * continuantDen a n ≤ continuantDen a (n + 1) ∧
      continuantDen a (n + 1) ≤ 2 * a (n + 1) * continuantDen a n := by
  constructor
  · rw [continuantDen_succ_eq]
    exact Nat.le_add_right _ _
  · rw [continuantDen_succ_eq]
    have hprev : continuantDenPrev a n ≤ continuantDen a n :=
      continuantDenPrev_le_continuantDen_of_partials_pos a hpos n
    have hcoef : a (n + 1) + 1 ≤ 2 * a (n + 1) := by
      have := hpos n
      omega
    calc
      a (n + 1) * continuantDen a n + continuantDenPrev a n
          ≤ a (n + 1) * continuantDen a n + continuantDen a n := by
            exact Nat.add_le_add_left hprev _
      _ = (a (n + 1) + 1) * continuantDen a n := by
            rw [Nat.add_mul, one_mul]
      _ ≤ 2 * a (n + 1) * continuantDen a n := by
            have hmul := Nat.mul_le_mul_right (continuantDen a n) hcoef
            simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

lemma one_le_continuantDen_of_partials_pos_global
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    1 ≤ continuantDen a n := by
  have hfib : Nat.fib (n + 1) ≤ continuantDen a n :=
    fib_le_continuantDen_of_partials_pos a hpos n
  have hfibpos : 0 < Nat.fib (n + 1) :=
    Nat.fib_pos.mpr (Nat.succ_pos n)
  exact (Nat.succ_le_of_lt hfibpos).trans hfib

lemma partialQuotient_le_continuantDen_succ
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    a (n + 1) ≤ continuantDen a (n + 1) := by
  have hqpos : 0 < continuantDen a n :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos n)
  have hle_mul :
      a (n + 1) ≤ a (n + 1) * continuantDen a n :=
    Nat.le_mul_of_pos_right (a (n + 1)) hqpos
  exact hle_mul.trans (continuantDen_succ_mul_bounds hpos n).1

lemma pow_two_half_le_continuantDen_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ n : ℕ, 2 ^ (n / 2) ≤ continuantDen a n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [continuantDen]
  | one =>
      simpa [continuantDen] using hpos 0
  | more n ih0 _ih1 =>
      have htwo := two_mul_continuantDen_le_two_step_of_partials_pos a hpos n
      have hdiv : (n + 2) / 2 = n / 2 + 1 := by
        omega
      rw [hdiv, pow_succ]
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_left 2 ih0).trans htwo

private lemma index_le_fib_add_two (j : ℕ) :
    j ≤ Nat.fib (j + 2) := by
  by_cases hj : j ≤ 2
  · interval_cases j <;> norm_num
  · have h5 : 5 ≤ j + 2 := by omega
    exact (by omega : j ≤ j + 2).trans (Nat.le_fib_self h5)

lemma index_le_continuantDen_succ_of_partials_pos
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    j ≤ continuantDen a (j + 1) := by
  have hjfib : j ≤ Nat.fib (j + 2) := index_le_fib_add_two j
  have hfib :
      Nat.fib (j + 2) ≤ continuantDen a (j + 1) := by
    simpa [Nat.add_assoc] using
      fib_le_continuantDen_of_partials_pos a hpos (j + 1)
  exact hjfib.trans hfib

lemma CFBlockDenominator_endpoint (a : ℕ → ℕ) (j : ℕ) :
    CFBlockDenominator a j (a (j + 1)) = continuantDen a (j + 1) := by
  cases j with
  | zero =>
      simp [CFBlockDenominator, continuantDen, continuantDenPrev]
  | succ j =>
      simp [CFBlockDenominator, continuantDen, continuantDenPrev, Nat.add_comm,
        show 1 + (j + 1) = j + 2 by omega]

lemma CFBlockNumerator_endpoint (a : ℕ → ℕ) (j : ℕ) :
    CFBlockNumerator a j (a (j + 1)) = continuantNum a (j + 1) := by
  cases j with
  | zero =>
      simp [CFBlockNumerator, continuantNum, continuantNumPrev, Nat.add_comm]
  | succ j =>
      simp [CFBlockNumerator, continuantNum, continuantNumPrev, Nat.add_comm,
        show 1 + (j + 1) = j + 2 by omega]

/-- Consecutive denominators inside the same continued-fraction block differ
by the current principal denominator `q_j`. -/
lemma CFBlockDenominator_succ (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockDenominator a j (t + 1) =
      CFBlockDenominator a j t + continuantDen a j := by
  unfold CFBlockDenominator
  ring

/-- The first denominator in the next block is `q_j + q_{j+1}`. -/
lemma CFBlockDenominator_next_block_first (a : ℕ → ℕ) (j : ℕ) :
    CFBlockDenominator a (j + 1) 1 =
      continuantDen a j + continuantDen a (j + 1) := by
  simp [CFBlockDenominator, continuantDenPrev]

/-- The gap from the endpoint of block `j` to the first denominator in block
`j + 1` is again `q_j`. -/
lemma CFBlockDenominator_boundary_succ (a : ℕ → ℕ) (j : ℕ) :
    CFBlockDenominator a (j + 1) 1 =
      CFBlockDenominator a j (a (j + 1)) + continuantDen a j := by
  rw [CFBlockDenominator_next_block_first, CFBlockDenominator_endpoint]
  rw [Nat.add_comm]

end IrrationalityAr

/-! ## Merged from IrrationalityAr/Blocks/Selected.lean -/


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

/-- The internal denominator step of the parity-selected block. -/
def canonicalOddBlockStep (a : ℕ → ℕ) (j : ℕ) : ℕ :=
  if Even (continuantNum a j) then
    continuantDen a j
  else
    2 * continuantDen a j

lemma canonicalOddBlockStep_pos
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    0 < canonicalOddBlockStep a j := by
  classical
  by_cases hcurr : Even (continuantNum a j)
  · have hq : 0 < continuantDen a j :=
      lt_of_lt_of_le Nat.zero_lt_one
        (one_le_continuantDen_of_partials_pos_global a hpos j)
    simpa [canonicalOddBlockStep, hcurr] using hq
  · have hq : 0 < continuantDen a j :=
      lt_of_lt_of_le Nat.zero_lt_one
        (one_le_continuantDen_of_partials_pos_global a hpos j)
    have htwo : 0 < 2 := by norm_num
    simpa [canonicalOddBlockStep, hcurr] using Nat.mul_pos htwo hq

lemma continuantDen_le_canonicalOddBlockStep
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    continuantDen a j ≤ canonicalOddBlockStep a j := by
  classical
  unfold canonicalOddBlockStep
  by_cases hcurr : Even (continuantNum a j)
  · simp [hcurr]
  · have hq : 0 < continuantDen a j :=
      lt_of_lt_of_le Nat.zero_lt_one
        (one_le_continuantDen_of_partials_pos_global a hpos j)
    simp [hcurr]
    omega

lemma canonicalOddBlockStep_eq_of_curr_even
    {a : ℕ → ℕ} {j : ℕ}
    (hcurr : Even (continuantNum a j)) :
    canonicalOddBlockStep a j = continuantDen a j := by
  simp [canonicalOddBlockStep, hcurr]

lemma canonicalOddBlockStep_eq_of_curr_odd
    {a : ℕ → ℕ} {j : ℕ}
    (hcurr : Odd (continuantNum a j)) :
    canonicalOddBlockStep a j = 2 * continuantDen a j := by
  have hnot : ¬ Even (continuantNum a j) :=
    Nat.not_even_iff_odd.mpr hcurr
  simp [canonicalOddBlockStep, hnot]

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

/-- If the current numerator is odd, the selected indices alternate, so after
discarding one endpoint correction the selected block has at most half the
available partial quotient. -/
lemma two_mul_canonicalBlockLength_sub_one_le_partialQuotient_of_curr_odd
    {a : ℕ → ℕ} {j : ℕ}
    (hcurrOdd : Odd (continuantNum a j)) :
    2 * (canonicalBlockLength a j - 1) ≤ a (j + 1) := by
  classical
  rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
  · have hblock := canonicalOddBlock_eq_odd_filter_of_prev_even_curr_odd
      (a := a) (j := j) hprevEven hcurrOdd
    have hlen : canonicalBlockLength a j = (a (j + 1) + 1) / 2 := by
      simp [canonicalBlockLength, hblock, card_odd_Icc]
    rw [hlen]
    omega
  · have hblock := canonicalOddBlock_eq_even_filter_of_prev_odd_curr_odd
      (a := a) (j := j) hprevOdd hcurrOdd
    have hlen : canonicalBlockLength a j = a (j + 1) / 2 := by
      simp [canonicalBlockLength, hblock, card_even_Icc]
    rw [hlen]
    omega

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

/-- The shifted parity-selected denominator block is exactly a finite
arithmetic progression with the canonical local step. -/
theorem exists_start_canonicalOddDenominatorBlock_eq_block
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    ∃ s : ℕ,
      canonicalOddDenominatorBlock a j =
        finiteArithmeticBlock s (canonicalOddBlockStep a j)
          (canonicalBlockLength a j) := by
  classical
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
    have hsub :
        finiteArithmeticBlock (CFBlockDenominator a j 1 - 1)
            (continuantDen a j) (canonicalBlockLength a j) ⊆
          canonicalOddDenominatorBlock a j := by
      intro x hx
      rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
      rw [canonicalOddDenominatorBlock, Finset.mem_image]
      refine ⟨r + 1, ?_, ?_⟩
      · rw [hblock, Finset.mem_Icc]
        simp [canonicalBlockLength, hblock] at hr
        omega
      · unfold CFBlockDenominator
        exact (denominator_sub_one_one_step
          (continuantDenPrev a j) (continuantDen a j) r hqpos).symm
    have hcard :
        (canonicalOddDenominatorBlock a j).card ≤
          (finiteArithmeticBlock (CFBlockDenominator a j 1 - 1)
            (continuantDen a j) (canonicalBlockLength a j)).card := by
      rw [canonicalOddDenominatorBlock_card a hpos j,
        finiteArithmeticBlock_card (s := CFBlockDenominator a j 1 - 1)
          (d := continuantDen a j) (m := canonicalBlockLength a j) hqpos]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    refine ⟨CFBlockDenominator a j 1 - 1, ?_⟩
    simpa [canonicalOddBlockStep, hcurrEven] using heq.symm
  · rcases Nat.even_or_odd (continuantNumPrev a j) with hprevEven | hprevOdd
    · have hblock := canonicalOddBlock_eq_odd_filter_of_prev_even_curr_odd
        (a := a) (j := j) hprevEven hcurrOdd
      have hsub :
          finiteArithmeticBlock (CFBlockDenominator a j 1 - 1)
              (2 * continuantDen a j) (canonicalBlockLength a j) ⊆
            canonicalOddDenominatorBlock a j := by
        intro x hx
        rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
        rw [canonicalOddDenominatorBlock, Finset.mem_image]
        refine ⟨2 * r + 1, ?_, ?_⟩
        · rw [hblock, Finset.mem_filter, Finset.mem_Icc]
          have hlen : canonicalBlockLength a j = (a (j + 1) + 1) / 2 := by
            simp [canonicalBlockLength, hblock, card_odd_Icc]
          rw [hlen] at hr
          exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩
        · unfold CFBlockDenominator
          exact (denominator_sub_one_odd_step
            (continuantDenPrev a j) (continuantDen a j) r hqpos).symm
      have hstep : 0 < 2 * continuantDen a j :=
        Nat.mul_pos (by norm_num) hqpos
      have hcard :
          (canonicalOddDenominatorBlock a j).card ≤
            (finiteArithmeticBlock (CFBlockDenominator a j 1 - 1)
              (2 * continuantDen a j) (canonicalBlockLength a j)).card := by
        rw [canonicalOddDenominatorBlock_card a hpos j,
          finiteArithmeticBlock_card (s := CFBlockDenominator a j 1 - 1)
            (d := 2 * continuantDen a j)
            (m := canonicalBlockLength a j) hstep]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      refine ⟨CFBlockDenominator a j 1 - 1, ?_⟩
      have hnot : ¬ Even (continuantNum a j) :=
        Nat.not_even_iff_odd.mpr hcurrOdd
      simpa [canonicalOddBlockStep, hnot] using heq.symm
    · have hblock := canonicalOddBlock_eq_even_filter_of_prev_odd_curr_odd
        (a := a) (j := j) hprevOdd hcurrOdd
      have hsub :
          finiteArithmeticBlock (CFBlockDenominator a j 2 - 1)
              (2 * continuantDen a j) (canonicalBlockLength a j) ⊆
            canonicalOddDenominatorBlock a j := by
        intro x hx
        rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
        rw [canonicalOddDenominatorBlock, Finset.mem_image]
        refine ⟨2 * (r + 1), ?_, ?_⟩
        · rw [hblock, Finset.mem_filter, Finset.mem_Icc]
          have hlen : canonicalBlockLength a j = a (j + 1) / 2 := by
            simp [canonicalBlockLength, hblock, card_even_Icc]
          rw [hlen] at hr
          exact ⟨⟨by omega, by omega⟩, ⟨r + 1, by omega⟩⟩
        · unfold CFBlockDenominator
          exact (denominator_sub_one_even_step
            (continuantDenPrev a j) (continuantDen a j) r hqpos).symm
      have hstep : 0 < 2 * continuantDen a j :=
        Nat.mul_pos (by norm_num) hqpos
      have hcard :
          (canonicalOddDenominatorBlock a j).card ≤
            (finiteArithmeticBlock (CFBlockDenominator a j 2 - 1)
              (2 * continuantDen a j) (canonicalBlockLength a j)).card := by
        rw [canonicalOddDenominatorBlock_card a hpos j,
          finiteArithmeticBlock_card (s := CFBlockDenominator a j 2 - 1)
            (d := 2 * continuantDen a j)
            (m := canonicalBlockLength a j) hstep]
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      refine ⟨CFBlockDenominator a j 2 - 1, ?_⟩
      have hnot : ¬ Even (continuantNum a j) :=
        Nat.not_even_iff_odd.mpr hcurrOdd
      simpa [canonicalOddBlockStep, hnot] using heq.symm

end IrrationalityAr

/-! ## Merged from IrrationalityAr/Blocks/Visible.lean -/


open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Visible canonical denominator sets and exponents

This module defines the finite denominator truncations and exponent functionals
used by the canonical block-growth layer.  The asymptotic estimates proving
their values remain in `CanonicalBlockGrowth`.
-/

/-- The visible part of a canonical denominator block, using the true
denominator cap `N`.  Since `canonicalOddDenominatorBlock` stores `Q - 1`, the
filter is `q + 1 ≤ N`. -/
def visibleCanonicalOddDenominatorBlock
    (a : ℕ → ℕ) (N j : ℕ) : Finset ℕ :=
  (canonicalOddDenominatorBlock a j).filter fun q => q + 1 ≤ N

/-- The largest visible local canonical block below denominator cap `N`, with a
logarithmic index cap. -/
def visibleCanonicalBlockMax
    (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  max 1 <| (Finset.range (2 * Nat.log 2 N + 3)).sup fun j =>
    (visibleCanonicalOddDenominatorBlock a N j).card

/-- Visible canonical block exponent, using the logarithmic visible block
maximum rather than the older endpoint-counting `canonicalBlockGrowth`. -/
noncomputable def visibleCanonicalBlockExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ))
    atTop

/-- All visible canonical parity-selected denominator elements `Q - 1` below
the true denominator cap `N`. -/
def visibleCanonicalDenominatorSet
    (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * Nat.log 2 N + 3)).biUnion fun j =>
    visibleCanonicalOddDenominatorBlock a N j

/-- The positive part of the visible canonical denominator set.

The full shifted denominator set can contain the harmless initial value
`0 = 1 - 1`; this version is the one that matches the floor-sum set `A`. -/
def positiveVisibleCanonicalDenominatorSet
    (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (visibleCanonicalDenominatorSet a N).erase 0

noncomputable def visiblePopularDifferenceExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisiblePopularDifferenceExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (popularDifferenceUpTo
          (positiveVisibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def visibleAdditiveEnergyExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisibleAdditiveEnergyExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (additiveEnergy (positiveVisibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def properHilbertCubeDimension (S : Finset ℕ) : ℕ :=
  by
    classical
    exact (Finset.range (S.card + 1)).sup fun h : ℕ =>
      if HasProperHilbertCube S h then h else 0

noncomputable def visibleHilbertCubeExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension
        (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisibleHilbertCubeExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension
        (positiveVisibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def popularDifferenceExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (popularDifferenceUpTo (S N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def additiveEnergyExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (additiveEnergy (S N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def hilbertCubeExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension (S N) : ℝ) /
        Real.log (N : ℝ))
    atTop

theorem popularDifferenceExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    popularDifferenceExponentOf S =
      popularDifferenceExponentOf T := by
  unfold popularDifferenceExponentOf
  congr
  ext N
  rw [hST N]

theorem additiveEnergyExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    additiveEnergyExponentOf S =
      additiveEnergyExponentOf T := by
  unfold additiveEnergyExponentOf
  congr
  ext N
  rw [hST N]

theorem hilbertCubeExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    hilbertCubeExponentOf S =
      hilbertCubeExponentOf T := by
  unfold hilbertCubeExponentOf
  congr
  ext N
  rw [hST N]

end IrrationalityAr

