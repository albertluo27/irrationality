import IrrationalityAr.ContinuedFractions
import IrrationalityAr.AdditiveBlockBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

namespace IrrationalityAr

/-!
# Canonical block growth

This file isolates the formal content of the writeup
`The Canonical Block Growth of A_r and the Irrationality Measure of e`.

The local continued-fraction block definitions are formalized directly:

* the numerator and denominator in a principal/intermediate block;
* the parity-selected block;
* the block length and capped block-growth sequence;
* the two exponent parameters used in the asymptotic argument.

The hard asymptotic steps are deliberately exposed as named interfaces rather
than asserted as axioms:

* `HasCanonicalBlockGrowthFormula`;
* `HasIrrationalityMeasureFromCF`;
* `HasEulerPartialQuotients`.

This keeps the compiled project proof-hole-free while giving us exact theorem
statements to attack next.
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

/-- A set of natural numbers has nondecreasing gaps between consecutive
members.  This avoids choosing an explicit increasing enumeration
`s = {a₁ < a₂ < ...}`. -/
def SetConsecutiveGapsNondecreasing (s : Set ℕ) : Prop :=
  ∀ a b c : ℕ,
    a ∈ s → b ∈ s → c ∈ s →
      a < b → b < c →
        (∀ x : ℕ, x ∈ s → a < x → x < b → False) →
          (∀ x : ℕ, x ∈ s → b < x → x < c → False) →
            b - a ≤ c - b

/-- Gap-monotonicity target for `A_r`. -/
def AGapsNondecreasing (r : ℝ) : Prop :=
  SetConsecutiveGapsNondecreasing (A r)

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

/-- A finite, capped version of the canonical block-growth function.

The cap `j < N + 1` keeps the maximum finite without having to prove
monotonicity of the denominators at definition time. Under the standard
continued-fraction positivity assumptions this agrees with the intended
maximum over all `j` satisfying `q_{j+1} ≤ N`. -/
def canonicalBlockGrowth (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  max 1 <| (Finset.range (N + 1)).sup fun j : ℕ =>
    if continuantDen a (j + 1) ≤ N then canonicalBlockLength a j else 0

/-- Upper canonical block-growth exponent. -/
noncomputable def canonicalBlockExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ))
    atTop

/-- The continued-fraction partial-quotient growth parameter
`tau = limsup log a_{j+1} / log q_j`. -/
noncomputable def partialQuotientGrowthTau (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun j : ℕ =>
      Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a j : ℝ))
    atTop

/-- The base partial-quotient logarithmic growth ratio
`x_j = log(a_{j+1}) / log(q_j)`. -/
noncomputable def pqLogRatio (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a j : ℝ)

/-- The base partial-quotient logarithmic growth ratios are frequently
arbitrarily large. This is the real-valued substitute for the extended-real
case `tau = ∞`. -/
def partialQuotientGrowthUnbounded (a : ℕ → ℕ) : Prop :=
  ∀ C : ℝ, ∃ᶠ j : ℕ in atTop, C ≤ pqLogRatio a j

/-- The endpoint partial-quotient logarithmic growth ratio
`y_j = log(a_{j+1}) / log(q_{j+1})`. -/
noncomputable def pqEndpointLogRatio (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a (j + 1) : ℝ)

/-- Endpoint partial-quotient exponent
`limsup_j log(a_{j+1}) / log(q_{j+1})`. -/
noncomputable def partialQuotientEndpointExponent (a : ℕ → ℕ) : ℝ :=
  limsup (pqEndpointLogRatio a) atTop

/-- The denominator logarithmic ratio `log(q_{j+1}) / log(q_j)`. -/
noncomputable def continuantDenLogRatio (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.log (continuantDen a (j + 1) : ℝ) /
    Real.log (continuantDen a j : ℝ)

/-- The transform `x ↦ x/(1+x)` applied to the base partial-quotient ratio. -/
noncomputable def pqLogRatioTransform (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  pqLogRatio a j / (1 + pqLogRatio a j)

/-- A globally monotone version of `x ↦ x/(1+x)`, clipped to the nonnegative
half-line. It agrees with `x/(1+x)` on the eventual range of `pqLogRatio`. -/
noncomputable def nonnegativeRatioTransform (x : ℝ) : ℝ :=
  max 0 x / (1 + max 0 x)

/-- Denominator-ratio exponent
`rho = limsup log q_{n+1} / log q_n`.

The classical continued-fraction irrationality-measure formula first gives
`mu(alpha) = 1 + rho`, then rewrites `rho = 1 + tau`. -/
noncomputable def denominatorRatioExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun n : ℕ =>
      Real.log (continuantDen a (n + 1) : ℝ) /
        Real.log (continuantDen a n : ℝ))
    atTop

/-- The asymptotic block-growth bridge asserted by the writeup:
`lambda = tau / (1 + tau)`. -/
def HasCanonicalBlockGrowthFormula (a : ℕ → ℕ) : Prop :=
  canonicalBlockExponent a =
    partialQuotientGrowthTau a / (1 + partialQuotientGrowthTau a)

/-- The standard continued-fraction formula for irrationality measure:
`mu = 2 + tau`. -/
def HasIrrationalityMeasureFromCF (a : ℕ → ℕ) (μ : ℝ) : Prop :=
  μ = 2 + partialQuotientGrowthTau a

/-- Literal real-number irrationality-measure predicate.

The first clause says every exponent below `μ` occurs infinitely often among
rational approximations to `α`; the second says every exponent above `μ`
eventually fails for all numerators at denominator `q`. -/
def HasIrrationalityMeasure (α μ : ℝ) : Prop :=
  (∀ ν : ℝ,
      ν < μ →
        ∃ᶠ q : ℕ in atTop,
          ∃ p : ℤ,
            0 < q ∧
              |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)) ∧
    (∀ ν : ℝ,
      μ < ν →
        ∀ᶠ q : ℕ in atTop,
          ∀ p : ℤ,
            0 < q →
              ¬ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν))

lemma eventually_nat_cast_pos_atTop :
    ∀ᶠ q : ℕ in atTop, (0 : ℝ) < q := by
  exact (eventually_ge_atTop 1).mono (fun q hq => by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))

lemma eventually_nat_cast_one_lt_atTop :
    ∀ᶠ q : ℕ in atTop, (1 : ℝ) < q := by
  exact (eventually_ge_atTop 2).mono (fun q hq => by
    exact_mod_cast hq)

lemma eventually_two_lt_nat_rpow_atTop {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (2 : ℝ) < (q : ℝ) ^ δ := by
  exact ((tendsto_rpow_atTop hδ).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 2

lemma eventually_inv_two_power_gt_power_neg
    {ε ν : ℝ}
    (h : 2 + ε < ν) :
    ∀ᶠ q : ℕ in atTop,
      1 / (2 * (q : ℝ) ^ (2 + ε)) >
        (q : ℝ) ^ (-ν) := by
  let δ : ℝ := ν - (2 + ε)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  filter_upwards
    [eventually_nat_cast_one_lt_atTop,
      eventually_two_lt_nat_rpow_atTop hδ] with q hqgt1 hpow
  let x : ℝ := q
  have hx : 0 < x := by
    dsimp [x]
    linarith
  have hνeq : ν = (2 + ε) + δ := by
    dsimp [δ]
    ring
  have hApos : 0 < x ^ (2 + ε) := Real.rpow_pos_of_pos hx _
  have hdenlt : 2 * x ^ (2 + ε) < x ^ (2 + ε) * x ^ δ := by
    nlinarith [mul_lt_mul_of_pos_left hpow hApos]
  have hinv :
      1 / (x ^ (2 + ε) * x ^ δ) <
        1 / (2 * x ^ (2 + ε)) := by
    exact one_div_lt_one_div_of_lt
      (mul_pos (by norm_num) hApos) hdenlt
  have hrewrite : x ^ (-ν) = 1 / (x ^ (2 + ε) * x ^ δ) := by
    rw [hνeq, neg_add, Real.rpow_add hx]
    rw [Real.rpow_neg hx.le, Real.rpow_neg hx.le]
    field_simp [Real.rpow_pos_of_pos hx (2 + ε),
      Real.rpow_pos_of_pos hx δ]
  have hgoal : x ^ (-ν) < 1 / (2 * x ^ (2 + ε)) := by
    simpa [hrewrite] using hinv
  simpa [x] using hgoal

theorem hasIrrationalityMeasure_congr_measure
    {α μ ν : ℝ}
    (h : μ = ν)
    (hm : HasIrrationalityMeasure α μ) :
    HasIrrationalityMeasure α ν := by
  subst h
  exact hm

theorem irrationalityMeasure_of_IsSimpleCFExpansion_of_denominatorRatio
    (hmain :
      ∀ {α : ℝ} {a : ℕ → ℕ},
        IsSimpleCFExpansion α a →
          HasIrrationalityMeasure α (1 + denominatorRatioExponent a))
    (hconvert :
      ∀ {a : ℕ → ℕ},
        (∀ n : ℕ, 0 < a (n + 1)) →
          1 + denominatorRatioExponent a =
            2 + partialQuotientGrowthTau a)
    {α : ℝ} {a : ℕ → ℕ} {μ : ℝ}
    (hcf : IsSimpleCFExpansion α a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    HasIrrationalityMeasure α μ := by
  rcases hcf with ⟨hpos, hconv, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, hconv, htails⟩
  have hmetric :
      HasIrrationalityMeasure α (1 + denominatorRatioExponent a) :=
    hmain hcf'
  have hμeq :
      μ = 1 + denominatorRatioExponent a := by
    have hμ' : μ = 2 + partialQuotientGrowthTau a := by
      simpa [HasIrrationalityMeasureFromCF] using hμ
    exact hμ'.trans (hconvert hpos).symm
  exact hasIrrationalityMeasure_congr_measure hμeq.symm hmetric

/-!
The next substantial bridge is the standard continued-fraction theorem:

```
theorem irrationalityMeasure_of_IsSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ} {μ : ℝ}
    (hcf : IsSimpleCFExpansion α a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    HasIrrationalityMeasure α μ
```

It requires the classical upper/lower irrationality-measure estimates from
continued fractions and is intentionally not asserted here without proof.

After introducing `denominatorRatioExponent`, this bridge is reduced to two
precise standard statements:

```
theorem irrationalityMeasure_eq_one_add_denominatorRatioExponent
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) :
    HasIrrationalityMeasure α (1 + denominatorRatioExponent a)
```

and

```
theorem one_add_denominatorRatioExponent_eq_two_add_tau
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    1 + denominatorRatioExponent a =
      2 + partialQuotientGrowthTau a
```
-/

/-- Euler's continued-fraction coefficient pattern:
`e = [2; 1,2,1, 1,4,1, 1,6,1, ...]`. -/
def HasEulerPartialQuotients (a : ℕ → ℕ) : Prop :=
  a 0 = 2 ∧ a 1 = 1 ∧
    ∀ m : ℕ,
      a (3 * m + 2) = 2 * (m + 1) ∧
      a (3 * m + 3) = 1 ∧
      a (3 * m + 4) = 1

theorem eulerPartialQuotients_linear_bound
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    ∀ n : ℕ, a n ≤ 2 * (n + 1) := by
  intro n
  rcases he with ⟨h0, h1, htail⟩
  rcases n with _ | n
  · simp [h0]
  rcases n with _ | n
  · simp [h1]
  let m : ℕ := n / 3
  let r : ℕ := n % 3
  have hn : n = 3 * m + r := by
    dsimp [m, r]
    omega
  have hrlt : r < 3 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr with hr0 | hr1 | hr2
  · have hidx : n + 2 = 3 * m + 2 := by omega
    have ha : a (n + 2) = 2 * (m + 1) := by
      rw [hidx]
      exact (htail m).1
    rw [ha]
    omega
  · have hidx : n + 2 = 3 * m + 3 := by omega
    have ha : a (n + 2) = 1 := by
      rw [hidx]
      exact (htail m).2.1
    rw [ha]
    omega
  · have hidx : n + 2 = 3 * m + 4 := by omega
    have ha : a (n + 2) = 1 := by
      rw [hidx]
      exact (htail m).2.2
    rw [ha]
    omega

theorem eulerPartialQuotients_pos_succ
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    ∀ n : ℕ, 0 < a (n + 1) := by
  intro n
  rcases he with ⟨_h0, h1, htail⟩
  rcases n with _ | n
  · simp [h1]
  let m : ℕ := n / 3
  let r : ℕ := n % 3
  have hn : n = 3 * m + r := by
    dsimp [m, r]
    omega
  have hrlt : r < 3 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr with hr0 | hr1 | hr2
  · have hidx : n + 2 = 3 * m + 2 := by omega
    have ha : a (n + 2) = 2 * (m + 1) := by
      rw [hidx]
      exact (htail m).1
    rw [ha]
    omega
  · have hidx : n + 2 = 3 * m + 3 := by omega
    have ha : a (n + 2) = 1 := by
      rw [hidx]
      exact (htail m).2.1
    rw [ha]
    norm_num
  · have hidx : n + 2 = 3 * m + 4 := by omega
    have ha : a (n + 2) = 1 := by
      rw [hidx]
      exact (htail m).2.2
    rw [ha]
    norm_num

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

lemma fib_le_continuantDen_of_eulerPartialQuotients
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    ∀ n : ℕ, Nat.fib (n + 1) ≤ continuantDen a n :=
  fib_le_continuantDen_of_partials_pos a (eulerPartialQuotients_pos_succ he)

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

theorem hasBlockParityLowerBound (a : ℕ → ℕ) : HasBlockParityLowerBound a := by
  intro j
  unfold canonicalBlockLength canonicalOddBlock CFBlockNumerator
  exact count_odd_affine_nat_lower_bound
    (continuantNumPrev a j) (continuantNum a j) (a (j + 1))
    (continuantNumPrev_not_even_and_even a j)

lemma canonicalBlockLength_lower_bound (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ canonicalBlockLength a j :=
  hasBlockParityLowerBound a j

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

/-- Consecutive numerators inside the same continued-fraction block differ by
the current principal numerator `p_j`. -/
lemma CFBlockNumerator_succ (a : ℕ → ℕ) (j t : ℕ) :
    CFBlockNumerator a j (t + 1) =
      CFBlockNumerator a j t + continuantNum a j := by
  unfold CFBlockNumerator
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

lemma canonicalOddCFIndex_iff_mem_canonicalOddBlock {a : ℕ → ℕ} {j t : ℕ} :
    CanonicalOddCFIndex a j t ↔ t ∈ canonicalOddBlock a j := by
  rw [mem_canonicalOddBlock_iff]
  rfl

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

noncomputable def visiblePopularDifferenceExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def visibleAdditiveEnergyExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
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

noncomputable def visibleCanonicalLocalRatio
    (a : ℕ → ℕ) (N j : ℕ) : ℝ :=
  Real.log ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) /
    Real.log (N : ℝ)

lemma one_le_visibleCanonicalBlockMax (a : ℕ → ℕ) (N : ℕ) :
    1 ≤ visibleCanonicalBlockMax a N := by
  unfold visibleCanonicalBlockMax
  exact le_max_left _ _

lemma visibleCanonicalOddDenominatorBlock_card_le_safeBlockLength
    {a : ℕ → ℕ} (N j : ℕ) :
    (visibleCanonicalOddDenominatorBlock a N j).card
      ≤ canonicalSafeBlockLength a j := by
  calc
    (visibleCanonicalOddDenominatorBlock a N j).card
        ≤ (canonicalOddDenominatorBlock a j).card := by
          unfold visibleCanonicalOddDenominatorBlock
          exact Finset.card_filter_le _ _
    _ ≤ canonicalBlockLength a j := by
          unfold canonicalOddDenominatorBlock canonicalBlockLength
          exact Finset.card_image_le
    _ ≤ canonicalSafeBlockLength a j := by
          unfold canonicalSafeBlockLength
          exact le_max_right _ _

lemma visibleCanonicalOddDenominatorBlock_card_mul_den_le
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (N j : ℕ) :
    (visibleCanonicalOddDenominatorBlock a N j).card *
      continuantDen a j ≤ N := by
  let qj : ℕ := continuantDen a j
  let T : Finset ℕ :=
    (canonicalOddBlock a j).filter fun t : ℕ =>
      CFBlockDenominator a j t ≤ N
  have hqpos : 0 < qj := by
    dsimp [qj]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hvisible_subset_image :
      visibleCanonicalOddDenominatorBlock a N j ⊆
        T.image (fun t : ℕ => CFBlockDenominator a j t - 1) := by
    intro x hx
    rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter] at hx
    rcases hx with ⟨hxblock, hxN⟩
    rw [canonicalOddDenominatorBlock] at hxblock
    rcases Finset.mem_image.mp hxblock with ⟨t, ht, htx⟩
    rw [Finset.mem_image]
    refine ⟨t, ?_, htx⟩
    dsimp [T]
    rw [Finset.mem_filter]
    refine ⟨ht, ?_⟩
    have ht1 : 1 ≤ t := (mem_canonicalOddBlock_iff.mp ht).1
    have hdenpos : 0 < CFBlockDenominator a j t := by
      unfold CFBlockDenominator
      dsimp [qj] at hqpos
      exact Nat.add_pos_right _ (Nat.mul_pos ht1 hqpos)
    have hxsucc :
        x + 1 = CFBlockDenominator a j t := by
      rw [← htx]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hdenpos)
    exact hxsucc ▸ hxN
  have hT_subset_Icc : T ⊆ Finset.Icc 1 (N / qj) := by
    intro t ht
    dsimp [T] at ht
    rw [Finset.mem_filter] at ht
    rcases ht with ⟨htblock, htN⟩
    rw [Finset.mem_Icc]
    have ht1 : 1 ≤ t := (mem_canonicalOddBlock_iff.mp htblock).1
    have htmul : t * qj ≤ N := by
      dsimp [qj]
      unfold CFBlockDenominator at htN
      exact (Nat.le_add_left (t * continuantDen a j) _).trans htN
    exact ⟨ht1, (Nat.le_div_iff_mul_le hqpos).2 htmul⟩
  have hcard_visible_le_T :
      (visibleCanonicalOddDenominatorBlock a N j).card ≤ T.card := by
    calc
      (visibleCanonicalOddDenominatorBlock a N j).card
          ≤ (T.image fun t : ℕ => CFBlockDenominator a j t - 1).card :=
            Finset.card_le_card hvisible_subset_image
      _ ≤ T.card := Finset.card_image_le
  have hTcard_le : T.card ≤ N / qj := by
    calc
      T.card ≤ (Finset.Icc 1 (N / qj)).card := Finset.card_le_card hT_subset_Icc
      _ = N / qj := by simp
  have hcard_div :
      (visibleCanonicalOddDenominatorBlock a N j).card ≤ N / qj :=
    hcard_visible_le_T.trans hTcard_le
  have hmul :
      (visibleCanonicalOddDenominatorBlock a N j).card * qj ≤
        (N / qj) * qj :=
    Nat.mul_le_mul_right qj hcard_div
  exact hmul.trans (Nat.div_mul_le_self N qj)

lemma continuantDen_le_succ_of_mem_canonicalOddDenominatorBlock
    {a : ℕ → ℕ} {j q : ℕ}
    (hq : q ∈ canonicalOddDenominatorBlock a j) :
    continuantDen a j ≤ q + 1 := by
  rw [canonicalOddDenominatorBlock] at hq
  rcases Finset.mem_image.mp hq with ⟨t, ht, htq⟩
  have ht1 : 1 ≤ t := (mem_canonicalOddBlock_iff.mp ht).1
  have hden_le_block :
      continuantDen a j ≤ CFBlockDenominator a j t := by
    unfold CFBlockDenominator
    have hle_mul : continuantDen a j ≤ t * continuantDen a j :=
      Nat.le_mul_of_pos_left (continuantDen a j) ht1
    exact hle_mul.trans (Nat.le_add_left _ _)
  have hblock_le_qsucc : CFBlockDenominator a j t ≤ q + 1 := by
    omega
  exact hden_le_block.trans hblock_le_qsucc

lemma canonicalOddDenominatorBlock_succ_le_endpoint
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j q : ℕ}
    (hq : q ∈ canonicalOddDenominatorBlock a j) :
    q + 1 ≤ continuantDen a (j + 1) := by
  rw [canonicalOddDenominatorBlock] at hq
  rcases Finset.mem_image.mp hq with ⟨t, ht, htq⟩
  have hsel := mem_canonicalOddBlock_iff.mp ht
  have hqpos : 0 < continuantDen a j :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_continuantDen_of_partials_pos_global a hpos j)
  have hblockpos : 0 < CFBlockDenominator a j t := by
    unfold CFBlockDenominator
    exact Nat.add_pos_right _ (Nat.mul_pos hsel.1 hqpos)
  have hqsucc_eq :
      q + 1 = CFBlockDenominator a j t := by
    rw [← htq]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hblockpos)
  rw [hqsucc_eq]
  rw [← CFBlockDenominator_endpoint a j]
  unfold CFBlockDenominator
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (continuantDen a j) hsel.2.1)
    (continuantDenPrev a j)

lemma canonicalOddDenominatorBlock_le_endpoint
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j q : ℕ}
    (hq : q ∈ canonicalOddDenominatorBlock a j) :
    q ≤ continuantDen a (j + 1) := by
  exact (Nat.le_succ q).trans
    (canonicalOddDenominatorBlock_succ_le_endpoint hpos hq)

lemma index_lt_log_bound_of_mem_visibleCanonicalBlock
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j q : ℕ}
    (hqmem : q ∈ canonicalOddDenominatorBlock a j)
    (hqN : q + 1 ≤ N) :
    j < 2 * Nat.log 2 N + 3 := by
  have hqj_le_qsucc :
      continuantDen a j ≤ q + 1 :=
    continuantDen_le_succ_of_mem_canonicalOddDenominatorBlock hqmem
  have hqj_le_N : continuantDen a j ≤ N :=
    hqj_le_qsucc.trans hqN
  have hpow : 2 ^ (j / 2) ≤ continuantDen a j :=
    pow_two_half_le_continuantDen_of_partials_pos a hpos j
  have hpowN : 2 ^ (j / 2) ≤ N :=
    hpow.trans hqj_le_N
  have hlog : j / 2 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hpowN
  omega

lemma mem_visibleCanonicalDenominatorSet_of_mem_block_le
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j q : ℕ}
    (hqmem : q ∈ canonicalOddDenominatorBlock a j)
    (hqN : q + 1 ≤ N) :
    q ∈ visibleCanonicalDenominatorSet a N := by
  have hj :
      j ∈ Finset.range (2 * Nat.log 2 N + 3) := by
    exact Finset.mem_range.mpr
      (index_lt_log_bound_of_mem_visibleCanonicalBlock hpos hqmem hqN)
  exact Finset.mem_biUnion.mpr ⟨j, hj, by
    rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter]
    exact ⟨hqmem, hqN⟩⟩

lemma mem_visibleCanonicalDenominatorSet_le
    {a : ℕ → ℕ} {N x : ℕ}
    (hx : x ∈ visibleCanonicalDenominatorSet a N) :
    x ≤ N := by
  rw [visibleCanonicalDenominatorSet] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxj⟩
  rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter] at hxj
  omega

theorem visibleCanonical_additive_upper_bridge
    {a : ℕ → ℕ}
    (_hpos : ∀ n : ℕ, 0 < a (n + 1))
    (N : ℕ) :
    popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N
      ≤ (2 * Nat.log 2 N + 3) * visibleCanonicalBlockMax a N + 1 ∧
    additiveEnergy (visibleCanonicalDenominatorSet a N)
      ≤ ((2 * Nat.log 2 N + 3) * visibleCanonicalBlockMax a N) ^ 3 ∧
    ∀ h : ℕ,
      HasProperHilbertCube (visibleCanonicalDenominatorSet a N) h →
        2 ^ h ≤ (2 * Nat.log 2 N + 3) * visibleCanonicalBlockMax a N := by
  let I : Finset ℕ := Finset.range (2 * Nat.log 2 N + 3)
  let B : ℕ → Finset ℕ := fun j =>
    visibleCanonicalOddDenominatorBlock a N j
  let S : Finset ℕ := visibleCanonicalDenominatorSet a N
  let M : ℕ := visibleCanonicalBlockMax a N
  have hcover : S ⊆ I.biUnion B := by
    intro x hx
    simpa [S, visibleCanonicalDenominatorSet, I, B] using hx
  have hBcard : ∀ i ∈ I, (B i).card ≤ M := by
    intro i hi
    dsimp [B, M, visibleCanonicalBlockMax]
    exact (Finset.le_sup
      (s := Finset.range (2 * Nat.log 2 N + 3))
      (f := fun j => (visibleCanonicalOddDenominatorBlock a N j).card)
      hi).trans (le_max_right _ _)
  constructor
  · have hpop := popularDifferenceUpTo_le_of_block_cover
      (I := I) (B := B) (S := S) (N := N) (M := M) hcover hBcard
    simpa [I, S, M] using hpop
  constructor
  · have henergy := additiveEnergy_le_of_block_cover
      (I := I) (B := B) (S := S) (M := M) hcover hBcard
    simpa [I, S, M] using henergy
  · intro h hcube
    have hcube_bound := two_pow_le_of_hasProperHilbertCube_of_block_cover
      (I := I) (B := B) (S := S) (M := M) hcover hBcard hcube
    simpa [I, S, M] using hcube_bound

lemma canonicalOddDenominatorBlock_subset_visibleSet_of_endpoint_le
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hjN : continuantDen a (j + 1) ≤ N) :
    canonicalOddDenominatorBlock a j ⊆ visibleCanonicalDenominatorSet a N := by
  intro q hq
  have hqN : q + 1 ≤ N :=
    (canonicalOddDenominatorBlock_succ_le_endpoint hpos hq).trans hjN
  exact mem_visibleCanonicalDenominatorSet_of_mem_block_le
    hpos hq hqN

lemma canonicalBlockLength_le_visibleCanonicalBlockMax_of_endpoint_le
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hjN : continuantDen a (j + 1) ≤ N) :
    canonicalBlockLength a j ≤ visibleCanonicalBlockMax a N := by
  have hqj_le_N : continuantDen a j ≤ N :=
    (continuantDen_mono_of_partials_pos a hpos j).trans hjN
  have hpowN : 2 ^ (j / 2) ≤ N :=
    (pow_two_half_le_continuantDen_of_partials_pos a hpos j).trans hqj_le_N
  have hlog : j / 2 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le Nat.one_lt_two hpowN
  have hjmem : j ∈ Finset.range (2 * Nat.log 2 N + 3) := by
    exact Finset.mem_range.mpr (by omega)
  have hblock_subset :
      canonicalOddDenominatorBlock a j ⊆
        visibleCanonicalOddDenominatorBlock a N j := by
    intro q hq
    rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter]
    exact ⟨hq, (canonicalOddDenominatorBlock_succ_le_endpoint hpos hq).trans hjN⟩
  have hcard :
      canonicalBlockLength a j ≤
        (visibleCanonicalOddDenominatorBlock a N j).card := by
    rw [← canonicalOddDenominatorBlock_card a hpos j]
    exact Finset.card_le_card hblock_subset
  have hvisible_le_max :
      (visibleCanonicalOddDenominatorBlock a N j).card ≤
        visibleCanonicalBlockMax a N := by
    unfold visibleCanonicalBlockMax
    exact (Finset.le_sup
      (s := Finset.range (2 * Nat.log 2 N + 3))
      (f := fun j => (visibleCanonicalOddDenominatorBlock a N j).card)
      hjmem).trans (le_max_right _ _)
  exact hcard.trans hvisible_le_max

lemma canonicalBlockGrowth_le_visibleCanonicalBlockMax
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (N : ℕ) :
    canonicalBlockGrowth a N ≤ visibleCanonicalBlockMax a N := by
  unfold canonicalBlockGrowth
  apply max_le
  · exact one_le_visibleCanonicalBlockMax a N
  · apply Finset.sup_le
    intro j _hj
    by_cases hden : continuantDen a (j + 1) ≤ N
    · simp [hden]
      exact canonicalBlockLength_le_visibleCanonicalBlockMax_of_endpoint_le
        hpos hden
    · simp [hden]

lemma visibleCanonicalOddDenominatorBlock_card_le_cap
    (a : ℕ → ℕ) (N j : ℕ) :
    (visibleCanonicalOddDenominatorBlock a N j).card ≤ N := by
  have hsub : visibleCanonicalOddDenominatorBlock a N j ⊆ Finset.range N := by
    intro q hq
    rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter] at hq
    exact Finset.mem_range.mpr (by omega)
  calc
    (visibleCanonicalOddDenominatorBlock a N j).card ≤ (Finset.range N).card :=
      Finset.card_le_card hsub
    _ = N := by simp

lemma visibleCanonicalBlockMax_le_self_of_one_le
    (a : ℕ → ℕ) {N : ℕ}
    (hN : 1 ≤ N) :
    visibleCanonicalBlockMax a N ≤ N := by
  unfold visibleCanonicalBlockMax
  apply max_le hN
  apply Finset.sup_le
  intro j _hj
  exact visibleCanonicalOddDenominatorBlock_card_le_cap a N j

lemma visibleCanonicalBlockMax_ratio_nonneg_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤
        Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro N hN
  have hlogR_nonneg :
      0 ≤ Real.log (visibleCanonicalBlockMax a N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast one_le_visibleCanonicalBlockMax a N)
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  exact div_nonneg hlogR_nonneg hlogN_nonneg

lemma visibleCanonicalBlockMax_ratio_le_one_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ) ≤ 1 := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let R : ℝ := visibleCanonicalBlockMax a N
  let X : ℝ := N
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_visibleCanonicalBlockMax a N))
  have hRX : R ≤ X := by
    dsimp [R, X]
    exact_mod_cast
      visibleCanonicalBlockMax_le_self_of_one_le a (by omega : 1 ≤ N)
  have hlogRX : Real.log R ≤ Real.log X :=
    Real.log_le_log hRpos hRX
  have hlogXpos : 0 < Real.log X := by
    dsimp [X]
    exact Real.log_pos (by exact_mod_cast hN)
  have hdiv : Real.log R / Real.log X ≤ Real.log X / Real.log X :=
    div_le_div_of_nonneg_right hlogRX hlogXpos.le
  have hright : Real.log X / Real.log X = 1 := div_self hlogXpos.ne'
  simpa [R, X, hright] using hdiv

lemma canonicalBlockExponent_le_visibleCanonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a ≤ visibleCanonicalBlockExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let G : ℕ → ℝ := fun N =>
    Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ)
  have hFG : F ≤ᶠ[atTop] G := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    let R : ℝ := canonicalBlockGrowth a N
    let V : ℝ := visibleCanonicalBlockMax a N
    let X : ℝ := N
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (by
          unfold canonicalBlockGrowth
          exact le_max_left _ _))
    have hRV : R ≤ V := by
      dsimp [R, V]
      exact_mod_cast canonicalBlockGrowth_le_visibleCanonicalBlockMax hpos N
    have hlogRV : Real.log R ≤ Real.log V :=
      Real.log_le_log hRpos hRV
    have hlogXpos : 0 < Real.log X := by
      dsimp [X]
      exact Real.log_pos (by exact_mod_cast hN)
    have hdiv : Real.log R / Real.log X ≤ Real.log V / Real.log X :=
      div_le_div_of_nonneg_right hlogRV hlogXpos.le
    simpa [F, G, R, V, X] using hdiv
  have hFnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ F N := by
    refine (eventually_ge_atTop 1).mono ?_
    intro N hN
    have hlogR_nonneg :
        0 ≤ Real.log (canonicalBlockGrowth a N : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast (by
          unfold canonicalBlockGrowth
          exact le_max_left _ _))
    have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    exact div_nonneg hlogR_nonneg hlogN_nonneg
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge hFnonneg.frequently
  have hGbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop G :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleCanonicalBlockMax_ratio_le_one_eventually a]
          with N hN
        simpa [G] using hN)
  have hlim := Filter.limsup_le_limsup hFG hFcobdd hGbdd
  simpa [canonicalBlockExponent, visibleCanonicalBlockExponent, F, G] using hlim

theorem fullCanonicalBlock_additive_lower_bridge
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hjN : continuantDen a (j + 1) ≤ N) :
    canonicalBlockLength a j
      ≤ popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N ∧
    (canonicalBlockLength a j) ^ 3
      ≤ 2 * additiveEnergy (visibleCanonicalDenominatorSet a N) ∧
    ∀ h : ℕ,
      2 ^ h ≤ canonicalBlockLength a j →
        HasProperHilbertCube (visibleCanonicalDenominatorSet a N) h := by
  obtain ⟨s, d, m, hd, hm, hblock⟩ :=
    exists_finiteArithmeticBlock_subset_canonicalOddDenominatorBlock
      (a := a) (j := j) hpos
  subst m
  have hcanon_subset :
      canonicalOddDenominatorBlock a j ⊆ visibleCanonicalDenominatorSet a N :=
    canonicalOddDenominatorBlock_subset_visibleSet_of_endpoint_le hpos hjN
  have hblock_visible :
      finiteArithmeticBlock s d (canonicalBlockLength a j)
        ⊆ visibleCanonicalDenominatorSet a N :=
    hblock.trans hcanon_subset
  constructor
  · by_cases hm2 : 2 ≤ canonicalBlockLength a j
    · have hdleN : d ≤ N :=
        block_step_le_of_two_le_length_subset_Iic
          (S := visibleCanonicalDenominatorSet a N)
          (s := s) (d := d) (m := canonicalBlockLength a j)
          (N := N) hm2 hblock_visible
          (fun x hx => mem_visibleCanonicalDenominatorSet_le hx)
      exact popularDifferenceUpTo_ge_of_block_subset
        (S := visibleCanonicalDenominatorSet a N)
        (N := N)
        ⟨Nat.succ_le_of_lt hd, hdleN⟩ hblock_visible
    · have hle1 : canonicalBlockLength a j ≤ 1 := by omega
      exact hle1.trans
        (one_le_popularDifferenceUpTo
          (visibleCanonicalDenominatorSet a N) N)
  constructor
  · exact additiveEnergy_ge_of_arithmeticBlock_subset
      (S := visibleCanonicalDenominatorSet a N)
      hd hblock_visible
  · intro h hh
    exact hasProperHilbertCube_of_two_pow_le_block_length
      (S := visibleCanonicalDenominatorSet a N)
      hd hh hblock_visible

lemma canonicalOddCFGap_same_block
    (a : ℕ → ℕ) {j t s : ℕ} (hts : t ≤ s) :
    CanonicalOddCFGap a j t j s =
      (s - t) * continuantDen a j := by
  unfold CanonicalOddCFGap CFBlockDenominator
  let d : ℕ := s - t
  have hs : s = t + d := by
    dsimp [d]
    omega
  rw [hs]
  rw [Nat.add_mul]
  rw [← Nat.add_assoc]
  rw [Nat.add_sub_cancel_left]
  dsimp [d]
  rw [Nat.add_sub_cancel_left]

lemma canonicalOddCFGap_same_block_succ
    (a : ℕ → ℕ) (j t : ℕ) :
    CanonicalOddCFGap a j t j (t + 1) = continuantDen a j := by
  rw [canonicalOddCFGap_same_block a (Nat.le_succ t)]
  simp

lemma canonicalOddCFGap_same_block_add_two
    (a : ℕ → ℕ) (j t : ℕ) :
    CanonicalOddCFGap a j t j (t + 2) = 2 * continuantDen a j := by
  rw [canonicalOddCFGap_same_block a (by omega : t ≤ t + 2)]
  simp [Nat.mul_comm]

lemma canonicalOddCFGap_boundary_endpoint_to_first
    (a : ℕ → ℕ) (j : ℕ) :
    CanonicalOddCFGap a j (a (j + 1)) (j + 1) 1 =
      continuantDen a j := by
  unfold CanonicalOddCFGap
  rw [CFBlockDenominator_boundary_succ]
  omega

lemma canonicalOddCFGap_boundary_pred_endpoint_to_first
    (a : ℕ → ℕ) {j : ℕ} (hb : 0 < a (j + 1)) :
    CanonicalOddCFGap a j (a (j + 1) - 1) (j + 1) 1 =
      2 * continuantDen a j := by
  unfold CanonicalOddCFGap
  have hsucc := CFBlockDenominator_succ a j (a (j + 1) - 1)
  have hpred : a (j + 1) - 1 + 1 = a (j + 1) := by omega
  rw [hpred] at hsucc
  have hboundary := CFBlockDenominator_boundary_succ a j
  rw [hsucc] at hboundary
  rw [hboundary]
  omega

lemma canonicalOddCFGap_endpoint_to_after_next_first
    (a : ℕ → ℕ) (j : ℕ) :
    CanonicalOddCFGap a j (a (j + 1)) (j + 2) 1 =
      continuantDen a (j + 2) := by
  unfold CanonicalOddCFGap
  rw [CFBlockDenominator_endpoint]
  have hfirst :
      CFBlockDenominator a (j + 2) 1 =
        continuantDen a (j + 1) + continuantDen a (j + 2) := by
    simpa [Nat.add_assoc] using CFBlockDenominator_next_block_first a (j + 1)
  rw [hfirst]
  omega

lemma incoming_gap_le_first_scale
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t k s : ℕ}
    (hprev : ConsecutiveSelected a j t k s)
    (hfirst : IsFirstSelectedInBlock a k s) :
    CanonicalOddCFGap a j t k s ≤ s * continuantDen a k := by
  rcases hprev with ⟨hjt, hks, hlt, hnone⟩
  rcases hlt with hjk | ⟨hjk, hts⟩
  · have hkcases : k = j + 1 ∨ k = j + 2 := by
      have hle := consecutiveCanonicalOddCFIndices_block_le_add_two
        (a := a) hpos ⟨hjt, hks, Or.inl hjk, hnone⟩
      omega
    rcases hkcases with hk | hk
    · subst k
      unfold CanonicalOddCFGap CFBlockDenominator
      have hprev_succ :
          continuantDenPrev a (j + 1) = continuantDen a j := by
        simp [continuantDenPrev]
      rw [hprev_succ]
      have hq_le :
          continuantDen a j ≤
            continuantDenPrev a j + t * continuantDen a j := by
        have htq : 1 * continuantDen a j ≤ t * continuantDen a j :=
          Nat.mul_le_mul_right _ hjt.1
        omega
      exact Nat.sub_le_iff_le_add.mpr (by omega)
    · subst k
      have hempty :
          a (j + 2) = 1 ∧
            Odd (continuantNumPrev a (j + 1)) ∧
              Odd (continuantNum a (j + 1)) :=
        emptyBlock_of_consecutiveCanonicalOddCFIndices_skip_two
          (a := a) hpos ⟨hjt, hks, Or.inl (by omega), hnone⟩ rfl
      have hend : CanonicalOddCFIndex a j (a (j + 1)) :=
        canonicalOddCFIndex_endpoint_of_next_emptyBlock hpos hempty
      have ht_end : t = a (j + 1) := by
        by_contra htne
        have htlt : t < a (j + 1) :=
          lt_of_le_of_ne hjt.2.1 htne
        exact hnone j (a (j + 1)) hend
          (Or.inr ⟨rfl, htlt⟩)
          (Or.inl (by omega))
      have hfirst_after_empty :
          CanonicalOddCFIndex a (j + 2) 1 :=
        canonicalOddCFIndex_next_of_emptyBlock
          (a := a) hpos hempty.1 hempty.2.1 hempty.2.2
      have hs_one : s = 1 := by
        rcases hfirst with ⟨_hs, hmin⟩
        by_contra hsne
        have h1lt : 1 < s := by
          exact lt_of_le_of_ne hks.1 (by
            intro h
            exact hsne h.symm)
        exact hmin 1 hfirst_after_empty h1lt
      subst t
      subst s
      rw [canonicalOddCFGap_endpoint_to_after_next_first]
      simp
  · subst k
    rw [canonicalOddCFGap_same_block a (Nat.le_of_lt hts)]
    have hle : s - t ≤ s := Nat.sub_le _ _
    exact Nat.mul_le_mul_right _ hle

lemma CFBlockDenominator_le_endpoint
    (a : ℕ → ℕ) {j t : ℕ}
    (ht : t ≤ a (j + 1)) :
    CFBlockDenominator a j t ≤ continuantDen a (j + 1) := by
  rw [← CFBlockDenominator_endpoint a j]
  unfold CFBlockDenominator
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (continuantDen a j) ht)
    (continuantDenPrev a j)

lemma CFBlockDenominator_next_block_ge_first
    (a : ℕ → ℕ) {j u : ℕ}
    (hu : 1 ≤ u) :
    continuantDen a j + continuantDen a (j + 1) ≤
      CFBlockDenominator a (j + 1) u := by
  unfold CFBlockDenominator
  have hprev :
      continuantDenPrev a (j + 1) = continuantDen a j := by
    simp [continuantDenPrev]
  rw [hprev]
  have hmul :
      1 * continuantDen a (j + 1) ≤
        u * continuantDen a (j + 1) :=
    Nat.mul_le_mul_right _ hu
  omega

lemma first_scale_le_outgoing_gap
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {k s l u : ℕ}
    (hnext : ConsecutiveSelected a k s l u)
    (hfirst : IsFirstSelectedInBlock a k s) :
    s * continuantDen a k ≤ CanonicalOddCFGap a k s l u := by
  rcases hnext with ⟨hks, hlu, hlt, hnone⟩
  have hs_cases : s = 1 ∨ s = 2 :=
    isFirstSelectedInBlock_eq_one_or_two hfirst
  rcases hlt with hkl | ⟨hkl, hsu⟩
  · have hl_cases : l = k + 1 ∨ l = k + 2 := by
      have hle := consecutiveCanonicalOddCFIndices_block_le_add_two
        (a := a) hpos ⟨hks, hlu, Or.inl hkl, hnone⟩
      omega
    rcases hl_cases with hl | hl
    · subst l
      rcases hs_cases with hs | hs
      · subst s
        unfold CanonicalOddCFGap CFBlockDenominator
        have hprev :
            continuantDenPrev a (k + 1) = continuantDen a k := by
          simp [continuantDenPrev]
        rw [hprev]
        have hqprev_le_q :
            continuantDenPrev a k ≤ continuantDen a k :=
          continuantDenPrev_le_continuantDen_of_partials_pos a hpos k
        have hq_le_uq :
            continuantDen a (k + 1) ≤
              u * continuantDen a (k + 1) := by
          simpa using
            (Nat.mul_le_mul_right (continuantDen a (k + 1)) hlu.1 :
              1 * continuantDen a (k + 1) ≤
                u * continuantDen a (k + 1))
        have hqk_le_qsucc :
            continuantDen a k ≤ continuantDen a (k + 1) :=
          continuantDen_mono_of_partials_pos a hpos k
        have hsub :
          continuantDenPrev a k + 1 * continuantDen a k ≤
            continuantDen a k + u * continuantDen a (k + 1) := by
          rw [continuantDen_succ_eq]
          have hq_le_aq :
              1 * continuantDen a k ≤
                a (k + 1) * continuantDen a k :=
            Nat.mul_le_mul_right _ (hpos k)
          have hleft_le_base :
              continuantDenPrev a k + 1 * continuantDen a k ≤
                a (k + 1) * continuantDen a k +
                  continuantDenPrev a k := by
            omega
          have hmul :
              1 * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) ≤
                u * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) :=
            Nat.mul_le_mul_right _ hlu.1
          have hbase_le_u :
              a (k + 1) * continuantDen a k + continuantDenPrev a k ≤
                u * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) := by
            simpa using hmul
          exact hleft_le_base.trans
            (hbase_le_u.trans (Nat.le_add_left _ _))
        have hsum :
            1 * continuantDen a k +
                (continuantDenPrev a k + 1 * continuantDen a k) ≤
              continuantDen a k + u * continuantDen a (k + 1) := by
          rw [continuantDen_succ_eq]
          have hq_le_aq :
              1 * continuantDen a k ≤
                a (k + 1) * continuantDen a k :=
            Nat.mul_le_mul_right _ (hpos k)
          have hleft_le_base :
              continuantDenPrev a k + 1 * continuantDen a k ≤
                a (k + 1) * continuantDen a k +
                  continuantDenPrev a k := by
            omega
          have hmul :
              1 * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) ≤
                u * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) :=
            Nat.mul_le_mul_right _ hlu.1
          have hbase_le_u :
              a (k + 1) * continuantDen a k + continuantDenPrev a k ≤
                u * (a (k + 1) * continuantDen a k +
                  continuantDenPrev a k) := by
            simpa using hmul
          simpa using
            Nat.add_le_add_left (hleft_le_base.trans hbase_le_u)
              (continuantDen a k)
        exact (Nat.le_sub_iff_add_le hsub).mpr hsum
      · subst s
        have hfirst2 : IsFirstSelectedInBlock a k 2 := hfirst
        have hodd_pair :
            Odd (continuantNumPrev a k) ∧ Odd (continuantNum a k) :=
          odd_num_pair_of_isFirstSelectedInBlock_eq_two hfirst2
        have hcoeff_le_three : a (k + 1) ≤ 3 := by
          by_contra hnot
          have h4le : 4 ≤ a (k + 1) := by omega
          have hsel4 : CanonicalOddCFIndex a k 4 := by
            refine ⟨by norm_num, h4le, ?_⟩
            exact (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
              hodd_pair.1 hodd_pair.2).2 (by norm_num)
          exact hnone k 4 hsel4
            (Or.inr ⟨rfl, by norm_num⟩)
            (Or.inl (by omega))
        have hcoeff_cases : a (k + 1) = 2 ∨ a (k + 1) = 3 := by
          have h2le : 2 ≤ a (k + 1) := hks.2.1
          omega
        rcases hcoeff_cases with ha2 | ha3
        · have hprev_next :
              continuantDenPrev a (k + 1) = continuantDen a k := by
            simp [continuantDenPrev]
          have hqsucc_eq :
              continuantDen a (k + 1) =
                2 * continuantDen a k + continuantDenPrev a k := by
            rw [continuantDen_succ_eq, ha2]
          have hprevOdd_next :
              Odd (continuantNumPrev a (k + 1)) := by
            simpa [continuantNumPrev] using hodd_pair.2
          have hcurrOdd_next :
              Odd (continuantNum a (k + 1)) := by
            rw [continuantNum_succ_eq, ha2]
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
              (Even.mul_left even_two (continuantNum a k)).add_odd
                hodd_pair.1
          have huEven : Even u :=
            (odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
              hprevOdd_next hcurrOdd_next).1 hlu.2.2
          rcases huEven with ⟨m, hm⟩
          have hu_ne_one : u ≠ 1 := by
            intro hu1
            omega
          have hu2 : 2 ≤ u := by
            cases u with
            | zero =>
                exact False.elim (Nat.not_succ_le_zero 0 hlu.1)
            | succ u =>
                cases u with
                | zero =>
                    exact False.elim (hu_ne_one rfl)
                | succ u =>
                    omega
          unfold CanonicalOddCFGap CFBlockDenominator
          rw [hprev_next, hqsucc_eq]
          exact (Nat.le_sub_iff_add_le (by
            have hmul :
                2 * (2 * continuantDen a k + continuantDenPrev a k) ≤
                  u * (2 * continuantDen a k + continuantDenPrev a k) :=
              Nat.mul_le_mul_right _ hu2
            have hleft :
                continuantDenPrev a k + 2 * continuantDen a k ≤
                  2 * (2 * continuantDen a k + continuantDenPrev a k) := by
              omega
            exact hleft.trans (hmul.trans (Nat.le_add_left _ _)) :
              continuantDenPrev a k + 2 * continuantDen a k ≤
              continuantDen a k +
                u * (2 * continuantDen a k + continuantDenPrev a k))).mpr
            (by
              have hmul :
                  2 * (2 * continuantDen a k + continuantDenPrev a k) ≤
                    u * (2 * continuantDen a k + continuantDenPrev a k) :=
                Nat.mul_le_mul_right _ hu2
              have hleft :
                  2 * continuantDen a k +
                      (continuantDenPrev a k + 2 * continuantDen a k) ≤
                    2 * (2 * continuantDen a k + continuantDenPrev a k) := by
                omega
              exact hleft.trans (hmul.trans (Nat.le_add_left _ _)))
        · have hprev_next :
              continuantDenPrev a (k + 1) = continuantDen a k := by
            simp [continuantDenPrev]
          have hqsucc_eq :
              continuantDen a (k + 1) =
                3 * continuantDen a k + continuantDenPrev a k := by
            rw [continuantDen_succ_eq, ha3]
          unfold CanonicalOddCFGap CFBlockDenominator
          rw [hprev_next, hqsucc_eq]
          exact (Nat.le_sub_iff_add_le (by
            have hmul :
                1 * (3 * continuantDen a k + continuantDenPrev a k) ≤
                  u * (3 * continuantDen a k + continuantDenPrev a k) :=
              Nat.mul_le_mul_right _ hlu.1
            have hbase_le_u :
                3 * continuantDen a k + continuantDenPrev a k ≤
                  u * (3 * continuantDen a k + continuantDenPrev a k) := by
              simpa using hmul
            have hleft :
                continuantDenPrev a k + 2 * continuantDen a k ≤
                  continuantDen a k +
                    (3 * continuantDen a k + continuantDenPrev a k) := by
              omega
            exact hleft.trans (Nat.add_le_add_left hbase_le_u _) :
              continuantDenPrev a k + 2 * continuantDen a k ≤
              continuantDen a k +
                u * (3 * continuantDen a k + continuantDenPrev a k))).mpr
            (by
              have hmul :
                  1 * (3 * continuantDen a k + continuantDenPrev a k) ≤
                    u * (3 * continuantDen a k + continuantDenPrev a k) :=
                Nat.mul_le_mul_right _ hlu.1
              have hbase_le_u :
                  3 * continuantDen a k + continuantDenPrev a k ≤
                    u * (3 * continuantDen a k + continuantDenPrev a k) := by
                simpa using hmul
              have hleft :
                  2 * continuantDen a k +
                      (continuantDenPrev a k + 2 * continuantDen a k) ≤
                    continuantDen a k +
                      (3 * continuantDen a k + continuantDenPrev a k) := by
                omega
              exact hleft.trans (Nat.add_le_add_left hbase_le_u _))
    · subst l
      have hcurrent_le :
          CFBlockDenominator a k s ≤ continuantDen a (k + 1) :=
        CFBlockDenominator_le_endpoint a hks.2.1
      have hnext_ge :
          continuantDen a (k + 1) + continuantDen a (k + 2) ≤
            CFBlockDenominator a (k + 2) u := by
        simpa [Nat.add_assoc] using
          CFBlockDenominator_next_block_ge_first (a := a) (j := k + 1) hlu.1
      have hsle2 : s ≤ 2 := by
        rcases hs_cases with hs | hs <;> omega
      have hscale :
          s * continuantDen a k ≤ continuantDen a (k + 2) := by
        have hmul :
            s * continuantDen a k ≤ 2 * continuantDen a k :=
          Nat.mul_le_mul_right _ hsle2
        exact hmul.trans
          (two_mul_continuantDen_le_two_step_of_partials_pos a hpos k)
      unfold CanonicalOddCFGap
      exact (Nat.le_sub_iff_add_le (by omega :
        CFBlockDenominator a k s ≤ CFBlockDenominator a (k + 2) u)).mpr (by
        omega)
  · subst l
    rw [canonicalOddCFGap_same_block a (Nat.le_of_lt hsu)]
    rcases hs_cases with hs | hs
    · subst s
      have hdiff : 1 ≤ u - 1 := by omega
      exact Nat.mul_le_mul_right _ hdiff
    · subst s
      have hfirst2 : IsFirstSelectedInBlock a k 2 := hfirst
      have huEven : Even u :=
        even_index_of_isFirstSelectedInBlock_eq_two hfirst2 hlu
      rcases huEven with ⟨m, hm⟩
      have hdiff : 2 ≤ u - 2 := by
        have hu_ne_two : u ≠ 2 := by omega
        omega
      exact Nat.mul_le_mul_right _ hdiff

theorem boundary_gap_le_next_gap_of_middle_first
    {a : ℕ → ℕ}
    (hpos : ∀ j : ℕ, 0 < a (j + 1))
    {j t k s l u : ℕ}
    (hprev : ConsecutiveSelected a j t k s)
    (hnext : ConsecutiveSelected a k s l u)
    (hfirst : IsFirstSelectedInBlock a k s) :
    CanonicalOddCFGap a j t k s ≤ CanonicalOddCFGap a k s l u := by
  exact (incoming_gap_le_first_scale hpos hprev hfirst).trans
    (first_scale_le_outgoing_gap hpos hnext hfirst)

lemma canonicalBlockLength_le_partialQuotient (a : ℕ → ℕ) (j : ℕ) :
    canonicalBlockLength a j ≤ a (j + 1) := by
  unfold canonicalBlockLength canonicalOddBlock
  calc
    ((Finset.Icc 1 (a (j + 1))).filter
        fun t : ℕ => Odd (CFBlockNumerator a j t)).card ≤
        (Finset.Icc 1 (a (j + 1))).card := by
      exact Finset.card_filter_le _ _
    _ = a (j + 1) := by
      simp

lemma canonicalBlockLength_bounds_of_parityLowerBound
    {a : ℕ → ℕ}
    (hparity : HasBlockParityLowerBound a)
    (j : ℕ) :
    a (j + 1) / 2 ≤ canonicalBlockLength a j ∧
      canonicalBlockLength a j ≤ a (j + 1) :=
  ⟨hparity j, canonicalBlockLength_le_partialQuotient a j⟩

lemma canonicalBlockLength_bounds (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ canonicalBlockLength a j ∧
      canonicalBlockLength a j ≤ a (j + 1) :=
  ⟨canonicalBlockLength_lower_bound a j,
    canonicalBlockLength_le_partialQuotient a j⟩

lemma one_le_canonicalSafeBlockLength (a : ℕ → ℕ) (j : ℕ) :
    1 ≤ canonicalSafeBlockLength a j := by
  unfold canonicalSafeBlockLength
  exact le_max_left _ _

lemma canonicalBlockLength_le_safeBlockLength (a : ℕ → ℕ) (j : ℕ) :
    canonicalBlockLength a j ≤ canonicalSafeBlockLength a j := by
  unfold canonicalSafeBlockLength
  exact le_max_right _ _

lemma canonicalBlockLength_div_two_le_safeBlockLength (a : ℕ → ℕ) (j : ℕ) :
    a (j + 1) / 2 ≤ canonicalSafeBlockLength a j :=
  (canonicalBlockLength_lower_bound a j).trans
    (canonicalBlockLength_le_safeBlockLength a j)

private lemma real_div_three_le_max_one_nat_div_two (n : ℕ) :
    (n : ℝ) / 3 ≤ (max 1 (n / 2) : ℕ) := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn2 : 2 ≤ n := by omega
    have hnat : n ≤ 3 * (n / 2) := by omega
    have hreal : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdiv : (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) := by
      nlinarith
    have hmax : ((n / 2 : ℕ) : ℝ) ≤ (max 1 (n / 2) : ℕ) := by
      exact_mod_cast (le_max_right 1 (n / 2))
    exact hdiv.trans hmax

lemma partialQuotient_div_three_le_safeBlockLength_real
    (a : ℕ → ℕ) (j : ℕ) :
    (a (j + 1) : ℝ) / 3 ≤
      (canonicalSafeBlockLength a j : ℝ) := by
  have hbase :
      (a (j + 1) : ℝ) / 3 ≤
        (max 1 (a (j + 1) / 2) : ℕ) :=
    real_div_three_le_max_one_nat_div_two (a (j + 1))
  have hsafe :
      max 1 (a (j + 1) / 2) ≤ canonicalSafeBlockLength a j := by
    unfold canonicalSafeBlockLength
    exact max_le_max (le_refl 1) (canonicalBlockLength_lower_bound a j)
  exact hbase.trans (by exact_mod_cast hsafe)

lemma canonicalSafeBlockLength_le_partialQuotient
    (a : ℕ → ℕ) {j : ℕ}
    (hpos : 0 < a (j + 1)) :
    canonicalSafeBlockLength a j ≤ a (j + 1) := by
  unfold canonicalSafeBlockLength
  exact max_le (by simpa using hpos) (canonicalBlockLength_le_partialQuotient a j)

lemma canonicalSafeBlockLength_le_partialQuotient_real
    (a : ℕ → ℕ) {j : ℕ}
    (hpos : 0 < a (j + 1)) :
    (canonicalSafeBlockLength a j : ℝ) ≤ (a (j + 1) : ℝ) := by
  exact_mod_cast canonicalSafeBlockLength_le_partialQuotient a hpos

lemma canonicalSafeBlockLength_bounds_real
    (a : ℕ → ℕ) {j : ℕ}
    (hpos : 0 < a (j + 1)) :
    (a (j + 1) : ℝ) / 3 ≤
        (canonicalSafeBlockLength a j : ℝ) ∧
      (canonicalSafeBlockLength a j : ℝ) ≤ (a (j + 1) : ℝ) :=
  ⟨partialQuotient_div_three_le_safeBlockLength_real a j,
    canonicalSafeBlockLength_le_partialQuotient_real a hpos⟩

lemma continuantDen_succ_le_six_safe_mul_den_real
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    (continuantDen a (j + 1) : ℝ)
      ≤ 6 * (canonicalSafeBlockLength a j : ℝ) *
          (continuantDen a j : ℝ) := by
  have hQ :
      (continuantDen a (j + 1) : ℝ)
        ≤ 2 * (a (j + 1) : ℝ) * (continuantDen a j : ℝ) := by
    exact_mod_cast (continuantDen_succ_mul_bounds hpos j).2
  have ha :
      (a (j + 1) : ℝ) ≤ 3 * (canonicalSafeBlockLength a j : ℝ) := by
    have h := partialQuotient_div_three_le_safeBlockLength_real a j
    nlinarith
  have hqnonneg : 0 ≤ (continuantDen a j : ℝ) := by positivity
  nlinarith

lemma two_le_continuantDen_succ_of_two_le_visibleCanonicalOddDenominatorBlock_card
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hv2 : 2 ≤ (visibleCanonicalOddDenominatorBlock a N j).card) :
    2 ≤ continuantDen a (j + 1) := by
  have hvM :
      (visibleCanonicalOddDenominatorBlock a N j).card ≤
        canonicalSafeBlockLength a j :=
    visibleCanonicalOddDenominatorBlock_card_le_safeBlockLength
      (a := a) N j
  have hMa :
      canonicalSafeBlockLength a j ≤ a (j + 1) :=
    canonicalSafeBlockLength_le_partialQuotient a (hpos j)
  have haQ :
      a (j + 1) ≤ continuantDen a (j + 1) :=
    partialQuotient_le_continuantDen_succ a hpos j
  exact hv2.trans (hvM.trans (hMa.trans haQ))

lemma log_ratio_le_log_ratio_add_const_of_mul_le
    {v M Q N K : ℝ}
    (hK : 1 ≤ K)
    (hv2 : 2 ≤ v)
    (hN2 : 2 ≤ N)
    (hQ2 : 2 ≤ Q)
    (hvM : v ≤ M)
    (hvN : v ≤ N)
    (hmul : v * Q ≤ K * M * N) :
    Real.log v / Real.log N
      ≤ Real.log M / Real.log Q + Real.log K / Real.log N := by
  let A : ℝ := Real.log v
  let B : ℝ := Real.log M
  let C : ℝ := Real.log Q
  let L : ℝ := Real.log N
  let k : ℝ := Real.log K
  have hvpos : 0 < v := by linarith
  have hMpos : 0 < M := by linarith
  have hQpos : 0 < Q := by linarith
  have hNpos : 0 < N := by linarith
  have hKpos : 0 < K := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hCpos : 0 < C := by
    dsimp [C]
    exact Real.log_pos (by linarith)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.log_nonneg (by linarith)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact Real.log_nonneg hK
  have hAleB : A ≤ B := by
    dsimp [A, B]
    exact Real.log_le_log hvpos hvM
  have hAleL : A ≤ L := by
    dsimp [A, L]
    exact Real.log_le_log hvpos hvN
  have hleftpos : 0 < v * Q := mul_pos hvpos hQpos
  have hlogmul0 :
      Real.log (v * Q) ≤ Real.log (K * M * N) :=
    Real.log_le_log hleftpos hmul
  have hlogmul : A + C ≤ k + B + L := by
    dsimp [A, B, C, L, k]
    rw [Real.log_mul hvpos.ne' hQpos.ne'] at hlogmul0
    rw [Real.log_mul (mul_pos hKpos hMpos).ne' hNpos.ne',
      Real.log_mul hKpos.ne' hMpos.ne'] at hlogmul0
    linarith
  change A / L ≤ B / C + k / L
  by_cases hQN : Q ≤ N
  · have hCleL : C ≤ L := by
      dsimp [C, L]
      exact Real.log_le_log hQpos hQN
    have hACleAL : A * C ≤ A * L :=
      mul_le_mul_of_nonneg_left hCleL hAnonneg
    have hALleBL : A * L ≤ B * L :=
      mul_le_mul_of_nonneg_right hAleB hLpos.le
    have hmain : A / L ≤ B / C := by
      rw [div_le_div_iff₀ hLpos hCpos]
      exact hACleAL.trans hALleBL
    have hkdiv_nonneg : 0 ≤ k / L := div_nonneg hk_nonneg hLpos.le
    linarith
  · have hNQ : N < Q := lt_of_not_ge hQN
    have hLltC : L < C := by
      dsimp [L, C]
      exact Real.log_lt_log hNpos hNQ
    have hLleC : L ≤ C := le_of_lt hLltC
    have hEta_nonneg : 0 ≤ C - L := by linarith
    have hEta_le : C - L ≤ B - A + k := by linarith
    have hDeltak_nonneg : 0 ≤ B - A + k := by linarith
    have hAeta_le_Leta :
        A * (C - L) ≤ L * (C - L) :=
      mul_le_mul_of_nonneg_right hAleL hEta_nonneg
    have hLeta_le_Ldeltak :
        L * (C - L) ≤ L * (B - A + k) :=
      mul_le_mul_of_nonneg_left hEta_le hLpos.le
    have hAeta_le_Ldeltak :
        A * (C - L) ≤ L * (B - A + k) :=
      hAeta_le_Leta.trans hLeta_le_Ldeltak
    have hkLleC : k * L ≤ k * C :=
      mul_le_mul_of_nonneg_left hLleC hk_nonneg
    have hmain : A * C ≤ B * L + k * C := by
      nlinarith
    calc
      A / L = (A * C) / (L * C) := by
        field_simp [hLpos.ne', hCpos.ne']
      _ ≤ (B * L + k * C) / (L * C) := by
        exact div_le_div_of_nonneg_right hmain
          (mul_nonneg hLpos.le hCpos.le)
      _ = B / C + k / L := by
        field_simp [hLpos.ne', hCpos.ne']

lemma visibleBlock_card_log_ratio_le_endpoint_safe_ratio_add_error
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hN : 2 ≤ N)
    (hv2 : 2 ≤ (visibleCanonicalOddDenominatorBlock a N j).card) :
    Real.log ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) /
        Real.log (N : ℝ)
      ≤
    Real.log (canonicalSafeBlockLength a j : ℝ) /
        Real.log (continuantDen a (j + 1) : ℝ)
      + Real.log 6 / Real.log (N : ℝ) := by
  let v : ℝ := (visibleCanonicalOddDenominatorBlock a N j).card
  let M : ℝ := canonicalSafeBlockLength a j
  let Q : ℝ := continuantDen a (j + 1)
  let X : ℝ := N
  have hv2real : 2 ≤ v := by
    dsimp [v]
    exact_mod_cast hv2
  have hX2 : 2 ≤ X := by
    dsimp [X]
    exact_mod_cast hN
  have hQ2nat :
      2 ≤ continuantDen a (j + 1) :=
    two_le_continuantDen_succ_of_two_le_visibleCanonicalOddDenominatorBlock_card
      hpos hv2
  have hQ2real : 2 ≤ Q := by
    dsimp [Q]
    exact_mod_cast hQ2nat
  have hvM : v ≤ M := by
    dsimp [v, M]
    exact_mod_cast
      visibleCanonicalOddDenominatorBlock_card_le_safeBlockLength
        (a := a) N j
  have hvX : v ≤ X := by
    dsimp [v, X]
    exact_mod_cast visibleCanonicalOddDenominatorBlock_card_le_cap a N j
  have hvq :
      v * (continuantDen a j : ℝ) ≤ (N : ℝ) := by
    dsimp [v]
    exact_mod_cast
      visibleCanonicalOddDenominatorBlock_card_mul_den_le
        (a := a) hpos N j
  have hQle :
      Q ≤ 6 * M * (continuantDen a j : ℝ) := by
    dsimp [Q, M]
    exact continuantDen_succ_le_six_safe_mul_den_real hpos j
  have hmul : v * Q ≤ 6 * M * X := by
    have h1 : v * Q ≤ v * (6 * M * (continuantDen a j : ℝ)) :=
      mul_le_mul_of_nonneg_left hQle (by positivity)
    have h2 :
        (6 * M) * (v * (continuantDen a j : ℝ)) ≤
          (6 * M) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hvq (by positivity)
    dsimp [X]
    nlinarith
  have hmain :=
    log_ratio_le_log_ratio_add_const_of_mul_le
      (v := v) (M := M) (Q := Q) (N := X) (K := 6)
      (by norm_num) hv2real hX2 hQ2real hvM hvX hmul
  simpa [v, M, Q, X] using hmain

lemma visibleCanonicalBlockMax_ratio_le_of_all_blocks
    {a : ℕ → ℕ} {N : ℕ} {C : ℝ}
    (hN : 1 < N)
    (hCnonneg : 0 ≤ C)
    (hblock :
      ∀ j ∈ Finset.range (2 * Nat.log 2 N + 3),
        Real.log ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) /
            Real.log (N : ℝ) ≤ C) :
    Real.log (visibleCanonicalBlockMax a N : ℝ) /
        Real.log (N : ℝ) ≤ C := by
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  by_cases hRone : visibleCanonicalBlockMax a N = 1
  · have hlogR : Real.log (visibleCanonicalBlockMax a N : ℝ) = 0 := by
      rw [hRone]
      norm_num
    simp [hlogR, hCnonneg]
  · let s : Finset ℕ := Finset.range (2 * Nat.log 2 N + 3)
    let f : ℕ → ℕ := fun j : ℕ =>
      (visibleCanonicalOddDenominatorBlock a N j).card
    have hsne : s.Nonempty := by
      refine ⟨0, ?_⟩
      simp [s]
    rcases Finset.exists_mem_eq_sup s hsne f with ⟨j, hjmem, hsup⟩
    have hRle : visibleCanonicalBlockMax a N ≤ f j := by
      unfold visibleCanonicalBlockMax
      change max 1 (s.sup f) ≤ f j
      rw [hsup]
      apply max_le
      · by_contra hlt
        have hfj0 : f j = 0 := by omega
        have hRone' : max 1 (f j) = 1 := by simp [hfj0]
        exact hRone (by
          unfold visibleCanonicalBlockMax
          change max 1 (s.sup f) = 1
          simpa [hsup] using hRone')
      · rfl
    let R : ℝ := visibleCanonicalBlockMax a N
    let V : ℝ := f j
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one
          (one_le_visibleCanonicalBlockMax a N))
    have hRV : R ≤ V := by
      dsimp [R, V]
      exact_mod_cast hRle
    have hlogRV : Real.log R ≤ Real.log V :=
      Real.log_le_log hRpos hRV
    have hdiv :
        Real.log R / Real.log (N : ℝ) ≤
          Real.log V / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogRV hlogNpos.le
    exact hdiv.trans (by simpa [s, f, V] using hblock j hjmem)

lemma one_le_finiteSafeBlockMax (a : ℕ → ℕ) (J : ℕ) :
    1 ≤ finiteSafeBlockMax a J := by
  unfold finiteSafeBlockMax
  exact le_max_left _ _

lemma canonicalSafeBlockLength_le_finiteSafeBlockMax_of_lt
    (a : ℕ → ℕ) {J j : ℕ}
    (hj : j < J) :
    canonicalSafeBlockLength a j ≤ finiteSafeBlockMax a J := by
  unfold finiteSafeBlockMax
  have hjmem : j ∈ Finset.range J := by
    simpa using hj
  exact (Finset.le_sup
    (s := Finset.range J)
    (f := fun j : ℕ => canonicalSafeBlockLength a j)
    hjmem).trans (le_max_right _ _)

lemma log_safeBlockLength_le_log_finiteSafeBlockMax_of_lt
    (a : ℕ → ℕ) {J j : ℕ}
    (hj : j < J) :
    Real.log (canonicalSafeBlockLength a j : ℝ) ≤
      Real.log (finiteSafeBlockMax a J : ℝ) := by
  have hMpos :
      0 < (canonicalSafeBlockLength a j : ℝ) := by
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalSafeBlockLength a j))
  exact Real.log_le_log hMpos
    (by
      exact_mod_cast canonicalSafeBlockLength_le_finiteSafeBlockMax_of_lt a hj)

lemma abs_log_safeBlockLength_sub_log_partialQuotient_le_log_three
    (a : ℕ → ℕ) {j : ℕ}
    (hpos : 0 < a (j + 1)) :
    |Real.log (canonicalSafeBlockLength a j : ℝ) -
        Real.log (a (j + 1) : ℝ)| ≤ Real.log 3 := by
  let M : ℝ := canonicalSafeBlockLength a j
  let A : ℝ := a (j + 1)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast hpos
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalSafeBlockLength a j))
  have hlow : A / 3 ≤ M := by
    dsimp [A, M]
    exact partialQuotient_div_three_le_safeBlockLength_real a j
  have hhigh : M ≤ A := by
    dsimp [A, M]
    exact canonicalSafeBlockLength_le_partialQuotient_real a hpos
  have hlog_high : Real.log M ≤ Real.log A :=
    Real.log_le_log hMpos hhigh
  have hAdivpos : 0 < A / 3 := by positivity
  have hlog_low : Real.log (A / 3) ≤ Real.log M :=
    Real.log_le_log hAdivpos hlow
  have habs :
      |Real.log M - Real.log A| = Real.log A - Real.log M := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlog_high)]
    ring
  have hdiff_le : Real.log A - Real.log M ≤ Real.log A - Real.log (A / 3) := by
    linarith
  have hdiff_eq : Real.log A - Real.log (A / 3) = Real.log 3 := by
    rw [Real.log_div hApos.ne' (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  calc
    |Real.log (canonicalSafeBlockLength a j : ℝ) -
        Real.log (a (j + 1) : ℝ)|
        = |Real.log M - Real.log A| := by rfl
    _ = Real.log A - Real.log M := habs
    _ ≤ Real.log A - Real.log (A / 3) := hdiff_le
    _ = Real.log 3 := hdiff_eq

/-- A block denominator lies on the full continued-fraction denominator path. -/
theorem CFBlockDenominator_path
    {a : ℕ → ℕ} {j t : ℕ}
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (j + 1)) :
    CFDenominatorPath a (CFBlockDenominator a j t) := by
  exact ⟨j, t, ht1, htle, rfl⟩

/-- A member of the canonical parity block gives an `OddCFPathPair`. -/
theorem oddCFPathPair_of_mem_canonicalOddBlock
    {a : ℕ → ℕ} {j t : ℕ}
    (ht : t ∈ canonicalOddBlock a j) :
    OddCFPathPair a (CFBlockNumerator a j t) (CFBlockDenominator a j t) := by
  rw [mem_canonicalOddBlock_iff] at ht
  rcases ht with ⟨ht1, htle, htodd⟩
  exact ⟨j, t, ht1, htle, rfl, rfl, htodd⟩

/-- A member of the parity block also gives a plain denominator-path entry. -/
theorem CFBlockDenominator_path_of_mem_canonicalOddBlock
    {a : ℕ → ℕ} {j t : ℕ}
    (ht : t ∈ canonicalOddBlock a j) :
    CFDenominatorPath a (CFBlockDenominator a j t) := by
  rw [mem_canonicalOddBlock_iff] at ht
  exact CFBlockDenominator_path ht.1 ht.2.1

/-- A reduced canonical parity-block denominator belongs to `oddCFDenoms`. -/
theorem blockDenominator_mem_oddCFDenoms_of_mem_canonicalOddBlock
    {α : ℝ} {a : ℕ → ℕ} {j t : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (ht : t ∈ canonicalOddBlock a j)
    (hQ : 2 ≤ CFBlockDenominator a j t)
    (hred : ReducedFraction (CFBlockNumerator a j t) (CFBlockDenominator a j t)) :
    CFBlockDenominator a j t ∈ oddCFDenoms α := by
  exact oddCFDenoms_mem_of_oddCFPathPair hcf
    (oddCFPathPair_of_mem_canonicalOddBlock ht) hQ hred

/-- Any chosen simple continued-fraction expansion describes `A α` as the set
of odd-numerator principal/intermediate block denominators, shifted down by
one. -/
theorem A_eq_oddBlockASet_of_IsSimpleCFExpansion
    {α : ℝ} {a : ℕ → ℕ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    (hcf : IsSimpleCFExpansion α a) :
    A α = oddBlockASet a := by
  rw [A_eq_odd_convergent_or_semiconvergent hαpos hαirr]
  ext n
  constructor
  · rintro ⟨P, Q, hnQ, hQ2, hred, hconv, hodd⟩
    rcases pair_path_of_convergent_or_semiconvergent_of_IsSimpleCFExpansion
        hαpos hαirr hcf hQ2 hred hconv with
      ⟨j, t, ht1, htle, hP, hQ⟩
    refine ⟨j, t, ht1, htle, ?_, ?_, ?_⟩
    · rw [hP] at hodd
      simpa [CFBlockNumerator] using hodd
    · rw [hQ] at hQ2
      simpa [CFBlockDenominator] using hQ2
    · rw [hQ] at hnQ
      simpa [CFBlockDenominator] using hnQ
  · rintro ⟨j, t, ht1, htle, hodd, hQ2, hnQ⟩
    refine ⟨CFBlockNumerator a j t, CFBlockDenominator a j t,
      hnQ, hQ2, ?_, ?_, hodd⟩
    · simpa [CFBlockNumerator, CFBlockDenominator] using
        reducedFraction_pathPair a (n := j) (t := t) ht1
    · refine ⟨a, hcf, Or.inr ?_⟩
      exact ⟨j, t, ht1, htle, rfl, rfl⟩

/-- Every non-initial block denominator is at least `2`. -/
lemma two_le_CFBlockDenominator_of_one_le_index
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {j t : ℕ}
    (hj : 1 ≤ j)
    (ht : 1 ≤ t) :
    2 ≤ CFBlockDenominator a j t := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj) with ⟨k, rfl⟩
  have hprev : 1 ≤ continuantDenPrev a (k + 1) := by
    simpa [continuantDenPrev] using
      one_le_continuantDen_of_partials_pos_global a hpos k
  have hcurr : 1 ≤ t * continuantDen a (k + 1) := by
    exact Nat.succ_le_of_lt <|
      Nat.mul_pos
        (lt_of_lt_of_le Nat.zero_lt_one ht)
        (lt_of_lt_of_le Nat.zero_lt_one
          (one_le_continuantDen_of_partials_pos_global a hpos (k + 1)))
  have hsum :
      1 + 1 ≤
        continuantDenPrev a (k + 1) + t * continuantDen a (k + 1) :=
    Nat.add_le_add hprev hcurr
  simpa [CFBlockDenominator, Nat.succ_eq_add_one] using hsum

lemma one_le_canonicalBlockGrowth (a : ℕ → ℕ) (N : ℕ) :
    1 ≤ canonicalBlockGrowth a N := by
  unfold canonicalBlockGrowth
  exact le_max_left _ _

lemma canonicalBlockLength_le_growth_of_endpoint_le
    (a : ℕ → ℕ) {j N : ℕ}
    (hj : j < N + 1)
    (hden : continuantDen a (j + 1) ≤ N) :
    canonicalBlockLength a j ≤ canonicalBlockGrowth a N := by
  unfold canonicalBlockGrowth
  have hjmem : j ∈ Finset.range (N + 1) := by
    simpa using hj
  have hleSup :
      canonicalBlockLength a j ≤
        (Finset.range (N + 1)).sup fun k : ℕ =>
          if continuantDen a (k + 1) ≤ N then canonicalBlockLength a k else 0 := by
    simpa [hden] using
      (Finset.le_sup
        (s := Finset.range (N + 1))
        (f := fun k : ℕ =>
          if continuantDen a (k + 1) ≤ N then canonicalBlockLength a k else 0)
        hjmem)
  exact hleSup.trans (le_max_right _ _)

lemma canonicalSafeBlockLength_le_growth_of_endpoint_le
    (a : ℕ → ℕ) {j N : ℕ}
    (hj : j < N + 1)
    (hden : continuantDen a (j + 1) ≤ N) :
    canonicalSafeBlockLength a j ≤ canonicalBlockGrowth a N := by
  unfold canonicalSafeBlockLength
  exact max_le (one_le_canonicalBlockGrowth a N)
    (canonicalBlockLength_le_growth_of_endpoint_le a hj hden)

lemma canonicalSafeBlockLength_le_growth_at_endpoint
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (j : ℕ) :
    canonicalSafeBlockLength a j ≤
      canonicalBlockGrowth a (continuantDen a (j + 1)) := by
  have hj :
      j < continuantDen a (j + 1) + 1 :=
    Nat.lt_succ_of_le (index_le_continuantDen_succ_of_partials_pos a hpos j)
  exact canonicalSafeBlockLength_le_growth_of_endpoint_le a hj le_rfl

lemma endpoint_safeBlock_ratio_le_growth_ratio_at_endpoint
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ j : ℕ in atTop,
      Real.log (canonicalSafeBlockLength a j : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) ≤
        Real.log
            (canonicalBlockGrowth a (continuantDen a (j + 1)) : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) := by
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  filter_upwards [hQgt1] with j hQjgt1
  let Q : ℝ := continuantDen a (j + 1)
  let M : ℝ := canonicalSafeBlockLength a j
  let R : ℝ := canonicalBlockGrowth a (continuantDen a (j + 1))
  have hlogQpos : 0 < Real.log Q := by
    dsimp [Q]
    exact Real.log_pos (by exact_mod_cast hQjgt1)
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalSafeBlockLength a j))
  have hMR : M ≤ R := by
    dsimp [M, R]
    exact_mod_cast canonicalSafeBlockLength_le_growth_at_endpoint a hpos j
  have hlogMR : Real.log M ≤ Real.log R :=
    Real.log_le_log hMpos hMR
  exact div_le_div_of_nonneg_right hlogMR hlogQpos.le

lemma canonicalBlockGrowth_le_of_visible_blockLength_le
    (a : ℕ → ℕ) {N B : ℕ}
    (hB : 1 ≤ B)
    (hvisible :
      ∀ j : ℕ,
        j < N + 1 →
          continuantDen a (j + 1) ≤ N →
            canonicalBlockLength a j ≤ B) :
    canonicalBlockGrowth a N ≤ B := by
  unfold canonicalBlockGrowth
  refine max_le hB ?_
  refine Finset.sup_le ?_
  intro j hj
  by_cases hden : continuantDen a (j + 1) ≤ N
  · simp [hden, hvisible j (by simpa using hj) hden]
  · simp [hden, le_trans (Nat.zero_le 1) hB]

lemma canonicalBlockGrowth_le_of_visible_safeBlockLength_le
    (a : ℕ → ℕ) {N B : ℕ}
    (hB : 1 ≤ B)
    (hvisible :
      ∀ j : ℕ,
        j < N + 1 →
          continuantDen a (j + 1) ≤ N →
            canonicalSafeBlockLength a j ≤ B) :
    canonicalBlockGrowth a N ≤ B := by
  exact canonicalBlockGrowth_le_of_visible_blockLength_le a hB
    (fun j hj hden =>
      (canonicalBlockLength_le_safeBlockLength a j).trans
        (hvisible j hj hden))

lemma canonicalBlockGrowth_eq_one_or_exists_visible_le_safe
    (a : ℕ → ℕ) (N : ℕ) :
    canonicalBlockGrowth a N = 1 ∨
      ∃ j : ℕ,
        j < N + 1 ∧
          continuantDen a (j + 1) ≤ N ∧
            canonicalBlockGrowth a N ≤ canonicalSafeBlockLength a j := by
  by_cases hgrowth : canonicalBlockGrowth a N = 1
  · exact Or.inl hgrowth
  · right
    let s : Finset ℕ := Finset.range (N + 1)
    let f : ℕ → ℕ := fun j : ℕ =>
      if continuantDen a (j + 1) ≤ N then canonicalBlockLength a j else 0
    have hsne : s.Nonempty := ⟨0, by simp [s]⟩
    rcases Finset.exists_mem_eq_sup s hsne f with ⟨j, hjmem, hsup⟩
    have hj : j < N + 1 := by
      simpa [s] using hjmem
    by_cases hden : continuantDen a (j + 1) ≤ N
    · refine ⟨j, hj, hden, ?_⟩
      have hsup_len :
          s.sup f = canonicalBlockLength a j := by
        simpa [f, hden] using hsup
      have hgrowth_eq :
          canonicalBlockGrowth a N = canonicalSafeBlockLength a j := by
        unfold canonicalBlockGrowth canonicalSafeBlockLength
        change max 1 (s.sup f) = max 1 (canonicalBlockLength a j)
        rw [hsup_len]
      exact le_of_eq hgrowth_eq
    · have hsup_zero : s.sup f = 0 := by
        simpa [f, hden] using hsup
      have hgrowth_one : canonicalBlockGrowth a N = 1 := by
        unfold canonicalBlockGrowth
        change max 1 (s.sup f) = 1
        simp [hsup_zero]
      exact False.elim (hgrowth hgrowth_one)

lemma canonicalBlockGrowth_ratio_le_of_visible_safeBlock_ratio_le
    (a : ℕ → ℕ) {N : ℕ} {C : ℝ}
    (hN : 1 < N)
    (hCnonneg : 0 ≤ C)
    (hvisible :
      ∀ j : ℕ,
        j < N + 1 →
          continuantDen a (j + 1) ≤ N →
            Real.log (canonicalSafeBlockLength a j : ℝ) /
              Real.log (N : ℝ) ≤ C) :
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ) ≤ C := by
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  rcases canonicalBlockGrowth_eq_one_or_exists_visible_le_safe a N with hRone |
      ⟨j, hj, hden, hRleM⟩
  · have hlogR : Real.log (canonicalBlockGrowth a N : ℝ) = 0 := by
      rw [hRone]
      norm_num
    simp [hlogR, hCnonneg]
  · let R : ℝ := canonicalBlockGrowth a N
    let M : ℝ := canonicalSafeBlockLength a j
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalBlockGrowth a N))
    have hRM : R ≤ M := by
      dsimp [R, M]
      exact_mod_cast hRleM
    have hlogRM : Real.log R ≤ Real.log M :=
      Real.log_le_log hRpos hRM
    have hdiv :
        Real.log R / Real.log (N : ℝ) ≤
          Real.log M / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogRM hlogNpos.le
    exact hdiv.trans (by simpa [M] using hvisible j hj hden)

lemma canonicalSafeBlockLength_le_endpoint
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (j : ℕ) :
    canonicalSafeBlockLength a j ≤ continuantDen a (j + 1) :=
  (canonicalSafeBlockLength_le_partialQuotient a (hpos j)).trans
    (partialQuotient_le_continuantDen_succ a hpos j)

lemma canonicalBlockGrowth_le_self_of_one_le
    (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N : ℕ}
    (hN : 1 ≤ N) :
    canonicalBlockGrowth a N ≤ N :=
  canonicalBlockGrowth_le_of_visible_safeBlockLength_le a hN
    (fun j _hj hden =>
      (canonicalSafeBlockLength_le_endpoint a hpos j).trans hden)

lemma endpoint_safeBlock_ratio_nonneg_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ j : ℕ in atTop,
      0 ≤
        Real.log (canonicalSafeBlockLength a j : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) := by
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  filter_upwards [hQgt1] with j hQjgt1
  have hlogM_nonneg :
      0 ≤ Real.log (canonicalSafeBlockLength a j : ℝ) :=
    Real.log_nonneg
      (by exact_mod_cast one_le_canonicalSafeBlockLength a j)
  have hlogQ_nonneg :
      0 ≤ Real.log (continuantDen a (j + 1) : ℝ) :=
    (Real.log_pos (by exact_mod_cast hQjgt1)).le
  exact div_nonneg hlogM_nonneg hlogQ_nonneg

lemma endpoint_safeBlock_ratio_le_one_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ j : ℕ in atTop,
      Real.log (canonicalSafeBlockLength a j : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) ≤ 1 := by
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  filter_upwards [hQgt1] with j hQjgt1
  let M : ℝ := canonicalSafeBlockLength a j
  let Q : ℝ := continuantDen a (j + 1)
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalSafeBlockLength a j))
  have hMQ : M ≤ Q := by
    dsimp [M, Q]
    exact_mod_cast canonicalSafeBlockLength_le_endpoint a hpos j
  have hlogMQ : Real.log M ≤ Real.log Q :=
    Real.log_le_log hMpos hMQ
  have hlogQpos : 0 < Real.log Q := by
    dsimp [Q]
    exact Real.log_pos (by exact_mod_cast hQjgt1)
  have hdiv :
      Real.log M / Real.log Q ≤ Real.log Q / Real.log Q :=
    div_le_div_of_nonneg_right hlogMQ hlogQpos.le
  have hright : Real.log Q / Real.log Q = 1 := by
    exact div_self hlogQpos.ne'
  simpa [M, Q, hright] using hdiv

lemma partialQuotient_endpoint_ratio_nonneg_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ j : ℕ in atTop,
      0 ≤
        Real.log (a (j + 1) : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) := by
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  filter_upwards [hQgt1] with j hQjgt1
  have ha1 : 1 ≤ a (j + 1) := Nat.succ_le_of_lt (hpos j)
  have hlogA_nonneg :
      0 ≤ Real.log (a (j + 1) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha1)
  have hlogQ_nonneg :
      0 ≤ Real.log (continuantDen a (j + 1) : ℝ) :=
    (Real.log_pos (by exact_mod_cast hQjgt1)).le
  exact div_nonneg hlogA_nonneg hlogQ_nonneg

lemma partialQuotient_endpoint_ratio_le_one_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ j : ℕ in atTop,
      Real.log (a (j + 1) : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ) ≤ 1 := by
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  filter_upwards [hQgt1] with j hQjgt1
  let A : ℝ := a (j + 1)
  let Q : ℝ := continuantDen a (j + 1)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast hpos j
  have hAQ : A ≤ Q := by
    dsimp [A, Q]
    exact_mod_cast partialQuotient_le_continuantDen_succ a hpos j
  have hlogAQ : Real.log A ≤ Real.log Q :=
    Real.log_le_log hApos hAQ
  have hlogQpos : 0 < Real.log Q := by
    dsimp [Q]
    exact Real.log_pos (by exact_mod_cast hQjgt1)
  have hdiv :
      Real.log A / Real.log Q ≤ Real.log Q / Real.log Q :=
    div_le_div_of_nonneg_right hlogAQ hlogQpos.le
  have hright : Real.log Q / Real.log Q = 1 := by
    exact div_self hlogQpos.ne'
  simpa [A, Q, hright] using hdiv

lemma pqLogRatio_nonneg_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ pqLogRatio a n := by
  have hqR : Tendsto (fun n : ℕ => continuantDen a n) atTop atTop :=
    continuantDen_tendsto_atTop_of_partials_pos hpos
  have hqgt1 : ∀ᶠ n : ℕ in atTop, 1 < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  filter_upwards [hqgt1] with n hqgt1n
  have ha1 : 1 ≤ a (n + 1) := Nat.succ_le_of_lt (hpos n)
  have hlogA_nonneg : 0 ≤ Real.log (a (n + 1) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ha1)
  have hlogq_nonneg : 0 ≤ Real.log (continuantDen a n : ℝ) :=
    (Real.log_pos (by exact_mod_cast hqgt1n)).le
  exact div_nonneg hlogA_nonneg hlogq_nonneg

lemma pqLogRatioTransform_nonneg_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ pqLogRatioTransform a n := by
  filter_upwards [pqLogRatio_nonneg_eventually hpos] with n hx
  have hden_nonneg : 0 ≤ 1 + pqLogRatio a n := by linarith
  exact div_nonneg hx hden_nonneg

lemma pqLogRatioTransform_le_one_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ n : ℕ in atTop, pqLogRatioTransform a n ≤ 1 := by
  filter_upwards [pqLogRatio_nonneg_eventually hpos] with n hx
  have hden_pos : 0 < 1 + pqLogRatio a n := by linarith
  have hle : pqLogRatio a n ≤ 1 + pqLogRatio a n := by linarith
  simpa [pqLogRatioTransform] using (div_le_one hden_pos).mpr hle

lemma nonnegativeRatioTransform_eq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    nonnegativeRatioTransform x = x / (1 + x) := by
  simp [nonnegativeRatioTransform, max_eq_right hx]

lemma monotone_nonnegativeRatioTransform :
    Monotone nonnegativeRatioTransform := by
  intro x y hxy
  let u : ℝ := max 0 x
  let v : ℝ := max 0 y
  have huv : u ≤ v := by
    dsimp [u, v]
    exact max_le_max le_rfl hxy
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact le_max_left 0 x
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact le_max_left 0 y
  have hdenu : 0 < 1 + u := by linarith
  have hdenv : 0 < 1 + v := by linarith
  unfold nonnegativeRatioTransform
  change u / (1 + u) ≤ v / (1 + v)
  rw [div_le_div_iff₀ hdenu hdenv]
  nlinarith

lemma continuous_nonnegativeRatioTransform :
    Continuous nonnegativeRatioTransform := by
  have hmax : Continuous (fun x : ℝ => max 0 x) :=
    continuous_const.max continuous_id
  have hden :
      ∀ x : ℝ, 1 + max 0 x ≠ 0 := by
    intro x
    have hx : 0 ≤ max 0 x := le_max_left 0 x
    linarith
  simpa [nonnegativeRatioTransform] using
    hmax.div (continuous_const.add hmax) hden

lemma limsup_endpoint_safeBlock_ratio_nonneg
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    0 ≤
      limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop := by
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hfreq : ∃ᶠ j : ℕ in atTop, 0 ≤ G j :=
    ((endpoint_safeBlock_ratio_nonneg_eventually hpos).frequently.mono
      (fun j hj => by simpa [G] using hj))
  have hbdd : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop G :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [endpoint_safeBlock_ratio_le_one_eventually hpos]
          with j hj
        simpa [G] using hj)
  simpa [G] using Filter.le_limsup_of_frequently_le hfreq hbdd

lemma canonicalBlockGrowth_ratio_nonneg_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤
        Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro N hN
  have hlogR_nonneg :
      0 ≤ Real.log (canonicalBlockGrowth a N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast one_le_canonicalBlockGrowth a N)
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  exact div_nonneg hlogR_nonneg hlogN_nonneg

lemma canonicalBlockGrowth_ratio_le_one_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ) ≤ 1 := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let R : ℝ := canonicalBlockGrowth a N
  let X : ℝ := N
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_canonicalBlockGrowth a N))
  have hRX : R ≤ X := by
    dsimp [R, X]
    exact_mod_cast
      canonicalBlockGrowth_le_self_of_one_le a hpos (by omega : 1 ≤ N)
  have hlogRX : Real.log R ≤ Real.log X :=
    Real.log_le_log hRpos hRX
  have hlogXpos : 0 < Real.log X := by
    dsimp [X]
    exact Real.log_pos (by exact_mod_cast hN)
  have hdiv : Real.log R / Real.log X ≤ Real.log X / Real.log X :=
    div_le_div_of_nonneg_right hlogRX hlogXpos.le
  have hright : Real.log X / Real.log X = 1 := div_self hlogXpos.ne'
  simpa [R, X, hright] using hdiv

lemma limsup_endpoint_safeBlock_ratio_le_limsup_endpoint_growth_ratio
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop ≤
      limsup
        (fun j : ℕ =>
          Real.log
              (canonicalBlockGrowth a (continuantDen a (j + 1)) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop := by
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  let H : ℕ → ℝ := fun j =>
    Real.log (canonicalBlockGrowth a (continuantDen a (j + 1)) : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hGH : G ≤ᶠ[atTop] H := by
    filter_upwards [endpoint_safeBlock_ratio_le_growth_ratio_at_endpoint hpos]
      with j hj
    simpa [G, H] using hj
  have hGcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop G :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((endpoint_safeBlock_ratio_nonneg_eventually hpos).frequently.mono
        (fun j hj => by simpa [G] using hj))
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hHle_one : H ≤ᶠ[atTop] fun _ : ℕ => (1 : ℝ) := by
    filter_upwards [hQ.eventually
      (canonicalBlockGrowth_ratio_le_one_eventually hpos)] with j hj
    simpa [H] using hj
  have hHbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop H :=
    Filter.isBoundedUnder_of_eventually_le hHle_one
  exact Filter.limsup_le_limsup hGH hGcobdd hHbdd

lemma limsup_endpoint_growth_ratio_le_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup
        (fun j : ℕ =>
          Real.log
              (canonicalBlockGrowth a (continuantDen a (j + 1)) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop ≤
      canonicalBlockExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let Q : ℕ → ℕ := fun j => continuantDen a (j + 1)
  have hQ : Tendsto Q atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hFbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [canonicalBlockGrowth_ratio_le_one_eventually hpos]
          with N hN
        simpa [F] using hN)
  have hFnonneg_map :
      ∀ᶠ N : ℕ in Filter.map Q atTop, 0 ≤ F N := by
    exact hQ
      (by
        filter_upwards [canonicalBlockGrowth_ratio_nonneg_eventually a]
          with N hN
        simpa [F] using hN)
  have hFmap_cobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y)
        (Filter.map Q atTop) F :=
    Filter.IsCoboundedUnder.of_frequently_ge hFnonneg_map.frequently
  have hlim :
      limsup (F ∘ Q) atTop ≤ limsup F atTop :=
    Filter.Tendsto.limsup_comp_le_limsup hQ hFmap_cobdd hFbdd
  unfold canonicalBlockExponent
  simpa [F, Q, Function.comp_def] using hlim

theorem limsup_endpoint_safeBlock_ratio_le_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop ≤
      canonicalBlockExponent a :=
  (limsup_endpoint_safeBlock_ratio_le_limsup_endpoint_growth_ratio hpos).trans
    (limsup_endpoint_growth_ratio_le_canonicalBlockExponent hpos)

lemma eventually_canonicalBlockGrowth_ratio_le_of_limsup_endpoint_lt
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {C : ℝ}
    (hC :
      limsup
          (fun j : ℕ =>
            Real.log (canonicalSafeBlockLength a j : ℝ) /
              Real.log (continuantDen a (j + 1) : ℝ))
          atTop < C) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ) ≤ C := by
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hLnonneg : 0 ≤ limsup G atTop := by
    simpa [G] using limsup_endpoint_safeBlock_ratio_nonneg hpos
  have hCpos : 0 < C := lt_of_le_of_lt hLnonneg (by simpa [G] using hC)
  have hGbdd : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop G :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [endpoint_safeBlock_ratio_le_one_eventually hpos]
          with j hj
        simpa [G] using hj)
  have hGlt : ∀ᶠ j : ℕ in atTop, G j < C :=
    Filter.eventually_lt_of_limsup_lt (by simpa [G] using hC) hGbdd
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  rcases eventually_atTop.1 (hGlt.and hQgt1) with ⟨J, hJ⟩
  let B : ℕ := finiteSafeBlockMax a J
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (B : ℝ) / Real.log (N : ℝ) < C := by
    have hlim :
        Tendsto
          (fun N : ℕ => Real.log (B : ℝ) / Real.log (N : ℝ))
          atTop (𝓝 0) :=
      log_const_over_log_nat_tendsto_zero (Real.log (B : ℝ))
    exact hlim.eventually (eventually_lt_nhds hCpos)
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hsmallN hN2
  have hNgt1 : 1 < N := by omega
  exact canonicalBlockGrowth_ratio_le_of_visible_safeBlock_ratio_le
    a hNgt1 hCpos.le (fun j _hj hden => by
      by_cases hjlt : j < J
      · have hMpos :
            0 < (canonicalSafeBlockLength a j : ℝ) := by
          exact_mod_cast
            (lt_of_lt_of_le Nat.zero_lt_one
              (one_le_canonicalSafeBlockLength a j))
        have hMB :
            (canonicalSafeBlockLength a j : ℝ) ≤ (B : ℝ) := by
          dsimp [B]
          exact_mod_cast
            canonicalSafeBlockLength_le_finiteSafeBlockMax_of_lt a hjlt
        have hlog_le :
            Real.log (canonicalSafeBlockLength a j : ℝ) ≤
              Real.log (B : ℝ) :=
          Real.log_le_log hMpos hMB
        have hlogNpos : 0 < Real.log (N : ℝ) :=
          Real.log_pos (by exact_mod_cast hNgt1)
        have hdiv :
            Real.log (canonicalSafeBlockLength a j : ℝ) /
                Real.log (N : ℝ) ≤
              Real.log (B : ℝ) / Real.log (N : ℝ) :=
          div_le_div_of_nonneg_right hlog_le hlogNpos.le
        exact hdiv.trans (le_of_lt hsmallN)
      · have hjge : J ≤ j := le_of_not_gt hjlt
        have htail := hJ j hjge
        have hGjlt : G j < C := htail.1
        have hQjgt1 : 1 < continuantDen a (j + 1) := htail.2
        let M : ℝ := canonicalSafeBlockLength a j
        let Q : ℝ := continuantDen a (j + 1)
        have hlogM_nonneg : 0 ≤ Real.log M := by
          dsimp [M]
          exact Real.log_nonneg
            (by exact_mod_cast one_le_canonicalSafeBlockLength a j)
        have hlogQpos : 0 < Real.log Q := by
          dsimp [Q]
          exact Real.log_pos (by exact_mod_cast hQjgt1)
        have hlogQ_le_logN :
            Real.log Q ≤ Real.log (N : ℝ) := by
          dsimp [Q]
          exact Real.log_le_log
            (by exact_mod_cast (lt_trans Nat.zero_lt_one hQjgt1))
            (by exact_mod_cast hden)
        have hcompare :
            Real.log M / Real.log (N : ℝ) ≤
              Real.log M / Real.log Q :=
          div_le_div_of_nonneg_left hlogM_nonneg hlogQpos hlogQ_le_logN
        exact hcompare.trans (le_of_lt (by simpa [G, M, Q] using hGjlt)))

theorem canonicalBlockExponent_le_limsup_endpoint_safeBlock_ratio
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a ≤
      limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((canonicalBlockGrowth_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [F] using hN))
  have hFbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [canonicalBlockGrowth_ratio_le_one_eventually hpos]
          with N hN
        simpa [F] using hN)
  unfold canonicalBlockExponent
  have hmain :
      limsup F atTop ≤ limsup G atTop := by
    rw [Filter.limsup_le_iff' hFcobdd hFbdd]
    intro C hC
    filter_upwards
      [eventually_canonicalBlockGrowth_ratio_le_of_limsup_endpoint_lt
        (a := a) hpos (by simpa [G] using hC)]
      with N hN
    simpa [F] using hN
  simpa [F, G] using hmain

theorem canonicalBlockExponent_eq_limsup_endpoint_safeBlock_ratio
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a =
      limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop :=
  le_antisymm
    (canonicalBlockExponent_le_limsup_endpoint_safeBlock_ratio hpos)
    (limsup_endpoint_safeBlock_ratio_le_canonicalBlockExponent hpos)

lemma eventually_visibleCanonicalBlockMax_ratio_le_of_limsup_endpoint_lt
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {C₀ C : ℝ}
    (hlim :
      limsup
          (fun j : ℕ =>
            Real.log (canonicalSafeBlockLength a j : ℝ) /
              Real.log (continuantDen a (j + 1) : ℝ))
          atTop < C₀)
    (hC₀C : C₀ < C) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (visibleCanonicalBlockMax a N : ℝ) /
          Real.log (N : ℝ) ≤ C := by
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hLnonneg : 0 ≤ limsup G atTop := by
    simpa [G] using limsup_endpoint_safeBlock_ratio_nonneg hpos
  have hC₀pos : 0 < C₀ := lt_of_le_of_lt hLnonneg (by simpa [G] using hlim)
  have hCpos : 0 < C := lt_trans hC₀pos hC₀C
  have hgap : 0 < C - C₀ := by linarith
  have hGbdd : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop G :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [endpoint_safeBlock_ratio_le_one_eventually hpos]
          with j hj
        simpa [G] using hj)
  have hGlt : ∀ᶠ j : ℕ in atTop, G j < C₀ :=
    Filter.eventually_lt_of_limsup_lt (by simpa [G] using hlim) hGbdd
  rcases eventually_atTop.1 hGlt with ⟨J, hJ⟩
  let B : ℕ := finiteSafeBlockMax a J
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (B : ℝ) / Real.log (N : ℝ) < C := by
    have hlimzero :
        Tendsto
          (fun N : ℕ => Real.log (B : ℝ) / Real.log (N : ℝ))
          atTop (𝓝 0) :=
      log_const_over_log_nat_tendsto_zero (Real.log (B : ℝ))
    exact hlimzero.eventually (eventually_lt_nhds hCpos)
  have herr :
      ∀ᶠ N : ℕ in atTop,
        Real.log 6 / Real.log (N : ℝ) < C - C₀ := by
    have hlimzero :
        Tendsto
          (fun N : ℕ => Real.log 6 / Real.log (N : ℝ))
          atTop (𝓝 0) :=
      log_const_over_log_nat_tendsto_zero (Real.log 6)
    exact hlimzero.eventually (eventually_lt_nhds hgap)
  filter_upwards [hsmall, herr, eventually_ge_atTop 2] with N hsmallN herrN hN2
  have hNgt1 : 1 < N := by omega
  exact visibleCanonicalBlockMax_ratio_le_of_all_blocks
    (a := a) hNgt1 hCpos.le (fun j hj => by
      by_cases hjlt : j < J
      · by_cases hcard0 :
          (visibleCanonicalOddDenominatorBlock a N j).card = 0
        · have hlog :
              Real.log
                ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) = 0 := by
            rw [hcard0]
            norm_num
          simp [hlog, hCpos.le]
        · have hcard_pos_nat :
              0 < (visibleCanonicalOddDenominatorBlock a N j).card := by
            omega
          have hcard_pos :
              0 < ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) := by
            exact_mod_cast hcard_pos_nat
          have hcardB :
              ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) ≤
                (B : ℝ) := by
            dsimp [B]
            exact_mod_cast
              (visibleCanonicalOddDenominatorBlock_card_le_safeBlockLength
                (a := a) N j).trans
                (canonicalSafeBlockLength_le_finiteSafeBlockMax_of_lt a hjlt)
          have hlog_le :
              Real.log
                  ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) ≤
                Real.log (B : ℝ) :=
            Real.log_le_log hcard_pos hcardB
          have hlogNpos : 0 < Real.log (N : ℝ) :=
            Real.log_pos (by exact_mod_cast hNgt1)
          have hdiv :
              Real.log
                  ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) /
                  Real.log (N : ℝ) ≤
                Real.log (B : ℝ) / Real.log (N : ℝ) :=
            div_le_div_of_nonneg_right hlog_le hlogNpos.le
          exact hdiv.trans (le_of_lt hsmallN)
      · have hjge : J ≤ j := le_of_not_gt hjlt
        by_cases hv2 : 2 ≤ (visibleCanonicalOddDenominatorBlock a N j).card
        · have hlocal :
              Real.log
                  ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) /
                  Real.log (N : ℝ) ≤
                Real.log (canonicalSafeBlockLength a j : ℝ) /
                    Real.log (continuantDen a (j + 1) : ℝ) +
                  Real.log 6 / Real.log (N : ℝ) :=
            visibleBlock_card_log_ratio_le_endpoint_safe_ratio_add_error
              (a := a) hpos hN2 hv2
          have htail : G j < C₀ := hJ j hjge
          have hsum :
              Real.log (canonicalSafeBlockLength a j : ℝ) /
                    Real.log (continuantDen a (j + 1) : ℝ) +
                  Real.log 6 / Real.log (N : ℝ) ≤ C := by
            nlinarith [htail, herrN]
          exact hlocal.trans hsum
        · have hcardle1 :
              (visibleCanonicalOddDenominatorBlock a N j).card ≤ 1 := by
            omega
          have hcases :
              (visibleCanonicalOddDenominatorBlock a N j).card = 0 ∨
                (visibleCanonicalOddDenominatorBlock a N j).card = 1 := by
            omega
          rcases hcases with hzero | hone
          · have hlog :
                Real.log
                  ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) = 0 := by
              rw [hzero]
              norm_num
            simp [hlog, hCpos.le]
          · have hlog :
                Real.log
                  ((visibleCanonicalOddDenominatorBlock a N j).card : ℝ) = 0 := by
              rw [hone]
              norm_num
            simp [hlog, hCpos.le])

theorem visibleCanonicalBlockExponent_le_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleCanonicalBlockExponent a ≤ canonicalBlockExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ)
  let G : ℕ → ℝ := fun j =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
      Real.log (continuantDen a (j + 1) : ℝ)
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((visibleCanonicalBlockMax_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [F] using hN))
  have hFbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleCanonicalBlockMax_ratio_le_one_eventually a]
          with N hN
        simpa [F] using hN)
  rw [canonicalBlockExponent_eq_limsup_endpoint_safeBlock_ratio
    (a := a) hpos]
  have hmain : limsup F atTop ≤ limsup G atTop := by
    rw [Filter.limsup_le_iff' hFcobdd hFbdd]
    intro C hC
    let L : ℝ := limsup G atTop
    let C₀ : ℝ := (L + C) / 2
    have hLC₀ : L < C₀ := by
      dsimp [C₀, L]
      linarith
    have hC₀C : C₀ < C := by
      dsimp [C₀, L]
      linarith
    filter_upwards
      [eventually_visibleCanonicalBlockMax_ratio_le_of_limsup_endpoint_lt
        (a := a) hpos (C₀ := C₀) (C := C)
        (by simpa [G, L, C₀] using hLC₀) hC₀C]
      with N hN
    simpa [F] using hN
  simpa [visibleCanonicalBlockExponent, F, G] using hmain

theorem visibleCanonicalBlockExponent_eq_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleCanonicalBlockExponent a = canonicalBlockExponent a :=
  le_antisymm
    (visibleCanonicalBlockExponent_le_canonicalBlockExponent hpos)
    (canonicalBlockExponent_le_visibleCanonicalBlockExponent hpos)

lemma limsup_eq_of_sub_tendsto_zero_of_eventually_bounded
    {u v : ℕ → ℝ}
    (hsub : Tendsto (fun n : ℕ => u n - v n) atTop (𝓝 0))
    (hv_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ v n)
    (hv_le_one : ∀ᶠ n : ℕ in atTop, v n ≤ 1) :
    limsup u atTop = limsup v atTop := by
  let d : ℕ → ℝ := fun n : ℕ => u n - v n
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa [d] using hsub
  have hd_le_one : ∀ᶠ n : ℕ in atTop, d n ≤ 1 :=
    hd.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hneg_one_le_hd : ∀ᶠ n : ℕ in atTop, (-1 : ℝ) ≤ d n :=
    hd.eventually (eventually_ge_nhds (by norm_num : (-1 : ℝ) < 0))
  have hv_bdd_above :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop v :=
    Filter.isBoundedUnder_of_eventually_le hv_le_one
  have hv_bdd_below :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop v :=
    Filter.isBoundedUnder_of_eventually_ge hv_nonneg
  have hv_cobdd_below :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop v :=
    Filter.IsCoboundedUnder.of_frequently_ge hv_nonneg.frequently
  have hd_bdd_above :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop d :=
    Filter.isBoundedUnder_of_eventually_le hd_le_one
  have hd_bdd_below :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop d :=
    Filter.isBoundedUnder_of_eventually_ge hneg_one_le_hd
  have hd_cobdd_below :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop d :=
    Filter.IsCoboundedUnder.of_frequently_ge hneg_one_le_hd.frequently
  have hlimsup_d : limsup d atTop = 0 := hd.limsup_eq
  have hliminf_d : liminf d atTop = 0 := hd.liminf_eq
  have hu_eq :
      limsup u atTop = limsup (fun n : ℕ => v n + d n) atTop := by
    refine Filter.limsup_congr ?_
    exact Filter.Eventually.of_forall (fun n => by
      dsimp [d]
      ring)
  have hupper : limsup u atTop ≤ limsup v atTop := by
    rw [hu_eq]
    have h :=
      limsup_add_le
        (u := v) (v := d) (f := atTop)
        hv_bdd_below hv_bdd_above hd_cobdd_below hd_bdd_above
    simpa [hlimsup_d] using h
  have hlower : limsup v atTop ≤ limsup u atTop := by
    rw [hu_eq]
    have h :=
      le_limsup_add
        (u := v) (v := d) (f := atTop)
        hv_bdd_above hv_cobdd_below hd_bdd_above hd_bdd_below
    simpa [hliminf_d] using h
  exact le_antisymm hupper hlower

lemma safeBlock_partialQuotient_endpoint_ratio_sub_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto
      (fun j : ℕ =>
        Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ) -
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
      atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun j : ℕ =>
    Real.log (canonicalSafeBlockLength a j : ℝ) /
        Real.log (continuantDen a (j + 1) : ℝ) -
      Real.log (a (j + 1) : ℝ) /
        Real.log (continuantDen a (j + 1) : ℝ)
  have hQ :
      Tendsto (fun j : ℕ => continuantDen a (j + 1)) atTop atTop := by
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := continuantDen a) 1).2
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hQgt1 :
      ∀ᶠ j : ℕ in atTop, 1 < continuantDen a (j + 1) :=
    hQ.eventually_gt_atTop 1
  have habs_tendsto :
      Tendsto (fun j : ℕ => |d j|) atTop (𝓝 0) := by
    refine squeeze_zero'
      (f := fun j : ℕ => |d j|)
      (g := fun j : ℕ =>
        Real.log 3 / Real.log (continuantDen a (j + 1) : ℝ))
      ?hnonneg ?hle ?htend
    · exact Filter.Eventually.of_forall (fun j => abs_nonneg (d j))
    · filter_upwards [hQgt1] with j hQjgt1
      let den : ℝ := Real.log (continuantDen a (j + 1) : ℝ)
      have hdenpos : 0 < den := by
        dsimp [den]
        exact Real.log_pos (by exact_mod_cast hQjgt1)
      have hdiff :
          |d j| =
            |Real.log (canonicalSafeBlockLength a j : ℝ) -
                Real.log (a (j + 1) : ℝ)| / den := by
        dsimp [d, den]
        rw [div_sub_div_same, abs_div, abs_of_pos hdenpos]
      have hlog_bound :
          |Real.log (canonicalSafeBlockLength a j : ℝ) -
              Real.log (a (j + 1) : ℝ)| ≤ Real.log 3 :=
        abs_log_safeBlockLength_sub_log_partialQuotient_le_log_three a (hpos j)
      calc
        |d j| =
            |Real.log (canonicalSafeBlockLength a j : ℝ) -
                Real.log (a (j + 1) : ℝ)| / den := hdiff
        _ ≤ Real.log 3 / den :=
            div_le_div_of_nonneg_right hlog_bound hdenpos.le
    · exact log_const_over_log_continuantDen_succ_tendsto_zero hpos (Real.log 3)
  have hd : Tendsto d atTop (𝓝 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero d).2
      (by simpa [Function.comp_def] using habs_tendsto)
  simpa [d] using hd

lemma limsup_safeBlock_endpoint_eq_limsup_partialQuotient_endpoint
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup
        (fun j : ℕ =>
          Real.log (canonicalSafeBlockLength a j : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop =
      limsup
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop :=
  limsup_eq_of_sub_tendsto_zero_of_eventually_bounded
    (safeBlock_partialQuotient_endpoint_ratio_sub_tendsto_zero hpos)
    (partialQuotient_endpoint_ratio_nonneg_eventually hpos)
    (partialQuotient_endpoint_ratio_le_one_eventually hpos)

theorem canonicalBlockExponent_eq_limsup_partialQuotient_endpoint
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a =
      limsup
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop :=
  (canonicalBlockExponent_eq_limsup_endpoint_safeBlock_ratio hpos).trans
    (limsup_safeBlock_endpoint_eq_limsup_partialQuotient_endpoint hpos)

/-- For Euler-pattern coefficients, the capped canonical block growth is at
most logarithmic in the denominator cutoff. -/
theorem canonicalBlockGrowth_le_euler_log_bound
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a)
    (N : ℕ) :
    canonicalBlockGrowth a N ≤ 2 * (2 * Nat.log 2 N + 3) := by
  have hpos : ∀ n : ℕ, 0 < a (n + 1) := eulerPartialQuotients_pos_succ he
  have hlin : ∀ n : ℕ, a n ≤ 2 * (n + 1) := eulerPartialQuotients_linear_bound he
  have hpow : ∀ n : ℕ, 2 ^ (n / 2) ≤ continuantDen a n :=
    pow_two_half_le_continuantDen_of_partials_pos a hpos
  suffices
      canonicalBlockGrowth a N ≤ max 1 (2 * (2 * Nat.log 2 N + 3)) by
    exact this.trans (max_le (by omega) le_rfl)
  unfold canonicalBlockGrowth
  apply max_le_max le_rfl
  apply Finset.sup_le
  intro j _hj
  by_cases hden : continuantDen a (j + 1) ≤ N
  · simp [hden]
    have hL : canonicalBlockLength a j ≤ a (j + 1) :=
      canonicalBlockLength_le_partialQuotient a j
    have ha : a (j + 1) ≤ 2 * (j + 2) := by
      simpa [Nat.add_assoc] using hlin (j + 1)
    have hpow_le_N : 2 ^ ((j + 1) / 2) ≤ N :=
      (hpow (j + 1)).trans hden
    have hhalf_le_log : (j + 1) / 2 ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le Nat.one_lt_two hpow_le_N
    have hjbound : j + 2 ≤ 2 * Nat.log 2 N + 3 := by
      omega
    calc
      canonicalBlockLength a j ≤ a (j + 1) := hL
      _ ≤ 2 * (j + 2) := ha
      _ ≤ 2 * (2 * Nat.log 2 N + 3) := Nat.mul_le_mul_left 2 hjbound
      _ ≤ max 1 (2 * (2 * Nat.log 2 N + 3)) := le_max_right _ _
  · simp [hden]

private lemma tendsto_log_div_self_atTop :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := (isLittleO_iff_tendsto (𝕜 := ℝ) (l := atTop)
    (f := Real.log) (g := id) (by
      intro x hx
      have hx0 : x = 0 := by
        simpa [id] using hx
      simp [hx0])).mp Real.isLittleO_log_id_atTop
  simpa [Function.comp_def, id] using h

private lemma isBigO_log_affine_log_atTop {c d : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.log (c * x + d)) =O[atTop] Real.log := by
  let K : ℝ := c + |d| + 1
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hO : (fun x : ℝ => Real.log (K * x)) =O[atTop] Real.log :=
    Real.isBigO_log_const_mul_log_atTop K
  rcases (isBigO_iff.mp hO) with ⟨C, hC⟩
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_ge_atTop (max 1 ((1 + |d|) / c))] with x hCx hx
  have hx1 : 1 ≤ x := le_of_max_le_left hx
  have hbound : (1 + |d|) / c ≤ x := le_of_max_le_right hx
  have hmul : 1 + |d| ≤ c * x := by
    have := (div_le_iff₀ hc).mp hbound
    nlinarith
  have hcx_ge_one : 1 ≤ c * x + d := by
    have hneg : -d ≤ |d| := neg_le_abs d
    nlinarith
  have hcx_pos : 0 < c * x + d :=
    lt_of_lt_of_le (by norm_num) hcx_ge_one
  have hKx_ge_one : 1 ≤ K * x := by
    have hKge_one : 1 ≤ K := by
      dsimp [K]
      nlinarith [hc.le, abs_nonneg d]
    nlinarith [mul_le_mul hKge_one hx1 (by norm_num : (0 : ℝ) ≤ 1) hKpos.le]
  have hle_arg : c * x + d ≤ K * x := by
    have hdle : d ≤ |d| := le_abs_self d
    have habsx : |d| ≤ |d| * x := by
      nlinarith [mul_le_mul_of_nonneg_left hx1 (abs_nonneg d)]
    dsimp [K]
    nlinarith
  have hlog_le : Real.log (c * x + d) ≤ Real.log (K * x) :=
    Real.log_le_log hcx_pos hle_arg
  have hlog_nonneg : 0 ≤ Real.log (c * x + d) :=
    Real.log_nonneg hcx_ge_one
  have hKlog_nonneg : 0 ≤ Real.log (K * x) :=
    Real.log_nonneg hKx_ge_one
  have habs : ‖Real.log (c * x + d)‖ ≤ ‖Real.log (K * x)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg,
      abs_of_nonneg hKlog_nonneg]
    exact hlog_le
  exact habs.trans hCx

private lemma tendsto_log_affine_div_self_atTop {c d : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (c * x + d) / x) atTop (𝓝 0) := by
  have hO : (fun x : ℝ => Real.log (c * x + d)) =O[atTop] Real.log :=
    isBigO_log_affine_log_atTop hc
  have ho : (fun x : ℝ => Real.log (c * x + d)) =o[atTop] id :=
    hO.trans_isLittleO Real.isLittleO_log_id_atTop
  simpa [Function.comp_def, id] using ho.tendsto_div_nhds_zero

private lemma tendsto_euler_block_log_bound :
    Tendsto
      (fun N : ℕ =>
        Real.log ((4 / Real.log 2) * Real.log (N : ℝ) + 6) /
          Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hanalytic :
      Tendsto
        (fun x : ℝ => Real.log ((4 / Real.log 2) * x + 6) / x)
        atTop (𝓝 0) := by
    exact tendsto_log_affine_div_self_atTop (by positivity)
  exact hanalytic.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma log_two_mul_natLog_add_const_div_log_tendsto_zero
    {c : ℕ} (hcpos : 1 ≤ c) (hc : c ≤ 6) :
    Tendsto
      (fun N : ℕ =>
        Real.log ((2 * Nat.log 2 N + c : ℕ) : ℝ) /
          Real.log (N : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?hnonneg ?hle tendsto_euler_block_log_bound
  · refine eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro N hN
    let B : ℕ := 2 * Nat.log 2 N + c
    have hBge : 1 ≤ B := by
      dsimp [B]
      omega
    have hnum_nonneg : 0 ≤ Real.log (B : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hBge)
    have hden_nonneg : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hN)
    exact div_nonneg hnum_nonneg hden_nonneg
  · refine eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro N hN
    let B : ℕ := 2 * Nat.log 2 N + c
    have hBpos : 0 < (B : ℝ) := by
      exact_mod_cast (by dsimp [B]; omega : 0 < B)
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hN)
    have hnatlog_le :
        ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
      simpa [Real.log_div_log] using (Real.natLog_le_logb N 2)
    have hfour :
        4 * ((Nat.log 2 N : ℕ) : ℝ) ≤
          4 * (Real.log (N : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hnatlog_le (by norm_num)
    have hc_real : (c : ℝ) ≤ 6 := by exact_mod_cast hc
    have hrewrite :
        4 * (Real.log (N : ℝ) / Real.log 2) + 6 =
          (4 / Real.log 2) * Real.log (N : ℝ) + 6 := by
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      field_simp [hlog2pos.ne']
    have hB_le :
        (B : ℝ) ≤ (4 / Real.log 2) * Real.log (N : ℝ) + 6 := by
      have hB_le' :
          (B : ℝ) ≤ 4 * (Real.log (N : ℝ) / Real.log 2) + 6 := by
        dsimp [B]
        norm_num
        nlinarith [hfour, hc_real]
      exact hB_le'.trans_eq hrewrite
    have hlogB_le :
        Real.log (B : ℝ) ≤
          Real.log ((4 / Real.log 2) * Real.log (N : ℝ) + 6) :=
      Real.log_le_log hBpos hB_le
    exact div_le_div_of_nonneg_right hlogB_le hlogNpos.le

lemma log_visible_popular_cover_factor_div_log_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log ((2 * Nat.log 2 N + 4 : ℕ) : ℝ) /
          Real.log (N : ℝ))
      atTop (𝓝 0) :=
  log_two_mul_natLog_add_const_div_log_tendsto_zero
    (by norm_num : 1 ≤ 4) (by norm_num : 4 ≤ 6)

lemma log_visible_energy_cover_factor_div_log_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
          Real.log (N : ℝ))
      atTop (𝓝 0) :=
  log_two_mul_natLog_add_const_div_log_tendsto_zero
    (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 6)

lemma visibleCanonicalDenominatorSet_card_le_cap
    (a : ℕ → ℕ) (N : ℕ) :
    (visibleCanonicalDenominatorSet a N).card ≤ N := by
  have hsub : visibleCanonicalDenominatorSet a N ⊆ Finset.range N := by
    intro q hq
    rw [visibleCanonicalDenominatorSet] at hq
    rcases Finset.mem_biUnion.mp hq with ⟨j, _hj, hqj⟩
    rw [visibleCanonicalOddDenominatorBlock, Finset.mem_filter] at hqj
    exact Finset.mem_range.mpr (by omega)
  calc
    (visibleCanonicalDenominatorSet a N).card ≤ (Finset.range N).card :=
      Finset.card_le_card hsub
    _ = N := by simp

lemma visiblePopularDifference_ratio_nonneg_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤
        Real.log
            (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
          Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro N hN
  have hnum_nonneg :
      0 ≤ Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) :=
    Real.log_nonneg
      (by
        exact_mod_cast
          one_le_popularDifferenceUpTo
            (visibleCanonicalDenominatorSet a N) N)
  have hden_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  exact div_nonneg hnum_nonneg hden_nonneg

lemma visiblePopularDifference_ratio_le_two_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log
          (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ) ≤ 2 := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let P : ℕ := popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N
  have hP_le_succ : P ≤ N + 1 := by
    dsimp [P]
    exact (popularDifferenceUpTo_le_card_add_one
      (visibleCanonicalDenominatorSet a N) N).trans
        (by
          have hcard := visibleCanonicalDenominatorSet_card_le_cap a N
          omega)
  have hP_le_sq : P ≤ N ^ 2 := by
    have hsq : N + 1 ≤ N ^ 2 := by
      rw [pow_two]
      nlinarith
    exact hP_le_succ.trans hsq
  have hPpos : 0 < (P : ℝ) := by
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_popularDifferenceUpTo
          (visibleCanonicalDenominatorSet a N) N))
  have hlog_le :
      Real.log (P : ℝ) ≤ Real.log ((N ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log hPpos (by exact_mod_cast hP_le_sq)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hdiv :
      Real.log (P : ℝ) / Real.log (N : ℝ) ≤
        Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_right hlog_le hlogNpos.le
  have hpowlog :
      Real.log ((N ^ 2 : ℕ) : ℝ) = 2 * Real.log (N : ℝ) := by
    norm_num [Nat.cast_pow, Real.log_pow]
  have hright :
      Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log (N : ℝ) = 2 := by
    rw [hpowlog]
    field_simp [hlogNpos.ne']
  rw [hright] at hdiv
  simpa [P] using hdiv

lemma canonicalBlockGrowth_le_visiblePopularDifference
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (N : ℕ) :
    canonicalBlockGrowth a N
      ≤ popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N := by
  exact canonicalBlockGrowth_le_of_visible_blockLength_le a
    (one_le_popularDifferenceUpTo
      (visibleCanonicalDenominatorSet a N) N)
    (fun j _hj hden =>
      (fullCanonicalBlock_additive_lower_bridge
        (a := a) hpos (N := N) (j := j) hden).1)

lemma log_popular_le_log_visibleBlockMax_add_log_log_error
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      Real.log
          (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ)
      ≤
      Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ) +
      Real.log ((2 * Nat.log 2 N + 4 : ℕ) : ℝ) / Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let P : ℕ := popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N
  let M : ℕ := visibleCanonicalBlockMax a N
  let K : ℕ := 2 * Nat.log 2 N + 4
  have hupper :
      P ≤ (2 * Nat.log 2 N + 3) * M + 1 := by
    dsimp [P, M]
    exact (visibleCanonical_additive_upper_bridge
      (a := a) hpos N).1
  have hP_le : P ≤ K * M := by
    have hM1 : 1 ≤ M := by
      dsimp [M]
      exact one_le_visibleCanonicalBlockMax a N
    have hstep :
        (2 * Nat.log 2 N + 3) * M + 1 ≤ K * M := by
      dsimp [K]
      calc
        (2 * Nat.log 2 N + 3) * M + 1
            ≤ (2 * Nat.log 2 N + 3) * M + M := by
              exact Nat.add_le_add_left hM1 _
        _ = (2 * Nat.log 2 N + 4) * M := by ring
    exact hupper.trans hstep
  have hPpos : 0 < (P : ℝ) := by
    dsimp [P]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_popularDifferenceUpTo
          (visibleCanonicalDenominatorSet a N) N))
  have hKpos : 0 < (K : ℝ) := by
    dsimp [K]
    positivity
  have hMpos : 0 < (M : ℝ) := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_visibleCanonicalBlockMax a N))
  have hlogP_le :
      Real.log (P : ℝ) ≤ Real.log (M : ℝ) + Real.log (K : ℝ) := by
    calc
      Real.log (P : ℝ) ≤ Real.log ((K * M : ℕ) : ℝ) :=
        Real.log_le_log hPpos (by exact_mod_cast hP_le)
      _ = Real.log ((K : ℝ) * (M : ℝ)) := by norm_num
      _ = Real.log (K : ℝ) + Real.log (M : ℝ) := by
        rw [Real.log_mul hKpos.ne' hMpos.ne']
      _ = Real.log (M : ℝ) + Real.log (K : ℝ) := by ring
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hdiv :
      Real.log (P : ℝ) / Real.log (N : ℝ) ≤
        (Real.log (M : ℝ) + Real.log (K : ℝ)) /
          Real.log (N : ℝ) :=
    div_le_div_of_nonneg_right hlogP_le hlogNpos.le
  have hsplit :
      (Real.log (M : ℝ) + Real.log (K : ℝ)) / Real.log (N : ℝ) =
        Real.log (M : ℝ) / Real.log (N : ℝ) +
          Real.log (K : ℝ) / Real.log (N : ℝ) := by
    ring
  rw [hsplit] at hdiv
  simpa [P, M, K] using hdiv

lemma canonicalBlockExponent_le_visiblePopularDifferenceExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a ≤ visiblePopularDifferenceExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let P : ℕ → ℝ := fun N =>
    Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
      Real.log (N : ℝ)
  have hFP : F ≤ᶠ[atTop] P := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    let R : ℝ := canonicalBlockGrowth a N
    let V : ℝ :=
      popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one
          (one_le_canonicalBlockGrowth a N))
    have hRV : R ≤ V := by
      dsimp [R, V]
      exact_mod_cast canonicalBlockGrowth_le_visiblePopularDifference
        (a := a) hpos N
    have hlogRV : Real.log R ≤ Real.log V :=
      Real.log_le_log hRpos hRV
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    exact div_le_div_of_nonneg_right hlogRV hlogNpos.le
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((canonicalBlockGrowth_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [F] using hN))
  have hPbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop P :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visiblePopularDifference_ratio_le_two_eventually a]
          with N hN
        simpa [P] using hN)
  have hlim := Filter.limsup_le_limsup hFP hFcobdd hPbdd
  simpa [canonicalBlockExponent, visiblePopularDifferenceExponent, F, P] using hlim

lemma visiblePopularDifferenceExponent_le_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visiblePopularDifferenceExponent a ≤ canonicalBlockExponent a := by
  let P : ℕ → ℝ := fun N =>
    Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
      Real.log (N : ℝ)
  let M : ℕ → ℝ := fun N =>
    Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ)
  have hPcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop P :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((visiblePopularDifference_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [P] using hN))
  have hPbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop P :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visiblePopularDifference_ratio_le_two_eventually a]
          with N hN
        simpa [P] using hN)
  have hMbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop M :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleCanonicalBlockMax_ratio_le_one_eventually a]
          with N hN
        simpa [M] using hN)
  have hmain : limsup P atTop ≤ limsup M atTop := by
    rw [Filter.limsup_le_iff' hPcobdd hPbdd]
    intro C hC
    let L : ℝ := limsup M atTop
    let C₀ : ℝ := (L + C) / 2
    have hLC₀ : L < C₀ := by
      dsimp [L, C₀]
      linarith
    have hC₀C : C₀ < C := by
      dsimp [L, C₀]
      linarith
    have hgap : 0 < C - C₀ := by linarith
    have hMlt : ∀ᶠ N : ℕ in atTop, M N < C₀ :=
      Filter.eventually_lt_of_limsup_lt hLC₀ hMbdd
    have herr :
        ∀ᶠ N : ℕ in atTop,
          Real.log ((2 * Nat.log 2 N + 4 : ℕ) : ℝ) /
              Real.log (N : ℝ) < C - C₀ :=
      log_visible_popular_cover_factor_div_log_tendsto_zero.eventually
        (eventually_lt_nhds hgap)
    filter_upwards
      [log_popular_le_log_visibleBlockMax_add_log_log_error
        (a := a) hpos, hMlt, herr]
      with N hfinite hMN herrN
    have hsum : M N +
        Real.log ((2 * Nat.log 2 N + 4 : ℕ) : ℝ) /
          Real.log (N : ℝ) ≤ C := by
      nlinarith
    exact hfinite.trans hsum
  have hM_eq :
      limsup M atTop = canonicalBlockExponent a := by
    simpa [M] using
      visibleCanonicalBlockExponent_eq_canonicalBlockExponent
        (a := a) hpos
  simpa [visiblePopularDifferenceExponent, P, M, hM_eq] using hmain

theorem visiblePopularDifferenceExponent_eq_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visiblePopularDifferenceExponent a = canonicalBlockExponent a :=
  le_antisymm
    (visiblePopularDifferenceExponent_le_canonicalBlockExponent hpos)
    (canonicalBlockExponent_le_visiblePopularDifferenceExponent hpos)

lemma visibleAdditiveEnergy_ratio_nonneg_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤
        Real.log
            (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
          Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro N hN
  let E : ℕ := additiveEnergy (visibleCanonicalDenominatorSet a N)
  have hlogE_nonneg : 0 ≤ Real.log (E : ℝ) := by
    by_cases hE0 : E = 0
    · simp [hE0]
    · exact Real.log_nonneg
        (by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hE0))
  have hden_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  exact div_nonneg hlogE_nonneg hden_nonneg

lemma visibleAdditiveEnergy_ratio_le_three_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log
          (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ) ≤ 3 := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let E : ℕ := additiveEnergy (visibleCanonicalDenominatorSet a N)
  by_cases hE0 : E = 0
  · simp [E, hE0]
  · have hE_le : E ≤ N ^ 3 := by
      dsimp [E]
      exact (additiveEnergy_le_card_cube
        (visibleCanonicalDenominatorSet a N)).trans
          (Nat.pow_le_pow_left
            (visibleCanonicalDenominatorSet_card_le_cap a N) 3)
    have hEpos : 0 < (E : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hE0
    have hlog_le :
        Real.log (E : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) :=
      Real.log_le_log hEpos (by exact_mod_cast hE_le)
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hdiv :
        Real.log (E : ℝ) / Real.log (N : ℝ) ≤
          Real.log ((N ^ 3 : ℕ) : ℝ) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlog_le hlogNpos.le
    have hpowlog :
        Real.log ((N ^ 3 : ℕ) : ℝ) = 3 * Real.log (N : ℝ) := by
      norm_num [Nat.cast_pow, Real.log_pow]
    have hright :
        Real.log ((N ^ 3 : ℕ) : ℝ) / Real.log (N : ℝ) = 3 := by
      rw [hpowlog]
      field_simp [hlogNpos.ne']
    rw [hright] at hdiv
    simpa [E] using hdiv

lemma log_energy_le_three_log_visibleBlockMax_add_error
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      Real.log
          (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ)
      ≤
      3 * (Real.log (visibleCanonicalBlockMax a N : ℝ) /
          Real.log (N : ℝ)) +
      3 * (Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
          Real.log (N : ℝ)) := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let E : ℕ := additiveEnergy (visibleCanonicalDenominatorSet a N)
  let M : ℕ := visibleCanonicalBlockMax a N
  let K : ℕ := 2 * Nat.log 2 N + 3
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hKpos : 0 < (K : ℝ) := by
    dsimp [K]
    positivity
  have hMpos : 0 < (M : ℝ) := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_visibleCanonicalBlockMax a N))
  have hRHS_nonneg :
      0 ≤
        3 * (Real.log (M : ℝ) / Real.log (N : ℝ)) +
        3 * (Real.log (K : ℝ) / Real.log (N : ℝ)) := by
    have hlogM_nonneg : 0 ≤ Real.log (M : ℝ) :=
      Real.log_nonneg (by
        dsimp [M]
        exact_mod_cast one_le_visibleCanonicalBlockMax a N)
    have hlogK_nonneg : 0 ≤ Real.log (K : ℝ) :=
      Real.log_nonneg (by
        have hKge : 1 ≤ K := by
          dsimp [K]
          omega
        exact_mod_cast hKge)
    positivity
  by_cases hE0 : E = 0
  · have hleft : Real.log (E : ℝ) / Real.log (N : ℝ) = 0 := by
      simp [hE0]
    rw [hleft]
    exact hRHS_nonneg
  · have hupper : E ≤ (K * M) ^ 3 := by
      dsimp [E, K, M]
      exact (visibleCanonical_additive_upper_bridge
        (a := a) hpos N).2.1
    have hEpos : 0 < (E : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hE0
    have hlogE_le :
        Real.log (E : ℝ) ≤ Real.log (((K * M) ^ 3 : ℕ) : ℝ) :=
      Real.log_le_log hEpos (by exact_mod_cast hupper)
    have hlogE_le_pow :
        Real.log (E : ℝ) ≤
          3 * Real.log ((K : ℝ) * (M : ℝ)) := by
      simpa [Nat.cast_pow, Nat.cast_mul, Real.log_pow] using hlogE_le
    have hlog_mul :
        Real.log ((K : ℝ) * (M : ℝ)) =
          Real.log (K : ℝ) + Real.log (M : ℝ) := by
      rw [Real.log_mul hKpos.ne' hMpos.ne']
    have hlogE_le' :
        Real.log (E : ℝ) ≤
          3 * (Real.log (K : ℝ) + Real.log (M : ℝ)) := by
      nlinarith
    have hdiv :
        Real.log (E : ℝ) / Real.log (N : ℝ) ≤
          (3 * (Real.log (K : ℝ) + Real.log (M : ℝ))) /
            Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogE_le' hlogNpos.le
    have hsplit :
        (3 * (Real.log (K : ℝ) + Real.log (M : ℝ))) /
            Real.log (N : ℝ) =
          3 * (Real.log (M : ℝ) / Real.log (N : ℝ)) +
          3 * (Real.log (K : ℝ) / Real.log (N : ℝ)) := by
      ring
    rw [hsplit] at hdiv
    simpa [E, M, K, add_comm, add_left_comm, add_assoc] using hdiv

lemma visibleAdditiveEnergyExponent_le_three_mul_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleAdditiveEnergyExponent a ≤ 3 * canonicalBlockExponent a := by
  let E : ℕ → ℝ := fun N =>
    Real.log
        (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
      Real.log (N : ℝ)
  let M : ℕ → ℝ := fun N =>
    Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ)
  have hEcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop E :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((visibleAdditiveEnergy_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [E] using hN))
  have hEbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop E :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleAdditiveEnergy_ratio_le_three_eventually a]
          with N hN
        simpa [E] using hN)
  have hMbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop M :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleCanonicalBlockMax_ratio_le_one_eventually a]
          with N hN
        simpa [M] using hN)
  have hM_eq :
      limsup M atTop = canonicalBlockExponent a := by
    simpa [M] using
      visibleCanonicalBlockExponent_eq_canonicalBlockExponent
        (a := a) hpos
  rw [← hM_eq]
  have hmain : limsup E atTop ≤ 3 * limsup M atTop := by
    rw [Filter.limsup_le_iff' hEcobdd hEbdd]
    intro C hC
    let L : ℝ := limsup M atTop
    let C₀ : ℝ := (L + C / 3) / 2
    have hLltCdiv : L < C / 3 := by
      nlinarith
    have hLC₀ : L < C₀ := by
      dsimp [C₀]
      nlinarith
    have h3C₀C : 3 * C₀ < C := by
      dsimp [C₀]
      nlinarith
    have hgap : 0 < (C - 3 * C₀) / 3 := by
      nlinarith
    have hMlt : ∀ᶠ N : ℕ in atTop, M N < C₀ :=
      Filter.eventually_lt_of_limsup_lt hLC₀ hMbdd
    have herr :
        ∀ᶠ N : ℕ in atTop,
          Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
              Real.log (N : ℝ) < (C - 3 * C₀) / 3 :=
      log_visible_energy_cover_factor_div_log_tendsto_zero.eventually
        (eventually_lt_nhds hgap)
    filter_upwards
      [log_energy_le_three_log_visibleBlockMax_add_error
        (a := a) hpos, hMlt, herr]
      with N hfinite hMN herrN
    have hsum :
        3 * M N +
          3 * (Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
            Real.log (N : ℝ)) ≤ C := by
      nlinarith
    exact hfinite.trans hsum
  simpa [visibleAdditiveEnergyExponent, E, M] using hmain

lemma three_log_canonicalBlockGrowth_sub_log_two_le_log_visibleEnergy
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      3 * (Real.log (canonicalBlockGrowth a N : ℝ) /
          Real.log (N : ℝ)) -
        Real.log 2 / Real.log (N : ℝ)
      ≤
      Real.log
          (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let R : ℕ := canonicalBlockGrowth a N
  let E : ℕ := additiveEnergy (visibleCanonicalDenominatorSet a N)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hElog_nonneg : 0 ≤ Real.log (E : ℝ) := by
    by_cases hE0 : E = 0
    · simp [hE0]
    · exact Real.log_nonneg
        (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hE0))
  have hEratio_nonneg :
      0 ≤ Real.log (E : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hElog_nonneg hlogNpos.le
  by_cases hRone : R = 1
  · have hlogR : Real.log (R : ℝ) = 0 := by
      rw [hRone]
      norm_num
    have hleft_nonpos :
        3 * (Real.log (R : ℝ) / Real.log (N : ℝ)) -
          Real.log 2 / Real.log (N : ℝ) ≤ 0 := by
      have hconst_nonneg :
          0 ≤ Real.log 2 / Real.log (N : ℝ) := by
        exact div_nonneg (Real.log_nonneg (by norm_num)) hlogNpos.le
      rw [hlogR]
      simp only [zero_div, mul_zero, zero_sub]
      exact neg_nonpos.mpr hconst_nonneg
    exact hleft_nonpos.trans hEratio_nonneg
  · have hRgt1 : 1 < R := by
      have hRge : 1 ≤ R := by
        dsimp [R]
        exact one_le_canonicalBlockGrowth a N
      omega
    rcases canonicalBlockGrowth_eq_one_or_exists_visible_le_safe a N with
      hRone' | ⟨j, _hj, hden, hRleSafe⟩
    · exact False.elim (hRone (by simpa [R] using hRone'))
    · have hsafe_gt : 1 < canonicalSafeBlockLength a j :=
        lt_of_lt_of_le hRgt1 hRleSafe
      have hsafe_le_len :
          canonicalSafeBlockLength a j ≤ canonicalBlockLength a j := by
        unfold canonicalSafeBlockLength at hsafe_gt ⊢
        omega
      have hRleLen : R ≤ canonicalBlockLength a j :=
        hRleSafe.trans hsafe_le_len
      have hbridge :
          (canonicalBlockLength a j) ^ 3 ≤ 2 * E := by
        dsimp [E]
        exact (fullCanonicalBlock_additive_lower_bridge
          (a := a) hpos (N := N) (j := j) hden).2.1
      have hRpow_le : R ^ 3 ≤ 2 * E :=
        (Nat.pow_le_pow_left hRleLen 3).trans hbridge
      have hRpos_nat : 0 < R := lt_trans Nat.zero_lt_one hRgt1
      have hRpow_pos : 0 < R ^ 3 := pow_pos hRpos_nat 3
      have hEpos_nat : 0 < E := by
        have h2Epos : 0 < 2 * E := lt_of_lt_of_le hRpow_pos hRpow_le
        omega
      have hRpos : 0 < (R : ℝ) := by exact_mod_cast hRpos_nat
      have hEpos : 0 < (E : ℝ) := by exact_mod_cast hEpos_nat
      have hlog_le :
          Real.log ((R ^ 3 : ℕ) : ℝ) ≤ Real.log ((2 * E : ℕ) : ℝ) :=
        Real.log_le_log
          (by exact_mod_cast hRpow_pos)
          (by exact_mod_cast hRpow_le)
      have hlogRpow :
          Real.log ((R ^ 3 : ℕ) : ℝ) = 3 * Real.log (R : ℝ) := by
        norm_num [Nat.cast_pow, Real.log_pow]
      have hlog2E :
          Real.log ((2 * E : ℕ) : ℝ) =
            Real.log 2 + Real.log (E : ℝ) := by
        norm_num [Nat.cast_mul]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hEpos.ne']
      have hineq :
          3 * Real.log (R : ℝ) ≤ Real.log 2 + Real.log (E : ℝ) := by
        nlinarith
      have hdiv :
          (3 * Real.log (R : ℝ)) / Real.log (N : ℝ) ≤
            (Real.log 2 + Real.log (E : ℝ)) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hineq hlogNpos.le
      have hsplit :
          (Real.log 2 + Real.log (E : ℝ)) / Real.log (N : ℝ) =
            Real.log 2 / Real.log (N : ℝ) +
              Real.log (E : ℝ) / Real.log (N : ℝ) := by
        ring
      rw [hsplit] at hdiv
      have hgoal_local :
          3 * (Real.log (R : ℝ) / Real.log (N : ℝ)) -
            Real.log 2 / Real.log (N : ℝ) ≤
          Real.log (E : ℝ) / Real.log (N : ℝ) := by
        have hthree :
            3 * (Real.log (R : ℝ) / Real.log (N : ℝ)) =
              (3 * Real.log (R : ℝ)) / Real.log (N : ℝ) := by
          ring
        rw [hthree]
        nlinarith
      simpa [R, E] using hgoal_local

lemma three_mul_canonicalBlockExponent_le_visibleAdditiveEnergyExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    3 * canonicalBlockExponent a ≤ visibleAdditiveEnergyExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let E : ℕ → ℝ := fun N =>
    Real.log
        (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
      Real.log (N : ℝ)
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((canonicalBlockGrowth_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [F] using hN))
  have hEbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop E :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleAdditiveEnergy_ratio_le_three_eventually a]
          with N hN
        simpa [E] using hN)
  rw [canonicalBlockExponent]
  refine le_of_forall_lt ?_
  intro C hC
  let L : ℝ := limsup F atTop
  let C₀ : ℝ := (C / 3 + L) / 2
  have hCdivL : C / 3 < L := by
    dsimp [L]
    nlinarith
  have hC₀L : C₀ < L := by
    dsimp [C₀]
    nlinarith
  have hC_lt_3C₀ : C < 3 * C₀ := by
    dsimp [C₀]
    nlinarith
  let D : ℝ := (C + 3 * C₀) / 2
  have hCD : C < D := by
    dsimp [D]
    nlinarith
  have hDlt : D < 3 * C₀ := by
    dsimp [D]
    nlinarith
  have hgap : 0 < 3 * C₀ - D := by nlinarith
  have hfreqF : ∃ᶠ N : ℕ in atTop, C₀ < F N :=
    Filter.frequently_lt_of_lt_limsup hFcobdd (by simpa [L] using hC₀L)
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log 2 / Real.log (N : ℝ) < 3 * C₀ - D :=
    (log_const_over_log_nat_tendsto_zero (Real.log 2)).eventually
      (eventually_lt_nhds hgap)
  have hlower :=
    three_log_canonicalBlockGrowth_sub_log_two_le_log_visibleEnergy
      (a := a) hpos
  have hfreqE : ∃ᶠ N : ℕ in atTop, D ≤ E N :=
    (hfreqF.and_eventually (hsmall.and hlower)).mono (fun N hN => by
      rcases hN with ⟨hFN, hsmallN, hlowerN⟩
      have hcalc : D ≤ 3 * F N - Real.log 2 / Real.log (N : ℝ) := by
        nlinarith
      exact hcalc.trans (by simpa [F, E] using hlowerN))
  exact (lt_of_lt_of_le hCD
    (Filter.le_limsup_of_frequently_le hfreqE hEbdd))

theorem visibleAdditiveEnergyExponent_eq_three_mul_canonicalBlockExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleAdditiveEnergyExponent a = 3 * canonicalBlockExponent a :=
  le_antisymm
    (visibleAdditiveEnergyExponent_le_three_mul_canonicalBlockExponent hpos)
    (three_mul_canonicalBlockExponent_le_visibleAdditiveEnergyExponent hpos)

lemma properHilbertCubeDimension_ge_of_hasProperHilbertCube
    {S : Finset ℕ} {h : ℕ}
    (hh : HasProperHilbertCube S h) :
    h ≤ properHilbertCubeDimension S := by
  classical
  have hcard_pow : 2 ^ h ≤ S.card :=
    two_pow_le_card_of_hasProperHilbertCube hh
  have hle_pow : h ≤ 2 ^ h :=
    Nat.le_of_lt h.lt_two_pow_self
  have hcard : h ≤ S.card := hle_pow.trans hcard_pow
  have hmem : h ∈ Finset.range (S.card + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)
  unfold properHilbertCubeDimension
  calc
    h = (if HasProperHilbertCube S h then h else 0) := by simp [hh]
    _ ≤ (Finset.range (S.card + 1)).sup
        (fun k : ℕ => if HasProperHilbertCube S k then k else 0) :=
      Finset.le_sup
        (s := Finset.range (S.card + 1))
        (f := fun k : ℕ => if HasProperHilbertCube S k then k else 0)
        hmem

lemma hasProperHilbertCube_properHilbertCubeDimension_of_pos
    {S : Finset ℕ}
    (hposdim : 0 < properHilbertCubeDimension S) :
    HasProperHilbertCube S (properHilbertCubeDimension S) := by
  classical
  let I : Finset ℕ := Finset.range (S.card + 1)
  let f : ℕ → ℕ := fun h : ℕ =>
    if HasProperHilbertCube S h then h else 0
  have hIne : I.Nonempty := ⟨0, by simp [I]⟩
  rcases Finset.exists_mem_eq_sup I hIne f with ⟨h, _hmem, hsup⟩
  have hfpos : 0 < f h := by
    have hdim_eq : properHilbertCubeDimension S = I.sup f := by
      simp [properHilbertCubeDimension, I, f]
    rw [hdim_eq, hsup] at hposdim
    exact hposdim
  have hcube : HasProperHilbertCube S h := by
    by_contra hnot
    have hfzero : f h = 0 := by simp [f, hnot]
    omega
  have hfh : f h = h := by simp [f, hcube]
  have hdim_eq : properHilbertCubeDimension S = h := by
    calc
      properHilbertCubeDimension S = I.sup f := by
        simp [properHilbertCubeDimension, I, f]
      _ = f h := hsup
      _ = h := hfh
  simpa [hdim_eq] using hcube

lemma two_pow_properHilbertCubeDimension_le_cover
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (N : ℕ) :
    2 ^ properHilbertCubeDimension
          (visibleCanonicalDenominatorSet a N)
      ≤
    (2 * Nat.log 2 N + 3) * visibleCanonicalBlockMax a N := by
  let S : Finset ℕ := visibleCanonicalDenominatorSet a N
  let H : ℕ := properHilbertCubeDimension S
  by_cases hH0 : H = 0
  · have hM1 : 1 ≤ visibleCanonicalBlockMax a N :=
      one_le_visibleCanonicalBlockMax a N
    rw [show properHilbertCubeDimension
        (visibleCanonicalDenominatorSet a N) = 0 by simpa [S, H] using hH0]
    simp only [pow_zero]
    exact Nat.succ_le_of_lt
      (Nat.mul_pos (by omega)
        (lt_of_lt_of_le Nat.zero_lt_one hM1))
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH0
    have hcube : HasProperHilbertCube S H :=
      hasProperHilbertCube_properHilbertCubeDimension_of_pos
        (S := S) hHpos
    have hupper :=
      (visibleCanonical_additive_upper_bridge (a := a) hpos N).2.2 H
    simpa [S, H] using hupper hcube

lemma natLog_two_canonicalBlockLength_le_visibleHilbertCubeDimension
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    {N j : ℕ}
    (hjN : continuantDen a (j + 1) ≤ N) :
    Nat.log 2 (canonicalBlockLength a j)
      ≤
    properHilbertCubeDimension
      (visibleCanonicalDenominatorSet a N) := by
  by_cases hm0 : canonicalBlockLength a j = 0
  · simp [hm0]
  · have hpow :
        2 ^ Nat.log 2 (canonicalBlockLength a j)
          ≤ canonicalBlockLength a j :=
      Nat.pow_log_le_self 2 hm0
    have hcube :
        HasProperHilbertCube
          (visibleCanonicalDenominatorSet a N)
          (Nat.log 2 (canonicalBlockLength a j)) :=
      (fullCanonicalBlock_additive_lower_bridge
        (a := a) hpos (N := N) (j := j) hjN).2.2
        (Nat.log 2 (canonicalBlockLength a j)) hpow
    exact properHilbertCubeDimension_ge_of_hasProperHilbertCube hcube

lemma real_log_le_succ_natLog_mul_log_two
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log (m : ℝ)
      ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hpow_lt : m < 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two m
  have hlog_le :
      Real.log (m : ℝ) ≤
        Real.log ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℝ) :=
    Real.log_le_log hmpos (by exact_mod_cast (le_of_lt hpow_lt))
  have hpowlog :
      Real.log ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℝ) =
        ((Nat.log 2 m + 1 : ℕ) : ℝ) * Real.log 2 := by
    norm_num [Nat.cast_pow, Real.log_pow]
  exact hlog_le.trans_eq hpowlog

lemma hilbertDimension_ratio_le_visibleBlockMax_ratio_div_log_two_add_error
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      (properHilbertCubeDimension
          (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ)
      ≤
      (Real.log (visibleCanonicalBlockMax a N : ℝ) /
          Real.log (N : ℝ) +
        Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
          Real.log (N : ℝ)) /
        Real.log 2 := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let H : ℕ := properHilbertCubeDimension
    (visibleCanonicalDenominatorSet a N)
  let M : ℕ := visibleCanonicalBlockMax a N
  let K : ℕ := 2 * Nat.log 2 N + 3
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hKpos : 0 < (K : ℝ) := by
    dsimp [K]
    positivity
  have hMpos : 0 < (M : ℝ) := by
    dsimp [M]
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (one_le_visibleCanonicalBlockMax a N))
  have hpow :
      2 ^ H ≤ K * M := by
    dsimp [H, K, M]
    exact two_pow_properHilbertCubeDimension_le_cover
      (a := a) hpos N
  have hpowpos : 0 < ((2 ^ H : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < 2) H)
  have hlog_le :
      Real.log ((2 ^ H : ℕ) : ℝ) ≤ Real.log ((K * M : ℕ) : ℝ) :=
    Real.log_le_log hpowpos (by exact_mod_cast hpow)
  have hlog_pow :
      Real.log ((2 ^ H : ℕ) : ℝ) = (H : ℝ) * Real.log 2 := by
    norm_num [Nat.cast_pow, Real.log_pow]
  have hlog_mul :
      Real.log ((K * M : ℕ) : ℝ) =
        Real.log (K : ℝ) + Real.log (M : ℝ) := by
    norm_num [Nat.cast_mul]
    rw [Real.log_mul hKpos.ne' hMpos.ne']
  have hmul_le :
      (H : ℝ) * Real.log 2 ≤
        Real.log (K : ℝ) + Real.log (M : ℝ) := by
    calc
      (H : ℝ) * Real.log 2 =
          Real.log ((2 ^ H : ℕ) : ℝ) := by rw [hlog_pow]
      _ ≤ Real.log ((K * M : ℕ) : ℝ) := hlog_le
      _ = Real.log (K : ℝ) + Real.log (M : ℝ) := hlog_mul
  have hdiv1 :
      (H : ℝ) ≤
        (Real.log (K : ℝ) + Real.log (M : ℝ)) / Real.log 2 := by
    exact (le_div_iff₀ hlog2pos).2 hmul_le
  have hdiv2 :
      (H : ℝ) / Real.log (N : ℝ) ≤
        ((Real.log (K : ℝ) + Real.log (M : ℝ)) / Real.log 2) /
          Real.log (N : ℝ) :=
    div_le_div_of_nonneg_right hdiv1 hlogNpos.le
  have hrewrite :
      ((Real.log (K : ℝ) + Real.log (M : ℝ)) / Real.log 2) /
          Real.log (N : ℝ) =
        (Real.log (M : ℝ) / Real.log (N : ℝ) +
          Real.log (K : ℝ) / Real.log (N : ℝ)) /
          Real.log 2 := by
    field_simp [hlog2pos.ne', hlogNpos.ne']
    ring
  rw [hrewrite] at hdiv2
  simpa [H, M, K] using hdiv2

lemma visibleHilbertCube_ratio_nonneg_eventually
    (a : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤
        (properHilbertCubeDimension
            (visibleCanonicalDenominatorSet a N) : ℝ) /
          Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 1).mono ?_
  intro N hN
  exact div_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast hN))

lemma visibleHilbertCube_ratio_le_two_div_log_two_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      (properHilbertCubeDimension
          (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ)
      ≤ 2 / Real.log 2 := by
  have herr :
      ∀ᶠ N : ℕ in atTop,
        Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
            Real.log (N : ℝ) < 1 :=
    log_visible_energy_cover_factor_div_log_tendsto_zero.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [hilbertDimension_ratio_le_visibleBlockMax_ratio_div_log_two_add_error
      (a := a) hpos,
      visibleCanonicalBlockMax_ratio_le_one_eventually a,
      herr]
    with N hfinite hM herrN
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum :
      (Real.log (visibleCanonicalBlockMax a N : ℝ) /
          Real.log (N : ℝ) +
        Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
          Real.log (N : ℝ)) /
        Real.log 2 ≤ 2 / Real.log 2 := by
    gcongr
    linarith
  exact hfinite.trans hsum

lemma visibleHilbertCubeExponent_le_canonicalBlockExponent_div_log_two
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleHilbertCubeExponent a
      ≤ canonicalBlockExponent a / Real.log 2 := by
  let H : ℕ → ℝ := fun N =>
    (properHilbertCubeDimension
        (visibleCanonicalDenominatorSet a N) : ℝ) /
      Real.log (N : ℝ)
  let M : ℕ → ℝ := fun N =>
    Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ)
  have hHcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop H :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((visibleHilbertCube_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [H] using hN))
  have hHbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop H :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards
          [visibleHilbertCube_ratio_le_two_div_log_two_eventually
            (a := a) hpos]
          with N hN
        simpa [H] using hN)
  have hMbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop M :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards [visibleCanonicalBlockMax_ratio_le_one_eventually a]
          with N hN
        simpa [M] using hN)
  have hM_eq :
      limsup M atTop = canonicalBlockExponent a := by
    simpa [M] using
      visibleCanonicalBlockExponent_eq_canonicalBlockExponent
        (a := a) hpos
  rw [← hM_eq]
  have hmain : limsup H atTop ≤ limsup M atTop / Real.log 2 := by
    rw [Filter.limsup_le_iff' hHcobdd hHbdd]
    intro C hC
    let L : ℝ := limsup M atTop
    let C₀ : ℝ := (L + C * Real.log 2) / 2
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLltClog : L < C * Real.log 2 := by
      have hmul := mul_lt_mul_of_pos_right hC hlog2pos
      field_simp [hlog2pos.ne'] at hmul
      simpa [L, mul_comm] using hmul
    have hLC₀ : L < C₀ := by
      dsimp [C₀]
      nlinarith
    have hC₀lt : C₀ < C * Real.log 2 := by
      dsimp [C₀]
      nlinarith
    have hgap : 0 < C * Real.log 2 - C₀ := by
      nlinarith
    have hMlt : ∀ᶠ N : ℕ in atTop, M N < C₀ :=
      Filter.eventually_lt_of_limsup_lt hLC₀ hMbdd
    have herr :
        ∀ᶠ N : ℕ in atTop,
          Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
              Real.log (N : ℝ) < C * Real.log 2 - C₀ :=
      log_visible_energy_cover_factor_div_log_tendsto_zero.eventually
        (eventually_lt_nhds hgap)
    filter_upwards
      [hilbertDimension_ratio_le_visibleBlockMax_ratio_div_log_two_add_error
        (a := a) hpos, hMlt, herr]
      with N hfinite hMN herrN
    have hsum :
        (M N +
          Real.log ((2 * Nat.log 2 N + 3 : ℕ) : ℝ) /
            Real.log (N : ℝ)) /
          Real.log 2 ≤ C := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith
    exact hfinite.trans (by simpa [M] using hsum)
  simpa [visibleHilbertCubeExponent, H, M] using hmain

lemma log_canonicalBlockGrowth_div_log_two_sub_inv_log_le_hilbertDimension
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ N : ℕ in atTop,
      (Real.log (canonicalBlockGrowth a N : ℝ) /
          Real.log (N : ℝ)) / Real.log 2 -
        1 / Real.log (N : ℝ)
      ≤
      (properHilbertCubeDimension
          (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ) := by
  refine (eventually_ge_atTop 2).mono ?_
  intro N hN
  let R : ℕ := canonicalBlockGrowth a N
  let H : ℕ := properHilbertCubeDimension
    (visibleCanonicalDenominatorSet a N)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hHratio_nonneg : 0 ≤ (H : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (by positivity) hlogNpos.le
  by_cases hRone : R = 1
  · have hlogR : Real.log (R : ℝ) = 0 := by
      rw [hRone]
      norm_num
    have hleft_nonpos :
        (Real.log (R : ℝ) / Real.log (N : ℝ)) / Real.log 2 -
          1 / Real.log (N : ℝ) ≤ 0 := by
      have hinv_nonneg : 0 ≤ 1 / Real.log (N : ℝ) := by positivity
      rw [hlogR]
      simp only [zero_div, sub_nonpos]
      exact hinv_nonneg
    exact hleft_nonpos.trans hHratio_nonneg
  · have hRgt1 : 1 < R := by
      have hRge : 1 ≤ R := by
        dsimp [R]
        exact one_le_canonicalBlockGrowth a N
      omega
    rcases canonicalBlockGrowth_eq_one_or_exists_visible_le_safe a N with
      hRone' | ⟨j, _hj, hden, hRleSafe⟩
    · exact False.elim (hRone (by simpa [R] using hRone'))
    · have hsafe_gt : 1 < canonicalSafeBlockLength a j :=
        lt_of_lt_of_le hRgt1 hRleSafe
      have hsafe_le_len :
          canonicalSafeBlockLength a j ≤ canonicalBlockLength a j := by
        unfold canonicalSafeBlockLength at hsafe_gt ⊢
        omega
      have hRleLen : R ≤ canonicalBlockLength a j :=
        hRleSafe.trans hsafe_le_len
      have hlen_ge : 1 ≤ canonicalBlockLength a j := by
        exact (le_of_lt hRgt1).trans hRleLen
      have hnatLog_le_H :
          Nat.log 2 (canonicalBlockLength a j) ≤ H := by
        dsimp [H]
        exact natLog_two_canonicalBlockLength_le_visibleHilbertCubeDimension
          (a := a) hpos (N := N) (j := j) hden
      have hRpos : 0 < (R : ℝ) := by
        exact_mod_cast (lt_trans Nat.zero_lt_one hRgt1)
      have hlogR_le_len :
          Real.log (R : ℝ) ≤
            Real.log (canonicalBlockLength a j : ℝ) :=
        Real.log_le_log hRpos (by exact_mod_cast hRleLen)
      have hlog_len_le :
          Real.log (canonicalBlockLength a j : ℝ) ≤
            ((Nat.log 2 (canonicalBlockLength a j) + 1 : ℕ) : ℝ) *
              Real.log 2 :=
        real_log_le_succ_natLog_mul_log_two hlen_ge
      have hnat_succ_le :
          ((Nat.log 2 (canonicalBlockLength a j) + 1 : ℕ) : ℝ)
            ≤ (H : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ hnatLog_le_H
      have hlogR_le_H :
          Real.log (R : ℝ) ≤ ((H : ℝ) + 1) * Real.log 2 := by
        calc
          Real.log (R : ℝ) ≤
              Real.log (canonicalBlockLength a j : ℝ) := hlogR_le_len
          _ ≤ ((Nat.log 2 (canonicalBlockLength a j) + 1 : ℕ) : ℝ) *
              Real.log 2 := hlog_len_le
          _ ≤ ((H : ℝ) + 1) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hnat_succ_le hlog2pos.le
      have hdiv_log2 :
          Real.log (R : ℝ) / Real.log 2 ≤ (H : ℝ) + 1 := by
        exact (div_le_iff₀ hlog2pos).2 hlogR_le_H
      have hdivN :
          (Real.log (R : ℝ) / Real.log 2) /
              Real.log (N : ℝ) ≤
            ((H : ℝ) + 1) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hdiv_log2 hlogNpos.le
      have hswap :
          (Real.log (R : ℝ) / Real.log (N : ℝ)) / Real.log 2 =
            (Real.log (R : ℝ) / Real.log 2) /
              Real.log (N : ℝ) := by
        field_simp [hlog2pos.ne', hlogNpos.ne']
      rw [hswap]
      have hgoal :
          (Real.log (R : ℝ) / Real.log 2) / Real.log (N : ℝ) -
              1 / Real.log (N : ℝ) ≤
            (H : ℝ) / Real.log (N : ℝ) := by
        calc
          (Real.log (R : ℝ) / Real.log 2) / Real.log (N : ℝ) -
              1 / Real.log (N : ℝ)
              ≤ ((H : ℝ) + 1) / Real.log (N : ℝ) -
                  1 / Real.log (N : ℝ) :=
            sub_le_sub_right hdivN _
          _ = (H : ℝ) / Real.log (N : ℝ) := by ring
      exact hgoal

lemma canonicalBlockExponent_div_log_two_le_visibleHilbertCubeExponent
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    canonicalBlockExponent a / Real.log 2
      ≤ visibleHilbertCubeExponent a := by
  let F : ℕ → ℝ := fun N =>
    Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ)
  let H : ℕ → ℝ := fun N =>
    (properHilbertCubeDimension
        (visibleCanonicalDenominatorSet a N) : ℝ) /
      Real.log (N : ℝ)
  have hFcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop F :=
    Filter.IsCoboundedUnder.of_frequently_ge
      ((canonicalBlockGrowth_ratio_nonneg_eventually a).frequently.mono
        (fun N hN => by simpa [F] using hN))
  have hHbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop H :=
    Filter.isBoundedUnder_of_eventually_le
      (by
        filter_upwards
          [visibleHilbertCube_ratio_le_two_div_log_two_eventually
            (a := a) hpos]
          with N hN
        simpa [H] using hN)
  refine le_of_forall_lt ?_
  intro C hC
  let L : ℝ := limsup F atTop
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC' : C < L / Real.log 2 := by
    simpa [canonicalBlockExponent, F, L] using hC
  have hCLog_lt_L : C * Real.log 2 < L := by
    have hmul := mul_lt_mul_of_pos_right hC' hlog2pos
    field_simp [hlog2pos.ne'] at hmul
    simpa [L, mul_comm] using hmul
  let C₀ : ℝ := (C * Real.log 2 + L) / 2
  have hCLog_C₀ : C * Real.log 2 < C₀ := by
    dsimp [C₀]
    nlinarith
  have hC₀L : C₀ < L := by
    dsimp [C₀]
    nlinarith
  have hC_lt_C₀div : C < C₀ / Real.log 2 := by
    rw [lt_div_iff₀ hlog2pos]
    exact hCLog_C₀
  let D : ℝ := (C + C₀ / Real.log 2) / 2
  have hCD : C < D := by
    dsimp [D]
    nlinarith
  have hDlt : D < C₀ / Real.log 2 := by
    dsimp [D]
    nlinarith
  have hgap : 0 < C₀ / Real.log 2 - D := by
    nlinarith
  have hfreqF : ∃ᶠ N : ℕ in atTop, C₀ < F N :=
    Filter.frequently_lt_of_lt_limsup hFcobdd
      (by simpa [L] using hC₀L)
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        1 / Real.log (N : ℝ) < C₀ / Real.log 2 - D :=
    (log_const_over_log_nat_tendsto_zero 1).eventually
      (eventually_lt_nhds hgap)
  have hlower :=
    log_canonicalBlockGrowth_div_log_two_sub_inv_log_le_hilbertDimension
      (a := a) hpos
  have hfreqH : ∃ᶠ N : ℕ in atTop, D ≤ H N :=
    (hfreqF.and_eventually (hsmall.and hlower)).mono (fun N hN => by
      rcases hN with ⟨hFN, hsmallN, hlowerN⟩
      have hFNdiv : C₀ / Real.log 2 < F N / Real.log 2 :=
        div_lt_div_of_pos_right hFN hlog2pos
      have hcalc : D ≤ F N / Real.log 2 -
          1 / Real.log (N : ℝ) := by
        nlinarith
      exact hcalc.trans (by simpa [F, H] using hlowerN))
  exact lt_of_lt_of_le hCD
    (Filter.le_limsup_of_frequently_le hfreqH hHbdd)

theorem visibleHilbertCubeExponent_eq_canonicalBlockExponent_div_log_two
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    visibleHilbertCubeExponent a =
      canonicalBlockExponent a / Real.log 2 := by
  exact le_antisymm
    (visibleHilbertCubeExponent_le_canonicalBlockExponent_div_log_two hpos)
    (canonicalBlockExponent_div_log_two_le_visibleHilbertCubeExponent hpos)

/-- For Euler-pattern coefficients, the canonical block growth is
sub-polynomial: `log R(N) / log N → 0`. -/
theorem euler_canonicalBlockGrowth_log_ratio_tendsto_zero
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    Tendsto
      (fun N : ℕ =>
        Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?hnonneg ?hle tendsto_euler_block_log_bound
  · refine eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro N hN
    have hRge : 1 ≤ canonicalBlockGrowth a N := one_le_canonicalBlockGrowth a N
    have hnum_nonneg : 0 ≤ Real.log (canonicalBlockGrowth a N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hRge)
    have hden_nonneg : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hN)
    exact div_nonneg hnum_nonneg hden_nonneg
  · refine eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro N hN
    let B : ℕ := 2 * (2 * Nat.log 2 N + 3)
    have hRleN : canonicalBlockGrowth a N ≤ B := by
      dsimp [B]
      exact canonicalBlockGrowth_le_euler_log_bound he N
    have hRpos : 0 < (canonicalBlockGrowth a N : ℝ) := by
      exact_mod_cast
        lt_of_lt_of_le (by norm_num : 0 < 1) (one_le_canonicalBlockGrowth a N)
    have hBlogpos : 0 < (B : ℝ) := by
      dsimp [B]
      positivity
    have hlogR_le_logB :
        Real.log (canonicalBlockGrowth a N : ℝ) ≤ Real.log (B : ℝ) := by
      exact Real.log_le_log hRpos (by exact_mod_cast hRleN)
    have hlogNpos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hN)
    have hratio1 :
        Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ) ≤
          Real.log (B : ℝ) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogR_le_logB hlogNpos.le
    have hnatlog_le :
        ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
      simpa [Real.log_div_log] using (Real.natLog_le_logb N 2)
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmul4 :
        4 * ((Nat.log 2 N : ℕ) : ℝ) ≤
          4 * (Real.log (N : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hnatlog_le (by norm_num)
    have hrewrite :
        4 * (Real.log (N : ℝ) / Real.log 2) + 6 =
          (4 / Real.log 2) * Real.log (N : ℝ) + 6 := by
      field_simp [hlog2pos.ne']
    have hB_le :
        (B : ℝ) ≤ (4 / Real.log 2) * Real.log (N : ℝ) + 6 := by
      have hB_le' : (B : ℝ) ≤ 4 * (Real.log (N : ℝ) / Real.log 2) + 6 := by
        dsimp [B]
        norm_num
        nlinarith
      exact hB_le'.trans_eq hrewrite
    have hlogB_le :
        Real.log (B : ℝ) ≤
          Real.log ((4 / Real.log 2) * Real.log (N : ℝ) + 6) :=
      Real.log_le_log hBlogpos hB_le
    have hratio2 :
        Real.log (B : ℝ) / Real.log (N : ℝ) ≤
          Real.log ((4 / Real.log 2) * Real.log (N : ℝ) + 6) /
            Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlogB_le hlogNpos.le
    exact hratio1.trans hratio2

theorem canonicalBlockExponent_eq_zero_of_eulerPartialQuotients
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    canonicalBlockExponent a = 0 := by
  unfold canonicalBlockExponent
  exact (euler_canonicalBlockGrowth_log_ratio_tendsto_zero he).limsup_eq

private lemma tendsto_euler_log_squeeze_bound :
    Tendsto
      (fun j : ℕ =>
        (12 / Real.log 2) *
          (Real.log (2 * ((j : ℝ) + 2)) / (2 * ((j : ℝ) + 2))))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    tendsto_log_div_self_atTop
  have hx : Tendsto (fun j : ℕ => 2 * ((j : ℝ) + 2)) atTop atTop := by
    have hj : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
    simpa [mul_comm] using hj.atTop_mul_const (by norm_num : (0 : ℝ) < 2)
  have h := (hlog.comp hx).const_mul (12 / Real.log 2)
  simpa [Function.comp_def] using h

/-- Euler's linear partial quotients and exponential denominator growth force
`log a_{j+1} / log q_j → 0`. -/
theorem euler_log_partialQuotient_div_log_continuantDen_tendsto_zero
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    Tendsto
      (fun j : ℕ =>
        Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a j : ℝ))
      atTop (𝓝 0) := by
  have hpos : ∀ n : ℕ, 0 < a (n + 1) := eulerPartialQuotients_pos_succ he
  have hlin : ∀ n : ℕ, a n ≤ 2 * (n + 1) := eulerPartialQuotients_linear_bound he
  have hpow : ∀ n : ℕ, 2 ^ (n / 2) ≤ continuantDen a n :=
    pow_two_half_le_continuantDen_of_partials_pos a hpos
  refine squeeze_zero' ?hnonneg ?hle tendsto_euler_log_squeeze_bound
  · refine eventually_atTop.2 ?_
    refine ⟨4, ?_⟩
    intro j hj
    have hnum_nonneg : 0 ≤ Real.log (a (j + 1) : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hpos j)
    have hQge : 2 ^ (j / 2) ≤ continuantDen a j := hpow j
    have hQgt1_nat : 1 < continuantDen a j := by
      have hpowgt : 1 < 2 ^ (j / 2) := by
        have hjdivpos : 0 < j / 2 := by
          omega
        exact Nat.one_lt_pow (Nat.ne_of_gt hjdivpos) (by norm_num : 1 < 2)
      exact hpowgt.trans_le hQge
    have hden_nonneg : 0 ≤ Real.log (continuantDen a j : ℝ) := by
      exact Real.log_nonneg
        (by exact_mod_cast (le_of_lt hQgt1_nat : 1 ≤ continuantDen a j))
    exact div_nonneg hnum_nonneg hden_nonneg
  · refine eventually_atTop.2 ?_
    refine ⟨4, ?_⟩
    intro j hj
    let x : ℝ := (j : ℝ) + 2
    let num : ℝ := Real.log (a (j + 1) : ℝ)
    let den : ℝ := Real.log (continuantDen a j : ℝ)
    let denLow : ℝ := (Real.log 2 / 6) * x
    let numHigh : ℝ := Real.log (2 * x)
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdenLow_pos : 0 < denLow := by
      dsimp [denLow]
      positivity
    have hApos : 0 < (a (j + 1) : ℝ) := by
      exact_mod_cast hpos j
    have hA_le_nat : a (j + 1) ≤ 2 * (j + 2) := by
      simpa [Nat.add_assoc] using hlin (j + 1)
    have hA_le : (a (j + 1) : ℝ) ≤ 2 * x := by
      dsimp [x]
      exact_mod_cast hA_le_nat
    have hnum_le : num ≤ numHigh := by
      dsimp [num, numHigh]
      exact Real.log_le_log hApos hA_le
    have hnumHigh_nonneg : 0 ≤ numHigh := by
      dsimp [numHigh]
      exact Real.log_nonneg (by
        dsimp [x]
        have hjnonneg : (0 : ℝ) ≤ j := by
          positivity
        nlinarith)
    have hpow_le_Q : 2 ^ (j / 2) ≤ continuantDen a j := hpow j
    have hpow_pos_real : 0 < (((2 ^ (j / 2) : ℕ) : ℝ)) := by
      positivity
    have hlogpow_le_den :
        Real.log (((2 ^ (j / 2) : ℕ) : ℝ)) ≤ den := by
      dsimp [den]
      exact Real.log_le_log hpow_pos_real (by exact_mod_cast hpow_le_Q)
    have hlogpow :
        Real.log (((2 ^ (j / 2) : ℕ) : ℝ)) =
          (((j / 2 : ℕ) : ℝ) * Real.log 2) := by
      norm_num [Nat.cast_pow, Real.log_pow]
    have hx_le : x ≤ 6 * (((j / 2 : ℕ) : ℝ)) := by
      dsimp [x]
      have hn : j + 2 ≤ 6 * (j / 2) := by
        omega
      exact_mod_cast hn
    have hdenLow_le_logpow :
        denLow ≤ (((j / 2 : ℕ) : ℝ)) * Real.log 2 := by
      dsimp [denLow]
      nlinarith [mul_le_mul_of_nonneg_right hx_le hlog2pos.le]
    have hdenLow_le_den : denLow ≤ den := by
      calc
        denLow ≤ (((j / 2 : ℕ) : ℝ)) * Real.log 2 := hdenLow_le_logpow
        _ = Real.log (((2 ^ (j / 2) : ℕ) : ℝ)) := hlogpow.symm
        _ ≤ den := hlogpow_le_den
    have hnum_nonneg : 0 ≤ num := by
      dsimp [num]
      exact Real.log_nonneg (by exact_mod_cast hpos j)
    have hratio : num / den ≤ numHigh / denLow :=
      div_le_div₀ hnumHigh_nonneg hnum_le hdenLow_pos hdenLow_le_den
    have hrewrite : numHigh / denLow =
        (12 / Real.log 2) *
          (Real.log (2 * ((j : ℝ) + 2)) / (2 * ((j : ℝ) + 2))) := by
      dsimp [numHigh, denLow, x]
      field_simp [hlog2pos.ne']
      ring
    simpa [num, den, hrewrite] using hratio

/-- Corollary: if `tau = 0`, then the canonical block exponent is zero. -/
theorem canonicalBlockExponent_eq_zero_of_tau_zero
    {a : ℕ → ℕ}
    (hformula : HasCanonicalBlockGrowthFormula a)
    (htau : partialQuotientGrowthTau a = 0) :
    canonicalBlockExponent a = 0 := by
  simpa [HasCanonicalBlockGrowthFormula, htau] using hformula

/-- If the block-growth log ratio tends to zero, then the upper block exponent
is zero. -/
theorem canonicalBlockExponent_eq_zero_of_blockGrowth_log_ratio_tendsto_zero
    {a : ℕ → ℕ}
    (hseq : Tendsto
      (fun N : ℕ =>
        Real.log (canonicalBlockGrowth a N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 0)) :
    canonicalBlockExponent a = 0 := by
  unfold canonicalBlockExponent
  exact hseq.limsup_eq

/-- Zero block exponent and zero partial-quotient exponent imply the
canonical block-growth formula. This packages the Euler route to `hblock`. -/
theorem hasCanonicalBlockGrowthFormula_of_zero_exponents
    {a : ℕ → ℕ}
    (hlambda : canonicalBlockExponent a = 0)
    (htau : partialQuotientGrowthTau a = 0) :
    HasCanonicalBlockGrowthFormula a := by
  simp [HasCanonicalBlockGrowthFormula, hlambda, htau]

theorem partialQuotientGrowthTau_eq_zero_of_tendsto_log_ratio
    {a : ℕ → ℕ}
    (hseq : Tendsto
      (fun j : ℕ =>
        Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a j : ℝ))
      atTop (𝓝 0)) :
    partialQuotientGrowthTau a = 0 := by
  unfold partialQuotientGrowthTau
  exact hseq.limsup_eq

lemma continuantDenLogRatio_sub_one_add_pqLogRatio_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto
      (fun n : ℕ =>
        continuantDenLogRatio a n - (1 + pqLogRatio a n))
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (f := fun n : ℕ =>
      continuantDenLogRatio a n - (1 + pqLogRatio a n))
    (g := fun n : ℕ =>
      Real.log 2 / Real.log (continuantDen a n : ℝ))
    ?hnonneg ?hle ?htend
  · refine eventually_atTop.2 ⟨4, ?_⟩
    intro n hn
    let qn : ℝ := continuantDen a n
    let qnext : ℝ := continuantDen a (n + 1)
    let an : ℝ := a (n + 1)
    let den : ℝ := Real.log qn
    have hpow : 2 ^ (n / 2) ≤ continuantDen a n :=
      pow_two_half_le_continuantDen_of_partials_pos a hpos n
    have hqgt1_nat : 1 < continuantDen a n := by
      have hpowgt : 1 < 2 ^ (n / 2) := by
        have hdivpos : 0 < n / 2 := by omega
        exact Nat.one_lt_pow (Nat.ne_of_gt hdivpos) (by norm_num : 1 < 2)
      exact hpowgt.trans_le hpow
    have hdenpos : 0 < den := by
      dsimp [den, qn]
      exact Real.log_pos (by exact_mod_cast hqgt1_nat)
    have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    have hqnext_pos : 0 < qnext := by
      dsimp [qnext]
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < continuantDen a n) hmono)
    have han_pos : 0 < an := by
      dsimp [an]
      exact_mod_cast hpos n
    have hqn_pos : 0 < qn := by
      dsimp [qn]
      exact_mod_cast (lt_trans zero_lt_one hqgt1_nat)
    have hlower_nat := (continuantDen_succ_mul_bounds hpos n).1
    have hlower : an * qn ≤ qnext := by
      dsimp [an, qn, qnext]
      exact_mod_cast hlower_nat
    have hlog_mul :
        Real.log (an * qn) = Real.log an + Real.log qn := by
      rw [Real.log_mul (ne_of_gt han_pos) (ne_of_gt hqn_pos)]
    have hlog_lower :
        Real.log an + den ≤ Real.log qnext := by
      have hlog_le : Real.log (an * qn) ≤ Real.log qnext :=
        Real.log_le_log (mul_pos han_pos hqn_pos) hlower
      simpa [den, hlog_mul, add_comm] using hlog_le
    have hratio_ge :
        1 + Real.log an / den ≤ Real.log qnext / den := by
      rw [le_div_iff₀ hdenpos]
      have hcalc : (1 + Real.log an / den) * den = den + Real.log an := by
        field_simp [hdenpos.ne']
      simpa [hcalc, add_comm] using hlog_lower
    have hnonneg :
        0 ≤ Real.log qnext / den - (1 + Real.log an / den) := by
      exact sub_nonneg.mpr hratio_ge
    simpa [continuantDenLogRatio, pqLogRatio, qn, qnext, an, den] using hnonneg
  · refine eventually_atTop.2 ⟨4, ?_⟩
    intro n hn
    let qn : ℝ := continuantDen a n
    let qnext : ℝ := continuantDen a (n + 1)
    let an : ℝ := a (n + 1)
    let den : ℝ := Real.log qn
    have hpow : 2 ^ (n / 2) ≤ continuantDen a n :=
      pow_two_half_le_continuantDen_of_partials_pos a hpos n
    have hqgt1_nat : 1 < continuantDen a n := by
      have hpowgt : 1 < 2 ^ (n / 2) := by
        have hdivpos : 0 < n / 2 := by omega
        exact Nat.one_lt_pow (Nat.ne_of_gt hdivpos) (by norm_num : 1 < 2)
      exact hpowgt.trans_le hpow
    have hdenpos : 0 < den := by
      dsimp [den, qn]
      exact Real.log_pos (by exact_mod_cast hqgt1_nat)
    have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    have hqnext_pos : 0 < qnext := by
      dsimp [qnext]
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < continuantDen a n) hmono)
    have han_pos : 0 < an := by
      dsimp [an]
      exact_mod_cast hpos n
    have hqn_pos : 0 < qn := by
      dsimp [qn]
      exact_mod_cast (lt_trans zero_lt_one hqgt1_nat)
    have hupper_nat := (continuantDen_succ_mul_bounds hpos n).2
    have hupper : qnext ≤ 2 * an * qn := by
      dsimp [qnext, an, qn]
      exact_mod_cast hupper_nat
    have hlog_le : Real.log qnext ≤ Real.log (2 * an * qn) :=
      Real.log_le_log hqnext_pos hupper
    have hlog_mul :
        Real.log (2 * an * qn) =
          Real.log qn + Real.log 2 + Real.log an := by
      rw [Real.log_mul]
      · rw [Real.log_mul]
        · ring
        · norm_num
        · exact ne_of_gt han_pos
      · exact mul_ne_zero (by norm_num) (ne_of_gt han_pos)
      · exact ne_of_gt hqn_pos
    have hlog_le_den :
        Real.log qnext ≤ den + Real.log 2 + Real.log an := by
      simpa [den, hlog_mul] using hlog_le
    have hdiv_le :
        Real.log qnext / den ≤
          (den + Real.log 2 + Real.log an) / den :=
      div_le_div_of_nonneg_right hlog_le_den hdenpos.le
    have hcalc :
        (den + Real.log 2 + Real.log an) / den -
            (1 + Real.log an / den) =
          Real.log 2 / den := by
      field_simp [hdenpos.ne']
      ring
    have hgoal :
        Real.log qnext / den - (1 + Real.log an / den) ≤
          Real.log 2 / den := by
      calc
        Real.log qnext / den - (1 + Real.log an / den) ≤
            (den + Real.log 2 + Real.log an) / den -
              (1 + Real.log an / den) := by linarith
        _ = Real.log 2 / den := hcalc
    simpa [continuantDenLogRatio, pqLogRatio, qn, qnext, an, den] using hgoal
  · exact log_const_over_log_continuantDen_tendsto_zero hpos (Real.log 2)

lemma one_add_pqLogRatio_le_continuantDenLogRatio_eventually
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ᶠ n : ℕ in atTop,
      1 + pqLogRatio a n ≤ continuantDenLogRatio a n := by
  refine eventually_atTop.2 ⟨4, ?_⟩
  intro n hn
  let qn : ℝ := continuantDen a n
  let qnext : ℝ := continuantDen a (n + 1)
  let an : ℝ := a (n + 1)
  let den : ℝ := Real.log qn
  have hpow : 2 ^ (n / 2) ≤ continuantDen a n :=
    pow_two_half_le_continuantDen_of_partials_pos a hpos n
  have hqgt1_nat : 1 < continuantDen a n := by
    have hpowgt : 1 < 2 ^ (n / 2) := by
      have hdivpos : 0 < n / 2 := by omega
      exact Nat.one_lt_pow (Nat.ne_of_gt hdivpos) (by norm_num : 1 < 2)
    exact hpowgt.trans_le hpow
  have hdenpos : 0 < den := by
    dsimp [den, qn]
    exact Real.log_pos (by exact_mod_cast hqgt1_nat)
  have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
    continuantDen_mono_of_partials_pos a hpos n
  have hqnext_pos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < continuantDen a n) hmono)
  have han_pos : 0 < an := by
    dsimp [an]
    exact_mod_cast hpos n
  have hqn_pos : 0 < qn := by
    dsimp [qn]
    exact_mod_cast (lt_trans zero_lt_one hqgt1_nat)
  have hlower_nat := (continuantDen_succ_mul_bounds hpos n).1
  have hlower : an * qn ≤ qnext := by
    dsimp [an, qn, qnext]
    exact_mod_cast hlower_nat
  have hlog_mul :
      Real.log (an * qn) = Real.log an + Real.log qn := by
    rw [Real.log_mul (ne_of_gt han_pos) (ne_of_gt hqn_pos)]
  have hlog_lower :
      Real.log an + den ≤ Real.log qnext := by
    have hlog_le : Real.log (an * qn) ≤ Real.log qnext :=
      Real.log_le_log (mul_pos han_pos hqn_pos) hlower
    simpa [den, hlog_mul, add_comm] using hlog_le
  have hratio_ge :
      1 + Real.log an / den ≤ Real.log qnext / den := by
    rw [le_div_iff₀ hdenpos]
    have hcalc : (1 + Real.log an / den) * den = den + Real.log an := by
      field_simp [hdenpos.ne']
    simpa [hcalc, add_comm] using hlog_lower
  simpa [continuantDenLogRatio, pqLogRatio, qn, qnext, an, den] using hratio_ge

lemma pqEndpointLogRatio_sub_transform_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto
      (fun n : ℕ => pqEndpointLogRatio a n - pqLogRatioTransform a n)
      atTop (𝓝 0) := by
  let err : ℕ → ℝ := fun n : ℕ =>
    continuantDenLogRatio a n - (1 + pqLogRatio a n)
  let diff : ℕ → ℝ := fun n : ℕ =>
    pqEndpointLogRatio a n - pqLogRatioTransform a n
  have herr_tendsto : Tendsto err atTop (𝓝 0) := by
    simpa [err] using
      continuantDenLogRatio_sub_one_add_pqLogRatio_tendsto_zero hpos
  have hqR : Tendsto (fun n : ℕ => continuantDen a n) atTop atTop :=
    continuantDen_tendsto_atTop_of_partials_pos hpos
  have hqgt1 : ∀ᶠ n : ℕ in atTop, 1 < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  have habs_tendsto :
      Tendsto (fun n : ℕ => |diff n|) atTop (𝓝 0) := by
    refine squeeze_zero'
      (f := fun n : ℕ => |diff n|)
      (g := err)
      ?hnonneg ?hle herr_tendsto
    · exact Filter.Eventually.of_forall (fun n => abs_nonneg (diff n))
    · filter_upwards
        [one_add_pqLogRatio_le_continuantDenLogRatio_eventually hpos,
          hqgt1, pqLogRatio_nonneg_eventually hpos]
        with n hone hqgt1n hxnonneg
      let x : ℝ := pqLogRatio a n
      let r : ℝ := continuantDenLogRatio a n
      let y : ℝ := pqEndpointLogRatio a n
      let t : ℝ := pqLogRatioTransform a n
      let e : ℝ := r - (1 + x)
      have he_nonneg : 0 ≤ e := by
        dsimp [e, x, r]
        exact sub_nonneg.mpr hone
      have hdenx : 0 < 1 + x := by
        dsimp [x]
        linarith
      have hrpos : 0 < r := by
        dsimp [r, x] at hdenx hone ⊢
        linarith
      have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
        continuantDen_mono_of_partials_pos a hpos n
      have hqnext_gt1 : 1 < continuantDen a (n + 1) :=
        hqgt1n.trans_le hmono
      have hlogqn_pos :
          0 < Real.log (continuantDen a n : ℝ) :=
        Real.log_pos (by exact_mod_cast hqgt1n)
      have hlogqnext_pos :
          0 < Real.log (continuantDen a (n + 1) : ℝ) :=
        Real.log_pos (by exact_mod_cast hqnext_gt1)
      have hy_eq : y = x / r := by
        dsimp [y, x, r, pqEndpointLogRatio, pqLogRatio,
          continuantDenLogRatio]
        field_simp [hlogqn_pos.ne', hlogqnext_pos.ne']
      have ht_eq : t = x / (1 + x) := by
        rfl
      have hy_le_t : y ≤ t := by
        rw [hy_eq, ht_eq]
        exact div_le_div_of_nonneg_left hxnonneg hdenx hone
      have habs : |y - t| = t - y := by
        rw [abs_of_nonpos (sub_nonpos.mpr hy_le_t)]
        ring
      have hformula :
          t - y = e * (x / ((1 + x) * r)) := by
        rw [hy_eq, ht_eq]
        dsimp [e]
        field_simp [hdenx.ne', hrpos.ne']
      have hr_ge_one : 1 ≤ r := by
        dsimp [r, x] at hone hxnonneg ⊢
        linarith
      have hdenom_pos : 0 < (1 + x) * r :=
        mul_pos hdenx hrpos
      have hx_le_oneadd : x ≤ 1 + x := by linarith
      have honeadd_le_prod : 1 + x ≤ (1 + x) * r := by
        have hmul := mul_le_mul_of_nonneg_left hr_ge_one hdenx.le
        simpa using hmul
      have hx_le_denom : x ≤ (1 + x) * r :=
        hx_le_oneadd.trans honeadd_le_prod
      have hfactor_le : x / ((1 + x) * r) ≤ 1 :=
        (div_le_one hdenom_pos).mpr hx_le_denom
      have hprod_le : e * (x / ((1 + x) * r)) ≤ e := by
        have hmul := mul_le_mul_of_nonneg_left hfactor_le he_nonneg
        simpa using hmul
      calc
        |diff n| = |y - t| := by rfl
        _ = t - y := habs
        _ = e * (x / ((1 + x) * r)) := hformula
        _ ≤ e := hprod_le
        _ = err n := by rfl
  have hdiff : Tendsto diff atTop (𝓝 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero diff).2
      (by simpa [Function.comp_def] using habs_tendsto)
  simpa [diff] using hdiff

lemma limsup_pqEndpointLogRatio_eq_limsup_transform
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup (pqEndpointLogRatio a) atTop =
      limsup (pqLogRatioTransform a) atTop :=
  limsup_eq_of_sub_tendsto_zero_of_eventually_bounded
    (pqEndpointLogRatio_sub_transform_tendsto_zero hpos)
    (pqLogRatioTransform_nonneg_eventually hpos)
    (pqLogRatioTransform_le_one_eventually hpos)

lemma limsup_partialQuotient_endpoint_eq_limsup_transform
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    limsup
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a (j + 1) : ℝ))
        atTop =
      limsup (pqLogRatioTransform a) atTop := by
  simpa [pqEndpointLogRatio] using
    limsup_pqEndpointLogRatio_eq_limsup_transform hpos

lemma limsup_pqLogRatioTransform_eq_tau_div_one_add_tau_of_bounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hbounded :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (pqLogRatio a)) :
    limsup (pqLogRatioTransform a) atTop =
      partialQuotientGrowthTau a /
        (1 + partialQuotientGrowthTau a) := by
  have hcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop
        (pqLogRatio a) :=
    Filter.IsCoboundedUnder.of_frequently_ge
      (pqLogRatio_nonneg_eventually hpos).frequently
  have hLnonneg :
      0 ≤ limsup (pqLogRatio a) atTop :=
    Filter.le_limsup_of_frequently_le
      (pqLogRatio_nonneg_eventually hpos).frequently hbounded
  have hcongr :
      limsup (pqLogRatioTransform a) atTop =
        limsup (nonnegativeRatioTransform ∘ pqLogRatio a) atTop := by
    refine Filter.limsup_congr ?_
    filter_upwards [pqLogRatio_nonneg_eventually hpos] with n hn
    simp [pqLogRatioTransform,
      nonnegativeRatioTransform_eq_of_nonneg hn]
  have hmap :
      nonnegativeRatioTransform (limsup (pqLogRatio a) atTop) =
        limsup (nonnegativeRatioTransform ∘ pqLogRatio a) atTop :=
    Monotone.map_limsup_of_continuousAt
      (F := atTop)
      monotone_nonnegativeRatioTransform
      (pqLogRatio a)
      continuous_nonnegativeRatioTransform.continuousAt
      hbounded
      hcobdd
  calc
    limsup (pqLogRatioTransform a) atTop
        = limsup (nonnegativeRatioTransform ∘ pqLogRatio a) atTop := hcongr
    _ = nonnegativeRatioTransform (limsup (pqLogRatio a) atTop) := hmap.symm
    _ = limsup (pqLogRatio a) atTop /
          (1 + limsup (pqLogRatio a) atTop) :=
        nonnegativeRatioTransform_eq_of_nonneg hLnonneg
    _ = partialQuotientGrowthTau a /
          (1 + partialQuotientGrowthTau a) := by
        have htau :
            limsup (pqLogRatio a) atTop =
              partialQuotientGrowthTau a := by
          rfl
        rw [htau]

theorem limsup_partialQuotient_endpoint_eq_tau_div_one_add_tau_of_bounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hbounded :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a j : ℝ))) :
    limsup
      (fun j : ℕ =>
        Real.log (a (j + 1) : ℝ) /
          Real.log (continuantDen a (j + 1) : ℝ))
      atTop =
    partialQuotientGrowthTau a /
      (1 + partialQuotientGrowthTau a) := by
  have hb :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (pqLogRatio a) := by
    simpa [pqLogRatio] using hbounded
  exact (limsup_partialQuotient_endpoint_eq_limsup_transform hpos).trans
    (limsup_pqLogRatioTransform_eq_tau_div_one_add_tau_of_bounded hpos hb)

theorem partialQuotientEndpointExponent_eq_tau_div_one_add_tau_of_bounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hbounded :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a j : ℝ))) :
    partialQuotientEndpointExponent a =
      partialQuotientGrowthTau a /
        (1 + partialQuotientGrowthTau a) := by
  simpa [partialQuotientEndpointExponent, pqEndpointLogRatio] using
    limsup_partialQuotient_endpoint_eq_tau_div_one_add_tau_of_bounded
      hpos hbounded

theorem hasCanonicalBlockGrowthFormula_of_partials_pos_of_tau_bounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hbounded :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun j : ℕ =>
          Real.log (a (j + 1) : ℝ) /
            Real.log (continuantDen a j : ℝ))) :
    HasCanonicalBlockGrowthFormula a := by
  unfold HasCanonicalBlockGrowthFormula
  rw [canonicalBlockExponent_eq_limsup_partialQuotient_endpoint hpos]
  exact limsup_partialQuotient_endpoint_eq_tau_div_one_add_tau_of_bounded
    hpos hbounded

lemma limsup_pqLogRatioTransform_eq_one_of_unbounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hunbounded : partialQuotientGrowthUnbounded a) :
    limsup (pqLogRatioTransform a) atTop = 1 := by
  have hcobdd :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop
        (pqLogRatioTransform a) :=
    Filter.IsCoboundedUnder.of_frequently_ge
      (pqLogRatioTransform_nonneg_eventually hpos).frequently
  have hbdd :
      Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
        (pqLogRatioTransform a) :=
    Filter.isBoundedUnder_of_eventually_le
      (pqLogRatioTransform_le_one_eventually hpos)
  have hle : limsup (pqLogRatioTransform a) atTop ≤ 1 := by
    rw [Filter.limsup_le_iff' hcobdd hbdd]
    intro y hy
    filter_upwards [pqLogRatioTransform_le_one_eventually hpos] with n hn
    exact hn.trans (le_of_lt hy)
  have hge : 1 ≤ limsup (pqLogRatioTransform a) atTop := by
    rw [Filter.le_limsup_iff' hcobdd hbdd]
    intro y hy
    let C : ℝ := 1 / (1 - y)
    have hden_pos : 0 < 1 - y := by linarith
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hCnonneg : 0 ≤ C := hCpos.le
    have hden2_pos : 0 < 2 - y := by linarith
    have hC_transform :
        C / (1 + C) = 1 / (2 - y) := by
      dsimp [C]
      field_simp [hden_pos.ne', hden2_pos.ne']
      ring
    have hy_le_C_transform : y ≤ C / (1 + C) := by
      rw [hC_transform]
      rw [le_div_iff₀ hden2_pos]
      nlinarith [sq_nonneg (1 - y)]
    exact (hunbounded C).mono fun n hCx => by
      have hxnonneg : 0 ≤ pqLogRatio a n := hCnonneg.trans hCx
      have hmono :
          nonnegativeRatioTransform C ≤
            nonnegativeRatioTransform (pqLogRatio a n) :=
        monotone_nonnegativeRatioTransform hCx
      have htransform :
          nonnegativeRatioTransform (pqLogRatio a n) =
            pqLogRatioTransform a n := by
        rw [nonnegativeRatioTransform_eq_of_nonneg hxnonneg]
        rfl
      calc
        y ≤ C / (1 + C) := hy_le_C_transform
        _ = nonnegativeRatioTransform C :=
          (nonnegativeRatioTransform_eq_of_nonneg hCnonneg).symm
        _ ≤ nonnegativeRatioTransform (pqLogRatio a n) := hmono
        _ = pqLogRatioTransform a n := htransform
  exact le_antisymm hle hge

theorem canonicalBlockExponent_eq_one_of_partialQuotientGrowthUnbounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hunbounded : partialQuotientGrowthUnbounded a) :
    canonicalBlockExponent a = 1 := by
  rw [canonicalBlockExponent_eq_limsup_partialQuotient_endpoint hpos]
  rw [limsup_partialQuotient_endpoint_eq_limsup_transform hpos]
  exact limsup_pqLogRatioTransform_eq_one_of_unbounded hpos hunbounded

theorem partialQuotientEndpointExponent_eq_one_of_unbounded
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hunbounded : partialQuotientGrowthUnbounded a) :
    partialQuotientEndpointExponent a = 1 := by
  unfold partialQuotientEndpointExponent
  rw [limsup_pqEndpointLogRatio_eq_limsup_transform hpos]
  exact limsup_pqLogRatioTransform_eq_one_of_unbounded hpos hunbounded

theorem denominatorRatio_tendsto_one_of_log_partialQuotient_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hseq : Tendsto
      (fun n : ℕ =>
        Real.log (a (n + 1) : ℝ) / Real.log (continuantDen a n : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (continuantDen a (n + 1) : ℝ) /
          Real.log (continuantDen a n : ℝ))
      atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero'
    (f := fun n : ℕ =>
      Real.log (continuantDen a (n + 1) : ℝ) /
          Real.log (continuantDen a n : ℝ) - 1)
    (g := fun n : ℕ =>
      Real.log 2 / Real.log (continuantDen a n : ℝ) +
        Real.log (a (n + 1) : ℝ) / Real.log (continuantDen a n : ℝ))
    ?hnonneg ?hle ?htend
  · refine eventually_atTop.2 ⟨4, ?_⟩
    intro n hn
    have hpow : 2 ^ (n / 2) ≤ continuantDen a n :=
      pow_two_half_le_continuantDen_of_partials_pos a hpos n
    have hqgt1_nat : 1 < continuantDen a n := by
      have hpowgt : 1 < 2 ^ (n / 2) := by
        have hdivpos : 0 < n / 2 := by omega
        exact Nat.one_lt_pow (Nat.ne_of_gt hdivpos) (by norm_num : 1 < 2)
      exact hpowgt.trans_le hpow
    have hlogpos : 0 < Real.log (continuantDen a n : ℝ) :=
      Real.log_pos (by exact_mod_cast hqgt1_nat)
    have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    have hlog_le :
        Real.log (continuantDen a n : ℝ) ≤
          Real.log (continuantDen a (n + 1) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmono)
    have hone_le :
        (1 : ℝ) ≤
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ) :=
      (le_div_iff₀ hlogpos).mpr (by simpa using hlog_le)
    linarith
  · refine eventually_atTop.2 ⟨4, ?_⟩
    intro n hn
    let qn : ℝ := continuantDen a n
    let qnext : ℝ := continuantDen a (n + 1)
    let an : ℝ := a (n + 1)
    let den : ℝ := Real.log qn
    have hpow : 2 ^ (n / 2) ≤ continuantDen a n :=
      pow_two_half_le_continuantDen_of_partials_pos a hpos n
    have hqgt1_nat : 1 < continuantDen a n := by
      have hpowgt : 1 < 2 ^ (n / 2) := by
        have hdivpos : 0 < n / 2 := by omega
        exact Nat.one_lt_pow (Nat.ne_of_gt hdivpos) (by norm_num : 1 < 2)
      exact hpowgt.trans_le hpow
    have hdenpos : 0 < den := by
      dsimp [den, qn]
      exact Real.log_pos (by exact_mod_cast hqgt1_nat)
    have hmono : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    have hqnext_pos : 0 < qnext := by
      dsimp [qnext]
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < continuantDen a n) hmono)
    have han_pos : 0 < an := by
      dsimp [an]
      exact_mod_cast hpos n
    have hqn_pos : 0 < qn := by
      dsimp [qn]
      exact_mod_cast (lt_trans zero_lt_one hqgt1_nat)
    have hupper_nat := (continuantDen_succ_mul_bounds hpos n).2
    have hupper : qnext ≤ 2 * an * qn := by
      dsimp [qnext, an, qn]
      exact_mod_cast hupper_nat
    have hlog_le : Real.log qnext ≤ Real.log (2 * an * qn) :=
      Real.log_le_log hqnext_pos hupper
    have hlog_mul :
        Real.log (2 * an * qn) =
          Real.log qn + Real.log 2 + Real.log an := by
      rw [Real.log_mul]
      · rw [Real.log_mul]
        · ring
        · norm_num
        · exact ne_of_gt han_pos
      · exact mul_ne_zero (by norm_num) (ne_of_gt han_pos)
      · exact ne_of_gt hqn_pos
    have hlog_le_den :
        Real.log qnext ≤ den + Real.log 2 + Real.log an := by
      simpa [den, hlog_mul] using hlog_le
    have hdiv_le :
        Real.log qnext / den ≤
          (den + Real.log 2 + Real.log an) / den :=
      div_le_div_of_nonneg_right hlog_le_den hdenpos.le
    have hcalc :
        (den + Real.log 2 + Real.log an) / den - 1 =
          Real.log 2 / den + Real.log an / den := by
      field_simp [hdenpos.ne']
      ring
    have hgoal :
        Real.log qnext / den - 1 ≤
          Real.log 2 / den + Real.log an / den := by
      calc
        Real.log qnext / den - 1 ≤
            (den + Real.log 2 + Real.log an) / den - 1 := by linarith
        _ = Real.log 2 / den + Real.log an / den := hcalc
    simpa [qn, qnext, an, den] using hgoal
  · have hconst :
        Tendsto
          (fun n : ℕ => Real.log 2 / Real.log (continuantDen a n : ℝ))
          atTop (𝓝 0) :=
      log_const_over_log_continuantDen_tendsto_zero hpos (Real.log 2)
    simpa using hconst.add hseq

lemma eventually_qsucc_le_power_of_denominatorRatio_tendsto_one
    {a : ℕ → ℕ} {ε : ℝ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hratio :
      Tendsto
        (fun n : ℕ =>
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ))
        atTop (𝓝 1))
    (heps : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (continuantDen a (n + 1) : ℝ) ≤
        (continuantDen a n : ℝ) ^ (1 + ε) := by
  have hratio_le :
      ∀ᶠ n : ℕ in atTop,
        Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ) ≤ 1 + ε := by
    exact hratio.eventually
      (eventually_le_nhds (by linarith : (1 : ℝ) < 1 + ε))
  have hqR : Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hqgt1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  filter_upwards [hratio_le, hqgt1] with n hle hqn_gt1
  let qn : ℝ := continuantDen a n
  let qnext : ℝ := continuantDen a (n + 1)
  have hqn_pos : 0 < qn := by
    dsimp [qn]
    linarith
  have hlogpos : 0 < Real.log qn := by
    dsimp [qn]
    exact Real.log_pos hqn_gt1
  have hqnext_gt1 : (1 : ℝ) < qnext := by
    dsimp [qnext]
    have hmono_nat : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    exact lt_of_lt_of_le hqn_gt1 (by exact_mod_cast hmono_nat)
  have hqnext_pos : 0 < qnext := by linarith
  have hrpow_pos : 0 < qn ^ (1 + ε) := Real.rpow_pos_of_pos hqn_pos _
  have hmul_le :
      (Real.log qnext / Real.log qn) * Real.log qn ≤
        (1 + ε) * Real.log qn := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [qn, qnext] using hle) hlogpos.le
  have hleft :
      (Real.log qnext / Real.log qn) * Real.log qn =
        Real.log qnext := by
    exact div_mul_cancel₀ _ hlogpos.ne'
  have hright : (1 + ε) * Real.log qn = Real.log (qn ^ (1 + ε)) := by
    rw [Real.log_rpow hqn_pos]
  have hlog_le : Real.log qnext ≤ Real.log (qn ^ (1 + ε)) := by
    simpa [hleft, hright] using hmul_le
  have hle' : qnext ≤ qn ^ (1 + ε) := by
    exact (Real.log_le_log_iff hqnext_pos hrpow_pos).mp hlog_le
  simpa [qn, qnext] using hle'

theorem lower_clause_from_convergents
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) :
    ∀ ν : ℝ,
      ν < 2 →
        ∃ᶠ q : ℕ in atTop,
          ∃ p : ℤ,
            0 < q ∧
              |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν) := by
  rcases hcf with ⟨hpos, hconv, htails⟩
  intro ν hν
  have hqT : Tendsto (continuantDen a) atTop atTop :=
    continuantDen_tendsto_atTop_of_partials_pos hpos
  refine hqT.frequently ?_
  have hqR : Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqT
  have hqgt1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  refine hqgt1.frequently.mono ?_
  intro n hqn_gt1
  refine ⟨(continuantNum a n : ℤ), ?_, ?_⟩
  · have hqn_pos_nat : 0 < continuantDen a n := by
      exact_mod_cast (lt_trans (zero_lt_one : (0 : ℝ) < 1) hqn_gt1)
    exact hqn_pos_nat
  · let qn : ℝ := continuantDen a n
    let qnext : ℝ := continuantDen a (n + 1)
    have hqn_pos : 0 < qn := by
      dsimp [qn]
      exact lt_trans zero_lt_one hqn_gt1
    have hqnext_pos : 0 < qnext := by
      dsimp [qnext]
      have hmono_nat : continuantDen a n ≤ continuantDen a (n + 1) :=
        continuantDen_mono_of_partials_pos a hpos n
      exact lt_of_lt_of_le (lt_trans zero_lt_one hqn_gt1)
        (by exact_mod_cast hmono_nat)
    have hmono : qn ≤ qnext := by
      dsimp [qn, qnext]
      exact_mod_cast continuantDen_mono_of_partials_pos a hpos n
    have hprod_le : qn * qn ≤ qn * qnext := by
      exact mul_le_mul_of_nonneg_left hmono hqn_pos.le
    have hprod_pos : 0 < qn * qn := mul_pos hqn_pos hqn_pos
    have hinv_le : 1 / (qn * qnext) ≤ 1 / (qn * qn) := by
      exact one_div_le_one_div_of_le hprod_pos hprod_le
    have hrpow_two : qn ^ (2 : ℝ) = qn * qn := by
      norm_num [Real.rpow_natCast, pow_two]
    have hsq_eq : 1 / (qn * qn) = qn ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hqn_pos.le]
      rw [hrpow_two]
      ring
    have hexp_lt : qn ^ (-(2 : ℝ)) < qn ^ (-ν) := by
      exact Real.rpow_lt_rpow_of_exponent_lt hqn_gt1 (by linarith)
    have htarget : 1 / (qn * qnext) < qn ^ (-ν) := by
      exact lt_of_le_of_lt (hinv_le.trans_eq hsq_eq) hexp_lt
    have herr := convergent_error_lt_inv_mul_q_qsucc (α := α) (a := a)
      ⟨hpos, hconv, htails⟩ n
    have hmain :
        |α - (continuantNum a n : ℝ) / (continuantDen a n : ℝ)| <
          (continuantDen a n : ℝ) ^ (-ν) := by
      exact herr.trans htarget
    simpa [qn, qnext, Int.cast_natCast] using hmain

theorem upper_clause_from_denominatorRatio_tendsto_one
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hratio :
      Tendsto
        (fun n : ℕ =>
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ))
        atTop (𝓝 1)) :
    ∀ ν : ℝ,
      2 < ν →
        ∀ᶠ q : ℕ in atTop,
          ∀ p : ℤ,
            0 < q →
              ¬ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν) := by
  rcases hcf with ⟨hpos, hconv, htails⟩
  intro ν hν
  let ε : ℝ := (ν - 2) / 2
  have heps : 0 < ε := by
    dsimp [ε]
    linarith
  have htwo_eps : 2 + ε < ν := by
    dsimp [ε]
    linarith
  have hqsucc :
      ∀ᶠ n : ℕ in atTop,
        (continuantDen a (n + 1) : ℝ) ≤
          (continuantDen a n : ℝ) ^ (1 + ε) :=
    eventually_qsucc_le_power_of_denominatorRatio_tendsto_one
      hpos hratio heps
  have hloc :
      ∀ᶠ q : ℕ in atTop,
        ∃ n : ℕ,
          (continuantDen a (n + 1) : ℝ) ≤
              (continuantDen a n : ℝ) ^ (1 + ε) ∧
            continuantDen a n ≤ q ∧
              q < continuantDen a (n + 1) :=
    eventually_exists_convergent_interval_of_eventually hpos hqsucc
  have hpowcmp :
      ∀ᶠ q : ℕ in atTop,
        1 / (2 * (q : ℝ) ^ (2 + ε)) >
          (q : ℝ) ^ (-ν) :=
    eventually_inv_two_power_gt_power_neg htwo_eps
  filter_upwards [hloc, hpowcmp, eventually_nat_cast_one_lt_atTop]
    with q hlocq hcmp hqgt1 p hqpos happ
  rcases hlocq with ⟨n, hqnext_le_qn_pow, hqlo, hqhi⟩
  let x : ℝ := q
  let qnext : ℝ := continuantDen a (n + 1)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast hqpos
  have hqnext_pos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast (lt_trans hqpos hqhi)
  have hqbase : (continuantDen a n : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hqlo
  have hqnext_le_qpow : qnext ≤ x ^ (1 + ε) := by
    have hpow_mono :
        (continuantDen a n : ℝ) ^ (1 + ε) ≤ x ^ (1 + ε) := by
      exact Real.rpow_le_rpow
        (by positivity : (0 : ℝ) ≤ continuantDen a n)
        hqbase
        (by linarith : 0 ≤ 1 + ε)
    exact hqnext_le_qn_pow.trans hpow_mono
  have hxpow_mul : x * x ^ (1 + ε) = x ^ (2 + ε) := by
    calc
      x * x ^ (1 + ε) = x ^ (1 : ℝ) * x ^ (1 + ε) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (1 + ε)) := by
        exact (Real.rpow_add hx (1 : ℝ) (1 + ε)).symm
      _ = x ^ (2 + ε) := by
        rw [show (1 : ℝ) + (1 + ε) = 2 + ε by ring]
  have hden_le :
      2 * x * qnext ≤ 2 * x ^ (2 + ε) := by
    calc
      2 * x * qnext = 2 * (x * qnext) := by ring
      _ ≤ 2 * (x * x ^ (1 + ε)) := by
        gcongr
      _ = 2 * x ^ (2 + ε) := by rw [hxpow_mul]
  have hden_pos : 0 < 2 * x * qnext := by positivity
  have hpower_den_pos : 0 < 2 * x ^ (2 + ε) := by positivity
  have hinv_le :
      1 / (2 * x ^ (2 + ε)) ≤ 1 / (2 * x * qnext) := by
    exact one_div_le_one_div_of_le hden_pos hden_le
  have hbest :
      1 / (2 * x * qnext) ≤ |α - (p : ℝ) / (q : ℝ)| := by
    have h :=
      rational_approx_lower_bound_between_convergents
        (α := α) (a := a) ⟨hpos, hconv, htails⟩ n q p
        hqlo hqhi hqpos
    simpa [x, qnext, mul_assoc] using h
  have htarget_lt_abs : (q : ℝ) ^ (-ν) < |α - (p : ℝ) / (q : ℝ)| := by
    exact lt_of_lt_of_le (lt_of_lt_of_le hcmp hinv_le) hbest
  exact not_lt_of_ge htarget_lt_abs.le happ

theorem irrationalityMeasure_eq_two_of_denominatorRatio_tendsto_one
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hratio :
      Tendsto
        (fun n : ℕ =>
          Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ))
        atTop (𝓝 1)) :
    HasIrrationalityMeasure α 2 := by
  constructor
  · exact lower_clause_from_convergents hcf
  · exact upper_clause_from_denominatorRatio_tendsto_one hcf hratio

lemma denominatorRatioExponent_eq_one_isBoundedUnder
    {a : ℕ → ℕ}
    (hrho : denominatorRatioExponent a = 1) :
    IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop
      (fun n : ℕ =>
        Real.log (continuantDen a (n + 1) : ℝ) /
          Real.log (continuantDen a n : ℝ)) := by
  let u : ℕ → ℝ := fun n =>
    Real.log (continuantDen a (n + 1) : ℝ) /
      Real.log (continuantDen a n : ℝ)
  by_contra hbdd
  have hset_empty : {b : ℝ | ∀ᶠ n : ℕ in atTop, u n ≤ b} = ∅ := by
    ext b
    constructor
    · intro hb
      exact False.elim (hbdd (Filter.isBoundedUnder_of_eventually_le hb))
    · intro hb
      cases hb
  have hlim0 : limsup u atTop = 0 := by
    rw [Filter.limsup_eq, hset_empty, Real.sInf_empty]
  have hlim1 : limsup u atTop = 1 := by
    simpa [denominatorRatioExponent, u] using hrho
  linarith

lemma eventually_ratio_lt_of_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {ε : ℝ}
    (hrho : denominatorRatioExponent a = 1)
    (heps : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (continuantDen a (n + 1) : ℝ) /
          Real.log (continuantDen a n : ℝ) < 1 + ε := by
  let u : ℕ → ℝ := fun n =>
    Real.log (continuantDen a (n + 1) : ℝ) /
      Real.log (continuantDen a n : ℝ)
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop u := by
    simpa [u] using
      denominatorRatioExponent_eq_one_isBoundedUnder (a := a) hrho
  have hlt : limsup u atTop < 1 + ε := by
    have hlim1 : limsup u atTop = 1 := by
      simpa [denominatorRatioExponent, u] using hrho
    rw [hlim1]
    linarith
  exact eventually_lt_of_limsup_lt hlt hbdd

lemma eventually_qsucc_le_power_of_denominatorRatioExponent_eq_one
    {a : ℕ → ℕ} {ε : ℝ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hrho : denominatorRatioExponent a = 1)
    (heps : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (continuantDen a (n + 1) : ℝ) ≤
        (continuantDen a n : ℝ) ^ (1 + ε) := by
  have hratio_lt :
      ∀ᶠ n : ℕ in atTop,
        Real.log (continuantDen a (n + 1) : ℝ) /
            Real.log (continuantDen a n : ℝ) < 1 + ε :=
    eventually_ratio_lt_of_denominatorRatioExponent_eq_one hrho heps
  have hqR : Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (continuantDen_tendsto_atTop_of_partials_pos hpos)
  have hqgt1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < continuantDen a n :=
    hqR.eventually_gt_atTop 1
  filter_upwards [hratio_lt, hqgt1] with n hlt hqn_gt1
  let qn : ℝ := continuantDen a n
  let qnext : ℝ := continuantDen a (n + 1)
  have hqn_pos : 0 < qn := by
    dsimp [qn]
    linarith
  have hlogpos : 0 < Real.log qn := by
    dsimp [qn]
    exact Real.log_pos hqn_gt1
  have hqnext_gt1 : (1 : ℝ) < qnext := by
    dsimp [qnext]
    have hmono_nat : continuantDen a n ≤ continuantDen a (n + 1) :=
      continuantDen_mono_of_partials_pos a hpos n
    exact lt_of_lt_of_le hqn_gt1 (by exact_mod_cast hmono_nat)
  have hqnext_pos : 0 < qnext := by linarith
  have hrpow_pos : 0 < qn ^ (1 + ε) := Real.rpow_pos_of_pos hqn_pos _
  have hmul_le :
      (Real.log qnext / Real.log qn) * Real.log qn ≤
        (1 + ε) * Real.log qn := by
    exact mul_le_mul_of_nonneg_right
      (le_of_lt (by simpa [qn, qnext] using hlt)) hlogpos.le
  have hleft :
      (Real.log qnext / Real.log qn) * Real.log qn =
        Real.log qnext := by
    exact div_mul_cancel₀ _ hlogpos.ne'
  have hright : (1 + ε) * Real.log qn = Real.log (qn ^ (1 + ε)) := by
    rw [Real.log_rpow hqn_pos]
  have hlog_le : Real.log qnext ≤ Real.log (qn ^ (1 + ε)) := by
    simpa [hleft, hright] using hmul_le
  have hle' : qnext ≤ qn ^ (1 + ε) := by
    exact (Real.log_le_log_iff hqnext_pos hrpow_pos).mp hlog_le
  simpa [qn, qnext] using hle'

theorem upper_clause_from_denominatorRatioExponent_eq_one
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hrho : denominatorRatioExponent a = 1) :
    ∀ ν : ℝ,
      2 < ν →
        ∀ᶠ q : ℕ in atTop,
          ∀ p : ℤ,
            0 < q →
              ¬ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν) := by
  rcases hcf with ⟨hpos, hconv, htails⟩
  intro ν hν
  let ε : ℝ := (ν - 2) / 2
  have heps : 0 < ε := by
    dsimp [ε]
    linarith
  have htwo_eps : 2 + ε < ν := by
    dsimp [ε]
    linarith
  have hqsucc :
      ∀ᶠ n : ℕ in atTop,
        (continuantDen a (n + 1) : ℝ) ≤
          (continuantDen a n : ℝ) ^ (1 + ε) :=
    eventually_qsucc_le_power_of_denominatorRatioExponent_eq_one
      hpos hrho heps
  have hloc :
      ∀ᶠ q : ℕ in atTop,
        ∃ n : ℕ,
          (continuantDen a (n + 1) : ℝ) ≤
              (continuantDen a n : ℝ) ^ (1 + ε) ∧
            continuantDen a n ≤ q ∧
              q < continuantDen a (n + 1) :=
    eventually_exists_convergent_interval_of_eventually hpos hqsucc
  have hpowcmp :
      ∀ᶠ q : ℕ in atTop,
        1 / (2 * (q : ℝ) ^ (2 + ε)) >
          (q : ℝ) ^ (-ν) :=
    eventually_inv_two_power_gt_power_neg htwo_eps
  filter_upwards [hloc, hpowcmp, eventually_nat_cast_one_lt_atTop]
    with q hlocq hcmp hqgt1 p hqpos happ
  rcases hlocq with ⟨n, hqnext_le_qn_pow, hqlo, hqhi⟩
  let x : ℝ := q
  let qnext : ℝ := continuantDen a (n + 1)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast hqpos
  have hqnext_pos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast (lt_trans hqpos hqhi)
  have hqbase : (continuantDen a n : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hqlo
  have hqnext_le_qpow : qnext ≤ x ^ (1 + ε) := by
    have hpow_mono :
        (continuantDen a n : ℝ) ^ (1 + ε) ≤ x ^ (1 + ε) := by
      exact Real.rpow_le_rpow
        (by positivity : (0 : ℝ) ≤ continuantDen a n)
        hqbase
        (by linarith : 0 ≤ 1 + ε)
    exact hqnext_le_qn_pow.trans hpow_mono
  have hxpow_mul : x * x ^ (1 + ε) = x ^ (2 + ε) := by
    calc
      x * x ^ (1 + ε) = x ^ (1 : ℝ) * x ^ (1 + ε) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (1 + ε)) := by
        exact (Real.rpow_add hx (1 : ℝ) (1 + ε)).symm
      _ = x ^ (2 + ε) := by
        rw [show (1 : ℝ) + (1 + ε) = 2 + ε by ring]
  have hden_le :
      2 * x * qnext ≤ 2 * x ^ (2 + ε) := by
    calc
      2 * x * qnext = 2 * (x * qnext) := by ring
      _ ≤ 2 * (x * x ^ (1 + ε)) := by
        gcongr
      _ = 2 * x ^ (2 + ε) := by rw [hxpow_mul]
  have hden_pos : 0 < 2 * x * qnext := by positivity
  have hinv_le :
      1 / (2 * x ^ (2 + ε)) ≤ 1 / (2 * x * qnext) := by
    exact one_div_le_one_div_of_le hden_pos hden_le
  have hbest :
      1 / (2 * x * qnext) ≤ |α - (p : ℝ) / (q : ℝ)| := by
    have h :=
      rational_approx_lower_bound_between_convergents
        (α := α) (a := a) ⟨hpos, hconv, htails⟩ n q p
        hqlo hqhi hqpos
    simpa [x, qnext, mul_assoc] using h
  have htarget_lt_abs : (q : ℝ) ^ (-ν) < |α - (p : ℝ) / (q : ℝ)| := by
    exact lt_of_lt_of_le (lt_of_lt_of_le hcmp hinv_le) hbest
  exact not_lt_of_ge htarget_lt_abs.le happ

theorem irrationalityMeasure_eq_two_of_denominatorRatioExponent_eq_one
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hrho : denominatorRatioExponent a = 1) :
    HasIrrationalityMeasure α 2 := by
  constructor
  · exact lower_clause_from_convergents hcf
  · exact upper_clause_from_denominatorRatioExponent_eq_one hcf hrho

theorem denominatorRatioExponent_eq_one_of_log_partialQuotient_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hseq : Tendsto
      (fun n : ℕ =>
        Real.log (a (n + 1) : ℝ) / Real.log (continuantDen a n : ℝ))
      atTop (𝓝 0)) :
    denominatorRatioExponent a = 1 := by
  unfold denominatorRatioExponent
  exact
    (denominatorRatio_tendsto_one_of_log_partialQuotient_tendsto_zero
      hpos hseq).limsup_eq

theorem partialQuotientGrowthTau_eq_zero_of_eulerPartialQuotients
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    partialQuotientGrowthTau a = 0 :=
  partialQuotientGrowthTau_eq_zero_of_tendsto_log_ratio
    (euler_log_partialQuotient_div_log_continuantDen_tendsto_zero he)

theorem denominatorRatioExponent_eq_one_of_eulerPartialQuotients
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    denominatorRatioExponent a = 1 :=
  denominatorRatioExponent_eq_one_of_log_partialQuotient_tendsto_zero
    (eulerPartialQuotients_pos_succ he)
    (euler_log_partialQuotient_div_log_continuantDen_tendsto_zero he)

/-- Euler-pattern coefficients satisfy the canonical block-growth bridge
`lambda = tau / (1 + tau)`.

This is the zero-exponent instance of the bridge: both sides are zero for the
Euler pattern. The fully general arbitrary-`tau` bridge remains the next hard
asymptotic theorem. -/
theorem hasCanonicalBlockGrowthFormula_of_eulerPartialQuotients
    {a : ℕ → ℕ}
    (he : HasEulerPartialQuotients a) :
    HasCanonicalBlockGrowthFormula a :=
  hasCanonicalBlockGrowthFormula_of_zero_exponents
    (canonicalBlockExponent_eq_zero_of_eulerPartialQuotients he)
    (partialQuotientGrowthTau_eq_zero_of_eulerPartialQuotients he)

/-- Corollary: if `mu = 2 + tau` and `tau = 0`, then `mu = 2`. -/
theorem irrationalityMeasureFromCF_eq_two_of_tau_zero
    {a : ℕ → ℕ} {μ : ℝ}
    (hμ : HasIrrationalityMeasureFromCF a μ)
    (htau : partialQuotientGrowthTau a = 0) :
    μ = 2 := by
  simpa [HasIrrationalityMeasureFromCF, htau] using hμ

/-- Algebraic extraction of the irrationality measure from the block exponent.

This proves the formal algebra behind
`lambda = (mu - 2)/(mu - 1)` and
`mu = (2 - lambda)/(1 - lambda)`. -/
theorem canonicalBlockExponent_eq_of_irrationalityMeasureFromCF
    {a : ℕ → ℕ} {μ : ℝ}
    (hblock : HasCanonicalBlockGrowthFormula a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    canonicalBlockExponent a = (μ - 2) / (μ - 1) := by
  let tau : ℝ := partialQuotientGrowthTau a
  have hlam_tau : canonicalBlockExponent a = tau / (1 + tau) := by
    simpa [tau, HasCanonicalBlockGrowthFormula] using hblock
  have hmu_tau : μ = 2 + tau := by
    simpa [tau, HasIrrationalityMeasureFromCF] using hμ
  rw [hlam_tau, hmu_tau]
  ring_nf

theorem blockExponent_eq_irrationalityMeasure_formula
    {a : ℕ → ℕ} {lam μ : ℝ}
    (hlam : lam = canonicalBlockExponent a)
    (hblock : HasCanonicalBlockGrowthFormula a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    lam = (μ - 2) / (μ - 1) := by
  rw [hlam]
  exact canonicalBlockExponent_eq_of_irrationalityMeasureFromCF hblock hμ

theorem irrationalityMeasure_eq_of_blockExponent_formula
    {a : ℕ → ℕ} {lam μ : ℝ}
    (hlam : lam = canonicalBlockExponent a)
    (hblock : HasCanonicalBlockGrowthFormula a)
    (hμ : HasIrrationalityMeasureFromCF a μ)
    (hden : 1 + partialQuotientGrowthTau a ≠ 0) :
    μ = (2 - lam) / (1 - lam) := by
  let τ : ℝ := partialQuotientGrowthTau a
  have hdenτ : 1 + τ ≠ 0 := by
    simpa [τ] using hden
  have hlamτ : lam = τ / (1 + τ) := by
    simpa [τ, HasCanonicalBlockGrowthFormula] using hlam.trans hblock
  have hμτ : μ = 2 + τ := by
    simpa [τ, HasIrrationalityMeasureFromCF] using hμ
  rw [hμτ, hlamτ]
  field_simp [hdenτ]
  ring_nf

/-- Conditional formal version of the final `e` corollary in the writeup.

To make this a theorem about the literal real number `Real.exp 1`, the remaining
work is to connect `a` to the actual simple continued fraction of `Real.exp 1`. -/
theorem e_irrationalityMeasure_eq_two_from_tau_zero
    {a : ℕ → ℕ} {μ : ℝ}
    (_he : HasEulerPartialQuotients a)
    (hμ : HasIrrationalityMeasureFromCF a μ)
    (htau : partialQuotientGrowthTau a = 0) :
    μ = 2 :=
  irrationalityMeasureFromCF_eq_two_of_tau_zero hμ htau

theorem e_irrationalityMeasure_eq_two_from_log_ratio
    {a : ℕ → ℕ} {μ : ℝ}
    (he : HasEulerPartialQuotients a)
    (hμ : HasIrrationalityMeasureFromCF a μ)
    (hseq : Tendsto
      (fun j : ℕ =>
        Real.log (a (j + 1) : ℝ) / Real.log (continuantDen a j : ℝ))
      atTop (𝓝 0)) :
    μ = 2 :=
  e_irrationalityMeasure_eq_two_from_tau_zero he hμ
    (partialQuotientGrowthTau_eq_zero_of_tendsto_log_ratio hseq)

theorem e_irrationalityMeasure_eq_two_of_eulerPartialQuotients
    {a : ℕ → ℕ} {μ : ℝ}
    (he : HasEulerPartialQuotients a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    μ = 2 :=
  e_irrationalityMeasure_eq_two_from_tau_zero he hμ
    (partialQuotientGrowthTau_eq_zero_of_eulerPartialQuotients he)

theorem blockExponent_eq_irrationalityMeasure_formula_of_eulerPartialQuotients
    {a : ℕ → ℕ} {μ : ℝ}
    (he : HasEulerPartialQuotients a)
    (hμ : HasIrrationalityMeasureFromCF a μ) :
    canonicalBlockExponent a = (μ - 2) / (μ - 1) :=
  canonicalBlockExponent_eq_of_irrationalityMeasureFromCF
    (hasCanonicalBlockGrowthFormula_of_eulerPartialQuotients he) hμ

end IrrationalityAr
