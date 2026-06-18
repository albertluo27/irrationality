import IrrationalityAr.ContinuedFractions
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

lemma mem_canonicalOddBlock_iff {a : ℕ → ℕ} {j t : ℕ} :
    t ∈ canonicalOddBlock a j ↔
      1 ≤ t ∧ t ≤ a (j + 1) ∧ Odd (CFBlockNumerator a j t) := by
  simp [canonicalOddBlock, and_assoc]

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
