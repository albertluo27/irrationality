import IrrationalityAr.CanonicalBlockGrowth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter
open scoped Interval
open scoped Topology

namespace IrrationalityAr

/-!
# Euler continued-fraction coefficients

This file adds the explicit coefficient sequence
`[2; 1, 2, 1, 1, 4, 1, 1, 6, 1, ...]` and connects it to the
abstract Euler-pattern API developed in `CanonicalBlockGrowth`.

The hard bridge still missing is the analytic theorem that this sequence is
the simple continued fraction expansion of `Real.exp 1`.
-/

/-- Explicit Euler coefficient sequence for
`e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, ...]`. -/
def eulerCoeff : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 =>
      if n % 3 = 0 then 2 * (n / 3 + 1)
      else 1

theorem eulerCoeff_hasEulerPartialQuotients :
    HasEulerPartialQuotients eulerCoeff := by
  refine ⟨rfl, rfl, ?_⟩
  intro m
  constructor
  · change eulerCoeff ((3 * m) + 2) = 2 * (m + 1)
    simp [eulerCoeff]
  constructor
  · change eulerCoeff ((3 * m + 1) + 2) = 1
    simp [eulerCoeff]
  · change eulerCoeff ((3 * m + 2) + 2) = 1
    simp [eulerCoeff]

theorem eulerCoeff_pos_succ (n : ℕ) :
    0 < eulerCoeff (n + 1) :=
  eulerPartialQuotients_pos_succ eulerCoeff_hasEulerPartialQuotients n

theorem eulerCoeff_canonicalBlockExponent_eq_zero :
    canonicalBlockExponent eulerCoeff = 0 :=
  canonicalBlockExponent_eq_zero_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients

theorem eulerCoeff_partialQuotientGrowthTau_eq_zero :
    partialQuotientGrowthTau eulerCoeff = 0 :=
  partialQuotientGrowthTau_eq_zero_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients

theorem eulerCoeff_denominatorRatioExponent_eq_one :
    denominatorRatioExponent eulerCoeff = 1 :=
  denominatorRatioExponent_eq_one_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients

theorem eulerCoeff_denominatorRatio_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        Real.log (continuantDen eulerCoeff (n + 1) : ℝ) /
          Real.log (continuantDen eulerCoeff n : ℝ))
      atTop (𝓝 1) :=
  denominatorRatio_tendsto_one_of_log_partialQuotient_tendsto_zero
    eulerCoeff_pos_succ
    (euler_log_partialQuotient_div_log_continuantDen_tendsto_zero
      eulerCoeff_hasEulerPartialQuotients)

theorem eulerCoeff_hasCanonicalBlockGrowthFormula :
    HasCanonicalBlockGrowthFormula eulerCoeff :=
  hasCanonicalBlockGrowthFormula_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients

theorem eulerCoeff_blockExponent_eq_irrationalityMeasure_formula :
    canonicalBlockExponent eulerCoeff = (2 - 2 : ℝ) / (2 - 1) :=
  blockExponent_eq_irrationalityMeasure_formula_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients
    (by
      simp [HasIrrationalityMeasureFromCF,
        eulerCoeff_partialQuotientGrowthTau_eq_zero])

theorem eulerCoeff_irrationalityMeasure_eq_two
    {μ : ℝ}
    (hμ : HasIrrationalityMeasureFromCF eulerCoeff μ) :
    μ = 2 :=
  e_irrationalityMeasure_eq_two_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients hμ

theorem exp_one_hasIrrationalityMeasureFromCF_two :
    HasIrrationalityMeasureFromCF eulerCoeff 2 := by
  simp [HasIrrationalityMeasureFromCF,
    eulerCoeff_partialQuotientGrowthTau_eq_zero]

/-- Cohn's auxiliary coefficient sequence:
`[1; 0, 1, 1, 2, 1, 1, 4, ...]`.

This is not a positive simple continued-fraction sequence, because the
coefficient at index `1` is zero. It is used only as an indexing bridge for
the Hermite/Cohn proof of Euler's continued fraction. -/
def cohnCoeff : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      if n % 3 = 0 then 1
      else if n % 3 = 1 then 1
      else 2 * (n / 3 + 1)

/-- The coefficient shift that drives the Cohn/Euler continuant identities. -/
theorem cohnCoeff_shift_succ_succ (n : ℕ) :
    cohnCoeff (n + 4) = eulerCoeff (n + 2) := by
  let m : ℕ := n / 3
  have hn : n = 3 * m + n % 3 := by
    dsimp [m]
    omega
  have hmod_lt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hmod_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases hmod_cases with h0 | h1 | h2
  · rw [hn, h0]
    simp [cohnCoeff, eulerCoeff]
    omega
  · rw [hn, h1]
    simp [cohnCoeff, eulerCoeff]
  · rw [hn, h2]
    simp [cohnCoeff, eulerCoeff]

/-- Numerators of Cohn's auxiliary convergents. -/
def Pcohn (n : ℕ) : ℕ := continuantNum cohnCoeff n

/-- Denominators of Cohn's auxiliary convergents. -/
def Qcohn (n : ℕ) : ℕ := continuantDen cohnCoeff n

/-- Numerators of Cohn's auxiliary convergents, using the notation from the
Hermite/Cohn proof plan. -/
def cohnNum (n : ℕ) : ℕ := Pcohn n

/-- Denominators of Cohn's auxiliary convergents, using the notation from the
Hermite/Cohn proof plan. -/
def cohnDen (n : ℕ) : ℕ := Qcohn n

theorem cohn_euler_continuantNum_shift (n : ℕ) :
    continuantNum cohnCoeff (n + 2) = continuantNum eulerCoeff n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih_succ =>
      change continuantNum cohnCoeff ((n + 3) + 1) =
        continuantNum eulerCoeff ((n + 1) + 1)
      rw [continuantNum_succ_eq cohnCoeff (n + 3),
        continuantNum_succ_eq eulerCoeff (n + 1)]
      simp [continuantNumPrev]
      rw [cohnCoeff_shift_succ_succ n, ih_succ, ih]

theorem cohn_euler_continuantDen_shift (n : ℕ) :
    continuantDen cohnCoeff (n + 2) = continuantDen eulerCoeff n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih_succ =>
      change continuantDen cohnCoeff ((n + 3) + 1) =
        continuantDen eulerCoeff ((n + 1) + 1)
      rw [continuantDen_succ_eq cohnCoeff (n + 3),
        continuantDen_succ_eq eulerCoeff (n + 1)]
      simp [continuantDenPrev]
      rw [cohnCoeff_shift_succ_succ n, ih_succ, ih]

theorem Pcohn_shift_eq_euler_continuantNum (n : ℕ) :
    Pcohn (n + 2) = continuantNum eulerCoeff n :=
  cohn_euler_continuantNum_shift n

theorem Qcohn_shift_eq_euler_continuantDen (n : ℕ) :
    Qcohn (n + 2) = continuantDen eulerCoeff n :=
  cohn_euler_continuantDen_shift n

theorem cohnNum_shift_two_eq_eulerNum (n : ℕ) :
    cohnNum (n + 2) = continuantNum eulerCoeff n :=
  cohn_euler_continuantNum_shift n

theorem cohnDen_shift_two_eq_eulerDen (n : ℕ) :
    cohnDen (n + 2) = continuantDen eulerCoeff n :=
  cohn_euler_continuantDen_shift n

/-- Hermite's integral
`Aₙ = ∫₀¹ xⁿ(x-1)ⁿ eˣ / n! dx`. -/
noncomputable def Aint (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ((x ^ n) * ((x - 1) ^ n) / (Nat.factorial n : ℝ)) * Real.exp x

/-- Hermite's integral
`Bₙ = ∫₀¹ xⁿ⁺¹(x-1)ⁿ eˣ / n! dx`. -/
noncomputable def Bint (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ((x ^ (n + 1)) * ((x - 1) ^ n) / (Nat.factorial n : ℝ)) * Real.exp x

/-- Hermite's integral
`Cₙ = ∫₀¹ xⁿ(x-1)ⁿ⁺¹ eˣ / n! dx`. -/
noncomputable def Cint (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ((x ^ n) * ((x - 1) ^ (n + 1)) / (Nat.factorial n : ℝ)) * Real.exp x

theorem Aint_zero :
    Aint 0 = Real.exp 1 - 1 := by
  simp [Aint]

theorem Bint_zero :
    Bint 0 = 1 := by
  simp [Bint]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => x * Real.exp x - Real.exp x)
    (f' := fun x : ℝ => x * Real.exp x)
    (fun x _hx => by
      have hmul : HasDerivAt (fun y : ℝ => y * Real.exp y)
          (Real.exp x + x * Real.exp x) x := by
        simpa using (hasDerivAt_id x).mul (Real.hasDerivAt_exp x)
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        hmul.sub (Real.hasDerivAt_exp x))
    ((continuous_id.mul Real.continuous_exp).intervalIntegrable 0 1)
  simpa using h

theorem Cint_zero :
    Cint 0 = 2 - Real.exp 1 := by
  simp [Cint]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => x * Real.exp x - 2 * Real.exp x)
    (f' := fun x : ℝ => (x - 1) * Real.exp x)
    (fun x _hx => by
      have hmul : HasDerivAt (fun y : ℝ => y * Real.exp y)
          (Real.exp x + x * Real.exp x) x := by
        simpa using (hasDerivAt_id x).mul (Real.hasDerivAt_exp x)
      have htwo : HasDerivAt (fun y : ℝ => 2 * Real.exp y)
          (2 * Real.exp x) x := by
        simpa using (Real.hasDerivAt_exp x).const_mul (2 : ℝ)
      convert hmul.sub htwo using 1
      ring_nf)
    (((continuous_id.sub continuous_const).mul Real.continuous_exp).intervalIntegrable 0 1)
  convert h using 1
  simp
  ring

theorem Cint_rec (n : ℕ) :
    Cint n = Bint n - Aint n := by
  rw [Aint, Bint, Cint]
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x _hx
    dsimp
    rw [pow_succ, pow_succ]
    ring
  · exact (by fun_prop : Continuous fun x : ℝ =>
      x ^ (n + 1) * (x - 1) ^ n / (Nat.factorial n : ℝ) * Real.exp x).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous fun x : ℝ =>
      x ^ n * (x - 1) ^ n / (Nat.factorial n : ℝ) * Real.exp x).intervalIntegrable 0 1

private lemma hasDerivAt_Aint_succ_integrand (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((y ^ (n + 1)) * ((y - 1) ^ (n + 1)) /
        (Nat.factorial (n + 1) : ℝ)) * Real.exp y)
      ((((x ^ (n + 1)) * ((x - 1) ^ (n + 1)) /
        (Nat.factorial (n + 1) : ℝ)) * Real.exp x) +
        (((x ^ (n + 1)) * ((x - 1) ^ n) /
          (Nat.factorial n : ℝ)) * Real.exp x) +
        (((x ^ n) * ((x - 1) ^ (n + 1)) /
          (Nat.factorial n : ℝ)) * Real.exp x))
      x := by
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hpowx : HasDerivAt (fun y : ℝ => y ^ (n + 1))
      ((n + 1 : ℝ) * x ^ n) x := by
    simpa using hasDerivAt_pow (n + 1) x
  have hpowxm1 : HasDerivAt (fun y : ℝ => (y - 1) ^ (n + 1))
      ((n + 1 : ℝ) * (x - 1) ^ n) x := by
    simpa using hsub.pow (n + 1)
  have hprod : HasDerivAt
      (fun y : ℝ => y ^ (n + 1) * (y - 1) ^ (n + 1))
      (((n + 1 : ℝ) * x ^ n) * (x - 1) ^ (n + 1) +
        x ^ (n + 1) * ((n + 1 : ℝ) * (x - 1) ^ n)) x := by
    simpa [mul_assoc] using hpowx.mul hpowxm1
  have hdiv : HasDerivAt
      (fun y : ℝ => y ^ (n + 1) * (y - 1) ^ (n + 1) /
        (Nat.factorial (n + 1) : ℝ))
      ((((n + 1 : ℝ) * x ^ n) * (x - 1) ^ (n + 1) +
        x ^ (n + 1) * ((n + 1 : ℝ) * (x - 1) ^ n)) /
        (Nat.factorial (n + 1) : ℝ)) x := by
    simpa using hprod.div_const (Nat.factorial (n + 1) : ℝ)
  convert hdiv.mul (Real.hasDerivAt_exp x) using 1
  rw [Nat.factorial_succ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
  push_cast
  ring_nf

theorem Aint_rec_succ (n : ℕ) :
    Aint (n + 1) = - Bint n - Cint n := by
  let fA : ℝ → ℝ := fun x =>
    ((x ^ (n + 1)) * ((x - 1) ^ (n + 1)) / (Nat.factorial (n + 1) : ℝ)) *
      Real.exp x
  let fB : ℝ → ℝ := fun x =>
    ((x ^ (n + 1)) * ((x - 1) ^ n) / (Nat.factorial n : ℝ)) * Real.exp x
  let fC : ℝ → ℝ := fun x =>
    ((x ^ n) * ((x - 1) ^ (n + 1)) / (Nat.factorial n : ℝ)) * Real.exp x
  have hA : IntervalIntegrable fA MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fA]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ (n + 1)) * ((x - 1) ^ (n + 1)) / (Nat.factorial (n + 1) : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hB : IntervalIntegrable fB MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fB]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ (n + 1)) * ((x - 1) ^ n) / (Nat.factorial n : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hC : IntervalIntegrable fC MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fC]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ n) * ((x - 1) ^ (n + 1)) / (Nat.factorial n : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt fA (fA x + fB x + fC x) x := by
    intro x _hx
    dsimp [fA, fB, fC]
    exact hasDerivAt_Aint_succ_integrand n x
  have htotal : ∫ x in (0 : ℝ)..1, (fA x + fB x + fC x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (f := fA) (f' := fun x : ℝ => fA x + fB x + fC x)
      hderiv ((hA.add hB).add hC)
    dsimp [fA] at h
    simpa using h
  have hsplit :
      ∫ x in (0 : ℝ)..1, (fA x + fB x + fC x) =
        Aint (n + 1) + Bint n + Cint n := by
    rw [intervalIntegral.integral_add (hA.add hB) hC]
    rw [intervalIntegral.integral_add hA hB]
    rfl
  have hsum : Aint (n + 1) + Bint n + Cint n = 0 := by
    rw [← hsplit]
    exact htotal
  linarith

theorem Aint_rec {n : ℕ} (hn : 0 < n) :
    Aint n = - Bint (n - 1) - Cint (n - 1) := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Aint_rec_succ n

private lemma hasDerivAt_Bint_succ_integrand (m : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((y ^ (m + 1)) * ((y - 1) ^ (m + 2)) /
        (Nat.factorial (m + 1) : ℝ)) * Real.exp y)
      ((((x ^ (m + 2)) * ((x - 1) ^ (m + 1)) /
        (Nat.factorial (m + 1) : ℝ)) * Real.exp x) +
        (2 * (m + 1 : ℝ)) *
          (((x ^ (m + 1)) * ((x - 1) ^ (m + 1)) /
            (Nat.factorial (m + 1) : ℝ)) * Real.exp x) -
        (((x ^ m) * ((x - 1) ^ (m + 1)) /
          (Nat.factorial m : ℝ)) * Real.exp x))
      x := by
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hpowx : HasDerivAt (fun y : ℝ => y ^ (m + 1))
      ((m + 1 : ℝ) * x ^ m) x := by
    simpa using hasDerivAt_pow (m + 1) x
  have hpowxm1 : HasDerivAt (fun y : ℝ => (y - 1) ^ (m + 2))
      ((m + 2 : ℝ) * (x - 1) ^ (m + 1)) x := by
    simpa using hsub.pow (m + 2)
  have hprod : HasDerivAt
      (fun y : ℝ => y ^ (m + 1) * (y - 1) ^ (m + 2))
      (((m + 1 : ℝ) * x ^ m) * (x - 1) ^ (m + 2) +
        x ^ (m + 1) * ((m + 2 : ℝ) * (x - 1) ^ (m + 1))) x := by
    simpa [mul_assoc] using hpowx.mul hpowxm1
  have hdiv : HasDerivAt
      (fun y : ℝ => y ^ (m + 1) * (y - 1) ^ (m + 2) /
        (Nat.factorial (m + 1) : ℝ))
      ((((m + 1 : ℝ) * x ^ m) * (x - 1) ^ (m + 2) +
        x ^ (m + 1) * ((m + 2 : ℝ) * (x - 1) ^ (m + 1))) /
        (Nat.factorial (m + 1) : ℝ)) x := by
    simpa using hprod.div_const (Nat.factorial (m + 1) : ℝ)
  convert hdiv.mul (Real.hasDerivAt_exp x) using 1
  rw [Nat.factorial_succ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
  push_cast
  ring_nf

theorem Bint_rec_succ (m : ℕ) :
    Bint (m + 1) = - (2 * (m + 1 : ℝ)) * Aint (m + 1) + Cint m := by
  let fD : ℝ → ℝ := fun x =>
    ((x ^ (m + 1)) * ((x - 1) ^ (m + 2)) / (Nat.factorial (m + 1) : ℝ)) *
      Real.exp x
  let fB : ℝ → ℝ := fun x =>
    ((x ^ (m + 2)) * ((x - 1) ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ)) *
      Real.exp x
  let fA : ℝ → ℝ := fun x =>
    ((x ^ (m + 1)) * ((x - 1) ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ)) *
      Real.exp x
  let fC : ℝ → ℝ := fun x =>
    ((x ^ m) * ((x - 1) ^ (m + 1)) / (Nat.factorial m : ℝ)) * Real.exp x
  let c : ℝ := 2 * (m + 1 : ℝ)
  have hD : IntervalIntegrable fD MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fD]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ (m + 1)) * ((x - 1) ^ (m + 2)) / (Nat.factorial (m + 1) : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hB : IntervalIntegrable fB MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fB]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ (m + 2)) * ((x - 1) ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hA : IntervalIntegrable fA MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fA]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ (m + 1)) * ((x - 1) ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hC : IntervalIntegrable fC MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp [fC]
    exact (by fun_prop : Continuous fun x : ℝ =>
      ((x ^ m) * ((x - 1) ^ (m + 1)) / (Nat.factorial m : ℝ)) *
        Real.exp x).intervalIntegrable 0 1
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt fD (fB x + c * fA x - fC x) x := by
    intro x _hx
    dsimp [fD, fB, fA, fC, c]
    exact hasDerivAt_Bint_succ_integrand m x
  have htotal : ∫ x in (0 : ℝ)..1, (fB x + c * fA x - fC x) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) (f := fD)
      (f' := fun x : ℝ => fB x + c * fA x - fC x)
      hderiv ((hB.add (hA.const_mul c)).sub hC)
    dsimp [fD] at h
    simpa using h
  have hsplit :
      ∫ x in (0 : ℝ)..1, (fB x + c * fA x - fC x) =
        Bint (m + 1) + c * Aint (m + 1) - Cint m := by
    rw [intervalIntegral.integral_sub (hB.add (hA.const_mul c)) hC]
    rw [intervalIntegral.integral_add hB (hA.const_mul c)]
    rw [intervalIntegral.integral_const_mul]
    rfl
  have hsum : Bint (m + 1) + c * Aint (m + 1) - Cint m = 0 := by
    rw [← hsplit]
    exact htotal
  dsimp [c] at hsum
  linarith

theorem Bint_rec {n : ℕ} (hn : 0 < n) :
    Bint n = - (2 * (n : ℝ)) * Aint n + Cint (n - 1) := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Bint_rec_succ n

private lemma Pcohn_three_mul_add_three (n : ℕ) :
    Pcohn (3 * n + 3) = Pcohn (3 * n + 2) + Pcohn (3 * n + 1) := by
  rw [show 3 * n + 3 = (3 * n + 2) + 1 by omega]
  rw [Pcohn, continuantNum_succ_eq]
  simp [Pcohn, continuantNumPrev]
  rw [show cohnCoeff (3 * n + 2 + 1) = 1 by
    change cohnCoeff ((3 * n + 1) + 2) = 1
    simp [cohnCoeff]
  ]
  simp

private lemma Qcohn_three_mul_add_three (n : ℕ) :
    Qcohn (3 * n + 3) = Qcohn (3 * n + 2) + Qcohn (3 * n + 1) := by
  rw [show 3 * n + 3 = (3 * n + 2) + 1 by omega]
  rw [Qcohn, continuantDen_succ_eq]
  simp [Qcohn, continuantDenPrev]
  rw [show cohnCoeff (3 * n + 2 + 1) = 1 by
    change cohnCoeff ((3 * n + 1) + 2) = 1
    simp [cohnCoeff]
  ]
  simp

private lemma Pcohn_three_mul_add_four (n : ℕ) :
    Pcohn (3 * n + 4) =
      2 * (n + 1) * Pcohn (3 * n + 3) + Pcohn (3 * n + 2) := by
  rw [show 3 * n + 4 = (3 * n + 3) + 1 by omega]
  rw [Pcohn, continuantNum_succ_eq]
  simp [Pcohn, continuantNumPrev]
  left
  change cohnCoeff ((3 * n + 2) + 2) = 2 * (n + 1)
  simp [cohnCoeff]
  omega

private lemma Qcohn_three_mul_add_four (n : ℕ) :
    Qcohn (3 * n + 4) =
      2 * (n + 1) * Qcohn (3 * n + 3) + Qcohn (3 * n + 2) := by
  rw [show 3 * n + 4 = (3 * n + 3) + 1 by omega]
  rw [Qcohn, continuantDen_succ_eq]
  simp [Qcohn, continuantDenPrev]
  left
  change cohnCoeff ((3 * n + 2) + 2) = 2 * (n + 1)
  simp [cohnCoeff]
  omega

private lemma Pcohn_three_mul_add_five (n : ℕ) :
    Pcohn (3 * n + 5) = Pcohn (3 * n + 4) + Pcohn (3 * n + 3) := by
  rw [show 3 * n + 5 = (3 * n + 4) + 1 by omega]
  rw [Pcohn, continuantNum_succ_eq]
  simp [Pcohn, continuantNumPrev]
  rw [show cohnCoeff (3 * n + 4 + 1) = 1 by
    change cohnCoeff ((3 * (n + 1)) + 2) = 1
    simp [cohnCoeff]
  ]
  simp

private lemma Qcohn_three_mul_add_five (n : ℕ) :
    Qcohn (3 * n + 5) = Qcohn (3 * n + 4) + Qcohn (3 * n + 3) := by
  rw [show 3 * n + 5 = (3 * n + 4) + 1 by omega]
  rw [Qcohn, continuantDen_succ_eq]
  simp [Qcohn, continuantDenPrev]
  rw [show cohnCoeff (3 * n + 4 + 1) = 1 by
    change cohnCoeff ((3 * (n + 1)) + 2) = 1
    simp [cohnCoeff]
  ]
  simp

theorem hermite_ABC_identity (n : ℕ) :
    Aint n = (Qcohn (3 * n) : ℝ) * Real.exp 1 - (Pcohn (3 * n) : ℝ) ∧
    Bint n = (Pcohn (3 * n + 1) : ℝ) -
      (Qcohn (3 * n + 1) : ℝ) * Real.exp 1 ∧
    Cint n = (Pcohn (3 * n + 2) : ℝ) -
      (Qcohn (3 * n + 2) : ℝ) * Real.exp 1 := by
  induction n with
  | zero =>
      constructor
      · simp [Aint_zero, Pcohn, Qcohn, cohnCoeff, continuantNum, continuantDen]
      constructor
      · simp [Bint_zero, Pcohn, Qcohn, cohnCoeff, continuantNum, continuantDen]
      · simp [Cint_zero, Pcohn, Qcohn, cohnCoeff, continuantNum, continuantDen]
  | succ n ih =>
      rcases ih with ⟨hA, _hB, hC⟩
      have hA_succ : Aint (n + 1) =
          (Qcohn (3 * (n + 1)) : ℝ) * Real.exp 1 -
            (Pcohn (3 * (n + 1)) : ℝ) := by
        rw [Aint_rec_succ, _hB, hC]
        rw [show 3 * (n + 1) = 3 * n + 3 by omega]
        rw [Qcohn_three_mul_add_three, Pcohn_three_mul_add_three]
        push_cast
        ring
      have hB_succ : Bint (n + 1) =
          (Pcohn (3 * (n + 1) + 1) : ℝ) -
            (Qcohn (3 * (n + 1) + 1) : ℝ) * Real.exp 1 := by
        rw [Bint_rec_succ, hA_succ, hC]
        rw [show 3 * (n + 1) = 3 * n + 3 by omega]
        rw [show 3 * n + 3 + 1 = 3 * n + 4 by omega]
        rw [Pcohn_three_mul_add_four, Qcohn_three_mul_add_four]
        push_cast
        ring
      have hC_succ : Cint (n + 1) =
          (Pcohn (3 * (n + 1) + 2) : ℝ) -
            (Qcohn (3 * (n + 1) + 2) : ℝ) * Real.exp 1 := by
        rw [Cint_rec, hB_succ, hA_succ]
        rw [show 3 * (n + 1) = 3 * n + 3 by omega]
        rw [show 3 * n + 3 + 1 = 3 * n + 4 by omega]
        rw [show 3 * n + 3 + 2 = 3 * n + 5 by omega]
        rw [Pcohn_three_mul_add_five, Qcohn_three_mul_add_five]
        push_cast
        ring
      exact ⟨hA_succ, hB_succ, hC_succ⟩

theorem hermite_A_identity (n : ℕ) :
    Aint n = (Qcohn (3 * n) : ℝ) * Real.exp 1 - (Pcohn (3 * n) : ℝ) :=
  (hermite_ABC_identity n).1

theorem hermite_B_identity (n : ℕ) :
    Bint n = (Pcohn (3 * n + 1) : ℝ) -
      (Qcohn (3 * n + 1) : ℝ) * Real.exp 1 :=
  (hermite_ABC_identity n).2.1

theorem hermite_C_identity (n : ℕ) :
    Cint n = (Pcohn (3 * n + 2) : ℝ) -
      (Qcohn (3 * n + 2) : ℝ) * Real.exp 1 :=
  (hermite_ABC_identity n).2.2

/-- Signed error of Cohn's auxiliary convergents. -/
noncomputable def cohnErr (i : ℕ) : ℝ :=
  (cohnDen i : ℝ) * Real.exp 1 - (cohnNum i : ℝ)

theorem cohnErr_three_mul (n : ℕ) :
    cohnErr (3 * n) = Aint n := by
  rw [cohnErr, cohnDen, cohnNum, hermite_A_identity]

theorem cohnErr_three_mul_add_one (n : ℕ) :
    cohnErr (3 * n + 1) = - Bint n := by
  rw [cohnErr, cohnDen, cohnNum, hermite_B_identity]
  ring

theorem cohnErr_three_mul_add_two (n : ℕ) :
    cohnErr (3 * n + 2) = - Cint n := by
  rw [cohnErr, cohnDen, cohnNum, hermite_C_identity]
  ring

private lemma norm_hermite_integrand_le_exp_div_factorial
    (i j n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖((x ^ i) * ((x - 1) ^ j) / (Nat.factorial n : ℝ)) * Real.exp x‖ ≤
      Real.exp 1 / (Nat.factorial n : ℝ) := by
  have hfac_pos : 0 < (Nat.factorial n : ℝ) := by positivity
  have hx_abs : ‖x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hxm1_abs : ‖x - 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    have hle0 : x - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hle0]
    linarith
  have hxp : ‖x ^ i‖ ≤ 1 := by
    calc
      ‖x ^ i‖ = ‖x‖ ^ i := norm_pow _ _
      _ ≤ 1 ^ i := pow_le_pow_left₀ (norm_nonneg _) hx_abs i
      _ = 1 := by simp
  have hxm1p : ‖(x - 1) ^ j‖ ≤ 1 := by
    calc
      ‖(x - 1) ^ j‖ = ‖x - 1‖ ^ j := norm_pow _ _
      _ ≤ 1 ^ j := pow_le_pow_left₀ (norm_nonneg _) hxm1_abs j
      _ = 1 := by simp
  have hexp_le : ‖Real.exp x‖ ≤ Real.exp 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.mpr hx1
  have hnorm :
      ‖((x ^ i) * ((x - 1) ^ j) / (Nat.factorial n : ℝ)) * Real.exp x‖ =
        (‖x ^ i‖ * ‖(x - 1) ^ j‖ / (Nat.factorial n : ℝ)) * ‖Real.exp x‖ := by
    rw [norm_mul, norm_div, norm_mul, Real.norm_of_nonneg hfac_pos.le]
  rw [hnorm]
  calc
    (‖x ^ i‖ * ‖(x - 1) ^ j‖ / (Nat.factorial n : ℝ)) * ‖Real.exp x‖
        ≤ (1 * 1 / (Nat.factorial n : ℝ)) * Real.exp 1 := by gcongr
    _ = Real.exp 1 / (Nat.factorial n : ℝ) := by ring

private lemma norm_hermite_integral_le_exp_div_factorial (i j n : ℕ) :
    ‖∫ x in (0 : ℝ)..1,
      ((x ^ i) * ((x - 1) ^ j) / (Nat.factorial n : ℝ)) * Real.exp x‖ ≤
      Real.exp 1 / (Nat.factorial n : ℝ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := Real.exp 1 / (Nat.factorial n : ℝ))
    (f := fun x : ℝ =>
      ((x ^ i) * ((x - 1) ^ j) / (Nat.factorial n : ℝ)) * Real.exp x)
    (fun x hx => by
      have hxI : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact norm_hermite_integrand_le_exp_div_factorial i j n (le_of_lt hxI.1) hxI.2)
  simpa using h

theorem abs_Aint_le_exp_div_factorial (n : ℕ) :
    |Aint n| ≤ Real.exp 1 / (Nat.factorial n : ℝ) := by
  simpa [Aint, Real.norm_eq_abs] using norm_hermite_integral_le_exp_div_factorial n n n

theorem abs_Bint_le_exp_div_factorial (n : ℕ) :
    |Bint n| ≤ Real.exp 1 / (Nat.factorial n : ℝ) := by
  simpa [Bint, Real.norm_eq_abs] using norm_hermite_integral_le_exp_div_factorial (n + 1) n n

theorem abs_Cint_le_exp_div_factorial (n : ℕ) :
    |Cint n| ≤ Real.exp 1 / (Nat.factorial n : ℝ) := by
  simpa [Cint, Real.norm_eq_abs] using norm_hermite_integral_le_exp_div_factorial n (n + 1) n

private theorem exp_div_factorial_tendsto_zero :
    Tendsto (fun n : ℕ => Real.exp 1 / (Nat.factorial n : ℝ)) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)).const_mul (Real.exp 1)
  simpa [div_eq_mul_inv] using h

theorem Aint_tendsto_zero :
    Tendsto Aint atTop (𝓝 0) := by
  exact squeeze_zero_norm (fun n => by
    simpa [Real.norm_eq_abs] using abs_Aint_le_exp_div_factorial n)
    exp_div_factorial_tendsto_zero

theorem Bint_tendsto_zero :
    Tendsto Bint atTop (𝓝 0) := by
  exact squeeze_zero_norm (fun n => by
    simpa [Real.norm_eq_abs] using abs_Bint_le_exp_div_factorial n)
    exp_div_factorial_tendsto_zero

theorem Cint_tendsto_zero :
    Tendsto Cint atTop (𝓝 0) := by
  exact squeeze_zero_norm (fun n => by
    simpa [Real.norm_eq_abs] using abs_Cint_le_exp_div_factorial n)
    exp_div_factorial_tendsto_zero

lemma abs_cohnErr_le_ABC_sum (i : ℕ) :
    |cohnErr i| ≤ |Aint (i / 3)| + |Bint (i / 3)| + |Cint (i / 3)| := by
  let m : ℕ := i / 3
  have hi : i = 3 * m + i % 3 := by
    dsimp [m]
    omega
  have hmod_lt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [hi, h0]
    simp
    rw [cohnErr_three_mul]
    have hBnonneg : 0 ≤ |Bint m| := abs_nonneg _
    have hCnonneg : 0 ≤ |Cint m| := abs_nonneg _
    linarith
  · have hdiv1 : (3 * m + 1) / 3 = m := by omega
    rw [hi, h1]
    simp [hdiv1]
    rw [cohnErr_three_mul_add_one, abs_neg]
    have hA_nonneg : 0 ≤ |Aint m| := abs_nonneg _
    have hC_nonneg : 0 ≤ |Cint m| := abs_nonneg _
    linarith
  · have hdiv2 : (3 * m + 2) / 3 = m := by omega
    rw [hi, h2]
    simp [hdiv2]
    rw [cohnErr_three_mul_add_two, abs_neg]
    have hA_nonneg : 0 ≤ |Aint m| := abs_nonneg _
    have hB_nonneg : 0 ≤ |Bint m| := abs_nonneg _
    linarith

theorem cohnErr_tendsto_zero :
    Tendsto cohnErr atTop (𝓝 0) := by
  have hdiv : Tendsto (fun i : ℕ => i / 3) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num : 3 ≠ 0)
  have hA : Tendsto (fun i : ℕ => |Aint (i / 3)|) atTop (𝓝 0) := by
    have h := Aint_tendsto_zero.comp hdiv
    simpa using h.abs
  have hB : Tendsto (fun i : ℕ => |Bint (i / 3)|) atTop (𝓝 0) := by
    have h := Bint_tendsto_zero.comp hdiv
    simpa using h.abs
  have hC : Tendsto (fun i : ℕ => |Cint (i / 3)|) atTop (𝓝 0) := by
    have h := Cint_tendsto_zero.comp hdiv
    simpa using h.abs
  have hbound : ∀ i : ℕ,
      ‖cohnErr i‖ ≤ |Aint (i / 3)| + |Bint (i / 3)| + |Cint (i / 3)| := by
    intro i
    simpa [Real.norm_eq_abs] using abs_cohnErr_le_ABC_sum i
  exact squeeze_zero_norm hbound (by simpa using (hA.add hB).add hC)

private lemma one_le_euler_continuantDen (n : ℕ) :
    1 ≤ continuantDen eulerCoeff n := by
  have hfib := fib_le_continuantDen_of_partials_pos eulerCoeff eulerCoeff_pos_succ n
  have hfibpos : 0 < Nat.fib (n + 1) := by
    simp
  exact Nat.succ_le_of_lt (lt_of_lt_of_le hfibpos hfib)

theorem cohn_convergents_shifted_tendsto_exp_one :
    Tendsto
      (fun n : ℕ => (cohnNum (n + 2) : ℝ) / (cohnDen (n + 2) : ℝ))
      atTop
      (𝓝 (Real.exp 1)) := by
  have herr_shift : Tendsto (fun n : ℕ => cohnErr (n + 2)) atTop (𝓝 0) :=
    (Filter.tendsto_add_atTop_iff_nat 2).2 cohnErr_tendsto_zero
  have herr_norm : Tendsto (fun n : ℕ => ‖cohnErr (n + 2)‖) atTop (𝓝 0) := by
    simpa using herr_shift.norm
  have hdiff : Tendsto
      (fun n : ℕ => (cohnNum (n + 2) : ℝ) / (cohnDen (n + 2) : ℝ) - Real.exp 1)
      atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) herr_norm
    have hden_nat : 1 ≤ cohnDen (n + 2) := by
      rw [cohnDen_shift_two_eq_eulerDen]
      exact one_le_euler_continuantDen n
    have hden_pos : 0 < (cohnDen (n + 2) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hden_nat)
    have hden_ge_one : (1 : ℝ) ≤ (cohnDen (n + 2) : ℝ) := by
      exact_mod_cast hden_nat
    have hden_norm_ge_one : (1 : ℝ) ≤ ‖(cohnDen (n + 2) : ℝ)‖ := by
      simpa [Real.norm_of_nonneg hden_pos.le] using hden_ge_one
    have hdiff_eq :
        (cohnNum (n + 2) : ℝ) / (cohnDen (n + 2) : ℝ) - Real.exp 1 =
          - cohnErr (n + 2) / (cohnDen (n + 2) : ℝ) := by
      field_simp [hden_pos.ne']
      rw [cohnErr]
      ring
    rw [hdiff_eq, norm_div, norm_neg]
    exact div_le_self (norm_nonneg _) hden_norm_ge_one
  exact tendsto_sub_nhds_zero_iff.mp hdiff

theorem eulerCoeff_convergents_tendsto_exp_one :
    Tendsto
      (fun n : ℕ =>
        (continuantNum eulerCoeff n : ℝ) / (continuantDen eulerCoeff n : ℝ))
      atTop
      (𝓝 (Real.exp 1)) := by
  simpa [cohnNum_shift_two_eq_eulerNum, cohnDen_shift_two_eq_eulerDen] using
    cohn_convergents_shifted_tendsto_exp_one

theorem finiteCFExact_split_prefix (a : ℕ → ℕ) (n m : ℕ) :
    finiteCFExact a (n + 1 + m) =
      finiteCFWithTail a n (finiteCFExact (fun i : ℕ => a (n + 1 + i)) m) := by
  induction n generalizing a with
  | zero =>
      rw [show 0 + 1 + m = m + 1 by omega]
      rw [finiteCFExact_succ_eq_head_add_inv_tail]
      simp [finiteCFWithTail]
      congr 1
      funext i
      congr 1
      omega
  | succ n ih =>
      rw [show n + 1 + 1 + m = (n + 1 + m) + 1 by omega]
      rw [finiteCFExact_succ_eq_head_add_inv_tail]
      rw [finiteCFWithTail_succ_eq_head_add_inv_tail]
      congr 2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (fun i : ℕ => a (i + 1))

theorem finiteCFExact_shift_prefix_commonPrefixMap
    (a : ℕ → ℕ) (n m : ℕ)
    (hpos : ∀ i : ℕ, 0 < a (n + 1 + i)) :
    finiteCFExact a (n + 1 + m) =
      commonPrefixMap a n (finiteCFExact (fun i : ℕ => a (n + 1 + i)) m) := by
  rw [finiteCFExact_split_prefix]
  rw [finiteCFWithTail_eq_commonPrefixMap]
  exact finiteCFExact_pos_of_pos (fun i : ℕ => a (n + 1 + i)) m
    (fun i _hi => hpos i)

theorem finiteCFExact_tendsto_of_convergents_tendsto
    {α : ℝ} {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hlim :
      Tendsto
        (fun n : ℕ =>
          (continuantNum a n : ℝ) / (continuantDen a n : ℝ))
        atTop
        (𝓝 α)) :
    Tendsto (fun n : ℕ => finiteCFExact a n) atTop (𝓝 α) := by
  refine hlim.congr' ?_
  exact Eventually.of_forall fun n => by
    change (continuantNum a n : ℝ) / (continuantDen a n : ℝ) = finiteCFExact a n
    symm
    rw [finiteCFExact_eq_ratValue_continuants]
    · rfl
    · intro i hi1 _hi
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi1) with ⟨j, rfl⟩
      exact hpos j

lemma finiteCFExact_head_le_of_pos
    (a : ℕ → ℕ)
    (hpos : ∀ i : ℕ, 0 < a i) :
    ∀ m : ℕ, (a 0 : ℝ) ≤ finiteCFExact a m
  | 0 => by simp [finiteCFExact]
  | m + 1 => by
      rw [finiteCFExact_succ_eq_head_add_inv_tail]
      have htail : 0 < finiteCFExact (fun i : ℕ => a (i + 1)) m :=
        finiteCFExact_pos_of_pos (fun i : ℕ => a (i + 1)) m
          (fun i _hi => hpos (i + 1))
      have hinv : 0 ≤ 1 / finiteCFExact (fun i : ℕ => a (i + 1)) m :=
        le_of_lt (one_div_pos.mpr htail)
      linarith

lemma finiteCFExact_le_head_add_one_of_pos
    (a : ℕ → ℕ)
    (hpos : ∀ i : ℕ, 0 < a i) :
    ∀ m : ℕ, finiteCFExact a m ≤ (a 0 : ℝ) + 1
  | 0 => by simp [finiteCFExact]
  | m + 1 => by
      rw [finiteCFExact_succ_eq_head_add_inv_tail]
      have htail_ge_head :
          ((fun i : ℕ => a (i + 1)) 0 : ℝ) ≤
            finiteCFExact (fun i : ℕ => a (i + 1)) m :=
        finiteCFExact_head_le_of_pos (fun i : ℕ => a (i + 1))
          (fun i => hpos (i + 1)) m
      have hhead_ge_one : (1 : ℝ) ≤ a 1 := by
        exact_mod_cast hpos 1
      have htail_ge_one :
          (1 : ℝ) ≤ finiteCFExact (fun i : ℕ => a (i + 1)) m := by
        exact le_trans hhead_ge_one htail_ge_head
      have htail_pos : 0 < finiteCFExact (fun i : ℕ => a (i + 1)) m := by
        linarith
      have hinv_le_one :
          1 / finiteCFExact (fun i : ℕ => a (i + 1)) m ≤ 1 := by
        exact (div_le_one htail_pos).mpr htail_ge_one
      linarith

lemma finite_tail_two_deep_mem_Icc
    (a : ℕ → ℕ) (n k : ℕ)
    (hpos : ∀ m : ℕ, 0 < a (m + 1)) :
    let L : ℝ :=
      (a (n + 1) : ℝ) + 1 / ((a (n + 2) : ℝ) + 1)
    let U : ℝ :=
      (a (n + 1) : ℝ) +
        1 / ((a (n + 2) : ℝ) +
          1 / ((a (n + 3) : ℝ) + 1))
    finiteCFExact (fun i : ℕ => a (n + 1 + i)) (k + 2)
      ∈ Set.Icc L U := by
  dsimp
  rw [show k + 2 = (k + 1) + 1 by omega]
  rw [finiteCFExact_succ_eq_head_add_inv_tail]
  rw [finiteCFExact_succ_eq_head_add_inv_tail]
  dsimp
  set δ : ℝ := finiteCFExact (fun i : ℕ => a (n + 1 + (i + 1 + 1))) k
  have hδ_ge_head :
      (a (n + 3) : ℝ) ≤ δ := by
    have h := finiteCFExact_head_le_of_pos
      (fun i : ℕ => a (n + 1 + (i + 1 + 1)))
      (fun i => by
        have := hpos (n + i + 2)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
      k
    simpa [δ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hδ_le_head_add_one :
      δ ≤ (a (n + 3) : ℝ) + 1 := by
    have h := finiteCFExact_le_head_add_one_of_pos
      (fun i : ℕ => a (n + 1 + (i + 1 + 1)))
      (fun i => by
        have := hpos (n + i + 2)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
      k
    simpa [δ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have ha3_ge_one : (1 : ℝ) ≤ a (n + 3) := by
    exact_mod_cast hpos (n + 2)
  have hδ_ge_one : (1 : ℝ) ≤ δ := le_trans ha3_ge_one hδ_ge_head
  have hδ_pos : 0 < δ := by linarith
  constructor
  · have hinvδ_le_one : 1 / δ ≤ 1 := by
      exact (div_le_one hδ_pos).mpr hδ_ge_one
    have hD_pos :
        0 < (a (n + 2) : ℝ) + 1 / δ := by
      have hinv_pos : 0 < 1 / δ := one_div_pos.mpr hδ_pos
      positivity
    have hD_le :
        (a (n + 2) : ℝ) + 1 / δ ≤ (a (n + 2) : ℝ) + 1 := by
      linarith
    have hrecip :
        1 / ((a (n + 2) : ℝ) + 1) ≤
          1 / ((a (n + 2) : ℝ) + 1 / δ) := by
      exact one_div_le_one_div_of_le hD_pos hD_le
    linarith
  · have hupper_den_pos : 0 < (a (n + 3) : ℝ) + 1 := by positivity
    have hrecip_lower :
        1 / ((a (n + 3) : ℝ) + 1) ≤ 1 / δ := by
      exact one_div_le_one_div_of_le hδ_pos hδ_le_head_add_one
    have hDmin_pos :
        0 < (a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1) := by
      have hinv_pos : 0 < 1 / ((a (n + 3) : ℝ) + 1) :=
        one_div_pos.mpr hupper_den_pos
      positivity
    have hDmin_le :
        (a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1) ≤
          (a (n + 2) : ℝ) + 1 / δ := by
      linarith
    have hrecip :
        1 / ((a (n + 2) : ℝ) + 1 / δ) ≤
          1 / ((a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1)) := by
      exact one_div_le_one_div_of_le hDmin_pos hDmin_le
    linarith

lemma finite_tail_interval_strict
    (a : ℕ → ℕ) (n : ℕ)
    (hpos : ∀ m : ℕ, 0 < a (m + 1)) :
    let L : ℝ := (a (n + 1) : ℝ) + 1 / ((a (n + 2) : ℝ) + 1)
    let U : ℝ := (a (n + 1) : ℝ) +
      1 / ((a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1))
    (a (n + 1) : ℝ) < L ∧ U < (a (n + 1) : ℝ) + 1 := by
  dsimp
  constructor
  · have hden : 0 < (a (n + 2) : ℝ) + 1 := by positivity
    have hinv : 0 < 1 / ((a (n + 2) : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  · have ha2 : (1 : ℝ) ≤ a (n + 2) := by
      exact_mod_cast hpos (n + 1)
    have hden_pos : 0 < (a (n + 3) : ℝ) + 1 := by positivity
    have hrec_pos : 0 < 1 / ((a (n + 3) : ℝ) + 1) := one_div_pos.mpr hden_pos
    have hden_gt_one :
        (1 : ℝ) < (a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1) := by
      linarith
    have hden_pos' :
        0 < (a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1) := by
      linarith
    have hinv_lt_one :
        1 / ((a (n + 2) : ℝ) + 1 / ((a (n + 3) : ℝ) + 1)) < 1 := by
      exact (div_lt_one hden_pos').mpr hden_gt_one
    linarith

private lemma one_le_continuantDen_of_partials_pos
    {a : ℕ → ℕ} (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    1 ≤ continuantDen a n := by
  have hfib := fib_le_continuantDen_of_partials_pos a hpos n
  have hfibpos : 0 < Nat.fib (n + 1) := by simp
  omega

private lemma commonPrefixMap_den_pos_of_partials
    {a : ℕ → ℕ} (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    0 < x * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) := by
  have hq1 : 1 ≤ continuantDen a n :=
    one_le_continuantDen_of_partials_pos hpos n
  have hqpos : (0 : ℝ) < continuantDen a n := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hq1)
  have hprod : 0 < x * (continuantDen a n : ℝ) := mul_pos hx hqpos
  have hprev : (0 : ℝ) ≤ continuantDenPrev a n := by positivity
  linarith

private lemma commonPrefixMap_continuousOn_of_pos
    {a : ℕ → ℕ} (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ)
    {s : Set ℝ} (hspos : ∀ x : ℝ, x ∈ s → 0 < x) :
    ContinuousOn (fun x : ℝ => commonPrefixMap a n x) s := by
  unfold commonPrefixMap
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x hx
    exact ne_of_gt (commonPrefixMap_den_pos_of_partials hpos n (hspos x hx))

theorem finiteCFExact_shift_prefix
    (a : ℕ → ℕ) (n k : ℕ)
    (hpos : ∀ m : ℕ, 0 < a (m + 1)) :
    finiteCFExact a (n + k + 3) =
      commonPrefixMap a n
        (finiteCFExact (fun i : ℕ => a (n + 1 + i)) (k + 2)) := by
  rw [show n + k + 3 = n + 1 + (k + 2) by omega]
  exact finiteCFExact_shift_prefix_commonPrefixMap a n (k + 2)
    (fun i => by
      have := hpos (n + i)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)

theorem hasContinuedFractionTails_of_positive_convergents_tendsto
    {α : ℝ} {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hlim :
      Tendsto
        (fun n : ℕ =>
          (continuantNum a n : ℝ) / (continuantDen a n : ℝ))
        atTop
        (𝓝 α)) :
    HasContinuedFractionTails α a := by
  intro n
  let L : ℝ :=
    (a (n + 1) : ℝ) + 1 / ((a (n + 2) : ℝ) + 1)
  let U : ℝ :=
    (a (n + 1) : ℝ) +
      1 / ((a (n + 2) : ℝ) +
        1 / ((a (n + 3) : ℝ) + 1))
  let I : Set ℝ := Set.Icc L U
  let Φ : ℝ → ℝ := fun x => commonPrefixMap a n x
  have hstrict :
      (a (n + 1) : ℝ) < L ∧ U < (a (n + 1) : ℝ) + 1 := by
    simpa [L, U] using finite_tail_interval_strict a n hpos
  have hLpos : 0 < L := by
    have ha_nonneg : (0 : ℝ) ≤ a (n + 1) := by positivity
    linarith
  have hIcompact : IsCompact I := by
    simpa [I] using (isCompact_Icc : IsCompact (Set.Icc L U))
  have hΦcont : ContinuousOn Φ I := by
    refine commonPrefixMap_continuousOn_of_pos hpos n ?_
    intro x hx
    have hxL : L ≤ x := by simpa [I] using hx.1
    exact lt_of_lt_of_le hLpos hxL
  have hclosed_image : IsClosed (Φ '' I) :=
    (hIcompact.image_of_continuousOn hΦcont).isClosed
  have hlimFinite : Tendsto (fun m : ℕ => finiteCFExact a m) atTop (𝓝 α) :=
    finiteCFExact_tendsto_of_convergents_tendsto hpos hlim
  have hlim_subseq :
      Tendsto (fun k : ℕ => finiteCFExact a (n + k + 3)) atTop (𝓝 α) := by
    have hmap : Tendsto (fun k : ℕ => n + k + 3) atTop atTop := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (tendsto_add_atTop_nat (n + 3))
    exact hlimFinite.comp hmap
  have hmem_subseq :
      ∀ k : ℕ, finiteCFExact a (n + k + 3) ∈ Φ '' I := by
    intro k
    refine ⟨finiteCFExact (fun i : ℕ => a (n + 1 + i)) (k + 2), ?_, ?_⟩
    · simpa [I, L, U] using finite_tail_two_deep_mem_Icc a n k hpos
    · simpa [Φ] using (finiteCFExact_shift_prefix a n k hpos).symm
  have hα_mem : α ∈ Φ '' I :=
    hclosed_image.mem_of_tendsto hlim_subseq (Eventually.of_forall hmem_subseq)
  rcases hα_mem with ⟨β, hβI, hβeq⟩
  refine ⟨β, ?_, ?_, ?_⟩
  · have hβL : L ≤ β := by simpa [I] using hβI.1
    exact lt_of_lt_of_le hstrict.1 hβL
  · have hβU : β ≤ U := by simpa [I] using hβI.2
    exact lt_of_le_of_lt hβU hstrict.2
  · simpa [Φ, commonPrefixMap] using hβeq.symm

theorem isSimpleCFExpansion_of_pos_convergents_tendsto
    {α : ℝ} {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (hlim :
      Tendsto
        (fun n : ℕ =>
          (continuantNum a n : ℝ) / (continuantDen a n : ℝ))
        atTop
        (𝓝 α)) :
    IsSimpleCFExpansion α a := by
  refine ⟨hpos, hlim, ?_⟩
  exact hasContinuedFractionTails_of_positive_convergents_tendsto hpos hlim

theorem exp_one_isSimpleCFExpansion_eulerCoeff :
    IsSimpleCFExpansion (Real.exp 1) eulerCoeff :=
  isSimpleCFExpansion_of_pos_convergents_tendsto
    eulerCoeff_pos_succ
    eulerCoeff_convergents_tendsto_exp_one

theorem exp_one_hasIrrationalityMeasure_two_of_CF_measure_bridge
    (hbridge :
      ∀ {α : ℝ} {a : ℕ → ℕ} {μ : ℝ},
        IsSimpleCFExpansion α a →
          HasIrrationalityMeasureFromCF a μ →
            HasIrrationalityMeasure α μ) :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  hbridge
    exp_one_isSimpleCFExpansion_eulerCoeff
    exp_one_hasIrrationalityMeasureFromCF_two

theorem exp_one_hasIrrationalityMeasure_two_of_denominatorRatio_bridge
    (hmain :
      ∀ {α : ℝ} {a : ℕ → ℕ},
        IsSimpleCFExpansion α a →
          HasIrrationalityMeasure α (1 + denominatorRatioExponent a))
    (hconvert :
      ∀ {a : ℕ → ℕ},
        (∀ n : ℕ, 0 < a (n + 1)) →
          1 + denominatorRatioExponent a =
            2 + partialQuotientGrowthTau a) :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  exp_one_hasIrrationalityMeasure_two_of_CF_measure_bridge
    (irrationalityMeasure_of_IsSimpleCFExpansion_of_denominatorRatio
      hmain hconvert)

theorem exp_one_hasIrrationalityMeasure_two_of_denominatorRatio_one_bridge
    (hmain :
      ∀ {α : ℝ} {a : ℕ → ℕ},
        IsSimpleCFExpansion α a →
          denominatorRatioExponent a = 1 →
            HasIrrationalityMeasure α 2) :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  hmain
    exp_one_isSimpleCFExpansion_eulerCoeff
    eulerCoeff_denominatorRatioExponent_eq_one

theorem exp_one_hasIrrationalityMeasure_two_of_denominatorRatioExponent :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  exp_one_hasIrrationalityMeasure_two_of_denominatorRatio_one_bridge
    irrationalityMeasure_eq_two_of_denominatorRatioExponent_eq_one

theorem exp_one_hasIrrationalityMeasure_two :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  irrationalityMeasure_eq_two_of_denominatorRatio_tendsto_one
    exp_one_isSimpleCFExpansion_eulerCoeff
    eulerCoeff_denominatorRatio_tendsto_one

end IrrationalityAr
