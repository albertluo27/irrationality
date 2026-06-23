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

/-- Alias matching the mathematical notation for Euler's partial quotients. -/
abbrev eulerPartialQuotients : ℕ → ℕ := eulerCoeff

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

private theorem eulerCoeff_six_mul_add_one (r : ℕ) :
    eulerCoeff (6 * r + 1) = 1 := by
  cases r with
  | zero =>
      norm_num [eulerCoeff]
  | succ r =>
      rw [show 6 * (r + 1) + 1 = 3 * (2 * r + 1) + 4 by ring]
      exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 1)).2.2

private theorem eulerCoeff_six_mul_add_two (r : ℕ) :
    eulerCoeff (6 * r + 2) = 4 * r + 2 := by
  rw [show 6 * r + 2 = 3 * (2 * r) + 2 by ring]
  rw [(eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r)).1]
  ring

private theorem eulerCoeff_six_mul_add_three (r : ℕ) :
    eulerCoeff (6 * r + 3) = 1 := by
  rw [show 6 * r + 3 = 3 * (2 * r) + 3 by ring]
  exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r)).2.1

private theorem eulerCoeff_six_mul_add_four (r : ℕ) :
    eulerCoeff (6 * r + 4) = 1 := by
  rw [show 6 * r + 4 = 3 * (2 * r) + 4 by ring]
  exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r)).2.2

private theorem eulerCoeff_six_mul_add_five (r : ℕ) :
    eulerCoeff (6 * r + 5) = 4 * r + 4 := by
  rw [show 6 * r + 5 = 3 * (2 * r + 1) + 2 by ring]
  rw [(eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 1)).1]
  ring

private theorem eulerCoeff_six_mul_add_six (r : ℕ) :
    eulerCoeff (6 * r + 6) = 1 := by
  rw [show 6 * r + 6 = 3 * (2 * r + 1) + 3 by ring]
  exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 1)).2.1

private theorem eulerCoeff_num_parity_cycle (r : ℕ) :
    Even (continuantNum eulerCoeff (6 * r)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 1)) ∧
    Even (continuantNum eulerCoeff (6 * r + 2)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 3)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 4)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 5)) := by
  induction r with
  | zero =>
      norm_num [continuantNum, eulerCoeff]
  | succ r ih =>
      rcases ih with ⟨hp0, hp1, hp2, hp3, hp4, hp5⟩
      have ha6 : eulerCoeff (6 * r + 6) = 1 := by
        rw [show 6 * r + 6 = 3 * (2 * r + 1) + 3 by ring]
        exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 1)).2.1
      have ha7 : eulerCoeff (6 * r + 7) = 1 := by
        rw [show 6 * r + 7 = 3 * (2 * r + 1) + 4 by ring]
        exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 1)).2.2
      have ha8even : Even (eulerCoeff (6 * r + 8)) := by
        rw [show 6 * r + 8 = 3 * (2 * r + 2) + 2 by ring]
        rw [(eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 2)).1]
        exact ⟨2 * r + 3, by ring⟩
      have ha9 : eulerCoeff (6 * r + 9) = 1 := by
        rw [show 6 * r + 9 = 3 * (2 * r + 2) + 3 by ring]
        exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 2)).2.1
      have ha10 : eulerCoeff (6 * r + 10) = 1 := by
        rw [show 6 * r + 10 = 3 * (2 * r + 2) + 4 by ring]
        exact (eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 2)).2.2
      have ha11even : Even (eulerCoeff (6 * r + 11)) := by
        rw [show 6 * r + 11 = 3 * (2 * r + 3) + 2 by ring]
        rw [(eulerCoeff_hasEulerPartialQuotients.2.2 (2 * r + 3)).1]
        exact ⟨2 * r + 4, by ring⟩
      have hp6 : Even (continuantNum eulerCoeff (6 * r + 6)) := by
        rw [show 6 * r + 6 = (6 * r + 4) + 2 by omega]
        simp [continuantNum, ha6]
        exact hp5.add_odd hp4
      have hp7 : Odd (continuantNum eulerCoeff (6 * r + 7)) := by
        rw [show 6 * r + 7 = (6 * r + 5) + 2 by omega]
        simp [continuantNum, ha7]
        exact hp6.add_odd hp5
      have hp8 : Even (continuantNum eulerCoeff (6 * r + 8)) := by
        rw [show 6 * r + 8 = (6 * r + 6) + 2 by omega]
        simp [continuantNum]
        exact (ha8even.mul_right _).add hp6
      have hp9 : Odd (continuantNum eulerCoeff (6 * r + 9)) := by
        rw [show 6 * r + 9 = (6 * r + 7) + 2 by omega]
        simp [continuantNum, ha9]
        exact hp8.add_odd hp7
      have hp10 : Odd (continuantNum eulerCoeff (6 * r + 10)) := by
        rw [show 6 * r + 10 = (6 * r + 8) + 2 by omega]
        simp [continuantNum, ha10]
        exact hp9.add_even hp8
      have hp11 : Odd (continuantNum eulerCoeff (6 * r + 11)) := by
        rw [show 6 * r + 11 = (6 * r + 9) + 2 by omega]
        simp [continuantNum]
        exact (ha11even.mul_right _).add_odd hp9
      rw [show 6 * (r + 1) = 6 * r + 6 by ring]
      refine ⟨hp6, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using hp7
      · simpa [Nat.add_assoc] using hp8
      · simpa [Nat.add_assoc] using hp9
      · simpa [Nat.add_assoc] using hp10
      · simpa [Nat.add_assoc] using hp11

private theorem eulerCoeff_prev_curr_parity_six_mul (r : ℕ) :
    Odd (continuantNumPrev eulerCoeff (6 * r)) ∧
    Even (continuantNum eulerCoeff (6 * r)) := by
  constructor
  · cases r with
    | zero =>
        norm_num [continuantNumPrev]
    | succ r =>
        rw [show 6 * (r + 1) = 6 * r + 6 by ring]
        change Odd (continuantNum eulerCoeff (6 * r + 5))
        exact (eulerCoeff_num_parity_cycle r).2.2.2.2.2
  · exact (eulerCoeff_num_parity_cycle r).1

private theorem eulerCoeff_prev_curr_parity_six_mul_add_one (r : ℕ) :
    Even (continuantNumPrev eulerCoeff (6 * r + 1)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 1)) := by
  simpa [continuantNumPrev] using
    ⟨(eulerCoeff_num_parity_cycle r).1,
      (eulerCoeff_num_parity_cycle r).2.1⟩

private theorem eulerCoeff_prev_curr_parity_six_mul_add_two (r : ℕ) :
    Odd (continuantNumPrev eulerCoeff (6 * r + 2)) ∧
    Even (continuantNum eulerCoeff (6 * r + 2)) := by
  simpa [continuantNumPrev, Nat.add_assoc] using
    ⟨(eulerCoeff_num_parity_cycle r).2.1,
      (eulerCoeff_num_parity_cycle r).2.2.1⟩

private theorem eulerCoeff_prev_curr_parity_six_mul_add_three (r : ℕ) :
    Even (continuantNumPrev eulerCoeff (6 * r + 3)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 3)) := by
  simpa [continuantNumPrev, Nat.add_assoc] using
    ⟨(eulerCoeff_num_parity_cycle r).2.2.1,
      (eulerCoeff_num_parity_cycle r).2.2.2.1⟩

private theorem eulerCoeff_prev_curr_parity_six_mul_add_four (r : ℕ) :
    Odd (continuantNumPrev eulerCoeff (6 * r + 4)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 4)) := by
  simpa [continuantNumPrev, Nat.add_assoc] using
    ⟨(eulerCoeff_num_parity_cycle r).2.2.2.1,
      (eulerCoeff_num_parity_cycle r).2.2.2.2.1⟩

private theorem eulerCoeff_prev_curr_parity_six_mul_add_five (r : ℕ) :
    Odd (continuantNumPrev eulerCoeff (6 * r + 5)) ∧
    Odd (continuantNum eulerCoeff (6 * r + 5)) := by
  simpa [continuantNumPrev, Nat.add_assoc] using
    ⟨(eulerCoeff_num_parity_cycle r).2.2.2.2.1,
      (eulerCoeff_num_parity_cycle r).2.2.2.2.2⟩

theorem eulerCoeff_odd_CFBlockNumerator_six_mul
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r) t) :=
  odd_CFBlockNumerator_of_prev_odd_curr_even
    (eulerCoeff_prev_curr_parity_six_mul r).1
    (eulerCoeff_prev_curr_parity_six_mul r).2

theorem eulerCoeff_odd_CFBlockNumerator_six_mul_add_one_iff
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r + 1) t) ↔ Odd t :=
  odd_CFBlockNumerator_iff_of_prev_even_curr_odd
    (eulerCoeff_prev_curr_parity_six_mul_add_one r).1
    (eulerCoeff_prev_curr_parity_six_mul_add_one r).2

theorem eulerCoeff_odd_CFBlockNumerator_six_mul_add_two
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r + 2) t) :=
  odd_CFBlockNumerator_of_prev_odd_curr_even
    (eulerCoeff_prev_curr_parity_six_mul_add_two r).1
    (eulerCoeff_prev_curr_parity_six_mul_add_two r).2

theorem eulerCoeff_odd_CFBlockNumerator_six_mul_add_three_iff
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r + 3) t) ↔ Odd t :=
  odd_CFBlockNumerator_iff_of_prev_even_curr_odd
    (eulerCoeff_prev_curr_parity_six_mul_add_three r).1
    (eulerCoeff_prev_curr_parity_six_mul_add_three r).2

theorem eulerCoeff_odd_CFBlockNumerator_six_mul_add_four_iff
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r + 4) t) ↔ Even t :=
  odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
    (eulerCoeff_prev_curr_parity_six_mul_add_four r).1
    (eulerCoeff_prev_curr_parity_six_mul_add_four r).2

theorem eulerCoeff_odd_CFBlockNumerator_six_mul_add_five_iff
    (r t : ℕ) :
    Odd (CFBlockNumerator eulerCoeff (6 * r + 5) t) ↔ Even t :=
  odd_CFBlockNumerator_iff_of_prev_odd_curr_odd
    (eulerCoeff_prev_curr_parity_six_mul_add_five r).1
    (eulerCoeff_prev_curr_parity_six_mul_add_five r).2

/-- The five-family explicit classification set from the Euler parity table.

This is the right-hand side of the pasted classification theorem. The remaining
bridge is to identify this set with the literal floor-sum set
`A (Real.exp 1)`. -/
def eulerExplicitASet : Set ℕ :=
  {n : ℕ |
    (∃ r : ℕ,
      1 ≤ r ∧
        n = continuantDen eulerCoeff (6 * r + 1) - 1) ∨
    (∃ r s : ℕ,
      s ≤ 2 * r ∧
        n = continuantDen eulerCoeff (6 * r) +
          (2 * s + 1) * continuantDen eulerCoeff (6 * r + 1) - 1) ∨
    (∃ r : ℕ,
      n = continuantDen eulerCoeff (6 * r + 3) - 1) ∨
    (∃ r : ℕ,
      n = continuantDen eulerCoeff (6 * r + 4) - 1) ∨
    (∃ r s : ℕ,
      1 ≤ s ∧ s ≤ 2 * r + 2 ∧
        n = continuantDen eulerCoeff (6 * r + 3) +
          2 * s * continuantDen eulerCoeff (6 * r + 4) - 1)}

private theorem exists_eq_six_mul_add_lt (j : ℕ) :
    ∃ r k : ℕ, k < 6 ∧ j = 6 * r + k := by
  refine ⟨j / 6, j % 6, Nat.mod_lt j (by norm_num), ?_⟩
  have h := Nat.div_add_mod j 6
  have h' : 6 * (j / 6) + j % 6 = j := by
    simpa [Nat.mul_comm] using h
  exact h'.symm

/-- Euler's parity table gives the explicit five-family classification of the
odd-numerator continued-fraction block denominator set. -/
theorem oddBlockASet_eulerCoeff_eq_eulerExplicitASet :
    oddBlockASet eulerCoeff = eulerExplicitASet := by
  ext n
  constructor
  · rintro ⟨j, t, ht1, htle, hodd, hQ2, hnQ⟩
    rcases exists_eq_six_mul_add_lt j with ⟨r, k, hk, rfl⟩
    interval_cases k
    · have hcoeff : eulerCoeff (6 * r + 1) = 1 :=
        eulerCoeff_six_mul_add_one r
      have ht : t = 1 := by
        rw [hcoeff] at htle
        omega
      subst t
      have hrpos : 1 ≤ r := by
        by_contra hr
        have hr0 : r = 0 := by omega
        subst r
        norm_num [CFBlockDenominator, continuantDenPrev, continuantDen] at hQ2
      left
      refine ⟨r, hrpos, ?_⟩
      have hden :
          CFBlockDenominator eulerCoeff (6 * r) 1 =
            continuantDen eulerCoeff (6 * r + 1) := by
        simpa [hcoeff] using
          CFBlockDenominator_endpoint eulerCoeff (6 * r)
      simpa [hden] using hnQ
    · have hcoeff : eulerCoeff (6 * r + 2) = 4 * r + 2 :=
        eulerCoeff_six_mul_add_two r
      have htodd : Odd t :=
        (eulerCoeff_odd_CFBlockNumerator_six_mul_add_one_iff r t).1 hodd
      rcases htodd with ⟨s, rfl⟩
      have hsle : s ≤ 2 * r := by
        rw [hcoeff] at htle
        omega
      right
      left
      refine ⟨r, s, hsle, ?_⟩
      simpa [CFBlockDenominator, continuantDenPrev, Nat.add_assoc,
        mul_assoc] using hnQ
    · have hcoeff : eulerCoeff (6 * r + 3) = 1 :=
        eulerCoeff_six_mul_add_three r
      have ht : t = 1 := by
        rw [hcoeff] at htle
        omega
      subst t
      right
      right
      left
      refine ⟨r, ?_⟩
      have hden :
          CFBlockDenominator eulerCoeff (6 * r + 2) 1 =
            continuantDen eulerCoeff (6 * r + 3) := by
        simpa [hcoeff, Nat.add_assoc] using
          CFBlockDenominator_endpoint eulerCoeff (6 * r + 2)
      simpa [hden] using hnQ
    · have hcoeff : eulerCoeff (6 * r + 4) = 1 :=
        eulerCoeff_six_mul_add_four r
      have ht : t = 1 := by
        rw [hcoeff] at htle
        omega
      subst t
      right
      right
      right
      left
      refine ⟨r, ?_⟩
      have hden :
          CFBlockDenominator eulerCoeff (6 * r + 3) 1 =
            continuantDen eulerCoeff (6 * r + 4) := by
        simpa [hcoeff, Nat.add_assoc] using
          CFBlockDenominator_endpoint eulerCoeff (6 * r + 3)
      simpa [hden] using hnQ
    · have hcoeff : eulerCoeff (6 * r + 5) = 4 * r + 4 :=
        eulerCoeff_six_mul_add_five r
      have hteven : Even t :=
        (eulerCoeff_odd_CFBlockNumerator_six_mul_add_four_iff r t).1 hodd
      rcases hteven with ⟨s, rfl⟩
      have hspos : 1 ≤ s := by omega
      have hsle : s ≤ 2 * r + 2 := by
        rw [hcoeff] at htle
        omega
      right
      right
      right
      right
      refine ⟨r, s, hspos, hsle, ?_⟩
      have hden :
          CFBlockDenominator eulerCoeff (6 * r + 4) (s + s) =
            continuantDen eulerCoeff (6 * r + 3) +
              2 * s * continuantDen eulerCoeff (6 * r + 4) := by
        simp [CFBlockDenominator, continuantDenPrev]
        rw [show s + s = 2 * s by omega]
        left
        rfl
      simpa [hden] using hnQ
    · have hcoeff : eulerCoeff (6 * r + 6) = 1 :=
        eulerCoeff_six_mul_add_six r
      have ht : t = 1 := by
        rw [hcoeff] at htle
        omega
      have hteven : Even t :=
        (eulerCoeff_odd_CFBlockNumerator_six_mul_add_five_iff r t).1 hodd
      subst t
      norm_num at hteven
  · intro hn
    rcases hn with h₁ | h₂ | h₃ | h₄ | h₅
    · rcases h₁ with ⟨r, hrpos, hn⟩
      refine ⟨6 * r, 1, by norm_num, ?_, ?_, ?_, ?_⟩
      · simp [eulerCoeff_six_mul_add_one r]
      · exact eulerCoeff_odd_CFBlockNumerator_six_mul r 1
      · exact two_le_CFBlockDenominator_of_one_le_index
          eulerCoeff_pos_succ (by omega) (by norm_num)
      · have hden :
            CFBlockDenominator eulerCoeff (6 * r) 1 =
              continuantDen eulerCoeff (6 * r + 1) := by
          simpa [eulerCoeff_six_mul_add_one r] using
            CFBlockDenominator_endpoint eulerCoeff (6 * r)
        simpa [hden] using hn
    · rcases h₂ with ⟨r, s, hsle, hn⟩
      refine ⟨6 * r + 1, 2 * s + 1, by omega, ?_, ?_, ?_, ?_⟩
      · rw [eulerCoeff_six_mul_add_two r]
        omega
      · exact
          (eulerCoeff_odd_CFBlockNumerator_six_mul_add_one_iff
            r (2 * s + 1)).2 ⟨s, by ring⟩
      · exact two_le_CFBlockDenominator_of_one_le_index
          eulerCoeff_pos_succ (by omega) (by omega)
      · simpa [CFBlockDenominator, continuantDenPrev, Nat.add_assoc,
          mul_assoc] using hn
    · rcases h₃ with ⟨r, hn⟩
      refine ⟨6 * r + 2, 1, by norm_num, ?_, ?_, ?_, ?_⟩
      · simp [eulerCoeff_six_mul_add_three r]
      · exact eulerCoeff_odd_CFBlockNumerator_six_mul_add_two r 1
      · exact two_le_CFBlockDenominator_of_one_le_index
          eulerCoeff_pos_succ (by omega) (by norm_num)
      · have hden :
            CFBlockDenominator eulerCoeff (6 * r + 2) 1 =
              continuantDen eulerCoeff (6 * r + 3) := by
          simpa [eulerCoeff_six_mul_add_three r, Nat.add_assoc] using
            CFBlockDenominator_endpoint eulerCoeff (6 * r + 2)
        simpa [hden] using hn
    · rcases h₄ with ⟨r, hn⟩
      refine ⟨6 * r + 3, 1, by norm_num, ?_, ?_, ?_, ?_⟩
      · simp [eulerCoeff_six_mul_add_four r]
      · exact
          (eulerCoeff_odd_CFBlockNumerator_six_mul_add_three_iff r 1).2
            ⟨0, by norm_num⟩
      · exact two_le_CFBlockDenominator_of_one_le_index
          eulerCoeff_pos_succ (by omega) (by norm_num)
      · have hden :
            CFBlockDenominator eulerCoeff (6 * r + 3) 1 =
              continuantDen eulerCoeff (6 * r + 4) := by
          simpa [eulerCoeff_six_mul_add_four r, Nat.add_assoc] using
            CFBlockDenominator_endpoint eulerCoeff (6 * r + 3)
        simpa [hden] using hn
    · rcases h₅ with ⟨r, s, hspos, hsle, hn⟩
      refine ⟨6 * r + 4, 2 * s, by omega, ?_, ?_, ?_, ?_⟩
      · rw [eulerCoeff_six_mul_add_five r]
        omega
      · exact
          (eulerCoeff_odd_CFBlockNumerator_six_mul_add_four_iff
            r (2 * s)).2 ⟨s, by ring⟩
      · exact two_le_CFBlockDenominator_of_one_le_index
          eulerCoeff_pos_succ (by omega) (by omega)
      · simpa [CFBlockDenominator, continuantDenPrev, Nat.add_assoc,
          mul_assoc] using hn

theorem eulerCoeff_canonicalBlockExponent_eq_zero :
    canonicalBlockExponent eulerCoeff = 0 :=
  canonicalBlockExponent_eq_zero_of_eulerPartialQuotients
    eulerCoeff_hasEulerPartialQuotients

theorem euler_visiblePopularDifferenceExponent_eq_zero :
    visiblePopularDifferenceExponent eulerPartialQuotients = 0 := by
  rw [visiblePopularDifferenceExponent_eq_canonicalBlockExponent
    eulerCoeff_pos_succ]
  exact eulerCoeff_canonicalBlockExponent_eq_zero

theorem euler_visibleAdditiveEnergyExponent_eq_zero :
    visibleAdditiveEnergyExponent eulerPartialQuotients = 0 := by
  rw [visibleAdditiveEnergyExponent_eq_three_mul_canonicalBlockExponent
    eulerCoeff_pos_succ]
  simp [eulerCoeff_canonicalBlockExponent_eq_zero]

theorem euler_visibleHilbertCubeExponent_eq_zero :
    visibleHilbertCubeExponent eulerPartialQuotients = 0 := by
  rw [visibleHilbertCubeExponent_eq_canonicalBlockExponent_div_log_two
    eulerCoeff_pos_succ]
  simp [eulerCoeff_canonicalBlockExponent_eq_zero]

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

/-- The floor-sum set for `e` is the odd-numerator
principal/intermediate block-denominator set attached to Euler's continued
fraction coefficients. -/
theorem A_exp_one_eq_oddBlockASet_eulerCoeff
    (hexpirr : IsIrrational (Real.exp 1)) :
    A (Real.exp 1) = oddBlockASet eulerCoeff :=
  A_eq_oddBlockASet_of_IsSimpleCFExpansion
    (Real.exp_pos 1)
    hexpirr
    exp_one_isSimpleCFExpansion_eulerCoeff

/-- Complete explicit classification of the floor-sum set `A_e`, conditional
only on irrationality of `e`. -/
theorem A_exp_one_eq_eulerExplicitASet
    (hexpirr : IsIrrational (Real.exp 1)) :
    A (Real.exp 1) = eulerExplicitASet := by
  rw [A_exp_one_eq_oddBlockASet_eulerCoeff hexpirr]
  exact oddBlockASet_eulerCoeff_eq_eulerExplicitASet

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

theorem exp_one_hasIrrationalityMeasure_two :
    HasIrrationalityMeasure (Real.exp 1) 2 :=
  irrationalityMeasure_eq_two_of_denominatorRatio_tendsto_one
    exp_one_isSimpleCFExpansion_eulerCoeff
    eulerCoeff_denominatorRatio_tendsto_one

/-- A real number with project-level irrationality measure `2` is irrational.

If `α = p / q` were rational, then every large multiple of `q` would give an
exact rational approximation with error `0`, contradicting the upper-failure
clause in `HasIrrationalityMeasure α 2` at exponent `3`. -/
theorem isIrrational_of_hasIrrationalityMeasure_two
    {α : ℝ}
    (hμ : HasIrrationalityMeasure α 2) :
    IsIrrational α := by
  intro hrat
  rcases hrat with ⟨r, hr⟩
  rcases hμ with ⟨_, hupper⟩
  have hbadEventually :
      ∀ᶠ q : ℕ in atTop,
        ∀ p : ℤ,
          0 < q →
            ¬ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-(3 : ℝ)) :=
    hupper 3 (by norm_num)
  rcases eventually_atTop.1 hbadEventually with ⟨N, hN⟩

  let k : ℕ := N + 1
  let Q : ℕ := r.den * k
  let P : ℤ := r.num * (k : ℤ)

  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hdenpos : 0 < r.den := r.den_pos
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Nat.mul_pos hdenpos hkpos
  have hQge : N ≤ Q := by
    have hden_ge_one : 1 ≤ r.den := Nat.succ_le_of_lt hdenpos
    have hkge : N + 1 ≤ Q := by
      dsimp [Q, k]
      simpa [one_mul] using
        (Nat.mul_le_mul_right (N + 1) hden_ge_one)
    exact (Nat.le_succ N).trans hkge

  have hbad := hN Q hQge P hQpos

  have hrat_eq :
      α = (P : ℝ) / (Q : ℝ) := by
    rw [← hr]
    have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hkpos
    have hdenR : (r.den : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hdenpos
    calc
      (r : ℝ)
          = (r.num : ℝ) / (r.den : ℝ) := by
              rw [Rat.cast_def]
      _ = ((r.num : ℝ) * (k : ℝ)) /
            ((r.den : ℝ) * (k : ℝ)) := by
              field_simp [hkR, hdenR]
      _ = (P : ℝ) / (Q : ℝ) := by
              simp [P, Q, Int.cast_mul, Nat.cast_mul]

  have hpowpos : 0 < (Q : ℝ) ^ (-(3 : ℝ)) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hQpos) _
  apply hbad
  rw [hrat_eq, sub_self, abs_zero]
  exact hpowpos

theorem exp_one_irrational : IsIrrational (Real.exp 1) :=
  isIrrational_of_hasIrrationalityMeasure_two
    exp_one_hasIrrationalityMeasure_two

theorem A_exp_one_eq_eulerExplicitASet_unconditional :
    A (Real.exp 1) = eulerExplicitASet :=
  A_exp_one_eq_eulerExplicitASet exp_one_irrational

/-- The coefficient-side visible canonical truncation for Euler's continued
fraction agrees with the true floor-sum truncation of `A_e`, up to erasing the
possible initial shifted denominator `0`. -/
theorem visibleCanonicalDenominatorSet_eulerCoeff_erase_zero_eq_A_exp_one_trunc
    (N : ℕ) :
    (visibleCanonicalDenominatorSet eulerCoeff N).erase 0 =
      visibleFloorSumASet (Real.exp 1) N :=
  visibleCanonicalDenominatorSet_erase_zero_eq_visibleFloorSumASet
    (Real.exp_pos 1)
    exp_one_irrational
    exp_one_isSimpleCFExpansion_eulerCoeff
    N

theorem positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc
    (N : ℕ) :
    positiveVisibleCanonicalDenominatorSet eulerCoeff N =
      visibleFloorSumASet (Real.exp 1) N := by
  simpa [positiveVisibleCanonicalDenominatorSet] using
    visibleCanonicalDenominatorSet_eulerCoeff_erase_zero_eq_A_exp_one_trunc N

theorem positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc_filter
    (N : ℕ) :
    positiveVisibleCanonicalDenominatorSet eulerCoeff N =
      (by
        classical
        exact (Finset.range N).filter (fun n => n ∈ A (Real.exp 1))) := by
  classical
  rw [positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc]
  rfl

theorem positiveVisiblePopularDifferenceExponent_eulerCoeff_eq_zero :
    positiveVisiblePopularDifferenceExponent eulerCoeff = 0 := by
  rw [positiveVisiblePopularDifferenceExponent_eq_canonicalBlockExponent
    eulerCoeff_pos_succ]
  exact eulerCoeff_canonicalBlockExponent_eq_zero

theorem positiveVisibleAdditiveEnergyExponent_eulerCoeff_eq_zero :
    positiveVisibleAdditiveEnergyExponent eulerCoeff = 0 := by
  rw [positiveVisibleAdditiveEnergyExponent_eq_three_mul_canonicalBlockExponent
    eulerCoeff_pos_succ]
  rw [eulerCoeff_canonicalBlockExponent_eq_zero]
  norm_num

theorem positiveVisibleHilbertCubeExponent_eulerCoeff_eq_zero :
    positiveVisibleHilbertCubeExponent eulerCoeff = 0 := by
  rw [positiveVisibleHilbertCubeExponent_eq_canonicalBlockExponent_div_log_two
    eulerCoeff_pos_succ]
  rw [eulerCoeff_canonicalBlockExponent_eq_zero]
  norm_num

theorem positiveVisiblePopularDifferenceExponent_eulerCoeff_eq_floorSumA_exp_one :
    positiveVisiblePopularDifferenceExponent eulerCoeff =
      floorSumAPopularDifferenceExponent (Real.exp 1) := by
  simpa [positiveVisiblePopularDifferenceExponent,
    floorSumAPopularDifferenceExponent, popularDifferenceExponentOf] using
    (popularDifferenceExponent_congr
      (S := positiveVisibleCanonicalDenominatorSet eulerCoeff)
      (T := visibleFloorSumASet (Real.exp 1))
      positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc)

theorem positiveVisibleAdditiveEnergyExponent_eulerCoeff_eq_floorSumA_exp_one :
    positiveVisibleAdditiveEnergyExponent eulerCoeff =
      floorSumAAdditiveEnergyExponent (Real.exp 1) := by
  simpa [positiveVisibleAdditiveEnergyExponent,
    floorSumAAdditiveEnergyExponent, additiveEnergyExponentOf] using
    (additiveEnergyExponent_congr
      (S := positiveVisibleCanonicalDenominatorSet eulerCoeff)
      (T := visibleFloorSumASet (Real.exp 1))
      positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc)

theorem positiveVisibleHilbertCubeExponent_eulerCoeff_eq_floorSumA_exp_one :
    positiveVisibleHilbertCubeExponent eulerCoeff =
      floorSumAHilbertCubeExponent (Real.exp 1) := by
  simpa [positiveVisibleHilbertCubeExponent,
    floorSumAHilbertCubeExponent, hilbertCubeExponentOf] using
    (hilbertCubeExponent_congr
      (S := positiveVisibleCanonicalDenominatorSet eulerCoeff)
      (T := visibleFloorSumASet (Real.exp 1))
      positiveVisibleCanonicalDenominatorSet_eulerCoeff_eq_A_exp_one_trunc)

theorem floorSumAPopularDifferenceExponent_exp_one_eq_zero :
    floorSumAPopularDifferenceExponent (Real.exp 1) = 0 := by
  rw [← positiveVisiblePopularDifferenceExponent_eulerCoeff_eq_floorSumA_exp_one]
  exact positiveVisiblePopularDifferenceExponent_eulerCoeff_eq_zero

theorem floorSumAAdditiveEnergyExponent_exp_one_eq_zero :
    floorSumAAdditiveEnergyExponent (Real.exp 1) = 0 := by
  rw [← positiveVisibleAdditiveEnergyExponent_eulerCoeff_eq_floorSumA_exp_one]
  exact positiveVisibleAdditiveEnergyExponent_eulerCoeff_eq_zero

theorem floorSumAHilbertCubeExponent_exp_one_eq_zero :
    floorSumAHilbertCubeExponent (Real.exp 1) = 0 := by
  rw [← positiveVisibleHilbertCubeExponent_eulerCoeff_eq_floorSumA_exp_one]
  exact positiveVisibleHilbertCubeExponent_eulerCoeff_eq_zero

lemma visibleFloorSumASet_exp_one_subset_visibleCanonicalDenominatorSet
    (N : ℕ) :
    visibleFloorSumASet (Real.exp 1) N ⊆
      visibleCanonicalDenominatorSet eulerCoeff N := by
  rw [← visibleCanonicalDenominatorSet_eulerCoeff_erase_zero_eq_A_exp_one_trunc N]
  exact Finset.erase_subset _ _

theorem A_exp_one_popularDifferenceExponent_eq_canonicalBlockExponent :
    floorSumAPopularDifferenceExponent (Real.exp 1) =
      canonicalBlockExponent eulerCoeff := by
  apply le_antisymm
  · exact
      (floorSumAPopularDifferenceExponent_le_visiblePopularDifferenceExponent
        visibleFloorSumASet_exp_one_subset_visibleCanonicalDenominatorSet).trans_eq
          (visiblePopularDifferenceExponent_eq_canonicalBlockExponent
            eulerCoeff_pos_succ)
  · rw [eulerCoeff_canonicalBlockExponent_eq_zero]
    exact floorSumAPopularDifferenceExponent_nonneg (Real.exp 1)

theorem A_exp_one_additiveEnergyExponent_eq_three_mul_canonicalBlockExponent :
    floorSumAAdditiveEnergyExponent (Real.exp 1) =
      3 * canonicalBlockExponent eulerCoeff := by
  apply le_antisymm
  · exact
      (floorSumAAdditiveEnergyExponent_le_visibleAdditiveEnergyExponent
        visibleFloorSumASet_exp_one_subset_visibleCanonicalDenominatorSet).trans_eq
          (visibleAdditiveEnergyExponent_eq_three_mul_canonicalBlockExponent
            eulerCoeff_pos_succ)
  · rw [eulerCoeff_canonicalBlockExponent_eq_zero]
    simpa using floorSumAAdditiveEnergyExponent_nonneg (Real.exp 1)

theorem A_exp_one_hilbertCubeExponent_eq_canonicalBlockExponent_div_log_two :
    floorSumAHilbertCubeExponent (Real.exp 1) =
      canonicalBlockExponent eulerCoeff / Real.log 2 := by
  apply le_antisymm
  · exact
      (floorSumAHilbertCubeExponent_le_visibleHilbertCubeExponent
        eulerCoeff_pos_succ
        visibleFloorSumASet_exp_one_subset_visibleCanonicalDenominatorSet).trans_eq
          (visibleHilbertCubeExponent_eq_canonicalBlockExponent_div_log_two
            eulerCoeff_pos_succ)
  · rw [eulerCoeff_canonicalBlockExponent_eq_zero]
    simpa using
      floorSumAHilbertCubeExponent_nonneg_of_subset
        eulerCoeff_pos_succ
        visibleFloorSumASet_exp_one_subset_visibleCanonicalDenominatorSet

end IrrationalityAr
