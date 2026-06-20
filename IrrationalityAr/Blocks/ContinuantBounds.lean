import IrrationalityAr.Blocks.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

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
