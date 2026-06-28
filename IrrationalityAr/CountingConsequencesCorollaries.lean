import IrrationalityAr.CountingConsequencesExtensions
import IrrationalityAr.Ramanujan

open Filter
open scoped Topology
open Asymptotics

namespace IrrationalityAr

noncomputable section

/-!
# Corollaries of the counting-consequence layer

This file packages the main counting results into reusable public forms:
logarithmic lower bounds with zero density, eventual pairwise spacing,
ratio-controlled seed subsequences, and the Ramanujan conditional count in
terms of `ACount`.
-/

/-- Public counting package for irrational floor-sum sets: the exact universal
logarithmic lower bound from the seed sequence, together with zero density in
standard little-o notation. -/
theorem ACount_log_lower_and_zeroDensity
    {α : ℝ} (hαirr : IsIrrational α) :
    (∀ N : ℕ, 1 ≤ N →
      Nat.log 3 ((N + 1) / 2) + 1 ≤ ACount α N) ∧
      (fun N : ℕ => (ACount α N : ℝ)) =o[atTop]
        (fun N : ℕ => (N : ℝ)) := by
  refine ⟨
    (fun N hN => one_add_log_three_half_le_ACount (α := α) hαirr hN),
    ?_⟩
  rw [isLittleO_iff]
  intro ε hε
  have h := ACount_eventually_le_mul (α := α) hαirr ε hε
  filter_upwards [h] with N hN
  have hcount_nonneg : 0 ≤ (ACount α N : ℝ) := by positivity
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  rw [Real.norm_of_nonneg hcount_nonneg, Real.norm_of_nonneg hN_nonneg]
  exact hN

/-- A public form of the spacing consequence behind the sublinear counting
theorem: if an unbounded set has nondecreasing consecutive gaps and no infinite
arithmetic progression, then sufficiently far out any two set elements are at
least `M` apart. -/
theorem natSet_eventually_pairwise_spaced_of_gaps_noAP
    {S : Set ℕ}
    (h1 : 1 ∈ S)
    (hunbounded : ∀ B : ℕ, ∃ y : ℕ, y ∈ S ∧ B < y)
    (hgap : SetConsecutiveGapsNondecreasing S)
    (hnoAP : ¬ ContainsInfiniteAP S) :
    ∀ M : ℕ, 0 < M →
      ∃ B : ℕ,
        ∀ x y : ℕ,
          x ∈ S → y ∈ S → B ≤ x → x < y → M ≤ y - x := by
  intro M _hM
  let E := NatSetEnumeration.setEnum S h1 hunbounded
  let G := NatSetEnumeration.setGap S h1 hunbounded
  have hmono : Monotone G := by
    dsimp [G]
    exact NatSetEnumeration.setGap_mono
      (S := S) (h1 := h1) (hunbounded := hunbounded) hgap
  rcases NatSetEnumeration.eventually_gaps_ge_of_noAP
      (S := S) (h1 := h1) (hunbounded := hunbounded)
      hmono hnoAP M with
    ⟨n0, hn0⟩
  refine ⟨E n0, ?_⟩
  intro x y hxS hyS hBx hxy
  have hEpos : 1 ≤ E n0 := by
    dsimp [E]
    have hlin := NatSetEnumeration.setEnum_lower_linear S h1 hunbounded n0
    omega
  have hxpos : 1 ≤ x := hEpos.trans hBx
  rcases NatSetEnumeration.exists_setEnum_eq_of_mem
      (S := S) (h1 := h1) (hunbounded := hunbounded)
      hxpos hxS with
    ⟨i, hi⟩
  have hypos : 1 ≤ y := by omega
  rcases NatSetEnumeration.exists_setEnum_eq_of_mem
      (S := S) (h1 := h1) (hunbounded := hunbounded)
      hypos hyS with
    ⟨j, hj⟩
  have hiE : E i = x := by
    simpa [E] using hi
  have hjE : E j = y := by
    simpa [E] using hj
  have hn0i : n0 ≤ i := by
    by_contra hnot
    have hi_lt : i < n0 := Nat.lt_of_not_ge hnot
    have hltE :
        E i < E n0 := by
      dsimp [E]
      exact (NatSetEnumeration.setEnum_strictMono S h1 hunbounded) hi_lt
    rw [hiE] at hltE
    omega
  have hij : i < j := by
    by_contra hnot
    have hji : j ≤ i := Nat.le_of_not_gt hnot
    have hle :
        E j ≤ E i := by
      dsimp [E]
      exact (NatSetEnumeration.setEnum_strictMono S h1 hunbounded).monotone hji
    rw [hiE, hjE] at hle
    omega
  have hgapM : M ≤ G i := hn0 i hn0i
  have hnext_le_y :
      E (i + 1) ≤ E j := by
    dsimp [E]
    exact (NatSetEnumeration.setEnum_strictMono S h1 hunbounded).monotone
      (Nat.succ_le_of_lt hij)
  have hM_le_next_sub : M ≤ E (i + 1) - E i := by
    simpa [E, G] using hgapM
  have hnext_gap_le_yx : E (i + 1) - E i ≤ y - x := by
    calc
      E (i + 1) - E i ≤ E j - E i :=
        Nat.sub_le_sub_right hnext_le_y (E i)
      _ = y - x := by
        rw [hiE, hjE]
  exact hM_le_next_sub.trans hnext_gap_le_yx

/-- For irrational `α`, sufficiently far out any two elements of `A α` are
arbitrarily far apart. -/
theorem A_eventually_pairwise_spaced_of_irrational
    {α : ℝ} (hαirr : IsIrrational α) :
    ∀ M : ℕ, 0 < M →
      ∃ B : ℕ,
        ∀ x y : ℕ,
          x ∈ A α → y ∈ A α → B ≤ x → x < y → M ≤ y - x := by
  intro M hM
  exact natSet_eventually_pairwise_spaced_of_gaps_noAP
    (S := A α)
    (h1 := one_mem_A (α := α))
    (hunbounded := A_unbounded_of_irrational hαirr)
    (hgap := AGapsNondecreasing_of_irrational hαirr)
    (hnoAP := irrational_no_infiniteAP hαirr)
    M hM

/-- Positive irrational parameters admit a seed sequence in `A α` with
successive shifted values growing by at most a factor of three. -/
theorem exists_A_seed_sequence_ratio_three_of_pos_irrational
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α) :
    ∃ f : ℕ → ℕ,
      f 0 = 1 ∧
      StrictMono f ∧
      (∀ n : ℕ, f n ∈ A α) ∧
      ∀ n : ℕ, f (n + 1) + 1 ≤ 3 * (f n + 1) := by
  rcases exists_simpleCFExpansion_of_irrational hαpos hαirr with ⟨a, hcf⟩
  let hpos : ∀ j : ℕ, 0 < a (j + 1) := hcf.1
  let f : ℕ → ℕ := oddBlockASeq a hpos
  refine ⟨f, oddBlockASeq_zero a hpos, oddBlockASeq_strictMono a hpos, ?_, ?_⟩
  · intro n
    rw [A_eq_oddBlockASet_of_IsSimpleCFExpansion hαpos hαirr hcf]
    exact oddBlockASeq_mem a hpos n
  · intro n
    have hnext :
        (selectedDenominatorSeq a hpos (n + 1) : ℕ) ≤
          3 * (selectedDenominatorSeq a hpos n : ℕ) := by
      simpa [selectedDenominatorSeq] using
        (nextSelectedDenominator_spec a hpos
          (selectedDenominatorSeq a hpos n)).2
    have hsucc_ge := selectedDenominatorSeq_ge_two a hpos (n + 1)
    have hn_ge := selectedDenominatorSeq_ge_two a hpos n
    have hf_succ :
        f (n + 1) + 1 =
          (selectedDenominatorSeq a hpos (n + 1) : ℕ) := by
      dsimp [f, oddBlockASeq]
      omega
    have hf :
        f n + 1 =
          (selectedDenominatorSeq a hpos n : ℕ) := by
      dsimp [f, oddBlockASeq]
      omega
    rw [hf_succ, hf]
    exact hnext

/-- Arbitrary irrational parameters inherit the ratio-three seed sequence after
period/reflection normalization. -/
theorem exists_A_seed_sequence_ratio_three_of_irrational
    {α : ℝ}
    (hαirr : IsIrrational α) :
    ∃ f : ℕ → ℕ,
      f 0 = 1 ∧
      StrictMono f ∧
      (∀ n : ℕ, f n ∈ A α) ∧
      ∀ n : ℕ, f (n + 1) + 1 ≤ 3 * (f n + 1) := by
  rcases exists_normalized_representative α hαirr with
    ⟨α₀, hα₀I, hA, _⟩
  have hα₀pos : 0 < α₀ := lt_of_lt_of_le (by norm_num) hα₀I.1
  have hα₀irr : IsIrrational α₀ :=
    irrational_of_A_eq_irrational hαirr hA
  rcases exists_A_seed_sequence_ratio_three_of_pos_irrational
      hα₀pos hα₀irr with
    ⟨f, hf0, hfmono, hfmem, hfratio⟩
  refine ⟨f, hf0, hfmono, ?_, hfratio⟩
  intro n
  simpa [hA] using hfmem n

/-- The exponential Ramanujan truncation is bounded by the corresponding
`ACount` value. -/
lemma AOneOverPiBelowExp_card_le_ACount_floor_exp
    (Λ : ℝ) (m : ℕ) :
    (AOneOverPiBelowExp Λ m).card ≤
      ACount (1 / Real.pi)
        (Nat.floor (Real.exp (Λ * (m : ℝ)))) := by
  classical
  unfold AOneOverPiBelowExp ACount natSetCount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_filter, Finset.mem_Icc]
  have hxrange := Finset.mem_range.mp hx.1
  have hxA : x ∈ A (1 / Real.pi) := by
    simpa [oneOverPi] using hx.2
  have hxpos : 1 ≤ x := Nat.succ_le_of_lt (mem_A_iff.mp hxA).1
  have hxle : x ≤ Nat.floor (Real.exp (Λ * (m : ℝ))) := by omega
  exact ⟨⟨hxpos, hxle⟩, hxA⟩

/-- Bauer-interface finite-measure Ramanujan production, expressed directly as
a lower bound for `ACount (1 / π)` at exponential checkpoints. -/
theorem exists_eventually_ACount_oneOverPi_floorExp_lower_of_Bauer_finiteMeasure
    (hBauer : BauerRamanujanIdentity)
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤
          (ACount (1 / Real.pi)
            (Nat.floor (Real.exp (Λ * (m : ℝ)))) : ℝ) := by
  rcases exists_eventually_AOneOverPiBelowExp_card_lower_of_Bauer_finiteMeasure
      hBauer hfin with
    ⟨ρ, Λ, hρ, hΛ, hcount⟩
  refine ⟨ρ, Λ, hρ, hΛ, ?_⟩
  filter_upwards [hcount] with m hm
  have hle :
      (AOneOverPiBelowExp Λ m).card ≤
        ACount (1 / Real.pi)
          (Nat.floor (Real.exp (Λ * (m : ℝ)))) :=
    AOneOverPiBelowExp_card_le_ACount_floor_exp Λ m
  have hleR :
      ((AOneOverPiBelowExp Λ m).card : ℝ) ≤
        (ACount (1 / Real.pi)
          (Nat.floor (Real.exp (Λ * (m : ℝ)))) : ℝ) := by
    exact_mod_cast hle
  exact hm.trans hleR

lemma natSetCount_mono {S : Set ℕ} {N M : ℕ} (hNM : N ≤ M) :
    natSetCount S N ≤ natSetCount S M := by
  classical
  unfold natSetCount
  apply Finset.card_mono
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxN, hxS⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hxN).1, le_trans (Finset.mem_Icc.mp hxN).2 hNM⟩, hxS⟩

/-- Finite-measure Ramanujan checkpoint bounds imply a concrete affine-log lower bound
    for `ACount (1 / π)` at all large `N`. -/
theorem eventually_ACount_oneOverPi_affine_lower_of_Bauer_finiteMeasure
    (hBauer : BauerRamanujanIdentity)
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧ 3 * Real.log 2 < Λ ∧
      ∀ᶠ N : ℕ in atTop,
        ρ * (Real.log N / Λ - 1) ≤ (ACount (1 / Real.pi) N : ℝ) := by
  rcases exists_eventually_ACount_oneOverPi_floorExp_lower_of_Bauer_finiteMeasure
      hBauer hfin with
    ⟨ρ, Λ, hρ, hΛ, hprod⟩
  have hΛpos : 0 < Λ := by
    have hlog2pos : 0 < Real.log 2 := by
      have h1 : (1 : ℝ) < 2 := by norm_num
      exact Real.log_pos h1
    have h : 3 * Real.log 2 < Λ := hΛ
    nlinarith [h, hlog2pos]
  rw [Filter.eventually_atTop] at hprod
  rcases hprod with ⟨M0, hM0⟩
  let N0 : ℕ := Nat.floor (Real.exp (Λ * (M0 : ℝ))) + 1
  refine ⟨ρ, Λ, hρ, hΛ, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N0, ?_⟩
  intro N hN
  have hN0_ge_one : 1 ≤ N0 := by
    dsimp [N0]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hN_ge_one : 1 ≤ N := hN0_ge_one.trans hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN_ge_one
  let m : ℕ := Nat.floor (Real.log (N : ℝ) / Λ)
  have hm_ge_M0 : M0 ≤ m := by
    have hExp_lt : Real.exp (Λ * (M0 : ℝ)) < (N : ℝ) := by
      have hlt_floor : Real.exp (Λ * (M0 : ℝ)) < (Nat.floor (Real.exp (Λ * (M0 : ℝ))) + 1) := by
        simpa [Nat.cast_add, Nat.cast_one] using
          (Nat.lt_floor_add_one (Real.exp (Λ * (M0 : ℝ))))
      have hfloor_le : Nat.floor (Real.exp (Λ * (M0 : ℝ))) + 1 ≤ N := by
        simpa [N0] using hN
      exact lt_of_lt_of_le hlt_floor (by exact_mod_cast hfloor_le)
    have hlog_lt : Λ * (M0 : ℝ) < Real.log (N : ℝ) := by
      simpa [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hExp_lt)
    have hM0' : (M0 : ℝ) ≤ Real.log (N : ℝ) / Λ := by
      have hΛ0 : Λ ≠ 0 := ne_of_gt hΛpos
      have hmul : (M0 : ℝ) * Λ ≤ Real.log (N : ℝ) := by
        simpa [mul_comm] using (le_of_lt hlog_lt)
      have htmp' : (M0 : ℝ) * Λ * Λ⁻¹ ≤ (Real.log (N : ℝ)) * Λ⁻¹ := by
        exact mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr (le_of_lt hΛpos))
      simpa [div_eq_mul_inv, hΛ0, mul_assoc, mul_left_comm, mul_comm] using htmp'
    exact Nat.le_floor hM0'
  have hcheckpoint :
      ρ * (m : ℝ) ≤
        (ACount (1 / Real.pi) (Nat.floor (Real.exp (Λ * (m : ℝ))) : ℕ) : ℝ) :=
    hM0 m hm_ge_M0
  have hle_arg : Real.exp (Λ * (m : ℝ)) ≤ (N : ℝ) := by
    have hmul : (m : ℝ) ≤ Real.log (N : ℝ) / Λ := by
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_one
      exact Nat.floor_le (by
        apply div_nonneg
        · exact Real.log_nonneg hN1R
        · exact le_of_lt hΛpos)
    have hmul' : (m : ℝ) * Λ ≤ Real.log (N : ℝ) / Λ * Λ := by
      exact mul_le_mul_of_nonneg_right hmul (le_of_lt hΛpos)
    have hmul'' : (m : ℝ) * Λ ≤ Real.log (N : ℝ) := by
      have hrewrite : Real.log (N : ℝ) / Λ * Λ = Real.log (N : ℝ) := by
        have hΛ0 : Λ ≠ 0 := ne_of_gt hΛpos
        field_simp [hΛ0]
      simpa [hrewrite] using hmul'
    have hExp_le_log : Real.exp (Λ * (m : ℝ)) ≤ Real.exp (Real.log (N : ℝ)) :=
      (Real.exp_le_exp).2 (by simpa [mul_comm] using hmul'')
    simpa [Real.exp_log hNpos] using hExp_le_log
  have hfloor_le : Nat.floor (Real.exp (Λ * (m : ℝ))) ≤ N := by
    have hcast : ((Nat.floor (Real.exp (Λ * (m : ℝ))) : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact (Nat.floor_le (by positivity : (0 : ℝ) ≤ Real.exp (Λ * (m : ℝ)))).trans hle_arg
    exact_mod_cast hcast
  have hMono :
      (ACount (1 / Real.pi) (Nat.floor (Real.exp (Λ * (m : ℝ))) : ℕ) : ℝ) ≤
      (ACount (1 / Real.pi) N : ℝ) := by
    exact_mod_cast (natSetCount_mono (S := A (1 / Real.pi)) hfloor_le)
  have hm_le : Real.log (N : ℝ) / Λ - 1 ≤ m := by
    have hfloor_lt : Real.log (N : ℝ) / Λ < (m : ℝ) + 1 :=
      Nat.lt_floor_add_one (Real.log (N : ℝ) / Λ)
    nlinarith
  have hmulρ : ρ * (Real.log N / Λ - 1) ≤ ρ * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hm_le (le_of_lt hρ)
  exact hmulρ.trans (hcheckpoint.trans hMono)

/-- From finite-measure Ramanujan data, `ACount (1 / π)` is eventually
bounded below by a positive multiple of `log N`. -/
theorem eventually_ACount_oneOverPi_log_lower_of_Bauer_finiteMeasure
    (hBauer : BauerRamanujanIdentity)
    (hfin : HasFiniteIrrationalityMeasure (1 / Real.pi)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ (ACount (1 / Real.pi) N : ℝ) := by
  rcases eventually_ACount_oneOverPi_affine_lower_of_Bauer_finiteMeasure
      hBauer hfin with
    ⟨ρ, Λ, hρ, hΛ, hprod⟩
  have hlog2pos : 0 < Real.log 2 := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos h1
  have hΛpos : 0 < Λ := by
    nlinarith [hΛ, hlog2pos]
  have hΛ0 : Λ ≠ 0 := ne_of_gt hΛpos
  let c : ℝ := ρ / (2 * Λ)
  let N₁ : ℕ := Nat.floor (Real.exp (2 * Λ)) + 1
  have hcpos : 0 < c := by
    dsimp [c]
    have h2Λpos : 0 < 2 * Λ := by nlinarith
    exact div_pos hρ h2Λpos
  rw [Filter.eventually_atTop] at hprod
  rcases hprod with ⟨N₀, hN₀⟩
  refine ⟨c, hcpos, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨Nat.max N₀ N₁, ?_⟩
  intro N hNmax
  have hN₀' : N₀ ≤ N := Nat.le_trans (Nat.le_max_left N₀ N₁) hNmax
  have hN₁' : N₁ ≤ N := Nat.le_trans (Nat.le_max_right N₀ N₁) hNmax
  have hN₁pos : 1 ≤ N₁ := by
    dsimp [N₁]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (hN₁pos.trans hN₁')
  have hExp : Real.exp (2 * Λ) ≤ (N : ℝ) := by
    have hExp_lt : Real.exp (2 * Λ) < (Nat.floor (Real.exp (2 * Λ)) + 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one (Real.exp (2 * Λ)))
    have hfloor_le : (Nat.floor (Real.exp (2 * Λ)) + 1) ≤ N := by
      simpa [N₁] using hN₁'
    have hfloor_cast' : ((Nat.floor (Real.exp (2 * Λ)) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hfloor_le
    have hfloor_cast : ((Nat.floor (Real.exp (2 * Λ)) : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hfloor_cast'
    exact le_of_lt (lt_of_lt_of_le hExp_lt hfloor_cast)
  have hlog₂ : (2 : ℝ) * Λ ≤ Real.log (N : ℝ) := by
    have hlogExp : Real.log (Real.exp (2 * Λ)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (Real.exp_pos _) hExp
    simpa [Real.log_exp] using hlogExp
  have hdiv₂ : (2 : ℝ) ≤ Real.log (N : ℝ) / Λ := by
    have htmp : (2 : ℝ) * Λ * Λ⁻¹ ≤ (Real.log (N : ℝ)) * Λ⁻¹ := by
      exact mul_le_mul_of_nonneg_right hlog₂ (inv_nonneg.mpr (le_of_lt hΛpos))
    simpa [div_eq_mul_inv, hΛ0, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hcheckpoint : ρ * (Real.log (N : ℝ) / Λ - 1) ≤
      (ACount (1 / Real.pi) N : ℝ) :=
    hN₀ N hN₀'
  have hscale : ρ / (2 * Λ) * Real.log (N : ℝ) ≤ ρ * (Real.log (N : ℝ) / Λ - 1) := by
    have htmp : (ρ / (2 * Λ)) * Real.log (N : ℝ) = (ρ / 2) * (Real.log (N : ℝ) / Λ) := by
      field_simp [hΛ0, mul_assoc, mul_left_comm, mul_comm]
    rw [htmp]
    have hscale' : (ρ / 2) * (Real.log (N : ℝ) / Λ) ≤ ρ * (Real.log (N : ℝ) / Λ - 1) := by
      nlinarith [hdiv₂, hρ]
    exact hscale'
  exact hscale.trans hcheckpoint

end

end IrrationalityAr

