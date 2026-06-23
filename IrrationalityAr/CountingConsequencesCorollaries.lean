import IrrationalityAr.CountingConsequences
import IrrationalityAr.Ramanujan

open Filter
open scoped Topology
open Asymptotics

namespace IrrationalityAr

noncomputable section

/-!
# Corollaries of the counting-consequence layer

This file packages the main counting results into reusable public forms:
divergence, little-o density, eventual pairwise spacing, ratio-controlled seed
subsequences, and the Ramanujan conditional count in terms of `ACount`.
-/

/-- The universal logarithmic lower bound implies that `A α` has counting
function tending to infinity for every irrational `α`. -/
theorem ACount_tendsto_atTop
    {α : ℝ} (hαirr : IsIrrational α) :
    Tendsto (fun N : ℕ => ACount α N) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro (B : ℕ)
  refine ⟨2 * 3 ^ B, ?_⟩
  intro N hN
  have hcap : 2 * 3 ^ B ≤ N + 1 := by omega
  have hcount :
      B + 1 ≤ ACount α N :=
    one_add_le_ACount_of_two_mul_pow_le
      (α := α) hαirr hcap
  omega

/-- The zero-density theorem in standard little-o notation. -/
theorem ACount_isLittleO
    {α : ℝ} (hαirr : IsIrrational α) :
    (fun N : ℕ => (ACount α N : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ)) := by
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

end

end IrrationalityAr
