import IrrationalityAr.CanonicalEntropyDissociationCFBridge


import IrrationalityAr.ArithmeticCircleFoundation

/-!
This file records a small “criteria lattice” for eventual-count conditions.

The project already has several concrete families of conditions (Ramanujan bad-
truncation, spike-shadow coverage, etc.).  Rather than mixing all details in one
place, we keep a tiny monotone core here:

1) A notion of eventual upper-density at threshold `δ`.
2) A strict version with a witness `δ < c`.
3) Monotonicity of these predicates under pointwise implication.

This lets us cleanly formalize comparisons like
“criterion A is stronger than criterion B” and “criterion B is weaker but equivalent
on the target threshold”.
-/

open Filter

namespace IrrationalityAr

noncomputable section

/-- Count in the initial segment `{0,1,...,N}`. -/
noncomputable def natInitialSegmentCount (B : ℕ → Prop) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range (N + 1)).filter B).card

/-- `UpperNatDensityAtMost B δ` means the set `B` has asymptotic upper density
at most `δ`. -/
def UpperNatDensityAtMost (B : ℕ → Prop) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop,
      (natInitialSegmentCount B N : ℝ) ≤ (δ + ε) * ((N : ℝ) + 1)

/-- Strict form with an explicit witness `δ < c`. -/
def UpperNatDensityLessThan (B : ℕ → Prop) (c : ℝ) : Prop :=
  ∃ δ : ℝ, 0 ≤ δ ∧ δ < c ∧ UpperNatDensityAtMost B δ

namespace Criteria

/-- A concrete partial order on criteria: pointwise implication. -/
def dominated (B C : ℕ → Prop) : Prop := ∀ n, B n → C n

/-- A criterion `B` is stronger than `C` iff it is pointwise implied by `B`. -/
def stronger (B C : ℕ → Prop) : Prop := dominated C B

/-- Two criteria are equivalent when they imply each other pointwise. -/
def equivalent (B C : ℕ → Prop) : Prop := dominated B C ∧ dominated C B

@[simp] theorem equivalent_iff (B C : ℕ → Prop) :
    equivalent B C ↔ dominated B C ∧ dominated C B := by
  rfl

theorem dominated.refl (B : ℕ → Prop) : dominated B B := by
  intro n hn
  exact hn

theorem dominated.trans {A B C : ℕ → Prop} (hAB : dominated A B)
    (hBC : dominated B C) : dominated A C := by
  intro n hn
  exact hBC n (hAB n hn)

theorem stronger.refl (B : ℕ → Prop) : stronger B B := by
  simpa [Criteria.stronger] using (Criteria.dominated.refl B)

theorem stronger.trans {A B C : ℕ → Prop} (hAB : stronger A B) (hBC : stronger B C) :
    stronger A C := by
  unfold Criteria.stronger at hAB hBC ⊢
  exact dominated.trans hBC hAB

theorem stronger.antisymm {A B : ℕ → Prop} (hAB : stronger A B) (hBA : stronger B A) :
    A = B := by
  funext n
  apply propext
  constructor
  · exact hBA n
  · exact hAB n

theorem equivalent.refl (B : ℕ → Prop) : equivalent B B := by
  unfold Criteria.equivalent
  exact ⟨Criteria.dominated.refl B, Criteria.dominated.refl B⟩

theorem equivalent_of_dominated (hBC : dominated B C) (hCB : dominated C B) :
    equivalent B C := by
  unfold Criteria.equivalent
  exact ⟨hBC, hCB⟩

theorem equivalent_comm {B C : ℕ → Prop} (h : equivalent B C) : equivalent C B := by
  exact h.symm

/-- Upper density is monotone under inclusion: stronger criterion ⇒ weaker criterion. -/
theorem upperDensityAtMost_mono {B C : ℕ → Prop} {δ : ℝ}
    (hBC : dominated B C) (hC : UpperNatDensityAtMost C δ) :
    UpperNatDensityAtMost B δ := by
  classical
  intro ε hε
  have hCε := hC ε hε
  filter_upwards [hCε] with N hN
  have hfilter :
      (Finset.range (N + 1)).filter B ⊆ (Finset.range (N + 1)).filter C := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hBC n hn.2⟩
  have hcast : ((natInitialSegmentCount B N : ℝ) ≤ (natInitialSegmentCount C N : ℝ)) := by
    dsimp [natInitialSegmentCount]
    exact_mod_cast (Finset.card_le_card hfilter)
  exact hcast.trans hN

/-- Strict upper-density deficit is also monotone by inclusion. -/
theorem upperDensityLessThan_mono {B C : ℕ → Prop} {c : ℝ}
    (hBC : dominated B C) (hC : UpperNatDensityLessThan C c) :
    UpperNatDensityLessThan B c := by
  classical
  rcases hC with ⟨δ, hδ0, hδc, hδ⟩
  exact ⟨δ, hδ0, hδc, upperDensityAtMost_mono hBC hδ⟩

/-- Strict form gives non-strict form at the same numeric threshold. -/
theorem upperNatDensityLessThan_to_atMost {B : ℕ → Prop} {c : ℝ}
    (hC : UpperNatDensityLessThan B c) :
    UpperNatDensityAtMost B c := by
  rcases hC with ⟨δ, hδ0, hδc, hδ⟩
  have hgap : 0 < c - δ := by linarith
  intro ε hε
  have hδ' := hδ (ε + (c - δ)) (by linarith)
  filter_upwards [hδ'] with N hN
  nlinarith

theorem upperNatDensityLessThan_iff_of_dominated_iff
    {B C : ℕ → Prop} {c : ℝ}
    (hBC : dominated B C) (hCB : dominated C B) :
    UpperNatDensityLessThan B c ↔ UpperNatDensityLessThan C c := by
  constructor
  · exact Criteria.upperDensityLessThan_mono hCB
  · exact Criteria.upperDensityLessThan_mono hBC

theorem upperNatDensityAtMost_iff_of_dominated_iff
    {B C : ℕ → Prop} {δ : ℝ}
    (hBC : dominated B C) (hCB : dominated C B) :
    UpperNatDensityAtMost B δ ↔ UpperNatDensityAtMost C δ := by
  constructor
  · exact Criteria.upperDensityAtMost_mono hCB
  · exact Criteria.upperDensityAtMost_mono hBC

theorem upperNatDensityLessThan_of_equivalent {B C : ℕ → Prop} {c : ℝ}
    (hBC : Criteria.equivalent B C) :
    UpperNatDensityLessThan B c ↔ UpperNatDensityLessThan C c :=
  Criteria.upperNatDensityLessThan_iff_of_dominated_iff hBC.1 hBC.2

theorem upperNatDensityAtMost_of_equivalent {B C : ℕ → Prop} {δ : ℝ}
    (hBC : Criteria.equivalent B C) :
    UpperNatDensityAtMost B δ ↔ UpperNatDensityAtMost C δ :=
  Criteria.upperNatDensityAtMost_iff_of_dominated_iff hBC.1 hBC.2

end Criteria

/-- Template theorem: if two criteria are pointwise equivalent, then their density
criteria are equivalent too. -/
theorem upperNatDensityEquiv_of_dominated_iff {B C : ℕ → Prop} {δ : ℝ}
    (hBC : Criteria.dominated B C) (hCB : Criteria.dominated C B)
    (hB : UpperNatDensityAtMost B δ) : UpperNatDensityAtMost C δ := by
  exact (Criteria.upperNatDensityAtMost_iff_of_dominated_iff hBC hCB).1 hB

/-- Compatibility alias for the earlier capitalized API name. -/
theorem UpperNatDensityEquiv_of_dominated_iff {B C : ℕ → Prop} {δ : ℝ}
    (hBC : Criteria.dominated B C) (hCB : Criteria.dominated C B)
    (hB : UpperNatDensityAtMost B δ) : UpperNatDensityAtMost C δ :=
  upperNatDensityEquiv_of_dominated_iff hBC hCB hB

end
end IrrationalityAr
