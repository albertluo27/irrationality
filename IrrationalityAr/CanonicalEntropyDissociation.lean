import IrrationalityAr.ReciprocalBlockDuality


open scoped BigOperators

namespace IrrationalityAr

noncomputable section

/-!
# Canonical entropy and dissociated differences

This module starts the finite additive-combinatorial side of the certified
block entropy argument.  The first layer is independent of continued fractions:
it defines nonnegative difference sets, subset-sum dissociation, dissociated
dimension, and dyadic scale packets.
-/

/-- Nonnegative pairwise differences coming from a finite set of natural
numbers. -/
def nonnegativeDifferenceSet (X : Finset ℕ) : Finset ℕ :=
  (X.product X).image (fun p : ℕ × ℕ => p.1 - p.2)

@[simp] lemma mem_nonnegativeDifferenceSet_iff
    {X : Finset ℕ} {d : ℕ} :
    d ∈ nonnegativeDifferenceSet X ↔
      ∃ x ∈ X, ∃ y ∈ X, d = x - y := by
  classical
  unfold nonnegativeDifferenceSet
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, hpd⟩
    have hp' : p.1 ∈ X ∧ p.2 ∈ X := by
      simpa using hp
    exact ⟨p.1, hp'.1, p.2, hp'.2, hpd.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [Finset.mem_image]
    exact ⟨(x, y), by simpa [Finset.mem_product] using ⟨hx, hy⟩, rfl⟩

lemma nonnegativeDifferenceSet_mono
    {X Y : Finset ℕ}
    (hXY : X ⊆ Y) :
    nonnegativeDifferenceSet X ⊆ nonnegativeDifferenceSet Y := by
  intro d hd
  rw [mem_nonnegativeDifferenceSet_iff] at hd ⊢
  rcases hd with ⟨x, hx, y, hy, hdiff⟩
  exact ⟨x, hXY hx, y, hXY hy, hdiff⟩

/-- A finite set is subset-sum dissociated if subset sums determine the subset. -/
def SubsetSumDissociated (D : Finset ℕ) : Prop :=
  ∀ U V : Finset ℕ,
    U ⊆ D → V ⊆ D →
      U.sum (fun x : ℕ => x) = V.sum (fun x : ℕ => x) →
        U = V

@[simp] lemma subsetSumDissociated_empty :
    SubsetSumDissociated ∅ := by
  intro U V hU hV _hsum
  have hUempty : U = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim ((Finset.notMem_empty x) (hU hx))
    · intro hx
      exact False.elim ((Finset.notMem_empty x) hx)
  have hVempty : V = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim ((Finset.notMem_empty x) (hV hx))
    · intro hx
      exact False.elim ((Finset.notMem_empty x) hx)
  rw [hUempty, hVempty]

lemma SubsetSumDissociated.subset
    {D E : Finset ℕ}
    (hD : SubsetSumDissociated D)
    (hED : E ⊆ D) :
    SubsetSumDissociated E := by
  intro U V hU hV hsum
  exact hD U V (fun x hx => hED (hU hx))
    (fun x hx => hED (hV hx)) hsum

lemma zero_not_mem_of_subsetSumDissociated
    {D : Finset ℕ}
    (hD : SubsetSumDissociated D) :
    0 ∉ D := by
  intro h0
  have hsingleton : ({0} : Finset ℕ) ⊆ D := by
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    simpa [hx0] using h0
  have hEq : (∅ : Finset ℕ) = {0} := by
    exact hD ∅ {0} (by simp) hsingleton (by simp)
  have hcard := congrArg Finset.card hEq
  simp at hcard

lemma sum_le_sum_of_subset_nat
    {U D : Finset ℕ}
    (hUD : U ⊆ D) :
    U.sum (fun x : ℕ => x) ≤ D.sum (fun x : ℕ => x) := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg hUD
    (by intro x _hxD _hxU; exact Nat.zero_le x)

lemma not_mem_of_sum_lt
    {D : Finset ℕ} {x : ℕ}
    (hx : D.sum (fun x : ℕ => x) < x) :
    x ∉ D := by
  intro hxD
  have hsub : ({x} : Finset ℕ) ⊆ D := by
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hxD
  have hle := sum_le_sum_of_subset_nat hsub
  simp at hle
  omega

lemma card_insert_of_sum_lt
    {D : Finset ℕ} {x : ℕ}
    (hx : D.sum (fun x : ℕ => x) < x) :
    (insert x D).card = D.card + 1 := by
  classical
  simp [not_mem_of_sum_lt hx]

lemma sum_insert_of_sum_lt
    {D : Finset ℕ} {x : ℕ}
    (hx : D.sum (fun x : ℕ => x) < x) :
    (insert x D).sum (fun x : ℕ => x) =
      D.sum (fun x : ℕ => x) + x := by
  classical
  rw [Finset.sum_insert (not_mem_of_sum_lt hx)]
  omega

/-- A superincreasing new element can be inserted into a dissociated set. -/
lemma subsetSumDissociated_insert_of_sum_lt
    {D : Finset ℕ} {x : ℕ}
    (hD : SubsetSumDissociated D)
    (hx : D.sum (fun x : ℕ => x) < x) :
    SubsetSumDissociated (insert x D) := by
  classical
  have hxnot : x ∉ D := not_mem_of_sum_lt hx
  intro U V hU hV hsum
  by_cases hxU : x ∈ U
  · by_cases hxV : x ∈ V
    · have hUeraseD : U.erase x ⊆ D := by
        intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyne, hyU⟩
        have hyins := hU hyU
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hyne hyx)
        · exact hyD
      have hVeraseD : V.erase x ⊆ D := by
        intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyne, hyV⟩
        have hyins := hV hyV
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hyne hyx)
        · exact hyD
      have hsumErase :
          (U.erase x).sum (fun x : ℕ => x) =
            (V.erase x).sum (fun x : ℕ => x) := by
        have hsum' := hsum
        rw [← Finset.insert_erase hxU, ← Finset.insert_erase hxV] at hsum'
        simpa [Finset.sum_insert, Finset.notMem_erase, add_left_cancel_iff] using hsum'
      have herase : U.erase x = V.erase x :=
        hD (U.erase x) (V.erase x) hUeraseD hVeraseD hsumErase
      rw [← Finset.insert_erase hxU, ← Finset.insert_erase hxV, herase]
    · have hVD : V ⊆ D := by
        intro y hy
        have hyins := hV hy
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hxV (hyx ▸ hy))
        · exact hyD
      have hVsum_le :
          V.sum (fun x : ℕ => x) ≤ D.sum (fun x : ℕ => x) :=
        sum_le_sum_of_subset_nat hVD
      have hsingleU : ({x} : Finset ℕ) ⊆ U := by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hxU
      have hx_le_U : x ≤ U.sum (fun x : ℕ => x) := by
        have hle := sum_le_sum_of_subset_nat hsingleU
        simpa using hle
      rw [hsum] at hx_le_U
      omega
  · by_cases hxV : x ∈ V
    · have hUD : U ⊆ D := by
        intro y hy
        have hyins := hU hy
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hxU (hyx ▸ hy))
        · exact hyD
      have hUsum_le :
          U.sum (fun x : ℕ => x) ≤ D.sum (fun x : ℕ => x) :=
        sum_le_sum_of_subset_nat hUD
      have hsingleV : ({x} : Finset ℕ) ⊆ V := by
        intro y hy
        have hyx : y = x := by simpa using hy
        simpa [hyx] using hxV
      have hx_le_V : x ≤ V.sum (fun x : ℕ => x) := by
        have hle := sum_le_sum_of_subset_nat hsingleV
        simpa using hle
      rw [← hsum] at hx_le_V
      omega
    · have hUD : U ⊆ D := by
        intro y hy
        have hyins := hU hy
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hxU (hyx ▸ hy))
        · exact hyD
      have hVD : V ⊆ D := by
        intro y hy
        have hyins := hV hy
        rw [Finset.mem_insert] at hyins
        rcases hyins with hyx | hyD
        · exact False.elim (hxV (hyx ▸ hy))
        · exact hyD
      exact hD U V hUD hVD hsum

/-- The largest cardinality of a subset-sum dissociated subset of `Y`. -/
noncomputable def subsetSumDissociatedDimension
    (Y : Finset ℕ) : ℕ := by
  classical
  exact (Y.powerset.filter SubsetSumDissociated).sup Finset.card

lemma card_le_subsetSumDissociatedDimension
    {D Y : Finset ℕ}
    (hDY : D ⊆ Y)
    (hD : SubsetSumDissociated D) :
    D.card ≤ subsetSumDissociatedDimension Y := by
  classical
  unfold subsetSumDissociatedDimension
  refine Finset.le_sup ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hDY, hD⟩

lemma subsetSumDissociatedDimension_mono
    {Y Z : Finset ℕ}
    (hYZ : Y ⊆ Z) :
    subsetSumDissociatedDimension Y ≤
      subsetSumDissociatedDimension Z := by
  classical
  unfold subsetSumDissociatedDimension
  refine Finset.sup_le ?_
  intro D hDmem
  rw [Finset.mem_filter, Finset.mem_powerset] at hDmem
  exact card_le_subsetSumDissociatedDimension
    (hD := hDmem.2) (hDY := hDmem.1.trans hYZ)


/-! ## Ambient bounds for subset-sum dissociated sets -/

lemma two_pow_card_le_sum_add_one_of_subsetSumDissociated
    {D : Finset ℕ}
    (hD : SubsetSumDissociated D) :
    2 ^ D.card ≤ D.sum (fun x : ℕ => x) + 1 := by
  classical
  let f : Finset ℕ → ℕ := fun U => U.sum (fun x : ℕ => x)
  have hinj : Set.InjOn f D.powerset := by
    intro U hU V hV hsum
    have hU' : U ⊆ D := by
      simpa [Finset.mem_powerset] using hU
    have hV' : V ⊆ D := by
      simpa [Finset.mem_powerset] using hV
    exact hD U V hU' hV' hsum
  have hcard_image :
      (D.powerset.image f).card = D.powerset.card :=
    Finset.card_image_of_injOn hinj
  have hsub :
      D.powerset.image f ⊆
        Finset.range (D.sum (fun x : ℕ => x) + 1) := by
    intro s hs
    rw [Finset.mem_image] at hs
    rcases hs with ⟨U, hU, rfl⟩
    rw [Finset.mem_range]
    rw [Finset.mem_powerset] at hU
    exact Nat.lt_succ_of_le (sum_le_sum_of_subset_nat hU)
  have hcard := Finset.card_le_card hsub
  simpa [hcard_image, Finset.card_powerset, f] using hcard

lemma card_le_two_log_add_one_of_subsetSumDissociated_bounded
    {D : Finset ℕ} {N : ℕ}
    (hD : SubsetSumDissociated D)
    (hDN : ∀ x ∈ D, x ≤ N) :
    D.card ≤ 2 * Nat.log 2 (N + 1) + 1 := by
  classical
  let k : ℕ := D.card
  let L : ℕ := Nat.log 2 (N + 1)
  have hsum_le : D.sum (fun x : ℕ => x) ≤ D.card * N := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.sum_le_card_nsmul D (fun x : ℕ => x) N hDN)
  have hpow_le : 2 ^ k ≤ k * N + 1 := by
    dsimp [k]
    exact (two_pow_card_le_sum_add_one_of_subsetSumDissociated hD).trans
      (Nat.succ_le_succ hsum_le)
  by_contra hnot
  have hk_gt : 2 * L + 1 < k := Nat.lt_of_not_ge hnot
  have hk_ge : 2 * L + 2 ≤ k := by omega
  let r : ℕ := k - (2 * L + 2)
  have hk_eq : k = 2 * L + 2 + r := by
    dsimp [r]
    omega
  have hNlog : N + 1 < 2 ^ (L + 1) := by
    dsimp [L]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two (N + 1)
  have hk_le_pow : k ≤ 2 ^ (L + 1 + r) := by
    calc
      k = 2 * (L + 1) + r := by omega
      _ ≤ 2 * (L + 1 + r) := by omega
      _ ≤ 2 ^ (L + 1 + r) :=
          Nat.mul_le_pow (by decide : 2 ≠ 1) (L + 1 + r)
  have hkpos : 0 < k := by omega
  have hlinear_le : k * N + 1 ≤ k * (N + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.succ_le_of_lt hkpos) _
  have hprod_lt : k * (N + 1) < 2 ^ k := by
    calc
      k * (N + 1) ≤ 2 ^ (L + 1 + r) * (N + 1) :=
          Nat.mul_le_mul_right _ hk_le_pow
      _ < 2 ^ (L + 1 + r) * 2 ^ (L + 1) :=
          Nat.mul_lt_mul_of_pos_left hNlog (Nat.two_pow_pos _)
      _ = 2 ^ k := by
          rw [← Nat.pow_add]
          congr 1
          omega
  have hcontr : 2 ^ k < 2 ^ k :=
    hpow_le.trans_lt (hlinear_le.trans_lt hprod_lt)
  exact (lt_irrefl _) hcontr

theorem subsetSumDissociatedDimension_le_two_log
    {Y : Finset ℕ} {N : ℕ}
    (hY : ∀ y ∈ Y, y ≤ N) :
    subsetSumDissociatedDimension Y ≤
      2 * Nat.log 2 (N + 1) + 1 := by
  classical
  unfold subsetSumDissociatedDimension
  refine Finset.sup_le ?_
  intro D hDmem
  rw [Finset.mem_filter, Finset.mem_powerset] at hDmem
  exact card_le_two_log_add_one_of_subsetSumDissociated_bounded
    hDmem.2 (fun x hx => hY x (hDmem.1 hx))


/-- The dyadic packet `d, 2d, ..., 2^(h-1)d`. -/
def dyadicScaleBlock (d h : ℕ) : Finset ℕ :=
  (Finset.range h).image (fun u : ℕ => 2 ^ u * d)

lemma dyadicScaleBlock_card
    {d h : ℕ} (hd : 0 < d) :
    (dyadicScaleBlock d h).card = h := by
  classical
  unfold dyadicScaleBlock
  rw [Finset.card_image_of_injOn]
  · simp
  · intro u _hu v _hv huv
    have hpows : 2 ^ u = 2 ^ v := by
      exact Nat.mul_right_cancel hd huv
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows

lemma sum_range_two_pow (h : ℕ) :
    (Finset.range h).sum (fun u : ℕ => 2 ^ u) = 2 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow : 0 < 2 ^ h := by positivity
      omega

lemma dyadicScaleBlock_sum
    {d h : ℕ} (hd : 0 < d) :
    (dyadicScaleBlock d h).sum (fun x : ℕ => x) =
      (2 ^ h - 1) * d := by
  classical
  unfold dyadicScaleBlock
  rw [Finset.sum_image]
  · rw [← Finset.sum_mul]
    rw [sum_range_two_pow]
  · intro u _hu v _hv huv
    have hpows : 2 ^ u = 2 ^ v := by
      exact Nat.mul_right_cancel hd huv
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows

lemma dyadicScaleBlock_succ
    {d h : ℕ} :
    dyadicScaleBlock d (h + 1) =
      insert (2 ^ h * d) (dyadicScaleBlock d h) := by
  classical
  unfold dyadicScaleBlock
  ext x
  simp [Finset.mem_range]
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases hux : u = h
    · exact Or.inl (by simp [hux])
    · exact Or.inr ⟨u, by omega, rfl⟩
  · intro hx
    rcases hx with hxh | hx
    · refine ⟨h, by omega, ?_⟩
      exact hxh.symm
    · rcases hx with ⟨u, hu, rfl⟩
      exact ⟨u, by omega, rfl⟩

/-- A whole dyadic packet may be appended above a dissociated set whose total
mass is smaller than the packet scale. -/
theorem subsetSumDissociated_union_dyadicScaleBlock
    {D : Finset ℕ} {d h : ℕ}
    (hD : SubsetSumDissociated D)
    (_hd : 0 < d)
    (hsum : D.sum (fun x : ℕ => x) < d) :
    SubsetSumDissociated (D ∪ dyadicScaleBlock d h) ∧
      (D ∪ dyadicScaleBlock d h).card = D.card + h ∧
      (D ∪ dyadicScaleBlock d h).sum (fun x : ℕ => x) =
        D.sum (fun x : ℕ => x) + (2 ^ h - 1) * d := by
  classical
  induction h with
  | zero =>
      simp [dyadicScaleBlock, hD]
  | succ h ih =>
      let E : Finset ℕ := D ∪ dyadicScaleBlock d h
      have hE_diss : SubsetSumDissociated E := by
        dsimp [E]
        exact ih.1
      have hE_card : E.card = D.card + h := by
        dsimp [E]
        exact ih.2.1
      have hE_sum :
          E.sum (fun x : ℕ => x) =
            D.sum (fun x : ℕ => x) + (2 ^ h - 1) * d := by
        dsimp [E]
        exact ih.2.2
      have hE_sum_lt : E.sum (fun x : ℕ => x) < 2 ^ h * d := by
        rw [hE_sum]
        have hcoeff : d + (2 ^ h - 1) * d = 2 ^ h * d := by
          have hpow : 1 ≤ 2 ^ h := by
            exact Nat.succ_le_of_lt (by positivity : 0 < 2 ^ h)
          calc
            d + (2 ^ h - 1) * d =
                ((2 ^ h - 1) + 1) * d := by ring
            _ = 2 ^ h * d := by rw [Nat.sub_add_cancel hpow]
        calc
          D.sum (fun x : ℕ => x) + (2 ^ h - 1) * d
              < d + (2 ^ h - 1) * d := by
                exact Nat.add_lt_add_right hsum _
          _ = 2 ^ h * d := hcoeff
      have hset :
          D ∪ dyadicScaleBlock d (h + 1) =
            insert (2 ^ h * d) E := by
        rw [dyadicScaleBlock_succ]
        ext x
        simp [E, or_left_comm]
      rw [hset]
      constructor
      · exact subsetSumDissociated_insert_of_sum_lt hE_diss hE_sum_lt
      constructor
      · rw [card_insert_of_sum_lt hE_sum_lt, hE_card]
        omega
      · rw [sum_insert_of_sum_lt hE_sum_lt, hE_sum]
        have hcoeff :
            (2 ^ (h + 1) - 1) * d =
              (2 ^ h - 1) * d + 2 ^ h * d := by
          have hpow : 0 < 2 ^ h := by positivity
          have hpow_le : 1 ≤ 2 ^ h := Nat.succ_le_of_lt hpow
          calc
            (2 ^ (h + 1) - 1) * d =
                (2 ^ h * 2 - 1) * d := by rw [pow_succ]
            _ = ((2 ^ h - 1) + 2 ^ h) * d := by
                congr 1
                omega
            _ = (2 ^ h - 1) * d + 2 ^ h * d := by ring
        rw [hcoeff]
        omega

end

end IrrationalityAr
