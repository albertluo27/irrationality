import Mathlib
import IrrationalityAr.ArithmeticCircleFoundation


namespace IrrationalityAr

open scoped BigOperators
open scoped Combinatorics.Additive
open scoped Pointwise

/-!
# Finite additive-combinatorial block bridge

This file contains the finite, continued-fraction-free part of the additive
bridge.  The definitions are deliberately phrased for `Finset ℕ`; later files
can instantiate them with canonical continued-fraction blocks.
-/

/-- Number of elements `x ∈ S` whose translate `x + d` also lies in `S`. -/
def popularDifferenceCount (S : Finset ℕ) (d : ℕ) : ℕ :=
  (S.filter fun x : ℕ => x + d ∈ S).card

/-- Bounded popular-difference statistic.

If `S ⊆ [0,N]`, every nonzero difference appearing inside `S` is at most `N`,
so this is the finite version of `1 + max_{d ≥ 1} r_S(d)`. -/
def popularDifferenceUpTo (S : Finset ℕ) (N : ℕ) : ℕ :=
  1 + (Finset.Icc 1 N).sup (popularDifferenceCount S)

/-- Additive energy of a finite set of natural numbers. -/
def additiveEnergy (S : Finset ℕ) : ℕ :=
  Finset.addEnergy S S

/-- The value of a Hilbert-cube vertex indexed by Boolean choices. -/
def hilbertCubeVertex {h : ℕ} (x₀ : ℕ) (steps : Fin h → ℕ)
    (ε : Fin h → Bool) : ℕ :=
  x₀ + ∑ i : Fin h, if ε i then steps i else 0

/-- `S` contains a proper Hilbert cube of dimension `h`. -/
def HasProperHilbertCube (S : Finset ℕ) (h : ℕ) : Prop :=
  ∃ x₀ : ℕ, ∃ steps : Fin h → ℕ,
    Function.Injective (hilbertCubeVertex x₀ steps) ∧
      ∀ ε : Fin h → Bool, hilbertCubeVertex x₀ steps ε ∈ S

/-- The finite arithmetic block `{s + r d : 0 ≤ r < m}`. -/
def finiteArithmeticBlock (s d m : ℕ) : Finset ℕ :=
  (Finset.range m).image fun r : ℕ => s + r * d

lemma mem_finiteArithmeticBlock_iff {s d m x : ℕ} :
    x ∈ finiteArithmeticBlock s d m ↔
      ∃ r : ℕ, r < m ∧ x = s + r * d := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, hxr⟩
    exact ⟨r, Finset.mem_range.mp hr, hxr.symm⟩
  · intro hx
    rcases hx with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩

/-- The binary value attached to a Boolean vector of length `h`. -/
def binaryValue (h : ℕ) (eps : Fin h → Bool) : ℕ :=
  ∑ i : Fin h, if eps i then 2 ^ (i : ℕ) else 0

/-- The same binary value, bundled as an element of `Fin (2 ^ h)`. -/
private def binaryFin (h : ℕ) (eps : Fin h → Bool) : Fin (2 ^ h) :=
  finFunctionFinEquiv
    (fun i : Fin h => if eps i then (1 : Fin 2) else (0 : Fin 2))

private lemma binaryFin_val (h : ℕ) (eps : Fin h → Bool) :
    (binaryFin h eps : ℕ) = binaryValue h eps := by
  unfold binaryFin binaryValue
  rw [finFunctionFinEquiv_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    by_cases hi : eps i <;> simp [hi])

lemma binaryValue_lt_two_pow
    {h : ℕ} (eps : Fin h → Bool) :
    binaryValue h eps < 2 ^ h := by
  rw [← binaryFin_val h eps]
  exact (binaryFin h eps).isLt

private lemma bool_to_fin_two_injective :
    Function.Injective
      (fun b : Bool => if b then (1 : Fin 2) else (0 : Fin 2)) := by
  intro b c hbc
  cases b <;> cases c <;> simp at hbc ⊢

lemma binaryValue_injective {h : ℕ} :
    Function.Injective (binaryValue h) := by
  intro eps eta hval
  have hfin : binaryFin h eps = binaryFin h eta := by
    apply Fin.ext
    rw [binaryFin_val h eps, binaryFin_val h eta]
    exact hval
  have hfun :
      (fun i : Fin h => if eps i then (1 : Fin 2) else (0 : Fin 2)) =
        (fun i : Fin h => if eta i then (1 : Fin 2) else (0 : Fin 2)) := by
    exact (Equiv.injective finFunctionFinEquiv) hfin
  ext i
  exact bool_to_fin_two_injective (congrFun hfun i)

lemma cubePoint_binaryValue
    {s d h : ℕ} (eps : Fin h → Bool) :
    hilbertCubeVertex s (fun i : Fin h => 2 ^ (i : ℕ) * d) eps =
      s + binaryValue h eps * d := by
  unfold hilbertCubeVertex binaryValue
  rw [Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    by_cases hi : eps i <;> simp [hi])

lemma hasProperHilbertCube_of_two_pow_le_block_length
    {S : Finset ℕ} {s d m h : ℕ}
    (hd : 0 < d)
    (hm : 2 ^ h ≤ m)
    (hsub : finiteArithmeticBlock s d m ⊆ S) :
    HasProperHilbertCube S h := by
  refine ⟨s, (fun i : Fin h => 2 ^ (i : ℕ) * d), ?_, ?_⟩
  · intro eps eta heq
    have hbin_mul :
        binaryValue h eps * d = binaryValue h eta * d := by
      exact Nat.add_left_cancel
        ((cubePoint_binaryValue (s := s) (d := d) eps).symm.trans
          (heq.trans (cubePoint_binaryValue (s := s) (d := d) eta)))
    have hbin : binaryValue h eps = binaryValue h eta :=
      mul_right_cancel₀ (Nat.ne_of_gt hd) hbin_mul
    exact binaryValue_injective hbin
  · intro eps
    apply hsub
    rw [mem_finiteArithmeticBlock_iff]
    refine ⟨binaryValue h eps, ?_, ?_⟩
    · exact (binaryValue_lt_two_pow eps).trans_le hm
    · exact cubePoint_binaryValue (s := s) (d := d) eps

lemma popularDifferenceCount_le_card (S : Finset ℕ) (d : ℕ) :
    popularDifferenceCount S d ≤ S.card := by
  unfold popularDifferenceCount
  exact Finset.card_filter_le _ _

lemma popularDifferenceCount_mono {S T : Finset ℕ}
    (hST : S ⊆ T) (d : ℕ) :
    popularDifferenceCount S d ≤ popularDifferenceCount T d := by
  unfold popularDifferenceCount
  exact Finset.card_le_card (by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hST hx.1, hST hx.2⟩)

lemma popularDifferenceUpTo_mono {S T : Finset ℕ}
    (hST : S ⊆ T) (N : ℕ) :
    popularDifferenceUpTo S N ≤ popularDifferenceUpTo T N := by
  unfold popularDifferenceUpTo
  simpa [Nat.succ_eq_add_one, add_comm] using
    Nat.succ_le_succ (Finset.sup_le (fun d hd =>
      (popularDifferenceCount_mono hST d).trans
        (Finset.le_sup (s := Finset.Icc 1 N)
          (f := popularDifferenceCount T) hd)))

lemma popularDifferenceUpTo_le_card_add_one (S : Finset ℕ) (N : ℕ) :
    popularDifferenceUpTo S N ≤ 1 + S.card := by
  unfold popularDifferenceUpTo
  have hsup :
      (Finset.Icc 1 N).sup (popularDifferenceCount S) ≤ S.card := by
    exact Finset.sup_le (fun d _ => popularDifferenceCount_le_card S d)
  omega

lemma one_le_popularDifferenceUpTo (S : Finset ℕ) (N : ℕ) :
    1 ≤ popularDifferenceUpTo S N := by
  unfold popularDifferenceUpTo
  omega

lemma additiveEnergy_le_card_cube (S : Finset ℕ) :
    additiveEnergy S ≤ S.card ^ 3 := by
  let quads : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    ((S.product S).product (S.product S)).filter fun q =>
      q.1.1 + q.2.1 = q.1.2 + q.2.2
  let triples : Finset ((ℕ × ℕ) × ℕ) := (S.product S).product S
  let proj : ((ℕ × ℕ) × (ℕ × ℕ)) → ((ℕ × ℕ) × ℕ) :=
    fun q => (q.1, q.2.1)
  have hmaps :
      Set.MapsTo proj (quads : Set ((ℕ × ℕ) × (ℕ × ℕ)))
        (triples : Set ((ℕ × ℕ) × ℕ)) := by
    intro q hq
    simp [quads, triples, proj] at hq ⊢
    exact ⟨hq.1.1, hq.1.2.1⟩
  have hinj :
      (quads : Set ((ℕ × ℕ) × (ℕ × ℕ))).InjOn proj := by
    intro q₁ hq₁ q₂ hq₂ hproj
    simp [quads, proj] at hq₁ hq₂ hproj ⊢
    rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨c₁, e₁⟩⟩
    rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨c₂, e₂⟩⟩
    simp at hq₁ hq₂ hproj ⊢
    rcases hproj with ⟨⟨ha, hb⟩, hc⟩
    subst a₂
    subst b₂
    subst c₂
    constructor
    · exact ⟨rfl, rfl⟩
    constructor
    · rfl
    · omega
  calc
    additiveEnergy S = quads.card := by
      rfl
    _ ≤ triples.card := Finset.card_le_card_of_injOn proj hmaps hinj
    _ = S.card ^ 3 := by
      simp [triples, pow_succ, Nat.mul_assoc]

lemma additiveEnergy_mono {S T : Finset ℕ}
    (hST : S ⊆ T) :
    additiveEnergy S ≤ additiveEnergy T := by
  exact Finset.addEnergy_mono hST hST

lemma hasProperHilbertCube_mono {S T : Finset ℕ}
    (hST : S ⊆ T) {h : ℕ}
    (hcube : HasProperHilbertCube S h) :
    HasProperHilbertCube T h := by
  rcases hcube with ⟨x₀, steps, hinj, hmem⟩
  exact ⟨x₀, steps, hinj, fun ε => hST (hmem ε)⟩

lemma two_pow_le_card_of_hasProperHilbertCube
    {S : Finset ℕ} {h : ℕ}
    (hcube : HasProperHilbertCube S h) :
    2 ^ h ≤ S.card := by
  rcases hcube with ⟨x₀, steps, hinj, hmem⟩
  let vertices : Finset ℕ :=
    (Finset.univ : Finset (Fin h → Bool)).image
      (hilbertCubeVertex x₀ steps)
  have hsubset : vertices ⊆ S := by
    intro x hx
    dsimp [vertices] at hx
    rcases Finset.mem_image.mp hx with ⟨ε, _hε, rfl⟩
    exact hmem ε
  have hcard_vertices :
      vertices.card = 2 ^ h := by
    dsimp [vertices]
    rw [Finset.card_image_of_injective]
    · simp
    · exact hinj
  rw [← hcard_vertices]
  exact Finset.card_le_card hsubset

/-- A finite set covered by blocks of size at most `M` has cardinality at
most the number of blocks times `M`. -/
lemma card_le_of_subset_biUnion_card_le
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {B : ι → Finset ℕ} {S : Finset ℕ} {M : ℕ}
    (hcover : S ⊆ I.biUnion B)
    (hBcard : ∀ i ∈ I, (B i).card ≤ M) :
    S.card ≤ I.card * M := by
  calc
    S.card ≤ (I.biUnion B).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ I, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, M := by
      exact Finset.sum_le_sum (fun i hi => hBcard i hi)
    _ = I.card * M := by simp [Nat.mul_comm]

lemma popularDifferenceUpTo_le_of_block_cover
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {B : ι → Finset ℕ} {S : Finset ℕ} {N M : ℕ}
    (hcover : S ⊆ I.biUnion B)
    (hBcard : ∀ i ∈ I, (B i).card ≤ M) :
    popularDifferenceUpTo S N ≤ I.card * M + 1 := by
  have hcard : S.card ≤ I.card * M :=
    card_le_of_subset_biUnion_card_le hcover hBcard
  exact (popularDifferenceUpTo_le_card_add_one (S := S) (N := N)).trans (by omega)

lemma additiveEnergy_le_of_block_cover
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {B : ι → Finset ℕ} {S : Finset ℕ} {M : ℕ}
    (hcover : S ⊆ I.biUnion B)
    (hBcard : ∀ i ∈ I, (B i).card ≤ M) :
    additiveEnergy S ≤ (I.card * M) ^ 3 := by
  have hcard : S.card ≤ I.card * M :=
    card_le_of_subset_biUnion_card_le hcover hBcard
  exact (additiveEnergy_le_card_cube (S := S)).trans
    (Nat.pow_le_pow_left hcard 3)

lemma two_pow_le_of_hasProperHilbertCube_of_block_cover
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {B : ι → Finset ℕ} {S : Finset ℕ} {M h : ℕ}
    (hcover : S ⊆ I.biUnion B)
    (hBcard : ∀ i ∈ I, (B i).card ≤ M)
    (hcube : HasProperHilbertCube S h) :
    2 ^ h ≤ I.card * M := by
  have hcard : S.card ≤ I.card * M :=
    card_le_of_subset_biUnion_card_le hcover hBcard
  exact (two_pow_le_card_of_hasProperHilbertCube hcube).trans hcard

lemma finiteArithmeticBlock_card
    {s d m : ℕ} (hd : 0 < d) :
    (finiteArithmeticBlock s d m).card = m := by
  unfold finiteArithmeticBlock
  rw [Finset.card_image_of_injOn]
  · simp
  · intro x hx y hy hxy
    have hmul : x * d = y * d := Nat.add_left_cancel hxy
    exact mul_right_cancel₀ (Nat.ne_of_gt hd) hmul

lemma finiteArithmeticBlock_inj_index
    {s d : ℕ} (hd : 0 < d) :
    Function.Injective fun r : ℕ => s + r * d := by
  intro x y hxy
  have hmul : x * d = y * d := Nat.add_left_cancel hxy
  exact mul_right_cancel₀ (Nat.ne_of_gt hd) hmul

lemma finiteArithmeticBlock_subset_iff
    {S : Finset ℕ} {s d m : ℕ} :
    finiteArithmeticBlock s d m ⊆ S ↔
      ∀ r : ℕ, r < m → s + r * d ∈ S := by
  constructor
  · intro h r hr
    exact h (by
      rw [mem_finiteArithmeticBlock_iff]
      exact ⟨r, hr, rfl⟩)
  · intro h x hx
    rcases mem_finiteArithmeticBlock_iff.mp hx with ⟨r, hr, rfl⟩
    exact h r hr

lemma block_step_le_of_two_le_length_subset_Iic
    {S : Finset ℕ} {s d m N : ℕ}
    (hm : 2 ≤ m)
    (hsub : finiteArithmeticBlock s d m ⊆ S)
    (hSle : ∀ x ∈ S, x ≤ N) :
    d ≤ N := by
  have hmem : s + 1 * d ∈ finiteArithmeticBlock s d m := by
    rw [mem_finiteArithmeticBlock_iff]
    exact ⟨1, by omega, rfl⟩
  have hSd : s + d ∈ S := by
    simpa using hsub hmem
  have hle : s + d ≤ N := hSle (s + d) hSd
  omega

lemma finiteArithmeticBlock_add_subset
    {s d m : ℕ} (hm : 0 < m) :
    finiteArithmeticBlock s d m + finiteArithmeticBlock s d m ⊆
      finiteArithmeticBlock (2 * s) d (2 * m - 1) := by
  intro x hx
  rw [mem_finiteArithmeticBlock_iff]
  rw [Finset.mem_add] at hx
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  rcases mem_finiteArithmeticBlock_iff.mp ha with ⟨i, hi, rfl⟩
  rcases mem_finiteArithmeticBlock_iff.mp hb with ⟨j, hj, rfl⟩
  refine ⟨i + j, ?_, ?_⟩
  · omega
  · ring

lemma additiveEnergy_finiteArithmeticBlock_lower
    {s d m : ℕ} (hd : 0 < d) :
    m ^ 3 ≤ 2 * additiveEnergy (finiteArithmeticBlock s d m) := by
  by_cases hm0 : m = 0
  · subst m
    simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  let B : Finset ℕ := finiteArithmeticBlock s d m
  have hBcard : B.card = m := finiteArithmeticBlock_card (s := s) (d := d) (m := m) hd
  have hsumcard : (B + B).card ≤ 2 * m := by
    have hsubset :
        B + B ⊆ finiteArithmeticBlock (2 * s) d (2 * m - 1) := by
      dsimp [B]
      exact finiteArithmeticBlock_add_subset (s := s) (d := d) (m := m) hmpos
    calc
      (B + B).card ≤ (finiteArithmeticBlock (2 * s) d (2 * m - 1)).card :=
        Finset.card_le_card hsubset
      _ = 2 * m - 1 := finiteArithmeticBlock_card (s := 2 * s) (d := d)
          (m := 2 * m - 1) hd
      _ ≤ 2 * m := by omega
  have hcauchy := Finset.le_card_add_mul_addEnergy B B
  have hstep :
      m ^ 2 * m ^ 2 ≤ (2 * m) * additiveEnergy B := by
    have hcauchy' :
        m ^ 2 * m ^ 2 ≤ (B + B).card * additiveEnergy B := by
      simpa [B, additiveEnergy, hBcard] using hcauchy
    exact hcauchy'.trans (Nat.mul_le_mul_right _ hsumcard)
  have hmul :
      m * m ^ 3 ≤ m * (2 * additiveEnergy B) := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hstep
  exact Nat.le_of_mul_le_mul_left hmul hmpos

lemma additiveEnergy_ge_of_arithmeticBlock_subset
    {S : Finset ℕ} {s d m : ℕ}
    (hd : 0 < d)
    (hsub : finiteArithmeticBlock s d m ⊆ S) :
    m ^ 3 ≤ 2 * additiveEnergy S := by
  have hmono :
      additiveEnergy (finiteArithmeticBlock s d m) ≤ additiveEnergy S :=
    additiveEnergy_mono hsub
  exact (additiveEnergy_finiteArithmeticBlock_lower
    (s := s) (d := d) (m := m) hd).trans
      (Nat.mul_le_mul_left 2 hmono)

lemma popularDifferenceCount_ge_block_pred
    {S : Finset ℕ} {s d m : ℕ}
    (hd : 0 < d)
    (hsub : finiteArithmeticBlock s d m ⊆ S) :
    m - 1 ≤ popularDifferenceCount S d := by
  let f : ℕ → ℕ := fun r => s + r * d
  have himage_subset :
      (Finset.range (m - 1)).image f ⊆
        S.filter fun x : ℕ => x + d ∈ S := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨r, hr, rfl⟩
    rw [Finset.mem_filter]
    have hrlt : r < m := by
      have : r < m - 1 := Finset.mem_range.mp hr
      omega
    have hrsucc : r + 1 < m := by
      have : r < m - 1 := Finset.mem_range.mp hr
      omega
    constructor
    · exact hsub (by
        rw [mem_finiteArithmeticBlock_iff]
        exact ⟨r, hrlt, rfl⟩)
    · have hstep : s + r * d + d = s + (r + 1) * d := by ring
      rw [hstep]
      exact hsub (by
        rw [mem_finiteArithmeticBlock_iff]
        exact ⟨r + 1, hrsucc, rfl⟩)
  calc
    m - 1 = ((Finset.range (m - 1)).image f).card := by
          unfold f
          rw [Finset.card_image_of_injOn]
          · simp
          · intro x hx y hy hxy
            have hmul : x * d = y * d := Nat.add_left_cancel hxy
            exact mul_right_cancel₀ (Nat.ne_of_gt hd) hmul
    _ ≤ popularDifferenceCount S d := by
          unfold popularDifferenceCount
          exact Finset.card_le_card himage_subset

lemma popularDifferenceUpTo_ge_of_block_subset
    {S : Finset ℕ} {N s d m : ℕ}
    (hdN : 1 ≤ d ∧ d ≤ N)
    (hsub : finiteArithmeticBlock s d m ⊆ S) :
    m ≤ popularDifferenceUpTo S N := by
  by_cases hm : m = 0
  · subst m
    simp [popularDifferenceUpTo]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hpred :
        m - 1 ≤ popularDifferenceCount S d :=
      popularDifferenceCount_ge_block_pred (lt_of_lt_of_le Nat.zero_lt_one hdN.1) hsub
    have hdmem : d ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact hdN
    unfold popularDifferenceUpTo
    have hle_sup :
        popularDifferenceCount S d ≤
          (Finset.Icc 1 N).sup (popularDifferenceCount S) :=
      Finset.le_sup (s := Finset.Icc 1 N) (f := popularDifferenceCount S) hdmem
    omega

/-- Finite block bridge: one large arithmetic block inside `S`, plus a block
cover of `S`, sandwiches popular differences, additive energy, and Hilbert
cubes.

The statistic `popularDifferenceUpTo` is bounded by `N`, so the lower bound
requires the block step `d` to lie in `[1, N]`. -/
theorem finite_block_cover_bridge
    {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {B : ι → Finset ℕ}
    {S : Finset ℕ} {N s d m M : ℕ}
    (hdN : 1 ≤ d ∧ d ≤ N)
    (hsubBlock : finiteArithmeticBlock s d m ⊆ S)
    (hcover : S ⊆ I.biUnion B)
    (hBcard : ∀ i ∈ I, (B i).card ≤ M) :
    m ≤ popularDifferenceUpTo S N ∧
      popularDifferenceUpTo S N ≤ I.card * M + 1 ∧
      m ^ 3 ≤ 2 * additiveEnergy S ∧
      additiveEnergy S ≤ (I.card * M) ^ 3 ∧
      (∀ h : ℕ, 2 ^ h ≤ m → HasProperHilbertCube S h) ∧
      (∀ h : ℕ, HasProperHilbertCube S h → 2 ^ h ≤ I.card * M) := by
  constructor
  · exact popularDifferenceUpTo_ge_of_block_subset hdN hsubBlock
  constructor
  · exact popularDifferenceUpTo_le_of_block_cover hcover hBcard
  constructor
  · exact additiveEnergy_ge_of_arithmeticBlock_subset
      (lt_of_lt_of_le Nat.zero_lt_one hdN.1) hsubBlock
  constructor
  · exact additiveEnergy_le_of_block_cover hcover hBcard
  constructor
  · intro h hh
    exact hasProperHilbertCube_of_two_pow_le_block_length
      (lt_of_lt_of_le Nat.zero_lt_one hdN.1) hh hsubBlock
  · intro h hcube
    exact two_pow_le_of_hasProperHilbertCube_of_block_cover hcover hBcard hcube

lemma finite_block_bridge_popular
    {S : Finset ℕ} {N K V : ℕ}
    {starts steps lengths : Fin K → ℕ}
    (hVpos : 1 ≤ V)
    (hcover :
      S ⊆ (Finset.univ : Finset (Fin K)).biUnion
        (fun i => finiteArithmeticBlock (starts i) (steps i) (lengths i)))
    (hlen : ∀ i : Fin K, lengths i ≤ V)
    (hexists :
      ∃ i : Fin K,
        lengths i = V ∧
          1 ≤ steps i ∧ steps i ≤ N ∧
          finiteArithmeticBlock (starts i) (steps i) (lengths i) ⊆ S) :
    V ≤ popularDifferenceUpTo S N ∧
      popularDifferenceUpTo S N ≤ 1 + K * V := by
  have _ : 0 < V := lt_of_lt_of_le Nat.zero_lt_one hVpos
  constructor
  · rcases hexists with ⟨i, hiV, hstep1, hstepN, hblock⟩
    rw [← hiV]
    exact popularDifferenceUpTo_ge_of_block_subset ⟨hstep1, hstepN⟩ hblock
  · have hcard_le :
        S.card ≤ K * V := by
      calc
        S.card ≤
            ((Finset.univ : Finset (Fin K)).biUnion
              (fun i => finiteArithmeticBlock (starts i) (steps i) (lengths i))).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ i : Fin K,
              (finiteArithmeticBlock (starts i) (steps i) (lengths i)).card := by
          exact Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin K, V := by
          exact Finset.sum_le_sum (fun i _ => by
            calc
            (finiteArithmeticBlock (starts i) (steps i) (lengths i)).card
                  ≤ lengths i := by
                    unfold finiteArithmeticBlock
                    simpa using
                      (Finset.card_image_le
                        (s := Finset.range (lengths i))
                        (f := fun r : ℕ => starts i + r * steps i))
              _ ≤ V := hlen i)
        _ = K * V := by simp
    exact (popularDifferenceUpTo_le_card_add_one S N).trans (by omega)

theorem finite_block_bridge_popular_energy
    {S : Finset ℕ} {N K V : ℕ}
    {starts steps lengths : Fin K → ℕ}
    (hVpos : 1 ≤ V)
    (hcover :
      S ⊆ (Finset.univ : Finset (Fin K)).biUnion
        (fun i => finiteArithmeticBlock (starts i) (steps i) (lengths i)))
    (hlen : ∀ i : Fin K, lengths i ≤ V)
    (hexists :
      ∃ i : Fin K,
        lengths i = V ∧
          1 ≤ steps i ∧ steps i ≤ N ∧
          finiteArithmeticBlock (starts i) (steps i) (lengths i) ⊆ S) :
    V ≤ popularDifferenceUpTo S N ∧
      popularDifferenceUpTo S N ≤ 1 + K * V ∧
      additiveEnergy S ≤ (K * V) ^ 3 := by
  have hpop :=
    finite_block_bridge_popular
      (S := S) (N := N) (K := K) (V := V)
      (starts := starts) (steps := steps) (lengths := lengths)
      hVpos hcover hlen hexists
  have hcard_le :
      S.card ≤ K * V := by
    calc
      S.card ≤
          ((Finset.univ : Finset (Fin K)).biUnion
            (fun i => finiteArithmeticBlock (starts i) (steps i) (lengths i))).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ i : Fin K,
            (finiteArithmeticBlock (starts i) (steps i) (lengths i)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin K, V := by
        exact Finset.sum_le_sum (fun i _ => by
          calc
            (finiteArithmeticBlock (starts i) (steps i) (lengths i)).card
                ≤ lengths i := by
                  unfold finiteArithmeticBlock
                  simpa using
                    (Finset.card_image_le
                      (s := Finset.range (lengths i))
                      (f := fun r : ℕ => starts i + r * steps i))
            _ ≤ V := hlen i)
      _ = K * V := by simp
  refine ⟨hpop.1, hpop.2, ?_⟩
  exact (additiveEnergy_le_card_cube S).trans (Nat.pow_le_pow_left hcard_le 3)

/-- The finite block bridge in the `K,V` form used in the writeup.

If `S` is covered by `K` arithmetic blocks of length at most `V`, and one
length-`V` block is contained in `S` with step in `[1,N]`, then popular
differences, additive energy, and Hilbert-cube dimensions are sandwiched by
the corresponding `V` and `K * V` scales. -/
theorem finite_block_bridge
    {S : Finset ℕ} {N K V : ℕ}
    {starts steps lengths : Fin K → ℕ}
    (hcover :
      S ⊆ (Finset.univ : Finset (Fin K)).biUnion
        (fun i => finiteArithmeticBlock (starts i) (steps i) (lengths i)))
    (hlen : ∀ i : Fin K, lengths i ≤ V)
    (hexists :
      ∃ i : Fin K,
        lengths i = V ∧
          1 ≤ steps i ∧ steps i ≤ N ∧
          finiteArithmeticBlock (starts i) (steps i) (lengths i) ⊆ S) :
    V ≤ popularDifferenceUpTo S N ∧
      popularDifferenceUpTo S N ≤ 1 + K * V ∧
      V ^ 3 ≤ 2 * additiveEnergy S ∧
      additiveEnergy S ≤ (K * V) ^ 3 ∧
      (∀ h : ℕ, 2 ^ h ≤ V → HasProperHilbertCube S h) ∧
      (∀ h : ℕ, HasProperHilbertCube S h → 2 ^ h ≤ K * V) := by
  rcases hexists with ⟨i, hiV, hstep1, hstepN, hblock⟩
  have hBcard :
      ∀ j ∈ (Finset.univ : Finset (Fin K)),
        (finiteArithmeticBlock (starts j) (steps j) (lengths j)).card ≤ V := by
    intro j _hj
    calc
      (finiteArithmeticBlock (starts j) (steps j) (lengths j)).card
          ≤ lengths j := by
            unfold finiteArithmeticBlock
            simpa using
              (Finset.card_image_le
                (s := Finset.range (lengths j))
                (f := fun r : ℕ => starts j + r * steps j))
      _ ≤ V := hlen j
  have hbridge :=
    finite_block_cover_bridge
      (I := (Finset.univ : Finset (Fin K)))
      (B := fun j => finiteArithmeticBlock (starts j) (steps j) (lengths j))
      (S := S) (N := N) (s := starts i) (d := steps i)
      (m := lengths i) (M := V)
      ⟨hstep1, hstepN⟩ hblock hcover hBcard
  rcases hbridge with
    ⟨hpop_low, hpop_high, henergy_low, henergy_high,
      hcube_low, hcube_high⟩
  subst hiV
  refine ⟨hpop_low, ?_, henergy_low, ?_, hcube_low, ?_⟩
  · simpa [Nat.add_comm, Nat.mul_comm] using hpop_high
  · simpa using henergy_high
  · intro h hcube
    simpa using hcube_high h hcube

end IrrationalityAr
