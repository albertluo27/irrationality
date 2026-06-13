import IrrationalityAr.FractionalParts

open scoped BigOperators

namespace IrrationalityAr

/-- The number of earlier fractional parts strictly above the fractional part
of `q r`:

`C_r(q) = #{k : 1 ≤ k < q and {q r} < {k r}}`.
-/
noncomputable def aboveCount (r : ℝ) (q : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 q).filter fun k => fracMul r q < fracMul r k).card

/-- The easy range estimate `C_r(q) ≤ q - 1`. -/
theorem aboveCount_le_pred (r : ℝ) (q : ℕ) :
    aboveCount r q ≤ q - 1 := by
  classical
  rw [aboveCount]
  calc
    ((Finset.Ico 1 q).filter fun k => fracMul r q < fracMul r k).card
        ≤ (Finset.Ico 1 q).card := Finset.card_filter_le _ _
    _ = q - 1 := by simp

/-- The defect in a paired floor sum.  It is `1` exactly when the fractional
part of `q r` is strictly smaller than the fractional part of `k r`. -/
noncomputable def pairDefect (r : ℝ) (q k : ℕ) : ℤ :=
  if fracMul r q < fracMul r k then 1 else 0

/-- The floor of a difference of two fractional parts is either `-1` or `0`.
This is the local arithmetic fact behind the pairing argument. -/
theorem floor_fract_sub_fract (x y : ℝ) :
    Int.floor (Int.fract x - Int.fract y) =
      if Int.fract x < Int.fract y then -1 else 0 := by
  by_cases h : Int.fract x < Int.fract y
  · rw [if_pos h]
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      linarith [Int.fract_nonneg x, Int.fract_lt_one y]
    · norm_num
      linarith
  · rw [if_neg h]
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · exact sub_nonneg.mpr (le_of_not_gt h)
    · linarith [Int.fract_lt_one x, Int.fract_nonneg y]

/-- Expand the floor of a difference into the difference of the floors and a
single possible borrow. -/
theorem floor_sub_eq_floor_sub_floor_add_defect (x y : ℝ) :
    Int.floor (x - y) =
      Int.floor x - Int.floor y +
        (if Int.fract x < Int.fract y then -1 else 0) := by
  calc
    Int.floor (x - y) =
        Int.floor ((((Int.floor x - Int.floor y : ℤ) : ℝ)) +
          (Int.fract x - Int.fract y)) := by
      congr 1
      simp only [Int.fract]
      push_cast
      ring
    _ = (Int.floor x - Int.floor y) +
          Int.floor (Int.fract x - Int.fract y) := by
      rw [Int.floor_intCast_add]
    _ = _ := by
      rw [floor_fract_sub_fract]

/-- The pointwise paired-floor identity. -/
theorem floorMul_add_floorMul_sub (r : ℝ) {q k : ℕ} (hk : k ≤ q) :
    floorMul r k + floorMul r (q - k) =
      floorMul r q - pairDefect r q k := by
  unfold floorMul pairDefect fracMul
  have hcast : (((q - k : ℕ) : ℝ) * r) = (q : ℝ) * r - (k : ℝ) * r := by
    rw [Nat.cast_sub hk]
    ring
  rw [hcast, floor_sub_eq_floor_sub_floor_add_defect]
  by_cases h : Int.fract ((q : ℝ) * r) < Int.fract ((k : ℝ) * r)
  · simp only [h, if_true]
    ring_nf
  · simp only [h, if_false]
    ring_nf

/-- Replacing the original closed interval by a half-open interval is useful
for the reflection argument. -/
theorem floorSum_pred_eq_sum_Ico (r : ℝ) (q : ℕ) :
    floorSum r (q - 1) = ∑ k ∈ Finset.Ico 1 q, floorMul r k := by
  unfold floorSum
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  · intro k hk
    rfl

/-- The involution `k ↦ q-k` reverses the interval `1 ≤ k < q`. -/
theorem sum_floorMul_reflect (r : ℝ) (q : ℕ) :
    (∑ k ∈ Finset.Ico 1 q, floorMul r (q - k)) =
      ∑ k ∈ Finset.Ico 1 q, floorMul r k := by
  simpa using
    (Finset.sum_Ico_reflect (floorMul r) 1 (show q ≤ q + 1 by omega))

/-- Summing the `0`-`1` defects counts exactly the filtered interval used in
`aboveCount`. -/
theorem sum_pairDefect_eq_cast_aboveCount (r : ℝ) (q : ℕ) :
    (∑ k ∈ Finset.Ico 1 q, pairDefect r q k) = (aboveCount r q : ℤ) := by
  classical
  rw [aboveCount]
  change (∑ k ∈ Finset.Ico 1 q,
      (if fracMul r q < fracMul r k then (1 : ℤ) else 0)) =
    (((Finset.Ico 1 q).filter fun k => fracMul r q < fracMul r k).card : ℤ)
  simp

/-!
# Shared pairing identity

For `q = n + 1`, pair the summands indexed by `k` and `q - k`.
For every `1 ≤ k < q`,

`⌊k r⌋ + ⌊(q-k) r⌋ = ⌊q r⌋ - 1_{ {q r} < {k r} }`.

Summing gives

`2 F_r(q-1) = (q-1) ⌊q r⌋ - C_r(q)`.
-/
theorem two_mul_floorSum_pred_eq (r : ℝ) (q : ℕ) :
    2 * floorSum r (q - 1) =
      ((q - 1 : ℕ) : ℤ) * floorMul r q - (aboveCount r q : ℤ) := by
  calc
    2 * floorSum r (q - 1) =
        (∑ k ∈ Finset.Ico 1 q, floorMul r k) +
          ∑ k ∈ Finset.Ico 1 q, floorMul r (q - k) := by
      rw [sum_floorMul_reflect, floorSum_pred_eq_sum_Ico]
      ring
    _ = ∑ k ∈ Finset.Ico 1 q,
          (floorMul r k + floorMul r (q - k)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.Ico 1 q,
          (floorMul r q - pairDefect r q k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact floorMul_add_floorMul_sub r (by
        have := (Finset.mem_Ico.mp hk).2
        omega)
    _ = ((q - 1 : ℕ) : ℤ) * floorMul r q - (aboveCount r q : ℤ) := by
      rw [Finset.sum_sub_distrib, sum_pairDefect_eq_cast_aboveCount]
      simp

/-- Pairing identity: upper endpoint plus even paired floor implies
membership in `A_r`. -/
theorem mem_A_of_aboveCount_zero_and_even_floor {r : ℝ} {n : ℕ}
    (hn : 0 < n) (hC : aboveCount r (n + 1) = 0)
    (heven : Even (floorMul r (n + 1))) :
    n ∈ A r := by
  rcases heven with ⟨z, hz⟩
  have hpair :
      2 * floorSum r n =
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    simpa using two_mul_floorSum_pred_eq r (n + 1)
  have hpair0 : 2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) := by
    simpa [hC] using hpair
  refine (mem_A_iff).mpr ⟨hn, ?_⟩
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  calc
    2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) := hpair0
    _ = (n : ℤ) * (z + z) := by rw [hz]
    _ = 2 * ((n : ℤ) * z) := by ring

/-- Pairing identity: membership at the upper endpoint forces the paired floor
to be even. -/
theorem even_floorMul_of_mem_A_and_aboveCount_zero {r : ℝ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A r)
    (hC : aboveCount r (n + 1) = 0) :
    Even (floorMul r (n + 1)) := by
  rcases (mem_A_iff.mp hA).2 with ⟨z, hz⟩
  have hpair :
      2 * floorSum r n =
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    simpa using two_mul_floorSum_pred_eq r (n + 1)
  have hpair0 : 2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) := by
    simpa [hC] using hpair
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hfloor : floorMul r (n + 1) = z + z := by
    apply mul_left_cancel₀ hnz
    calc
      (n : ℤ) * floorMul r (n + 1) = 2 * floorSum r n := hpair0.symm
      _ = 2 * ((n : ℤ) * z) := by rw [hz]
      _ = (n : ℤ) * (z + z) := by ring
  exact ⟨z, hfloor⟩

/-- A nonnegative integer multiple of a positive natural `n`, bounded above by
`n`, is one of the two endpoints. -/
private theorem eq_zero_or_eq_of_int_dvd_of_le {n c : ℕ}
    (hn : 0 < n) (hle : c ≤ n) (hdiv : (n : ℤ) ∣ (c : ℤ)) :
    c = 0 ∨ c = n := by
  rcases hdiv with ⟨z, hz⟩
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hcz_nonneg : (0 : ℤ) ≤ (c : ℤ) := by exact_mod_cast Nat.zero_le c
  have hcz_le : (c : ℤ) ≤ (n : ℤ) := by exact_mod_cast hle
  have hz_nonneg : 0 ≤ z := by
    by_contra hnot
    have hzneg : z < 0 := lt_of_not_ge hnot
    have hprod_neg : (n : ℤ) * z < 0 :=
      mul_neg_of_pos_of_neg hnz hzneg
    linarith
  have hz_le_one : z ≤ 1 := by
    by_contra hnot
    have htwo_le : (2 : ℤ) ≤ z := by omega
    have hprod_le : (n : ℤ) * 2 ≤ (n : ℤ) * z :=
      mul_le_mul_of_nonneg_left htwo_le (le_of_lt hnz)
    have hn_lt_twice : (n : ℤ) < (n : ℤ) * 2 := by
      nlinarith
    nlinarith
  have hz_cases : z = 0 ∨ z = 1 := by omega
  rcases hz_cases with rfl | rfl
  · left
    have : (c : ℤ) = 0 := by simpa using hz
    exact_mod_cast this
  · right
    have : (c : ℤ) = (n : ℤ) := by simpa using hz
    exact_mod_cast this

/-- If `n ∈ A_r`, the pairing identity forces `C_r(n+1)` to be an endpoint:
either `0` or `n`. -/
theorem aboveCount_eq_zero_or_eq_of_mem_A {r : ℝ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A r) :
    aboveCount r (n + 1) = 0 ∨ aboveCount r (n + 1) = n := by
  have hfloor_dvd : (n : ℤ) ∣ floorSum r n := (mem_A_iff.mp hA).2
  have hpair :
      2 * floorSum r n =
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    simpa using two_mul_floorSum_pred_eq r (n + 1)
  have htwice_dvd : (n : ℤ) ∣ 2 * floorSum r n := by
    simpa [mul_comm] using (dvd_mul_of_dvd_left hfloor_dvd (2 : ℤ))
  have hpair_dvd :
      (n : ℤ) ∣
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    rw [← hpair]
    exact htwice_dvd
  have hmain_dvd : (n : ℤ) ∣ (n : ℤ) * floorMul r (n + 1) := by
    exact dvd_mul_right (n : ℤ) (floorMul r (n + 1))
  have hcount_dvd : (n : ℤ) ∣ (aboveCount r (n + 1) : ℤ) := by
    have hsub := dvd_sub hmain_dvd hpair_dvd
    simpa using hsub
  have hcount_le : aboveCount r (n + 1) ≤ n := by
    simpa using aboveCount_le_pred r (n + 1)
  exact eq_zero_or_eq_of_int_dvd_of_le hn hcount_le hcount_dvd

end IrrationalityAr
