import IrrationalityAr.Pairing
import IrrationalityAr.Progressions

namespace IrrationalityAr

/-!
# Rational case

The formalization should use the shared pairing identity rather than a long
closed formula for the entire floor sum.

Let `r = a / b`, with `b > 0` and `gcd(|a|, b) = 1`. For `n ≥ b`, the first
`n` fractional parts include every residue class modulo `b`. Therefore the
endpoint alternative from `aboveCount_eq_zero_or_eq_of_mem_A` simplifies:

* `C_r(n+1) = n` is impossible because one of the earlier fractional parts is
  `0`;
* `C_r(n+1) = 0` holds exactly when `{(n+1)r} = (b-1)/b`.

The parity condition from the pairing identity then yields the explicit tail
criterion

`n ∈ A_(a/b) ↔ a * (n + 1) ≡ b - 1 [ZMOD 2*b]`.

This congruence is a single residue class after dividing the modulus by the
relevant gcd. It is the precise source of the eventual arithmetic progression.
-/

/-- Rational fractional parts are residues modulo the denominator. This is the
formal version of the write-up's repeated use of residues `ka mod b`. -/
private theorem fracMul_rat_eq_int_emod (a : ℤ) (b k : ℕ) :
    fracMul ((a : ℝ) / (b : ℝ)) k =
      (((a * (k : ℤ)) % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) := by
  unfold fracMul
  have harg :
      ((k : ℝ) * ((a : ℝ) / (b : ℝ))) =
        (((a * (k : ℤ) : ℤ) : ℝ) / (b : ℝ)) := by
    norm_num
    ring
  rw [harg]
  simpa [mul_comm] using
    (Int.fract_div_intCast_eq_div_intCast_mod
      (k := ℝ) (m := a * (k : ℤ)) (n := b))

/-- Rational floors are integer division by the denominator. -/
private theorem floorMul_rat_eq_ediv (a : ℤ) (b k : ℕ) :
    floorMul ((a : ℝ) / (b : ℝ)) k = (a * (k : ℤ)) / (b : ℤ) := by
  unfold floorMul
  have harg :
      ((k : ℝ) * ((a : ℝ) / (b : ℝ))) =
        (((a * (k : ℤ) : ℤ) : ℝ) / (b : ℝ)) := by
    norm_num
    ring
  rw [harg]
  rw [Int.floor_div_natCast]
  rw [Int.floor_intCast]

/-- A congruence modulo `b` fixes the fractional part of `k * a / b`. -/
private theorem fracMul_rat_eq_of_modEq {a : ℤ} {b k j : ℕ}
    (hj : j < b)
    (hmod : a * (k : ℤ) ≡ (j : ℤ) [ZMOD (b : ℤ)]) :
    fracMul ((a : ℝ) / (b : ℝ)) k = (j : ℝ) / (b : ℝ) := by
  rw [fracMul_rat_eq_int_emod]
  have hjmod : ((j : ℤ) % (b : ℤ)) = (j : ℤ) := by
    exact Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le j) (by exact_mod_cast hj)
  have hem : ((a * (k : ℤ)) % (b : ℤ)) = (j : ℤ) := by
    simpa [Int.ModEq, hjmod] using hmod
  rw [hem]
  norm_num

/-- The residue of `a * k` modulo `b` is always at most `b - 1`, hence so is
the corresponding fractional part. -/
private theorem fracMul_rat_le_top (a : ℤ) {b k : ℕ} (hb : 0 < b) :
    fracMul ((a : ℝ) / (b : ℝ)) k ≤ ((b - 1 : ℕ) : ℝ) / (b : ℝ) := by
  rw [fracMul_rat_eq_int_emod]
  have hbz : 0 < (b : ℤ) := by exact_mod_cast hb
  have hleZ : (a * (k : ℤ)) % (b : ℤ) ≤ ((b - 1 : ℕ) : ℤ) := by
    have hlt : (a * (k : ℤ)) % (b : ℤ) < (b : ℤ) :=
      Int.emod_lt_of_pos _ hbz
    omega
  have hleR :
      (((a * (k : ℤ)) % (b : ℤ) : ℤ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hleZ
  exact div_le_div_of_nonneg_right hleR (by positivity)

/-- The denominator index has fractional part `0`. This is the concrete
earlier fractional part that rules out the `aboveCount = n` endpoint. -/
private theorem fracMul_rat_den_eq_zero (a : ℤ) {b : ℕ} (hb : 0 < b) :
    fracMul ((a : ℝ) / (b : ℝ)) b = 0 := by
  have hmod : a * (b : ℤ) ≡ (0 : ℤ) [ZMOD (b : ℤ)] := by
    exact Int.modEq_zero_iff_dvd.mpr ⟨a, by ring⟩
  have hfrac := fracMul_rat_eq_of_modEq
    (a := a) (b := b) (k := b) (j := 0) (by omega) hmod
  simpa using hfrac

/-- Since multiplication by `a` permutes residues modulo `b`, the first `n`
indices contain a representative of every residue once `n ≥ b`. -/
private theorem exists_Ico_int_mul_modEq_of_coprime {a : ℤ} {b n j : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) (hn : b ≤ n) :
    ∃ k ∈ Finset.Ico 1 (n + 1),
      a * (k : ℤ) ≡ (j : ℤ) [ZMOD (b : ℤ)] := by
  haveI : NeZero b := ⟨Nat.ne_of_gt hb⟩
  have hcop : IsCoprime a (b : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    exact hab
  let x : ZMod b := (a : ZMod b)⁻¹ * (j : ZMod b)
  have hax : (a : ZMod b) * x = (j : ZMod b) := by
    dsimp [x]
    rw [← mul_assoc, ZMod.coe_int_mul_inv_eq_one hcop]
    simp
  by_cases hx : x = 0
  · refine ⟨b, ?_, ?_⟩
    · simp [Finset.mem_Ico]
      omega
    · have hjZ : (j : ZMod b) = 0 := by
        rw [← hax, hx]
        simp
      have hz : ((a * (b : ℤ) : ℤ) : ZMod b) = ((j : ℤ) : ZMod b) := by
        calc
          ((a * (b : ℤ) : ℤ) : ZMod b) = (a : ZMod b) * (b : ZMod b) := by
            norm_num
          _ = 0 := by simp
          _ = (j : ZMod b) := hjZ.symm
          _ = ((j : ℤ) : ZMod b) := by norm_num
      exact (ZMod.intCast_eq_intCast_iff (a * (b : ℤ)) (j : ℤ) b).mp hz
  · refine ⟨x.val, ?_, ?_⟩
    · have hxpos : 0 < x.val := (ZMod.val_pos).mpr hx
      have hxlt : x.val < b := ZMod.val_lt x
      simp [Finset.mem_Ico]
      omega
    · have hz : ((a * (x.val : ℤ) : ℤ) : ZMod b) = ((j : ℤ) : ZMod b) := by
        calc
          ((a * (x.val : ℤ) : ℤ) : ZMod b) =
              (a : ZMod b) * ((x.val : ℕ) : ZMod b) := by
            norm_num
          _ = (a : ZMod b) * x := by
            rw [ZMod.natCast_zmod_val x]
          _ = (j : ZMod b) := hax
          _ = ((j : ℤ) : ZMod b) := by norm_num
      exact (ZMod.intCast_eq_intCast_iff (a * (x.val : ℤ)) (j : ℤ) b).mp hz

/-- For rational `a / b`, the upper endpoint in the pairing alternative is
impossible once the earlier indices include `b`, whose fractional part is `0`. -/
private theorem aboveCount_rat_ne_n {a : ℤ} {b n : ℕ}
    (hb : 0 < b) (hn : b ≤ n) :
    aboveCount ((a : ℝ) / (b : ℝ)) (n + 1) ≠ n := by
  intro hC
  have hfilter_card :
      (((Finset.Ico 1 (n + 1)).filter fun k =>
          fracMul ((a : ℝ) / (b : ℝ)) (n + 1) <
            fracMul ((a : ℝ) / (b : ℝ)) k).card =
        (Finset.Ico 1 (n + 1)).card) := by
    rw [show (Finset.Ico 1 (n + 1)).card = n by simp]
    simpa [aboveCount] using hC
  have hall := (Finset.card_filter_eq_iff.mp hfilter_card)
  have hbmem : b ∈ Finset.Ico 1 (n + 1) := by
    simp [Finset.mem_Ico]
    omega
  have hlt := hall b hbmem
  have hzero := fracMul_rat_den_eq_zero a hb
  rw [hzero] at hlt
  have hnonneg : 0 ≤ fracMul ((a : ℝ) / (b : ℝ)) (n + 1) := by
    unfold fracMul
    exact Int.fract_nonneg _
  linarith

/-- If no earlier rational fractional part lies above the endpoint, then the
endpoint must be the largest residue `(b - 1) / b`. -/
private theorem fracMul_rat_eq_top_of_aboveCount_zero {a : ℤ} {b n : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) (hn : b ≤ n)
    (hC : aboveCount ((a : ℝ) / (b : ℝ)) (n + 1) = 0) :
    fracMul ((a : ℝ) / (b : ℝ)) (n + 1) =
      ((b - 1 : ℕ) : ℝ) / (b : ℝ) := by
  have hnone :
      ∀ k ∈ Finset.Ico 1 (n + 1),
        ¬ fracMul ((a : ℝ) / (b : ℝ)) (n + 1) <
            fracMul ((a : ℝ) / (b : ℝ)) k := by
    simpa [aboveCount] using
      (Finset.card_filter_eq_zero_iff.mp hC)
  obtain ⟨k, hk, hmod⟩ :=
    exists_Ico_int_mul_modEq_of_coprime
      (a := a) (b := b) (n := n) (j := b - 1) hb hab hn
  have hkfrac :
      fracMul ((a : ℝ) / (b : ℝ)) k =
        ((b - 1 : ℕ) : ℝ) / (b : ℝ) := by
    exact fracMul_rat_eq_of_modEq
      (a := a) (b := b) (k := k) (j := b - 1) (by omega) hmod
  have htop_le :
      ((b - 1 : ℕ) : ℝ) / (b : ℝ) ≤
        fracMul ((a : ℝ) / (b : ℝ)) (n + 1) := by
    rw [← hkfrac]
    exact le_of_not_gt (hnone k hk)
  have hle_top :
      fracMul ((a : ℝ) / (b : ℝ)) (n + 1) ≤
        ((b - 1 : ℕ) : ℝ) / (b : ℝ) :=
    fracMul_rat_le_top a hb
  exact le_antisymm hle_top htop_le

/-- A modulo-`2b` congruence says the fractional part is the largest residue. -/
private theorem fracMul_rat_eq_top_of_modEq_two_mul {a : ℤ} {b q : ℕ}
    (hb : 0 < b)
    (hmod : a * (q : ℤ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))]) :
    fracMul ((a : ℝ) / (b : ℝ)) q =
      ((b - 1 : ℕ) : ℝ) / (b : ℝ) := by
  have hmodb : a * (q : ℤ) ≡ (b : ℤ) - 1 [ZMOD (b : ℤ)] :=
    Int.ModEq.of_dvd (by exact dvd_mul_left (b : ℤ) (2 : ℤ)) hmod
  have hpred : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
  exact fracMul_rat_eq_of_modEq
    (a := a) (b := b) (k := q) (j := b - 1) (by omega) (by
      simpa [hpred] using hmodb)

/-- A modulo-`2b` congruence makes the rational paired floor even. -/
private theorem even_floorMul_rat_of_modEq_two_mul {a : ℤ} {b q : ℕ}
    (hb : 0 < b)
    (hmod : a * (q : ℤ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))]) :
    Even (floorMul ((a : ℝ) / (b : ℝ)) q) := by
  rw [floorMul_rat_eq_ediv]
  let T : ℤ := a * (q : ℤ)
  let B : ℤ := b
  change Even (T / B)
  have hmodT : T ≡ B - 1 [ZMOD 2 * B] := by
    simpa [T, B] using hmod
  obtain ⟨s, hs⟩ := Int.modEq_iff_add_fac.mp hmodT
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast hb
  have hrem_nonneg : 0 ≤ B - 1 := by omega
  have hrem_lt : B - 1 < B := by omega
  have hdecomp : (B - 1) + B * (-2 * s) = T := by
    rw [hs]
    ring
  have hquot : T / B = -2 * s :=
    ((Int.ediv_emod_unique hBpos).mpr ⟨hdecomp, hrem_nonneg, hrem_lt⟩).1
  rw [hquot]
  exact ⟨-s, by ring⟩

/-- If the endpoint is the largest residue, no earlier fractional part lies
strictly above it. -/
private theorem aboveCount_rat_eq_zero_of_modEq_two_mul {a : ℤ} {b q : ℕ}
    (hb : 0 < b)
    (hmod : a * (q : ℤ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))]) :
    aboveCount ((a : ℝ) / (b : ℝ)) q = 0 := by
  have htop := fracMul_rat_eq_top_of_modEq_two_mul
    (a := a) (b := b) (q := q) hb hmod
  rw [aboveCount]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro k hk
  rw [htop]
  exact not_lt_of_ge (fracMul_rat_le_top a hb)

/-- Largest residue plus even rational paired floor reconstructs the full
congruence modulo `2b`. -/
private theorem modEq_two_mul_of_fracMul_top_and_even_floor {a : ℤ} {b q : ℕ}
    (hb : 0 < b)
    (hfrac : fracMul ((a : ℝ) / (b : ℝ)) q =
      ((b - 1 : ℕ) : ℝ) / (b : ℝ))
    (heven : Even (floorMul ((a : ℝ) / (b : ℝ)) q)) :
    a * (q : ℤ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] := by
  let T : ℤ := a * (q : ℤ)
  let B : ℤ := b
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast hb
  have hBneR : (b : ℝ) ≠ 0 := by positivity
  have hfrac' :
      (((T % B : ℤ) : ℝ) / (b : ℝ)) =
        ((b - 1 : ℕ) : ℝ) / (b : ℝ) := by
    simpa [T, B, fracMul_rat_eq_int_emod] using hfrac
  have hremNat : T % B = ((b - 1 : ℕ) : ℤ) := by
    have hnumR :
        (((T % B : ℤ) : ℝ)) = ((b - 1 : ℕ) : ℝ) :=
      (div_left_inj' hBneR).mp hfrac'
    exact_mod_cast hnumR
  have hpred : ((b - 1 : ℕ) : ℤ) = B - 1 := by
    dsimp [B]
    omega
  have hrem : T % B = B - 1 := by
    simpa [hpred] using hremNat
  have heven' : Even (T / B) := by
    simpa [T, B, floorMul_rat_eq_ediv] using heven
  rw [even_iff_two_dvd] at heven'
  rcases heven' with ⟨s, hquot⟩
  have hT : T = (B - 1) + (2 * B) * s := by
    calc
      T = B * (T / B) + T % B := by rw [Int.mul_ediv_add_emod]
      _ = B * (2 * s) + (B - 1) := by rw [hquot, hrem]
      _ = (B - 1) + (2 * B) * s := by ring
  have hmodeqT : T ≡ B - 1 [ZMOD 2 * B] := by
    rw [Int.modEq_iff_add_fac]
    refine ⟨-s, ?_⟩
    rw [hT]
    ring
  simpa [T, B] using hmodeqT

/-- Explicit rational-tail membership criterion. This is the main local target
for the rational direction. -/
theorem mem_A_rat_iff_modEq {a : ℤ} {b n : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) (hn : b ≤ n) :
    n ∈ A ((a : ℝ) / (b : ℝ)) ↔
      a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] := by
  constructor
  · intro hA
    have hnpos : 0 < n := lt_of_lt_of_le hb hn
    have hCalt := aboveCount_eq_zero_or_eq_of_mem_A
      (r := ((a : ℝ) / (b : ℝ))) hnpos hA
    have hC : aboveCount ((a : ℝ) / (b : ℝ)) (n + 1) = 0 := by
      rcases hCalt with hzero | htop
      · exact hzero
      · exact False.elim (aboveCount_rat_ne_n (a := a) (b := b) hb hn htop)
    have hfrac := fracMul_rat_eq_top_of_aboveCount_zero
      (a := a) (b := b) (n := n) hb hab hn hC
    have heven := even_floorMul_of_mem_A_and_aboveCount_zero
      (r := ((a : ℝ) / (b : ℝ))) hnpos hA hC
    exact modEq_two_mul_of_fracMul_top_and_even_floor
      (a := a) (b := b) (q := n + 1) hb hfrac heven
  · intro hmod
    have hnpos : 0 < n := lt_of_lt_of_le hb hn
    have hC := aboveCount_rat_eq_zero_of_modEq_two_mul
      (a := a) (b := b) (q := n + 1) hb hmod
    have heven := even_floorMul_rat_of_modEq_two_mul
      (a := a) (b := b) (q := n + 1) hb hmod
    exact mem_A_of_aboveCount_zero_and_even_floor hnpos hC heven

/-- Odd numerator case of the rational tail congruence: `a` is invertible
modulo `2b`, so the congruence is one residue class modulo `2b`. -/
private theorem rat_modEq_single_residue_odd {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) (haodd : Odd a.natAbs) :
    ∃ c d : ℕ, 0 < d ∧ ∀ n : ℕ,
      (a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] ↔
        n % d = c % d) := by
  let m : ℕ := 2 * b
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hcop : IsCoprime a (m : ℤ) := by
    dsimp [m]
    rw [Int.isCoprime_iff_nat_coprime]
    change Nat.Coprime a.natAbs (2 * b)
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by simpa using haodd.coprime_two_right, hab⟩
  let x : ZMod m := (a : ZMod m)⁻¹ * ((b : ℤ) - 1)
  refine ⟨(x - 1).val, m, hmpos, ?_⟩
  intro n
  constructor
  · intro h
    have hZ :
        ((a * (n + 1 : ℕ) : ℤ) : ZMod m) =
          (((b : ℤ) - 1 : ℤ) : ZMod m) := by
      rw [ZMod.intCast_eq_intCast_iff]
      simpa [m] using h
    have hnp1 : ((n + 1 : ℕ) : ZMod m) = x := by
      calc
        ((n + 1 : ℕ) : ZMod m) =
            ((a : ZMod m)⁻¹ * (a : ZMod m)) * ((n + 1 : ℕ) : ZMod m) := by
          rw [ZMod.coe_int_inv_mul_eq_one hcop]
          simp
        _ = (a : ZMod m)⁻¹ * ((a * (n + 1 : ℕ) : ℤ) : ZMod m) := by
          norm_num [mul_assoc]
        _ = x := by
          rw [hZ]
          simp [x]
    have hnZ : (n : ZMod m) = x - 1 := by
      have := congrArg (fun y : ZMod m => y - 1) hnp1
      simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    have hnZval : (n : ZMod m) = ((x - 1).val : ZMod m) := by
      rw [hnZ]
      exact (ZMod.natCast_zmod_val (x - 1)).symm
    exact (ZMod.natCast_eq_natCast_iff' n (x - 1).val m).mp hnZval
  · intro hnmod
    have hnZval : (n : ZMod m) = ((x - 1).val : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff' n (x - 1).val m).mpr hnmod
    have hnZ : (n : ZMod m) = x - 1 := by
      simpa using hnZval.trans (ZMod.natCast_zmod_val (x - 1))
    have hnp1 : ((n + 1 : ℕ) : ZMod m) = x := by
      calc
        ((n + 1 : ℕ) : ZMod m) = (n : ZMod m) + 1 := by
          norm_num
        _ = x := by
          rw [hnZ]
          simp [sub_eq_add_neg, add_assoc]
    have hZ :
        ((a * (n + 1 : ℕ) : ℤ) : ZMod m) =
          (((b : ℤ) - 1 : ℤ) : ZMod m) := by
      calc
        ((a * (n + 1 : ℕ) : ℤ) : ZMod m) =
            (a : ZMod m) * ((n + 1 : ℕ) : ZMod m) := by
          norm_num
        _ = (a : ZMod m) * x := by
          rw [hnp1]
        _ = (((b : ℤ) - 1 : ℤ) : ZMod m) := by
          dsimp [x]
          rw [← mul_assoc, ZMod.coe_int_mul_inv_eq_one hcop]
          simp
    rw [ZMod.intCast_eq_intCast_iff] at hZ
    simpa [m] using hZ

/-- Even numerator case of the rational tail congruence: coprimality forces
`b` odd, so the congruence can be divided by `2` and solved modulo `b`. -/
private theorem rat_modEq_single_residue_even {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) (haeven : Even a) :
    ∃ c d : ℕ, 0 < d ∧ ∀ n : ℕ,
      (a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] ↔
        n % d = c % d) := by
  let a₂ : ℤ := a / 2
  let y : ℤ := ((b : ℤ) - 1) / 2
  let m : ℕ := b
  have hmpos : 0 < m := by
    simpa [m] using hb
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hbodd : Odd b := by
    have h2a : 2 ∣ a.natAbs := by
      rw [← Int.ofNat_dvd_left]
      simpa [even_iff_two_dvd] using haeven
    have hcop2b : Nat.Coprime 2 b := Nat.Coprime.of_dvd_left h2a hab
    simpa using hcop2b
  have hcop : IsCoprime a₂ (m : ℤ) := by
    dsimp [a₂, m]
    rw [Int.isCoprime_iff_nat_coprime]
    change Nat.Coprime (a / 2).natAbs b
    exact Nat.Coprime.of_dvd_left (by
      rw [Int.natAbs_dvd_natAbs]
      refine ⟨2, ?_⟩
      simpa [mul_comm] using (Int.ediv_two_mul_two_of_even haeven).symm) hab
  have ha_eq : a = 2 * a₂ := by
    dsimp [a₂]
    simpa using (Int.two_mul_ediv_two_of_even haeven).symm
  have hy_eq : (b : ℤ) - 1 = 2 * y := by
    dsimp [y]
    exact (Int.two_mul_ediv_two_of_even (by
      rw [Int.even_sub_one]
      rw [Int.even_coe_nat]
      exact Nat.not_even_iff_odd.mpr hbodd)).symm
  let x : ZMod m := (a₂ : ZMod m)⁻¹ * y
  refine ⟨(x - 1).val, m, hmpos, ?_⟩
  intro n
  have hhalf_iff :
      (a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] ↔
        a₂ * (n + 1 : ℕ) ≡ y [ZMOD (m : ℤ)]) := by
    calc
      a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))]
          ↔ 2 * (a₂ * (n + 1 : ℕ)) ≡ 2 * y [ZMOD 2 * (m : ℤ)] := by
        subst m
        rw [ha_eq, hy_eq]
        ring_nf
      _ ↔ a₂ * (n + 1 : ℕ) ≡ y [ZMOD (m : ℤ)] :=
        Int.ModEq.mul_left_cancel_iff' (by norm_num : (2 : ℤ) ≠ 0)
  rw [hhalf_iff]
  constructor
  · intro h
    have hZ : ((a₂ * (n + 1 : ℕ) : ℤ) : ZMod m) = (y : ZMod m) := by
      rw [ZMod.intCast_eq_intCast_iff]
      simp at h ⊢
      exact h
    have hnp1 : ((n + 1 : ℕ) : ZMod m) = x := by
      calc
        ((n + 1 : ℕ) : ZMod m) =
            ((a₂ : ZMod m)⁻¹ * (a₂ : ZMod m)) * ((n + 1 : ℕ) : ZMod m) := by
          simp [ZMod.coe_int_inv_mul_eq_one hcop]
        _ = (a₂ : ZMod m)⁻¹ * ((a₂ * (n + 1 : ℕ) : ℤ) : ZMod m) := by
          norm_num [mul_assoc]
        _ = x := by
          rw [hZ]
    have hnZ : (n : ZMod m) = x - 1 := by
      have := congrArg (fun z : ZMod m => z - 1) hnp1
      simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    have hnZval : (n : ZMod m) = ((x - 1).val : ZMod m) := by
      rw [hnZ]
      exact (ZMod.natCast_zmod_val (x - 1)).symm
    exact (ZMod.natCast_eq_natCast_iff' n (x - 1).val m).mp hnZval
  · intro hnmod
    have hnZval : (n : ZMod m) = ((x - 1).val : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff' n (x - 1).val m).mpr hnmod
    have hnZ : (n : ZMod m) = x - 1 := by
      simpa using hnZval.trans (ZMod.natCast_zmod_val (x - 1))
    have hnp1 : ((n + 1 : ℕ) : ZMod m) = x := by
      calc
        ((n + 1 : ℕ) : ZMod m) = (n : ZMod m) + 1 := by
          norm_num
        _ = x := by
          rw [hnZ]
          simp [sub_eq_add_neg, add_assoc]
    have hZ : ((a₂ * (n + 1 : ℕ) : ℤ) : ZMod m) = (y : ZMod m) := by
      calc
        ((a₂ * (n + 1 : ℕ) : ℤ) : ZMod m) =
            (a₂ : ZMod m) * ((n + 1 : ℕ) : ZMod m) := by
          norm_num
        _ = (a₂ : ZMod m) * x := by
          rw [hnp1]
        _ = (y : ZMod m) := by
          dsimp [x]
          rw [← mul_assoc, ZMod.coe_int_mul_inv_eq_one hcop]
          simp
    rw [ZMod.intCast_eq_intCast_iff] at hZ
    simpa using hZ

/-- A reduced linear congruence from the rational tail is one natural-number
residue class. Keeping this separate isolates the modular-arithmetic work from
the floor-sum work. -/
theorem rat_modEq_is_single_residue_class {a : ℤ} {b : ℕ}
    (hb : 0 < b) (hab : Nat.Coprime a.natAbs b) :
    ∃ c d : ℕ, 0 < d ∧ ∀ n : ℕ,
      (a * (n + 1 : ℕ) ≡ (b : ℤ) - 1 [ZMOD (2 * (b : ℤ))] ↔
        n % d = c % d) := by
  by_cases haeven : Even a
  · exact rat_modEq_single_residue_even hb hab haeven
  · exact rat_modEq_single_residue_odd hb hab (by
      exact Nat.not_even_iff_odd.mp ((not_congr (by
        rw [even_iff_two_dvd, even_iff_two_dvd]
        exact Int.ofNat_dvd_left.symm)).mpr haeven))

/-- Main rational-case theorem: for rational `r`, `A_r` is eventually a single
arithmetic progression. -/
theorem rational_eventuallyAP {r : ℝ} (hr : IsRational r) :
    IsEventuallyAP (A r) := by
  rcases hr with ⟨q, hq⟩
  subst r
  rcases rat_modEq_is_single_residue_class
      (a := q.num) (b := q.den) q.den_pos q.reduced with
    ⟨c, d, hd, hresidue⟩
  refine ⟨c, d, q.den, hd, ?_⟩
  intro n hn
  have htail := mem_A_rat_iff_modEq
    (a := q.num) (b := q.den) (n := n) q.den_pos q.reduced hn
  have hcast : A (q : ℝ) = A ((q.num : ℝ) / (q.den : ℝ)) := by
    ext m
    simp [Rat.cast_def]
  rw [hcast]
  exact htail.trans (hresidue n)

end IrrationalityAr
