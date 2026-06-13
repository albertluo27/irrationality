import IrrationalityAr.Pairing
import IrrationalityAr.Progressions

namespace IrrationalityAr

/-!
# Irrational case

The first theorem is the elementary bridge. It follows from the shared pairing
identity and the fact that the fractional parts of positive multiples of an
irrational real are distinct.
-/

/-- Distinct positive-index multiples of an irrational real have distinct
fractional parts. -/
private theorem fracMul_ne_of_irrational {r : ℝ} (hr : IsIrrational r)
    {k q : ℕ} (hkq : k < q) :
    fracMul r q ≠ fracMul r k := by
  intro h
  unfold fracMul at h
  rcases (Int.fract_eq_fract.mp h) with ⟨z, hz⟩
  let d : ℕ := q - k
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hmul : (d : ℝ) * r = (z : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hkq.le]
    calc
      ((q : ℝ) - (k : ℝ)) * r = (q : ℝ) * r - (k : ℝ) * r := by ring
      _ = (z : ℝ) := hz
  apply hr
  refine ⟨(z : ℚ) / (d : ℚ), ?_⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hdpos
  have hcast :
      (((z : ℚ) / (d : ℚ) : ℚ) : ℝ) = (z : ℝ) / (d : ℝ) := by
    norm_num
  rw [hcast]
  have : r = (z : ℝ) / (d : ℝ) := by
    rw [eq_div_iff hdR]
    rw [← hmul]
    ring
  exact this.symm

/-- Project-local irrationality agrees with mathlib's `Irrational` predicate. -/
private theorem irrational_of_isIrrational {r : ℝ} (hr : IsIrrational r) :
    Irrational r := by
  rintro ⟨q, hq⟩
  exact hr ⟨q, hq⟩

/-- For irrational `r`, the lower endpoint `aboveCount = 0` says the new point
is a strict upper record. -/
private theorem aboveCount_zero_iff_upperRecord {r : ℝ} (hr : IsIrrational r)
    {n : ℕ} :
    aboveCount r (n + 1) = 0 ↔ IsUpperRecord r (n + 1) := by
  constructor
  · intro hC
    refine ⟨by omega, ?_⟩
    intro k hkpos hklt
    have hnone :
        ∀ k ∈ Finset.Ico 1 (n + 1),
          ¬ fracMul r (n + 1) < fracMul r k := by
      simpa [aboveCount] using
        (Finset.card_filter_eq_zero_iff.mp hC)
    have hkmem : k ∈ Finset.Ico 1 (n + 1) := by
      simp [Finset.mem_Ico]
      omega
    have hle : fracMul r k ≤ fracMul r (n + 1) :=
      le_of_not_gt (hnone k hkmem)
    have hne : fracMul r k ≠ fracMul r (n + 1) :=
      (fracMul_ne_of_irrational hr hklt).symm
    exact lt_of_le_of_ne hle hne
  · rintro ⟨_, hupper⟩
    rw [aboveCount]
    apply Finset.card_filter_eq_zero_iff.mpr
    intro k hk
    rcases Finset.mem_Ico.mp hk with ⟨hkpos, hklt⟩
    exact not_lt_of_gt (hupper k hkpos hklt)

/-- The upper endpoint of the count is exactly the strict lower-record
condition. -/
private theorem aboveCount_eq_n_iff_lowerRecord {r : ℝ} {n : ℕ} :
    aboveCount r (n + 1) = n ↔ IsLowerRecord r (n + 1) := by
  constructor
  · intro hC
    refine ⟨by omega, ?_⟩
    have hfilter_card :
        (((Finset.Ico 1 (n + 1)).filter fun k =>
            fracMul r (n + 1) < fracMul r k).card =
          (Finset.Ico 1 (n + 1)).card) := by
      rw [show (Finset.Ico 1 (n + 1)).card = n by simp]
      simpa [aboveCount] using hC
    have hall := Finset.card_filter_eq_iff.mp hfilter_card
    intro k hkpos hklt
    exact hall k (by
      simp [Finset.mem_Ico]
      omega)
  · rintro ⟨_, hlower⟩
    have hall :
        ∀ k ∈ Finset.Ico 1 (n + 1),
          fracMul r (n + 1) < fracMul r k := by
      intro k hk
      rcases Finset.mem_Ico.mp hk with ⟨hkpos, hklt⟩
      exact hlower k hkpos hklt
    have hcard := Finset.card_filter_eq_iff.mpr hall
    simpa [aboveCount] using hcard

/-- Pairing identity: lower record plus odd paired floor implies membership. -/
private theorem mem_A_of_aboveCount_eq_n_and_odd_floor {r : ℝ} {n : ℕ}
    (hn : 0 < n) (hC : aboveCount r (n + 1) = n)
    (hodd : Odd (floorMul r (n + 1))) :
    n ∈ A r := by
  rcases hodd with ⟨z, hz⟩
  have hpair :
      2 * floorSum r n =
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    simpa using two_mul_floorSum_pred_eq r (n + 1)
  have hpairn :
      2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) - (n : ℤ) := by
    simpa [hC] using hpair
  refine (mem_A_iff).mpr ⟨hn, ?_⟩
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  calc
    2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) - (n : ℤ) := hpairn
    _ = (n : ℤ) * (2 * z + 1) - (n : ℤ) := by rw [hz]
    _ = 2 * ((n : ℤ) * z) := by ring

/-- If membership chooses the lower endpoint, the paired floor is odd. -/
private theorem odd_floorMul_of_mem_A_and_aboveCount_eq_n {r : ℝ} {n : ℕ}
    (hn : 0 < n) (hA : n ∈ A r)
    (hC : aboveCount r (n + 1) = n) :
    Odd (floorMul r (n + 1)) := by
  rcases (mem_A_iff.mp hA).2 with ⟨z, hz⟩
  have hpair :
      2 * floorSum r n =
        (n : ℤ) * floorMul r (n + 1) - (aboveCount r (n + 1) : ℤ) := by
    simpa using two_mul_floorSum_pred_eq r (n + 1)
  have hpairn :
      2 * floorSum r n = (n : ℤ) * floorMul r (n + 1) - (n : ℤ) := by
    simpa [hC] using hpair
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hfloor : floorMul r (n + 1) = 2 * z + 1 := by
    apply mul_left_cancel₀ hnz
    calc
      (n : ℤ) * floorMul r (n + 1) =
          (n : ℤ) * floorMul r (n + 1) - (n : ℤ) + (n : ℤ) := by ring
      _ = 2 * floorSum r n + (n : ℤ) := by rw [← hpairn]
      _ = 2 * ((n : ℤ) * z) + (n : ℤ) := by rw [hz]
      _ = (n : ℤ) * (2 * z + 1) := by ring
  exact ⟨z, hfloor⟩

/-- For irrational `r`, membership of `n` in `A_r` is equivalent to `n + 1`
being a record fractional-part extremum with the required parity. -/
theorem mem_A_iff_record_extreme {r : ℝ} (hr : IsIrrational r)
    {n : ℕ} (hn : 0 < n) :
    n ∈ A r ↔
      (IsLowerRecord r (n + 1) ∧ Odd (floorMul r (n + 1))) ∨
      (IsUpperRecord r (n + 1) ∧ Even (floorMul r (n + 1))) := by
  constructor
  · intro hA
    have hCalt := aboveCount_eq_zero_or_eq_of_mem_A hn hA
    rcases hCalt with hzero | htop
    · right
      exact ⟨(aboveCount_zero_iff_upperRecord hr).mp hzero,
        even_floorMul_of_mem_A_and_aboveCount_zero hn hA hzero⟩
    · left
      exact ⟨aboveCount_eq_n_iff_lowerRecord.mp htop,
        odd_floorMul_of_mem_A_and_aboveCount_eq_n hn hA htop⟩
  · rintro (⟨hlower, hodd⟩ | ⟨hupper, heven⟩)
    · exact mem_A_of_aboveCount_eq_n_and_odd_floor hn
        (aboveCount_eq_n_iff_lowerRecord.mpr hlower) hodd
    · exact mem_A_of_aboveCount_zero_and_even_floor hn
        ((aboveCount_zero_iff_upperRecord hr).mpr hupper) heven

/-!
To rule out an infinite arithmetic progression, suppose `a + k d ∈ A_r` for
all `k`. Then the fractional parts at indices `a + k d + 1` are all new record
minima or maxima. Starting from the first two distinct values, all later values
must avoid the nonempty open interval between them.

On the other hand, the orbit is a translate of the rotation by `d r`. Since
`d r` is irrational, its orbit is dense modulo one. This gives a contradiction.

Mathlib contains the circle-level density theorem
`AddCircle.denseRange_zsmul_coe_iff`. The project-local bridge below translates
it to the required natural-index arithmetic progression.
-/

/-- Project-local density bridge for a translated natural orbit modulo one.

The target is the additive circle, not `ℝ`: fractional parts live in `[0, 1)`,
so they cannot be dense in all of `ℝ`. -/
theorem denseRange_translated_nat_toAddCircle {r : ℝ} (hr : IsIrrational r)
    {d : ℕ} (hd : 0 < d) (q₀ : ℕ) :
    DenseRange (fun k : ℕ =>
      (((((q₀ + k * d : ℕ) : ℝ) * r : ℝ) : AddCircle (1 : ℝ)))) := by
  let a : ℝ := (d : ℝ) * r
  let t : AddCircle (1 : ℝ) := (((q₀ : ℝ) * r : ℝ) : AddCircle (1 : ℝ))
  have hirr : Irrational r := irrational_of_isIrrational hr
  have hairr : Irrational (a / (1 : ℝ)) := by
    dsimp [a]
    simpa using (Irrational.natCast_mul hirr (Nat.ne_of_gt hd))
  have hdenseZ : DenseRange (fun k : ℤ =>
      k • ((a : ℝ) : AddCircle (1 : ℝ))) := by
    exact (AddCircle.denseRange_zsmul_coe_iff
      (a := a) (p := (1 : ℝ))).mpr hairr
  have hdenseN : DenseRange (fun k : ℕ =>
      k • ((a : ℝ) : AddCircle (1 : ℝ))) := by
    exact denseRange_zsmul_iff_nsmul.mp hdenseZ
  have htrans : DenseRange
      ((Homeomorph.addLeft t) ∘ fun k : ℕ =>
        k • ((a : ℝ) : AddCircle (1 : ℝ))) := by
    exact DenseRange.comp
      (Function.Surjective.denseRange (Homeomorph.addLeft t).surjective)
      hdenseN (Homeomorph.addLeft t).continuous
  simpa [Function.comp, a, t, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    AddCircle.coe_add, mul_add, add_mul, mul_assoc] using htrans

/-- Fractional parts are represented in the standard half-open interval. -/
private theorem fracMul_mem_Ico (r : ℝ) (q : ℕ) :
    fracMul r q ∈ Set.Ico (0 : ℝ) 1 := by
  unfold fracMul
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The additive-circle point represented by `q * r` is represented by its
fractional part. -/
private theorem coe_fracMul_eq (r : ℝ) (q : ℕ) :
    ((fracMul r q : ℝ) : AddCircle (1 : ℝ)) =
      (((q : ℝ) * r : ℝ) : AddCircle (1 : ℝ)) := by
  unfold fracMul
  exact AddCircle.coe_fract _

/-- If a translated natural orbit is dense on `AddCircle 1`, then it hits every
nonempty real interval inside the standard fractional-part fundamental domain. -/
private theorem exists_fracMul_mem_Ioo_of_dense_toAddCircle
    {r : ℝ} {q₀ d : ℕ} {u v : ℝ}
    (hdense : DenseRange (fun k : ℕ =>
      (((((q₀ + k * d : ℕ) : ℝ) * r : ℝ) : AddCircle (1 : ℝ)))))
    (hu : 0 ≤ u) (huv : u < v) (hv : v < 1) :
    ∃ k : ℕ, fracMul r (q₀ + k * d) ∈ Set.Ioo u v := by
  let U : Set (AddCircle (1 : ℝ)) :=
    ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo u v
  have hUopen : IsOpen U := by
    dsimp [U]
    exact QuotientAddGroup.isOpenMap_coe (Set.Ioo u v) isOpen_Ioo
  have hUne : U.Nonempty := by
    rcases (Set.nonempty_Ioo.mpr huv) with ⟨y, hy⟩
    exact ⟨(y : AddCircle (1 : ℝ)), ⟨y, hy, rfl⟩⟩
  rcases hdense.exists_mem_open hUopen hUne with ⟨k, hkU⟩
  rcases hkU with ⟨y, hyIoo, hycircle⟩
  refine ⟨k, ?_⟩
  let q : ℕ := q₀ + k * d
  have hyIco : y ∈ Set.Ico (0 : ℝ) 1 := by
    exact ⟨le_trans hu hyIoo.1.le, lt_trans hyIoo.2 hv⟩
  have hfIco : fracMul r q ∈ Set.Ico (0 : ℝ) 1 :=
    fracMul_mem_Ico r q
  have hycircle' :
      (y : AddCircle (1 : ℝ)) = (fracMul r q : AddCircle (1 : ℝ)) := by
    dsimp [q] at hycircle ⊢
    exact hycircle.trans (coe_fracMul_eq r (q₀ + k * d)).symm
  have hy_eq_frac : y = fracMul r q := by
    have hyIco' : y ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using hyIco
    have hfIco' : fracMul r q ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      simpa using hfIco
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := (0 : ℝ)) hyIco' hfIco').mp hycircle'
  simpa [q, hy_eq_frac] using hyIoo

/-- In an arithmetic progression contained in `A_r`, the first term is
positive. This is the write-up's harmless `a ≥ 1` reduction. -/
private theorem ap_start_pos {r : ℝ} {a d : ℕ}
    (hAP : ∀ k : ℕ, a + k * d ∈ A r) :
    0 < a := by
  have hA0 : a ∈ A r := by
    simpa using hAP 0
  exact (mem_A_iff.mp hA0).1

/-- The write-up's shifted AP indices `q_k = a + k d + 1` are all lower or
upper records. -/
private theorem records_of_ap_mem_A {r : ℝ} (hr : IsIrrational r)
    {a d : ℕ} (ha : 0 < a)
    (hAP : ∀ k : ℕ, a + k * d ∈ A r) :
    ∀ k : ℕ,
      IsLowerRecord r (a + k * d + 1) ∨
      IsUpperRecord r (a + k * d + 1) := by
  intro k
  have hnpos : 0 < a + k * d := by omega
  have hiff :=
    (mem_A_iff_record_extreme (r := r) hr (n := a + k * d) hnpos).mp
      (hAP k)
  rcases hiff with hlow | hup
  · exact Or.inl (by simpa [Nat.add_assoc] using hlow.1)
  · exact Or.inr (by simpa [Nat.add_assoc] using hup.1)

/-- The first two fractional parts in the shifted AP are distinct. -/
private theorem ap_first_two_fracMul_ne {r : ℝ} (hr : IsIrrational r)
    {a d : ℕ} (hd : 0 < d) :
    fracMul r (a + 1) ≠ fracMul r (a + d + 1) := by
  have hlt : a + 1 < a + d + 1 := by omega
  exact (fracMul_ne_of_irrational hr hlt).symm

/-- The open interval between the first two shifted fractional parts is a
nonempty interval inside the standard fractional-part domain `[0,1)`. -/
private theorem ap_first_interval_bounds {r : ℝ} (hr : IsIrrational r)
    {a d : ℕ} (hd : 0 < d) :
    0 ≤ min (fracMul r (a + 1)) (fracMul r (a + d + 1)) ∧
      min (fracMul r (a + 1)) (fracMul r (a + d + 1)) <
        max (fracMul r (a + 1)) (fracMul r (a + d + 1)) ∧
      max (fracMul r (a + 1)) (fracMul r (a + d + 1)) < 1 := by
  have hne := ap_first_two_fracMul_ne (r := r) hr (a := a) hd
  have hnonneg0 : 0 ≤ fracMul r (a + 1) := (fracMul_mem_Ico r (a + 1)).1
  have hnonneg1 : 0 ≤ fracMul r (a + d + 1) :=
    (fracMul_mem_Ico r (a + d + 1)).1
  have hlt_one0 : fracMul r (a + 1) < 1 := (fracMul_mem_Ico r (a + 1)).2
  have hlt_one1 : fracMul r (a + d + 1) < 1 :=
    (fracMul_mem_Ico r (a + d + 1)).2
  refine ⟨le_min hnonneg0 hnonneg1, ?_, max_lt hlt_one0 hlt_one1⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
  · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt

/-- Every later shifted AP record avoids the open interval between the first
two shifted fractional parts. -/
private theorem later_records_avoid_first_interval {r : ℝ} {a d : ℕ}
    (hd : 0 < d)
    (hrecords : ∀ k : ℕ,
      IsLowerRecord r (a + k * d + 1) ∨
      IsUpperRecord r (a + k * d + 1)) :
    ∀ k : ℕ, 2 ≤ k →
      fracMul r (a + k * d + 1) ∉
        Set.Ioo
          (min (fracMul r (a + 1)) (fracMul r (a + d + 1)))
          (max (fracMul r (a + 1)) (fracMul r (a + d + 1))) := by
  intro k hk2 hIoo
  have hq0_lt : a + 1 < a + k * d + 1 := by
    have hkpos : 0 < k := by omega
    have hkdpos : 0 < k * d := Nat.mul_pos hkpos hd
    omega
  have hq1_lt : a + d + 1 < a + k * d + 1 := by
    have hk1 : 1 < k := by omega
    have hmul : 1 * d < k * d := Nat.mul_lt_mul_of_pos_right hk1 hd
    omega
  rcases hrecords k with hlower | hupper
  · have hlt0 : fracMul r (a + k * d + 1) < fracMul r (a + 1) :=
      hlower.2 (a + 1) (by omega) hq0_lt
    have hlt1 : fracMul r (a + k * d + 1) < fracMul r (a + d + 1) :=
      hlower.2 (a + d + 1) (by omega) hq1_lt
    have hlt_min :
        fracMul r (a + k * d + 1) <
          min (fracMul r (a + 1)) (fracMul r (a + d + 1)) :=
      lt_min hlt0 hlt1
    exact not_lt_of_ge hlt_min.le hIoo.1
  · have hgt0 : fracMul r (a + 1) < fracMul r (a + k * d + 1) :=
      hupper.2 (a + 1) (by omega) hq0_lt
    have hgt1 : fracMul r (a + d + 1) < fracMul r (a + k * d + 1) :=
      hupper.2 (a + d + 1) (by omega) hq1_lt
    have hmax_lt :
        max (fracMul r (a + 1)) (fracMul r (a + d + 1)) <
          fracMul r (a + k * d + 1) :=
      max_lt hgt0 hgt1
    exact not_lt_of_ge hmax_lt.le hIoo.2

/-- Re-index the tail of the shifted AP as the translated orbit beginning at
`q_2`. -/
private theorem ap_later_index_shift (a d m : ℕ) :
    a + (m + 2) * d + 1 = a + 2 * d + 1 + m * d := by
  ring

/-- Main irrational-case theorem: `A_r` contains no infinite arithmetic
progression when `r` is irrational. -/
theorem irrational_no_infiniteAP {r : ℝ} (hr : IsIrrational r) :
    ¬ ContainsInfiniteAP (A r) := by
  rintro ⟨a, d, hd, hAP⟩
  have ha : 0 < a := ap_start_pos hAP
  have hrecords := records_of_ap_mem_A hr ha hAP
  let u : ℝ := min (fracMul r (a + 1)) (fracMul r (a + d + 1))
  let v : ℝ := max (fracMul r (a + 1)) (fracMul r (a + d + 1))
  have hbounds := ap_first_interval_bounds (r := r) hr (a := a) hd
  have hu0 : 0 ≤ u := by simpa [u] using hbounds.1
  have huv : u < v := by simpa [u, v] using hbounds.2.1
  have hv1 : v < 1 := by simpa [v] using hbounds.2.2
  have havoid :
      ∀ k : ℕ, 2 ≤ k → fracMul r (a + k * d + 1) ∉ Set.Ioo u v := by
    simpa [u, v] using later_records_avoid_first_interval (r := r)
      (a := a) (d := d) hd hrecords
  have hdense :=
    denseRange_translated_nat_toAddCircle (r := r) hr (d := d) hd
      (q₀ := a + 2 * d + 1)
  rcases exists_fracMul_mem_Ioo_of_dense_toAddCircle hdense hu0 huv hv1 with
    ⟨m, hmIoo⟩
  have hq_shift : a + (m + 2) * d + 1 = a + 2 * d + 1 + m * d :=
    ap_later_index_shift a d m
  exact havoid (m + 2) (by omega) (by simpa [hq_shift] using hmIoo)

end IrrationalityAr
