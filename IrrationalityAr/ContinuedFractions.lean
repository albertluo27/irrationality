import IrrationalityAr.IrrationalCase

open Filter
open scoped BigOperators
open scoped Topology

namespace IrrationalityAr

/-!
# Continued-fraction layer

Do not use this layer to prove the elementary record-extremum theorem. Instead,
formalize the bridge from one-sided record approximations to convergents and
semiconvergents here. This isolates any continued-fraction API choices from
the main floor-sum argument.

Target mathematical statement:

For irrational `r`, the elements of `A_r` are precisely the numbers `q - 1`
for which the relevant one-sided best approximation with denominator `q` has
odd numerator. Equivalently, after the standard continued-fraction bridge is
proved, these are the parity-filtered convergents and semiconvergents.

The write-up's continued-fraction section decomposes this target into the
following future Lean statements:

* coprime floor-sum formula:
  `sum k = 1..q-1, floor(k * p / q) = (p - 1)(q - 1) / 2` when `(p, q) = 1`;
* gcd floor-sum formula:
  `sum k = 1..q-1, floor(k * p / q) = ((p - 1)(q - 1) + gcd(p,q) - 1) / 2`;
* continuant formula:
  `[a0; ...; an, x] = (x * p_n + p_{n-1}) / (x * q_n + q_{n-1})`;
* semiconvergents lie between the irrational and the adjacent convergent;
* Farey-neighbor denominator lower bound;
* semiconvergent floor agreement:
  `floor(k * alpha) = floor(k * p / q)` for `1 <= k <= q - 1`;
* floor agreement implies no smaller-denominator rational lies between
  `alpha` and `p/q`;
* no-smaller-denominator approximation iff convergent or semiconvergent;
* final classification:
  `A_alpha = {q - 1 | p/q is a reduced convergent or semiconvergent of alpha, p odd}`.

They are documented here but not asserted as Lean theorems yet, so the compiled
AP characterization remains proof-hole-free.
-/

/-- The rational floor sum from Lemmas 3.2 and 3.3 of the write-up. -/
noncomputable def rationalFloorSum (p q : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 (q - 1),
    Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ))

/-- Numerators `p_n` of the simple continued-fraction convergents associated
with a sequence of partial quotients `a`. -/
def continuantNum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => a 0
  | 1 => a 1 * a 0 + 1
  | n + 2 => a (n + 2) * continuantNum a (n + 1) + continuantNum a n

/-- Denominators `q_n` of the simple continued-fraction convergents associated
with a sequence of partial quotients `a`. -/
def continuantDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * continuantDen a (n + 1) + continuantDen a n

/-- The previous numerator, with `p_{-1} = 1`. -/
def continuantNumPrev (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => continuantNum a n

/-- The previous denominator, with `q_{-1} = 0`. -/
def continuantDenPrev (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => continuantDen a n

/-- The finite continued fraction `[a₀; ...; aₙ, x]`, encoded from the
right-hand tail `x`. -/
noncomputable def finiteCFWithTail (a : ℕ → ℕ) : ℕ → ℝ → ℝ
  | 0, x => (a 0 : ℝ) + 1 / x
  | n + 1, x => finiteCFWithTail a n ((a (n + 1) : ℝ) + 1 / x)

/-- The complete quotients of the simple continued fraction of `α`. -/
noncomputable def completeQuotient (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => 1 / Int.fract (completeQuotient α n)

/-- The natural partial quotients attached to the complete quotients. -/
noncomputable def simplePartialQuotient (α : ℝ) (n : ℕ) : ℕ :=
  (Int.floor (completeQuotient α n)).toNat

/-- The exact finite continued fraction `[a₀; ...; aₘ]`.  For `m = 0` this is
the integer `a₀`; for `m + 1` it is encoded as `[a₀; ...; aₘ, aₘ₊₁]`. -/
noncomputable def finiteCFExact (a : ℕ → ℕ) : ℕ → ℝ
  | 0 => (a 0 : ℝ)
  | m + 1 => finiteCFWithTail a m (a (m + 1))

/-- Splitting off the head coefficient of a finite continued fraction with a
variable final tail. -/
theorem finiteCFWithTail_succ_eq_head_add_inv_tail
    (a : ℕ → ℕ) (n : ℕ) (x : ℝ) :
    finiteCFWithTail a (n + 1) x =
      (a 0 : ℝ) + 1 / finiteCFWithTail (fun i : ℕ => a (i + 1)) n x := by
  induction n generalizing x with
  | zero =>
      simp [finiteCFWithTail]
  | succ n ih =>
      rw [finiteCFWithTail, ih]
      rfl

/-- Splitting off the head coefficient of an exact finite continued fraction. -/
theorem finiteCFExact_succ_eq_head_add_inv_tail
    (a : ℕ → ℕ) (n : ℕ) :
    finiteCFExact a (n + 1) =
      (a 0 : ℝ) + 1 / finiteCFExact (fun i : ℕ => a (i + 1)) n := by
  cases n with
  | zero =>
      simp [finiteCFExact, finiteCFWithTail]
  | succ n =>
      dsimp [finiteCFExact]
      exact finiteCFWithTail_succ_eq_head_add_inv_tail a n (a (n + 2))

/-- The real value of the rational `p / q`. -/
noncomputable def ratValue (p q : ℕ) : ℝ :=
  (p : ℝ) / (q : ℝ)

/-- Euclidean division as an identity of rational values. -/
theorem ratValue_eq_nat_div_add_mod {p q : ℕ} (hq : 0 < q) :
    ratValue p q =
      ((p / q : ℕ) : ℝ) + ((p % q : ℕ) : ℝ) / (q : ℝ) := by
  unfold ratValue
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  rw [div_eq_iff hqR]
  have hdiv : (p / q) * q + p % q = p := by
    rw [mul_comm]
    exact Nat.div_add_mod p q
  calc
    (p : ℝ) = ((p / q : ℕ) : ℝ) * (q : ℝ) +
        ((p % q : ℕ) : ℝ) := by
      exact_mod_cast hdiv.symm
    _ = (((p / q : ℕ) : ℝ) + ((p % q : ℕ) : ℝ) / (q : ℝ)) *
        (q : ℝ) := by
      field_simp [hqR]

/-- Euclidean division rewritten in the form used to prepend a continued
fraction head. -/
theorem ratValue_eq_nat_div_add_inv_ratValue_mod {p q : ℕ}
    (hq : 0 < q) (hr : 0 < p % q) :
    ratValue p q =
      ((p / q : ℕ) : ℝ) + 1 / ratValue q (p % q) := by
  rw [ratValue_eq_nat_div_add_mod hq]
  unfold ratValue
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hrR : ((p % q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  field_simp [hqR, hrR]

/-- The Möbius map associated with the common continued-fraction prefix
`[a₀; ...; aₙ, z]`. -/
noncomputable def commonPrefixMap (a : ℕ → ℕ) (n : ℕ) (z : ℝ) : ℝ :=
  (z * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ)) /
    (z * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ))

/-- `y` lies strictly between `x` and `z`. -/
def StrictBetween (x y z : ℝ) : Prop :=
  (x < y ∧ y < z) ∨ (z < y ∧ y < x)

/-- A reduced natural rational `p / q`. -/
def ReducedFraction (p q : ℕ) : Prop :=
  0 < q ∧ Nat.Coprime p q

/-- A reduced fraction with denominator at least `2` has nonzero Euclidean
remainder, so its canonical finite continued fraction has a genuine tail. -/
theorem reducedFraction_mod_pos {p q : ℕ}
    (hred : ReducedFraction p q) (hq : 2 ≤ q) :
    0 < p % q := by
  have hnot_dvd : ¬ q ∣ p := by
    intro hdvd
    have hq_dvd_one : q ∣ 1 := by
      have hdiv : q ∣ 1 * p := by simpa using hdvd
      exact Nat.Coprime.dvd_of_dvd_mul_right hred.2.symm hdiv
    have hqle1 : q ≤ 1 := Nat.le_of_dvd (by norm_num) hq_dvd_one
    omega
  exact Nat.pos_of_ne_zero (by
    intro hmod
    exact hnot_dvd (Nat.dvd_of_mod_eq_zero hmod))

/-- The Euclidean recursive pair remains reduced. -/
theorem reducedFraction_mod_reduced {p q : ℕ}
    (hred : ReducedFraction p q) (hq : 2 ≤ q) :
    ReducedFraction q (p % q) := by
  refine ⟨reducedFraction_mod_pos hred hq, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
  have hgcd := Nat.ModEq.gcd_eq (Nat.mod_modEq p q)
  rw [hgcd]
  exact hred.2.gcd_eq_one

/-- A project-local record for a canonical finite continued fraction for
`p / q`, represented by a coefficient sequence and its last valid index.

For the current project `p q : ℕ`, so the head coefficient is also natural.
If we later classify signed rationals, this can be split into an integer head
and a positive natural tail. -/
structure CanonicalFiniteCF (p q : ℕ) where
  coeff : ℕ → ℕ
  last : ℕ
  last_pos : 0 < last
  value_eq : ratValue p q = finiteCFExact coeff last
  positive_after_head : ∀ i : ℕ, 1 ≤ i → i ≤ last → 0 < coeff i
  last_ge_two : 2 ≤ coeff last

namespace CanonicalFiniteCF

/-- The finite tail `[bⱼ; ...; bₘ]`, encoded by shifting the coefficient
sequence.  The value is meaningful for `j ≤ e.last`; outside that range it is
only a harmless total definition. -/
noncomputable def tailValue {p q : ℕ} (e : CanonicalFiniteCF p q)
    (j : ℕ) : ℝ :=
  finiteCFExact (fun i : ℕ => e.coeff (j + i)) (e.last - j)

/-- The finite expansion agrees with an infinite coefficient sequence through
its last coefficient. -/
def AgreesThrough {p q : ℕ} (e : CanonicalFiniteCF p q)
    (a : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, i ≤ e.last → e.coeff i = a i

/-- `j` is a first differing coefficient after a shared head. -/
def FirstDifference {p q : ℕ} (e : CanonicalFiniteCF p q)
    (a : ℕ → ℕ) (j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ e.last ∧
    (∀ i : ℕ, i < j → e.coeff i = a i) ∧
      e.coeff j ≠ a j

@[simp] theorem tailValue_last {p q : ℕ} (e : CanonicalFiniteCF p q) :
    e.tailValue e.last = (e.coeff e.last : ℝ) := by
  unfold tailValue
  rw [Nat.sub_self]
  simp [finiteCFExact]

@[simp] theorem tailValue_zero {p q : ℕ} (e : CanonicalFiniteCF p q) :
    e.tailValue 0 = ratValue p q := by
  unfold tailValue
  simp [finiteCFExact, e.value_eq]

/-- A nonterminal finite tail splits as `bⱼ + 1 / γⱼ₊₁`. -/
theorem tailValue_step {p q : ℕ} (e : CanonicalFiniteCF p q)
    {j : ℕ} (hj : j < e.last) :
    e.tailValue j =
      (e.coeff j : ℝ) + 1 / e.tailValue (j + 1) := by
  unfold tailValue
  have hsub : e.last - j = (e.last - (j + 1)) + 1 := by omega
  rw [hsub, finiteCFExact_succ_eq_head_add_inv_tail]
  simp [Nat.add_comm, Nat.add_left_comm]

/-- Splitting a canonical finite continued fraction at a non-final index:
`[b₀; ...; b_last] = [b₀; ...; b_n, tail_{n+1}]`. -/
theorem tailValue_zero_eq_finiteCFWithTail {p q : ℕ}
    (e : CanonicalFiniteCF p q) :
    ∀ n : ℕ, n < e.last →
      e.tailValue 0 = finiteCFWithTail e.coeff n (e.tailValue (n + 1))
  | 0, hn => by
      simpa [finiteCFWithTail] using tailValue_step e hn
  | n + 1, hn => by
      have hnlt : n < e.last := by omega
      have hstep : e.tailValue (n + 1) =
          (e.coeff (n + 1) : ℝ) + 1 / e.tailValue (n + 2) :=
        tailValue_step e hn
      calc
        e.tailValue 0 =
            finiteCFWithTail e.coeff n (e.tailValue (n + 1)) :=
          tailValue_zero_eq_finiteCFWithTail e n hnlt
        _ =
            finiteCFWithTail e.coeff n
              ((e.coeff (n + 1) : ℝ) + 1 / e.tailValue (n + 2)) := by
          rw [hstep]
        _ = finiteCFWithTail e.coeff (n + 1) (e.tailValue (n + 2)) := by
          rw [finiteCFWithTail]

end CanonicalFiniteCF

/-- Positivity of an exact finite continued fraction whose coefficients are
positive through the last index. -/
theorem finiteCFExact_pos_of_pos (a : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i : ℕ, i ≤ m → 0 < a i) → 0 < finiteCFExact a m
  | 0, hpos => by
      simp [finiteCFExact]
      exact_mod_cast hpos 0 le_rfl
  | m + 1, hpos => by
      rw [finiteCFExact_succ_eq_head_add_inv_tail]
      have hhead : (0 : ℝ) < a 0 := by exact_mod_cast hpos 0 (by omega)
      have htail : 0 < finiteCFExact (fun i : ℕ => a (i + 1)) m :=
        finiteCFExact_pos_of_pos (fun i : ℕ => a (i + 1)) m
          (by
            intro i hi
            exact hpos (i + 1) (by omega))
      positivity

namespace CanonicalFiniteCF

/-- Positive finite tails after the head of a canonical finite continued
fraction. -/
theorem tailValue_pos {p q : ℕ} (e : CanonicalFiniteCF p q)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ e.last) :
    0 < e.tailValue j := by
  unfold tailValue
  apply finiteCFExact_pos_of_pos
  intro i hi
  exact e.positive_after_head (j + i) (by omega) (by omega)

/-- Every positive-index canonical finite tail is greater than `1`. -/
theorem one_lt_tailValue {p q : ℕ} (e : CanonicalFiniteCF p q)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ e.last) :
    1 < e.tailValue j := by
  by_cases hlast : j = e.last
  · subst j
    rw [tailValue_last]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) e.last_ge_two)
  · have hjlt : j < e.last := lt_of_le_of_ne hj hlast
    rw [tailValue_step e hjlt]
    have hcoeff : (1 : ℝ) ≤ e.coeff j := by
      exact_mod_cast e.positive_after_head j hj1 hj
    have hnext : 0 < e.tailValue (j + 1) :=
      tailValue_pos e (by omega) (by omega)
    have hinv : 0 < 1 / e.tailValue (j + 1) :=
      one_div_pos.mpr hnext
    linarith

/-- A canonical finite continued fraction lies strictly between its head
coefficient and the next integer. -/
theorem head_lt_value_lt_succ {p q : ℕ} (e : CanonicalFiniteCF p q) :
    (e.coeff 0 : ℝ) < ratValue p q ∧
      ratValue p q < (e.coeff 0 : ℝ) + 1 := by
  have hstep := tailValue_step e e.last_pos
  have hlast_one : 1 ≤ e.last := Nat.succ_le_of_lt e.last_pos
  have htail_pos : 0 < e.tailValue 1 :=
    tailValue_pos e (by norm_num) hlast_one
  have htail_gt_one : 1 < e.tailValue 1 :=
    one_lt_tailValue e (by norm_num) hlast_one
  have hinv_pos : 0 < 1 / e.tailValue 1 :=
    one_div_pos.mpr htail_pos
  have hinv_lt_one : 1 / e.tailValue 1 < 1 :=
    (div_lt_one htail_pos).mpr htail_gt_one
  have hvalue : ratValue p q =
      (e.coeff 0 : ℝ) + 1 / e.tailValue 1 := by
    rw [← tailValue_zero e, hstep]
  constructor <;> rw [hvalue] <;> linarith

/-- A nonterminal canonical finite tail lies strictly between its head
coefficient and the next integer. -/
theorem tailValue_between_head_and_succ {p q : ℕ}
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hj1 : 1 ≤ j) (hjlt : j < e.last) :
    (e.coeff j : ℝ) < e.tailValue j ∧
      e.tailValue j < (e.coeff j : ℝ) + 1 := by
  rw [tailValue_step e hjlt]
  have hnext_pos : 0 < e.tailValue (j + 1) :=
    tailValue_pos e (by omega) (by omega)
  have hnext_gt_one : 1 < e.tailValue (j + 1) :=
    one_lt_tailValue e (by omega) (by omega)
  have hinv_pos : 0 < 1 / e.tailValue (j + 1) :=
    one_div_pos.mpr hnext_pos
  have hinv_lt_one : 1 / e.tailValue (j + 1) < 1 := by
    exact (div_lt_one hnext_pos).mpr hnext_gt_one
  constructor <;> linarith

/-- If a canonical finite continued fraction represents a rational greater
than `1`, then its head coefficient is positive.  This is the fact needed when
the Euclidean algorithm recursively expands `q / (p % q)` and then prepends
the original head coefficient. -/
theorem head_pos_of_one_lt_value {p q : ℕ}
    (e : CanonicalFiniteCF p q) (hval : 1 < ratValue p q) :
    0 < e.coeff 0 := by
  by_contra hnot
  have hhead : e.coeff 0 = 0 := Nat.eq_zero_of_not_pos hnot
  have hstep := tailValue_step e e.last_pos
  have hlast_one : 1 ≤ e.last := Nat.succ_le_of_lt e.last_pos
  have htail_pos : 0 < e.tailValue 1 :=
    tailValue_pos e (by norm_num) hlast_one
  have htail_gt_one : 1 < e.tailValue 1 :=
    one_lt_tailValue e (by norm_num) hlast_one
  have hinv_lt_one : 1 / e.tailValue 1 < 1 := by
    exact (div_lt_one htail_pos).mpr htail_gt_one
  have hvalue : ratValue p q = 1 / e.tailValue 1 := by
    rw [← tailValue_zero e, hstep, hhead]
    norm_num
  linarith

/-- The finite comparison with an infinite coefficient sequence either differs
at the head, agrees through the end, or has a first positive differing
coefficient. -/
theorem head_ne_or_agreesThrough_or_firstDifference {p q : ℕ}
    (e : CanonicalFiniteCF p q) (a : ℕ → ℕ) :
    e.coeff 0 ≠ a 0 ∨ e.AgreesThrough a ∨
      ∃ j : ℕ, e.FirstDifference a j := by
  classical
  by_cases hhead : e.coeff 0 = a 0
  · right
    by_cases hagree : e.AgreesThrough a
    · left
      exact hagree
    · right
      have hex : ∃ i : ℕ, i ≤ e.last ∧ e.coeff i ≠ a i := by
        by_contra hnone
        apply hagree
        intro i hi
        by_contra hne
        exact hnone ⟨i, hi, hne⟩
      let j : ℕ := Nat.find hex
      have hj := Nat.find_spec hex
      refine ⟨j, ?_⟩
      refine ⟨?_, hj.1, ?_, hj.2⟩
      · have hjne : j ≠ 0 := by
          intro hz
          have hbad : e.coeff 0 ≠ a 0 := by
            simpa [j, hz] using hj.2
          exact hbad hhead
        omega
      · intro i hi
        by_contra hne
        have hprop : i ≤ e.last ∧ e.coeff i ≠ a i :=
          ⟨le_trans (Nat.le_of_lt hi) hj.1, hne⟩
        exact (Nat.find_min hex hi) hprop
  · left
    exact hhead

end CanonicalFiniteCF

private theorem canonicalFiniteCF_exists_aux :
    ∀ q : ℕ, 2 ≤ q → ∀ p : ℕ, ReducedFraction p q →
      Nonempty (CanonicalFiniteCF p q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro hq p hred
      let r : ℕ := p % q
      have hqpos : 0 < q := by omega
      have hrpos : 0 < r := by
        dsimp [r]
        exact reducedFraction_mod_pos hred hq
      have hrlt : r < q := by
        dsimp [r]
        exact Nat.mod_lt p hqpos
      by_cases hr1 : r = 1
      · let coeff : ℕ → ℕ := fun i => if i = 0 then p / q else q
        refine ⟨{
          coeff := coeff
          last := 1
          last_pos := by norm_num
          value_eq := ?_
          positive_after_head := ?_
          last_ge_two := ?_ }⟩
        · rw [ratValue_eq_nat_div_add_mod hqpos]
          dsimp [coeff, finiteCFExact, finiteCFWithTail, r] at hr1 ⊢
          rw [hr1]
          norm_num
        · intro i _ hi
          have hi_eq : i = 1 := by omega
          subst i
          exact hqpos
        · dsimp [coeff]
          simpa using hq
      · have hrge2 : 2 ≤ r := by omega
        have hred_tail : ReducedFraction q r := by
          dsimp [r]
          exact reducedFraction_mod_reduced hred hq
        rcases ih r hrlt hrge2 q hred_tail with ⟨tail⟩
        let coeff : ℕ → ℕ
          | 0 => p / q
          | k + 1 => tail.coeff k
        refine ⟨{
          coeff := coeff
          last := tail.last + 1
          last_pos := by omega
          value_eq := ?_
          positive_after_head := ?_
          last_ge_two := ?_ }⟩
        · rw [finiteCFExact_succ_eq_head_add_inv_tail]
          have hshift : (fun i : ℕ => coeff (i + 1)) = tail.coeff := by
            funext i
            rfl
          rw [hshift, ← tail.value_eq]
          dsimp [coeff]
          dsimp [r] at hrpos ⊢
          exact ratValue_eq_nat_div_add_inv_ratValue_mod hqpos hrpos
        · intro i hi1 hi
          cases i with
          | zero => omega
          | succ k =>
              dsimp [coeff]
              have hk_le : k ≤ tail.last := by omega
              by_cases hk0 : k = 0
              · subst k
                exact CanonicalFiniteCF.head_pos_of_one_lt_value tail (by
                  unfold ratValue
                  rw [one_lt_div₀ (by exact_mod_cast hrpos)]
                  exact_mod_cast hrlt)
              · have hk1 : 1 ≤ k := by omega
                exact tail.positive_after_head k hk1 hk_le
        · dsimp [coeff]
          exact tail.last_ge_two

/-- Every reduced rational with denominator at least `2` has a canonical
finite continued-fraction expansion. -/
theorem canonicalFiniteCF_exists {p q : ℕ}
    (hred : ReducedFraction p q) (hq : 2 ≤ q) :
    Nonempty (CanonicalFiniteCF p q) :=
  canonicalFiniteCF_exists_aux q hq p hred

/-- No rational with positive denominator `< q` lies strictly between `α` and
`p / q`. This is the best-approximation property used in Lemmas 3.8 and 3.9. -/
def NoSmallDenominatorBetween (α : ℝ) (p q : ℕ) : Prop :=
  ∀ a b : ℕ, 0 < b → b < q →
    ¬ StrictBetween α (ratValue a b) (ratValue p q)

/-- Floor agreement up to denominator `q - 1`. -/
def FloorAgreement (α : ℝ) (p q : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ q - 1 →
    Int.floor ((k : ℝ) * α) =
      Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ))

/-- The tail data for the continued-fraction expansion at every index.  The
number `β` is the infinite tail `[aₙ₊₁; aₙ₊₂, ...]`.  The bounds say this
tail lies in the standard interval `(aₙ₊₁, aₙ₊₁ + 1)`, exactly the fact used
in the first-difference argument. -/
def HasContinuedFractionTails (α : ℝ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∃ β : ℝ,
    (a (n + 1) : ℝ) < β ∧
      β < (a (n + 1) : ℝ) + 1 ∧
      α =
        (β * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ)) /
          (β * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ))

/-- The sequence `a` is a simple continued-fraction expansion for `α`, in the
minimal form currently needed by the project: positive partial quotients,
convergence of convergents, and the tail formula needed for semiconvergents.
Later we can replace or refine this with mathlib's continued-fraction API. -/
def IsSimpleCFExpansion (α : ℝ) (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, 0 < a (n + 1)) ∧
    Tendsto (fun n : ℕ =>
      (continuantNum a n : ℝ) / (continuantDen a n : ℝ)) atTop (𝓝 α) ∧
    HasContinuedFractionTails α a

/-- `p / q` is the `n`-th convergent attached to the partial quotients `a`. -/
def IsConvergentOf (a : ℕ → ℕ) (n p q : ℕ) : Prop :=
  p = continuantNum a n ∧ q = continuantDen a n

/-- `p / q = (p_{n-1} + t p_n) / (q_{n-1} + t q_n)` is a semiconvergent
attached to the partial quotients `a`. -/
def IsSemiconvergentOf (a : ℕ → ℕ) (n t p q : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ a (n + 1) ∧
    p = continuantNumPrev a n + t * continuantNum a n ∧
    q = continuantDenPrev a n + t * continuantDen a n

/-- Project-local predicate for the final classification theorem. -/
def IsConvergentOrSemiconvergent (α : ℝ) (p q : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, IsSimpleCFExpansion α a ∧
    ((∃ n : ℕ, IsConvergentOf a n p q) ∨
      ∃ n t : ℕ, IsSemiconvergentOf a n t p q)

/-- The parity-filtered principal/intermediate convergent denominator set. -/
def oddCFDenoms (α : ℝ) : Set ℕ :=
  {q : ℕ |
    ∃ p : ℕ,
      2 ≤ q ∧ ReducedFraction p q ∧
        IsConvergentOrSemiconvergent α p q ∧ Odd p}

/-- A denominator occurring in the full principal/intermediate denominator path
of the coefficient sequence `a`. -/
def CFDenominatorPath (a : ℕ → ℕ) (Q : ℕ) : Prop :=
  ∃ n t : ℕ,
    1 ≤ t ∧ t ≤ a (n + 1) ∧
      Q = continuantDenPrev a n + t * continuantDen a n

/-- A parity-selected numerator/denominator pair in the full
principal/intermediate path of `a`. -/
def OddCFPathPair (a : ℕ → ℕ) (P Q : ℕ) : Prop :=
  ∃ n t : ℕ,
    1 ≤ t ∧ t ≤ a (n + 1) ∧
      P = continuantNumPrev a n + t * continuantNum a n ∧
      Q = continuantDenPrev a n + t * continuantDen a n ∧
      Odd P

theorem oddCFDenoms_mem_of_oddCFPathPair
    {α : ℝ} {a : ℕ → ℕ} {P Q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hpair : OddCFPathPair a P Q)
    (hQ : 2 ≤ Q)
    (hred : ReducedFraction P Q) :
    Q ∈ oddCFDenoms α := by
  rcases hpair with ⟨n, t, ht1, htle, hP, hQeq, hOdd⟩
  refine ⟨P, hQ, hred, ?_, hOdd⟩
  refine ⟨a, hcf, Or.inr ?_⟩
  refine ⟨n, t, ht1, htle, hP, hQeq⟩

private theorem continuantNum_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantNum a (n + 1) =
      a (n + 1) * continuantNum a n + continuantNumPrev a n := by
  cases n <;> simp [continuantNum, continuantNumPrev]

private theorem continuantDen_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantDen a (n + 1) =
      a (n + 1) * continuantDen a n + continuantDenPrev a n := by
  cases n <;> simp [continuantDen, continuantDenPrev]

private theorem continuantNumPrev_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantNumPrev a (n + 1) = continuantNum a n := by
  simp [continuantNumPrev]

private theorem continuantDenPrev_succ (a : ℕ → ℕ) (n : ℕ) :
    continuantDenPrev a (n + 1) = continuantDen a n := by
  simp [continuantDenPrev]

private theorem continuantDen_pair_pos (a : ℕ → ℕ) (n : ℕ) :
    (0 : ℝ) < (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [continuantDen, continuantDenPrev]
  | one =>
      have hnon : (0 : ℝ) ≤ a 1 := by positivity
      simp [continuantDen, continuantDenPrev]
      linarith
  | more n _ ih1 =>
      have hpos' :
          (0 : ℝ) < (continuantDen a (n + 1) : ℝ) +
            (continuantDen a n : ℝ) := by
        simpa [continuantDenPrev] using ih1
      have hnon :
          (0 : ℝ) ≤
            (a (n + 2) : ℝ) * (continuantDen a (n + 1) : ℝ) := by
        positivity
      rw [continuantDen, continuantDenPrev]
      push_cast
      linarith

private theorem continuant_denominator_pos (a : ℕ → ℕ) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (0 : ℝ) < x * (continuantDen a n : ℝ) +
      (continuantDenPrev a n : ℝ) := by
  by_cases hD : continuantDen a n = 0
  · have hpair := continuantDen_pair_pos a n
    have hprevpos : (0 : ℝ) < continuantDenPrev a n := by
      simpa [hD] using hpair
    simpa [hD] using hprevpos
  · have hDpos : (0 : ℝ) < continuantDen a n := by
      exact_mod_cast Nat.pos_of_ne_zero hD
    have hprod : 0 < x * (continuantDen a n : ℝ) := mul_pos hx hDpos
    have hprevnon : (0 : ℝ) ≤ continuantDenPrev a n := by positivity
    linarith

private theorem continuantDen_pos_of_partials (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    0 < continuantDen a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuantDen]
  | one => simpa [continuantDen] using hpos 0
  | more n ih _ =>
      rw [continuantDen]
      exact Nat.add_pos_right _ ih

/-- Positivity of a continuant denominator only needs positivity of the
coefficients that actually occur in the finite prefix. -/
private theorem continuantDen_pos_of_prefix (a : ℕ → ℕ) :
    ∀ n : ℕ, (∀ i : ℕ, 1 ≤ i → i ≤ n → 0 < a i) →
      0 < continuantDen a n
  | 0, _ => by simp [continuantDen]
  | 1, hpos => by
      simpa [continuantDen] using hpos 1 (by norm_num) le_rfl
  | n + 2, hpos => by
      rw [continuantDen]
      have hprev : 0 < continuantDen a n :=
        continuantDen_pos_of_prefix a n
          (by
            intro i hi1 hi
            exact hpos i hi1 (by omega))
      exact Nat.add_pos_right _ hprev

private theorem continuantDen_ge_two_of_last_ge_two (a : ℕ → ℕ) :
    ∀ n : ℕ,
      1 ≤ n →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → 0 < a i) →
      2 ≤ a n →
        2 ≤ continuantDen a n
  | 0, hn, _, _ => by omega
  | 1, _, _, hlast => by
      simpa [continuantDen] using hlast
  | n + 2, _, hpos, _ => by
      rw [continuantDen]
      have hcoeff : 0 < a (n + 2) :=
        hpos (n + 2) (by omega) le_rfl
      have hden_succ : 0 < continuantDen a (n + 1) :=
        continuantDen_pos_of_prefix a (n + 1)
          (by
            intro i hi1 hi
            exact hpos i hi1 (by omega))
      have hden_prev : 0 < continuantDen a n :=
        continuantDen_pos_of_prefix a n
          (by
            intro i hi1 hi
            exact hpos i hi1 (by omega))
      have hprod : 0 < a (n + 2) * continuantDen a (n + 1) :=
        Nat.mul_pos hcoeff hden_succ
      omega

private theorem continuantNum_pos_of_head_pos (a : ℕ → ℕ)
    (hhead : 0 < a 0) :
    ∀ n : ℕ, 0 < continuantNum a n
  | 0 => by
      simpa [continuantNum] using hhead
  | 1 => by
      simp [continuantNum]
  | n + 2 => by
      rw [continuantNum]
      exact Nat.add_pos_right _ (continuantNum_pos_of_head_pos a hhead n)

private theorem continuant_det (a : ℕ → ℕ) (n : ℕ) :
    (continuantNum a n : ℤ) * (continuantDenPrev a n : ℤ) -
      (continuantNumPrev a n : ℤ) * (continuantDen a n : ℤ) =
        (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero =>
      simp [continuantNum, continuantNumPrev, continuantDen, continuantDenPrev]
  | succ n ih =>
      rw [continuantNum_succ, continuantDen_succ,
        continuantNumPrev_succ, continuantDenPrev_succ]
      push_cast
      calc
        ((a (n + 1) : ℤ) * (continuantNum a n : ℤ) +
              (continuantNumPrev a n : ℤ)) * (continuantDen a n : ℤ) -
            (continuantNum a n : ℤ) *
              ((a (n + 1) : ℤ) * (continuantDen a n : ℤ) +
                (continuantDenPrev a n : ℤ))
            = - ((continuantNum a n : ℤ) * (continuantDenPrev a n : ℤ) -
                (continuantNumPrev a n : ℤ) * (continuantDen a n : ℤ)) := by
              ring
        _ = - ((-1 : ℤ) ^ (n + 1)) := by rw [ih]
        _ = (-1 : ℤ) ^ (n + 1 + 1) := by
              rw [pow_succ]
              ring

/-- The determinant of consecutive continuant numerator/denominator vectors
has absolute value one. -/
theorem continuant_det_abs_one (a : ℕ → ℕ) (n : ℕ) :
    |(continuantNum a n : ℤ) * (continuantDenPrev a n : ℤ) -
      (continuantNumPrev a n : ℤ) * (continuantDen a n : ℤ)| = 1 := by
  rw [continuant_det]
  norm_num

private theorem continuantNum_coprime_prev (a : ℕ → ℕ) :
    ∀ n : ℕ, Nat.Coprime (continuantNum a n) (continuantNumPrev a n)
  | 0 => by
      simp [continuantNumPrev]
  | n + 1 => by
      rw [continuantNum_succ, continuantNumPrev_succ]
      have ih : Nat.Coprime (continuantNum a n) (continuantNumPrev a n) :=
        continuantNum_coprime_prev a n
      simpa [Nat.add_comm, Nat.mul_comm, Nat.coprime_comm] using
        (Nat.coprime_add_mul_right_left
          (continuantNumPrev a n) (continuantNum a n) (a (n + 1))).mpr ih.symm

private theorem floor_add_floor_int_sub_of_not_int (z : ℤ) {x : ℝ}
    (hnot : ∀ m : ℤ, x ≠ (m : ℝ)) :
    Int.floor x + Int.floor ((z : ℝ) - x) = z - 1 := by
  have hfloor_lt : (Int.floor x : ℝ) < x := by
    have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have hne : (Int.floor x : ℝ) ≠ x := by
      intro h
      exact hnot (Int.floor x) h.symm
    exact lt_of_le_of_ne hle hne
  have hsecond : Int.floor ((z : ℝ) - x) = z - Int.floor x - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · have hlt := Int.lt_floor_add_one x
      push_cast
      linarith
    · push_cast
      linarith
  omega

private theorem floor_add_floor_int_sub_of_int (z m : ℤ) {x : ℝ}
    (hm : x = (m : ℝ)) :
    Int.floor x + Int.floor ((z : ℝ) - x) = z := by
  subst x
  norm_num

private theorem rat_int_of_dvd {p q k : ℕ}
    (hq : 0 < q) (hdiv : q ∣ k * p) :
    ∃ m : ℤ, ((k : ℝ) * (p : ℝ)) / (q : ℝ) = (m : ℝ) := by
  refine ⟨(((k * p) / q : ℕ) : ℤ), ?_⟩
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hmul : (k * p) / q * q = k * p := Nat.div_mul_cancel hdiv
  calc
    ((k : ℝ) * (p : ℝ)) / (q : ℝ)
        = (((k * p : ℕ) : ℝ) / (q : ℝ)) := by norm_num
    _ = (((k * p) / q : ℕ) : ℝ) := by
        rw [div_eq_iff hqR]
        exact_mod_cast hmul.symm

private theorem rat_not_int_of_not_dvd {p q k : ℕ}
    (hq : 0 < q) (hnot : ¬ q ∣ k * p) :
    ∀ m : ℤ, ((k : ℝ) * (p : ℝ)) / (q : ℝ) ≠ (m : ℝ) := by
  intro m hm
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have heqR : ((k * p : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by
    rw [div_eq_iff hqR] at hm
    norm_num at hm ⊢
    linarith
  have heqZ : ((k * p : ℕ) : ℤ) = m * (q : ℤ) := by
    exact_mod_cast heqR
  have hdvdZ : (q : ℤ) ∣ ((k * p : ℕ) : ℤ) :=
    ⟨m, by rw [heqZ]; ring⟩
  have hdvdNat : q ∣ k * p := by
    exact_mod_cast hdvdZ
  exact hnot hdvdNat

private theorem mul_irrational_not_int {α : ℝ} (hirr : IsIrrational α)
    {k : ℕ} (hkpos : 0 < k) :
    ∀ m : ℤ, (k : ℝ) * α ≠ (m : ℝ) := by
  intro m hm
  apply hirr
  refine ⟨(m : ℚ) / (k : ℚ), ?_⟩
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hkpos
  have hcast : (((m : ℚ) / (k : ℚ) : ℚ) : ℝ) =
      (m : ℝ) / (k : ℝ) := by norm_num
  rw [hcast]
  rw [div_eq_iff hkR]
  rw [← hm]
  ring

private theorem floor_lt_of_not_int {x : ℝ}
    (hnot : ∀ m : ℤ, x ≠ (m : ℝ)) :
    (Int.floor x : ℝ) < x := by
  have hle : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hne : (Int.floor x : ℝ) ≠ x := by
    intro h
    exact hnot (Int.floor x) h.symm
  exact lt_of_le_of_ne hle hne

private theorem rat_not_int_of_coprime {p q k : ℕ}
    (hq : 0 < q) (hpq : Nat.Coprime p q) (hkpos : 0 < k) (hklt : k < q) :
    ∀ m : ℤ, ((k : ℝ) * (p : ℝ)) / (q : ℝ) ≠ (m : ℝ) := by
  intro m hm
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have heqR : ((k * p : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by
    rw [div_eq_iff hqR] at hm
    norm_num at hm ⊢
    linarith
  have heqZ : ((k * p : ℕ) : ℤ) = m * (q : ℤ) := by
    exact_mod_cast heqR
  have hdvdZ : (q : ℤ) ∣ ((k * p : ℕ) : ℤ) :=
    ⟨m, by rw [heqZ]; ring⟩
  have hdvdNat : q ∣ k * p := by
    exact_mod_cast hdvdZ
  have hq_dvd_k : q ∣ k := by
    exact (Nat.Coprime.dvd_of_dvd_mul_left hpq.symm
      (by simpa [mul_comm] using hdvdNat))
  rcases hq_dvd_k with ⟨t, rfl⟩
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := Nat.eq_zero_of_not_pos h
    subst t
    simp at hkpos
  nlinarith [Nat.mul_le_mul_left q ht0]

private theorem rational_floor_pair {p q k : ℕ}
    (hq : 0 < q) (hpq : Nat.Coprime p q) (hkpos : 0 < k) (hklt : k < q) :
    Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ)) +
      Int.floor ((((q - k : ℕ) : ℝ) * (p : ℝ)) / (q : ℝ)) =
        (p : ℤ) - 1 := by
  have harg : (((q - k : ℕ) : ℝ) * (p : ℝ)) / (q : ℝ) =
      (p : ℝ) - (((k : ℝ) * (p : ℝ)) / (q : ℝ)) := by
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp [hqR]
    rw [Nat.cast_sub hklt.le]
    ring
  rw [harg]
  exact floor_add_floor_int_sub_of_not_int (p : ℤ)
    (rat_not_int_of_coprime hq hpq hkpos hklt)

private theorem rational_floor_pair_gcd {p q k : ℕ}
    (hq : 0 < q) (hklt : k < q) :
    Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ)) +
      Int.floor ((((q - k : ℕ) : ℝ) * (p : ℝ)) / (q : ℝ)) =
        if q ∣ k * p then (p : ℤ) else (p : ℤ) - 1 := by
  have harg : (((q - k : ℕ) : ℝ) * (p : ℝ)) / (q : ℝ) =
      (p : ℝ) - (((k : ℝ) * (p : ℝ)) / (q : ℝ)) := by
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp [hqR]
    rw [Nat.cast_sub hklt.le]
    ring
  by_cases hdiv : q ∣ k * p
  · simp [hdiv]
    rw [harg]
    rcases rat_int_of_dvd hq hdiv with ⟨m, hm⟩
    exact floor_add_floor_int_sub_of_int (p : ℤ) m hm
  · simp [hdiv]
    rw [harg]
    exact floor_add_floor_int_sub_of_not_int (p : ℤ)
      (rat_not_int_of_not_dvd hq hdiv)

private theorem dvd_mul_iff_div_gcd_dvd {p q k : ℕ} (hq : 0 < q) :
    q ∣ k * p ↔ q / Nat.gcd p q ∣ k := by
  constructor
  · intro h
    have hm : k * p ≡ 0 * p [MOD q] := by
      rw [zero_mul]
      exact Nat.modEq_zero_iff_dvd.mpr h
    have hc := Nat.ModEq.cancel_right_div_gcd hq hm
    have hden : q / q.gcd p = q / p.gcd q := by
      rw [Nat.gcd_comm]
    rw [hden] at hc
    exact Nat.modEq_zero_iff_dvd.mp hc
  · intro hk
    let g := Nat.gcd p q
    rcases hk with ⟨t, rfl⟩
    have hgq : g ∣ q := by exact Nat.gcd_dvd_right p q
    have hgp : g ∣ p := by exact Nat.gcd_dvd_left p q
    have hqeq : g * (q / g) = q := by
      rw [mul_comm, Nat.div_mul_cancel hgq]
    have hpeq : g * (p / g) = p := by
      rw [mul_comm, Nat.div_mul_cancel hgp]
    refine ⟨t * (p / g), ?_⟩
    calc
      (q / g * t) * p = (q / g * t) * (g * (p / g)) := by
        rw [hpeq]
      _ = (g * (q / g)) * (t * (p / g)) := by ring
      _ = q * (t * (p / g)) := by rw [hqeq]

private theorem card_dvd_mul_Ico {p q : ℕ} (hq : 0 < q) :
    ((Finset.Ico 1 q).filter fun k => q ∣ k * p).card =
      Nat.gcd p q - 1 := by
  let g := Nat.gcd p q
  let c := q / g
  have hgq : g ∣ q := by exact Nat.gcd_dvd_right p q
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgq hq
  have hgleq : g ≤ q := Nat.le_of_dvd hq hgq
  have hcpos : 0 < c := Nat.div_pos hgleq hgpos
  have hqeq : g * c = q := by
    dsimp [c]
    rw [mul_comm, Nat.div_mul_cancel hgq]
  calc
    ((Finset.Ico 1 q).filter fun k => q ∣ k * p).card
        = (Finset.Ico 1 g).card := by
          symm
          refine Finset.card_bij (fun i _ => i * c) ?_ ?_ ?_
          · intro i hi
            rcases Finset.mem_Ico.mp hi with ⟨hi1, hilt⟩
            rw [Finset.mem_filter, Finset.mem_Ico]
            constructor
            · constructor
              · have hpos : 0 < i * c := Nat.mul_pos (by omega) hcpos
                exact Nat.succ_le_iff.mpr hpos
              · have hlt : i * c < g * c :=
                  (Nat.mul_lt_mul_right hcpos).mpr hilt
                rwa [hqeq] at hlt
            · apply (dvd_mul_iff_div_gcd_dvd hq).mpr
              change c ∣ i * c
              exact ⟨i, by rw [mul_comm]⟩
          · intro i _ j _ hij
            exact Nat.eq_of_mul_eq_mul_right hcpos hij
          · intro k hk
            rw [Finset.mem_filter, Finset.mem_Ico] at hk
            rcases hk with ⟨⟨hk1, hklt⟩, hdiv⟩
            have hc_dvd : c ∣ k := by
              change q / Nat.gcd p q ∣ k
              exact (dvd_mul_iff_div_gcd_dvd hq).mp hdiv
            rcases hc_dvd with ⟨i, hik⟩
            refine ⟨i, ?_, ?_⟩
            · rw [Finset.mem_Ico]
              constructor
              · by_contra hnot
                have hi0 : i = 0 := Nat.eq_zero_of_not_pos (by omega)
                subst i
                simp at hik
                omega
              · have hltmul : i * c < g * c := by
                  calc
                    i * c = k := by rw [hik, mul_comm]
                    _ < q := hklt
                    _ = g * c := hqeq.symm
                exact (Nat.mul_lt_mul_right hcpos).mp hltmul
            · change i * c = k
              rw [hik, mul_comm]
    _ = g - 1 := by rw [Nat.card_Ico]

/-- Lemma 3.2: the coprime rational floor-sum formula. -/
theorem coprime_rationalFloorSum {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q) :
    rationalFloorSum p q =
      (((p : ℤ) - 1) * ((q : ℤ) - 1)) / 2 := by
  have _ : 0 < p := hp
  let f : ℕ → ℤ := fun k =>
    Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ))
  have hIccIco : Finset.Icc 1 (q - 1) = Finset.Ico 1 q := by
    ext k
    simp [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hreflect :
      (∑ k ∈ Finset.Ico 1 q, f (q - k)) =
        ∑ k ∈ Finset.Ico 1 q, f k := by
    simpa using
      (Finset.sum_Ico_reflect f 1 (show q ≤ q + 1 by omega))
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have htwo : 2 * (∑ k ∈ Finset.Ico 1 q, f k) =
      ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) := by
    calc
      2 * (∑ k ∈ Finset.Ico 1 q, f k)
          = (∑ k ∈ Finset.Ico 1 q, f k) +
              ∑ k ∈ Finset.Ico 1 q, f (q - k) := by
            rw [hreflect]
            ring
      _ = ∑ k ∈ Finset.Ico 1 q, (f k + f (q - k)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ k ∈ Finset.Ico 1 q, ((p : ℤ) - 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            rcases Finset.mem_Ico.mp hk with ⟨hkpos, hklt⟩
            exact rational_floor_pair hq hpq hkpos hklt
      _ = ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) := by
            simp
            rw [hqsub]
            ring
  have htarget : (((p : ℤ) - 1) * ((q : ℤ) - 1)) / 2 =
      ∑ k ∈ Finset.Ico 1 q, f k := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num)
    rw [htwo]
    rw [hqsub]
    ring
  rw [rationalFloorSum, hIccIco]
  exact htarget.symm

/-- Lemma 3.3: the rational floor-sum formula with a gcd correction term. -/
theorem gcd_rationalFloorSum {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    rationalFloorSum p q =
      (((p : ℤ) - 1) * ((q : ℤ) - 1) + ((Nat.gcd p q : ℤ) - 1)) / 2 := by
  have _ : 0 < p := hp
  let f : ℕ → ℤ := fun k =>
    Int.floor (((k : ℝ) * (p : ℝ)) / (q : ℝ))
  have hIccIco : Finset.Icc 1 (q - 1) = Finset.Ico 1 q := by
    ext k
    simp [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hreflect :
      (∑ k ∈ Finset.Ico 1 q, f (q - k)) =
        ∑ k ∈ Finset.Ico 1 q, f k := by
    simpa using
      (Finset.sum_Ico_reflect f 1 (show q ≤ q + 1 by omega))
  have hgoodCard :
      (((Finset.Ico 1 q).filter fun k => q ∣ k * p).card : ℤ) =
        (Nat.gcd p q : ℤ) - 1 := by
    rw [card_dvd_mul_Ico (p := p) (q := q) hq]
    have hgpos : 0 < Nat.gcd p q :=
      Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right p q) hq
    omega
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hsumPair :
      (∑ k ∈ Finset.Ico 1 q,
          (if q ∣ k * p then (p : ℤ) else (p : ℤ) - 1)) =
        ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) +
          ((Nat.gcd p q : ℤ) - 1) := by
    calc
      (∑ k ∈ Finset.Ico 1 q,
          (if q ∣ k * p then (p : ℤ) else (p : ℤ) - 1))
          = ∑ k ∈ Finset.Ico 1 q,
              (((p : ℤ) - 1) + if q ∣ k * p then (1 : ℤ) else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases h : q ∣ k * p <;> simp [h]
      _ = (∑ k ∈ Finset.Ico 1 q, ((p : ℤ) - 1)) +
            ∑ k ∈ Finset.Ico 1 q,
              (if q ∣ k * p then (1 : ℤ) else 0) := by
            rw [Finset.sum_add_distrib]
      _ = ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) +
            (((Finset.Ico 1 q).filter fun k => q ∣ k * p).card : ℤ) := by
            rw [Finset.sum_boole]
            simp
            ring
      _ = ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) +
            ((Nat.gcd p q : ℤ) - 1) := by
            rw [hgoodCard]
  have htwo : 2 * (∑ k ∈ Finset.Ico 1 q, f k) =
      ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) +
        ((Nat.gcd p q : ℤ) - 1) := by
    calc
      2 * (∑ k ∈ Finset.Ico 1 q, f k)
          = (∑ k ∈ Finset.Ico 1 q, f k) +
              ∑ k ∈ Finset.Ico 1 q, f (q - k) := by
            rw [hreflect]
            ring
      _ = ∑ k ∈ Finset.Ico 1 q, (f k + f (q - k)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ k ∈ Finset.Ico 1 q,
            (if q ∣ k * p then (p : ℤ) else (p : ℤ) - 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            rcases Finset.mem_Ico.mp hk with ⟨_, hklt⟩
            exact rational_floor_pair_gcd hq hklt
      _ = ((q - 1 : ℕ) : ℤ) * ((p : ℤ) - 1) +
            ((Nat.gcd p q : ℤ) - 1) := hsumPair
  have htarget :
      (((p : ℤ) - 1) * ((q : ℤ) - 1) +
          ((Nat.gcd p q : ℤ) - 1)) / 2 =
        ∑ k ∈ Finset.Ico 1 q, f k := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num)
    rw [htwo]
    rw [hqsub]
    ring
  rw [rationalFloorSum, hIccIco]
  exact htarget.symm

/-- Lemma 3.4: the continuant formula
`[a₀; ...; aₙ, x] = (x pₙ + pₙ₋₁) / (x qₙ + qₙ₋₁)`. -/
theorem continuant_formula (a : ℕ → ℕ) (n : ℕ) {x : ℝ}
    (hx : 0 < x) :
    finiteCFWithTail a n x =
      (x * (continuantNum a n : ℝ) + (continuantNumPrev a n : ℝ)) /
        (x * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) := by
  induction n generalizing x with
  | zero =>
      dsimp [finiteCFWithTail, continuantNum, continuantNumPrev,
        continuantDen, continuantDenPrev]
      field_simp [ne_of_gt hx]
      ring
  | succ n ih =>
      rw [finiteCFWithTail]
      have hy : (0 : ℝ) < (a (n + 1) : ℝ) + 1 / x := by
        exact add_pos_of_nonneg_of_pos (by positivity) (one_div_pos.mpr hx)
      rw [ih hy]
      have hden_rec :
          ((a (n + 1) : ℝ) + 1 / x) * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ) ≠ 0 :=
        ne_of_gt (continuant_denominator_pos a n hy)
      have hxne : x ≠ 0 := ne_of_gt hx
      rw [continuantNum_succ, continuantDen_succ,
        continuantNumPrev_succ, continuantDenPrev_succ]
      push_cast
      field_simp [hxne, hden_rec]
      ring

/-- The common-prefix map is the same as evaluating the finite continued
fraction with a variable final tail. -/
theorem finiteCFWithTail_eq_commonPrefixMap (a : ℕ → ℕ) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    finiteCFWithTail a n x = commonPrefixMap a n x := by
  simpa [commonPrefixMap] using continuant_formula a n hx

/-- Exact finite continued fractions are given by the continuant numerator and
denominator. -/
theorem finiteCFExact_eq_ratValue_continuants (a : ℕ → ℕ) :
    ∀ n : ℕ,
      (∀ i : ℕ, 1 ≤ i → i ≤ n → 0 < a i) →
        finiteCFExact a n =
          ratValue (continuantNum a n) (continuantDen a n)
  | 0, _ => by
      simp [finiteCFExact, ratValue, continuantNum, continuantDen]
  | n + 1, hpos => by
      have htail : 0 < a (n + 1) := hpos (n + 1) (by omega) le_rfl
      dsimp [finiteCFExact]
      rw [finiteCFWithTail_eq_commonPrefixMap a n (by exact_mod_cast htail)]
      unfold commonPrefixMap ratValue
      rw [continuantNum_succ, continuantDen_succ]
      push_cast
      ring

/-- A canonical finite tail is the reduced continuant fraction of the shifted
coefficient sequence. -/
theorem CanonicalFiniteCF.tailValue_eq_ratValue_continuants {p q : ℕ}
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ e.last) :
    e.tailValue j =
      ratValue
        (continuantNum (fun i : ℕ => e.coeff (j + i)) (e.last - j))
        (continuantDen (fun i : ℕ => e.coeff (j + i)) (e.last - j)) := by
  unfold CanonicalFiniteCF.tailValue
  exact finiteCFExact_eq_ratValue_continuants
    (fun i : ℕ => e.coeff (j + i)) (e.last - j)
    (by
      intro i hi1 hi
      exact e.positive_after_head (j + i) (by omega) (by omega))

/-- The denominator of the reduced continuant fraction for a canonical finite
tail is positive. -/
theorem CanonicalFiniteCF.tailContinuantDen_pos {p q : ℕ}
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ e.last) :
    0 <
      continuantDen (fun i : ℕ => e.coeff (j + i)) (e.last - j) := by
  apply continuantDen_pos_of_prefix
  intro i hi1 hi
  exact e.positive_after_head (j + i) (by omega) (by omega)

/-- A nonterminal canonical finite tail has denominator at least `2`. -/
theorem CanonicalFiniteCF.two_le_tailContinuantDen {p q : ℕ}
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hj1 : 1 ≤ j) (hjlt : j < e.last) :
    2 ≤
      continuantDen (fun i : ℕ => e.coeff (j + i)) (e.last - j) := by
  apply continuantDen_ge_two_of_last_ge_two
  · omega
  · intro i hi1 hi
    exact e.positive_after_head (j + i) (by omega) (by omega)
  · have hidx : j + (e.last - j) = e.last := by omega
    simpa [hidx] using e.last_ge_two

/-- Continuant numerators and denominators are coprime. -/
theorem continuant_coprime (a : ℕ → ℕ) (n : ℕ) :
    Nat.Coprime (continuantNum a n) (continuantDen a n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g : ℕ := Nat.gcd (continuantNum a n) (continuantDen a n)
  have hg_num : g ∣ continuantNum a n := Nat.gcd_dvd_left _ _
  have hg_den : g ∣ continuantDen a n := Nat.gcd_dvd_right _ _
  have hg_numZ : (g : ℤ) ∣ (continuantNum a n : ℤ) := by
    exact_mod_cast hg_num
  have hg_denZ : (g : ℤ) ∣ (continuantDen a n : ℤ) := by
    exact_mod_cast hg_den
  have hdet := continuant_det a n
  have hg_pow :
      (g : ℤ) ∣ (-1 : ℤ) ^ (n + 1) := by
    rw [← hdet]
    exact dvd_sub
      (dvd_mul_of_dvd_left hg_numZ _)
      (dvd_mul_of_dvd_right hg_denZ _)
  have hg_oneZ : (g : ℤ) ∣ (1 : ℤ) := by
    rcases neg_one_pow_eq_or ℤ (n + 1) with hpow | hpow
    · simpa [hpow] using hg_pow
    · have : (g : ℤ) ∣ -(1 : ℤ) := by
        simpa [hpow] using hg_pow
      simpa using dvd_neg.mp this
  have hg_one : g ∣ 1 := by
    exact_mod_cast hg_oneZ
  exact Nat.dvd_one.mp hg_one

/-- Convergents form reduced natural fractions once the partial denominators
after the head are positive. -/
theorem reducedFraction_continuant (a : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) (n : ℕ) :
    ReducedFraction (continuantNum a n) (continuantDen a n) :=
  ⟨continuantDen_pos_of_partials a hpos n, continuant_coprime a n⟩

/-- Equality of reduced natural rational values forces equality of numerator
and denominator. -/
theorem reducedFraction_eq_of_ratValue_eq {p q r s : ℕ}
    (hpq : ReducedFraction p q) (hrs : ReducedFraction r s)
    (hval : ratValue p q = ratValue r s) :
    p = r ∧ q = s := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpq.1
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hrs.1
  have hcrossR : (p : ℝ) * (s : ℝ) = (r : ℝ) * (q : ℝ) := by
    unfold ratValue at hval
    exact (div_eq_div_iff hqR hsR).mp hval
  have hcrossN : p * s = r * q := by
    exact_mod_cast hcrossR
  have hq_dvd_ps : q ∣ p * s := by
    rw [hcrossN]
    exact Nat.dvd_mul_left q r
  have hq_dvd_s : q ∣ s :=
    hpq.2.symm.dvd_of_dvd_mul_left hq_dvd_ps
  have hs_dvd_rq : s ∣ r * q := by
    rw [← hcrossN]
    exact Nat.dvd_mul_left s p
  have hs_dvd_q : s ∣ q :=
    hrs.2.symm.dvd_of_dvd_mul_left hs_dvd_rq
  have hqs : q = s := Nat.dvd_antisymm hq_dvd_s hs_dvd_q
  subst s
  have hpr : p = r := Nat.mul_right_cancel hpq.1 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcrossN)
  exact ⟨hpr, rfl⟩

/-- Applying a common prefix to a natural tail gives the corresponding natural
fraction. -/
theorem ratValue_commonPrefix_nat (a : ℕ → ℕ) (n t : ℕ) :
    ratValue
        (t * continuantNum a n + continuantNumPrev a n)
        (t * continuantDen a n + continuantDenPrev a n) =
      commonPrefixMap a n t := by
  unfold ratValue commonPrefixMap
  push_cast
  ring

/-- Applying a common prefix to a positive rational tail gives the expected
natural numerator and denominator. -/
theorem ratValue_commonPrefix_fraction (a : ℕ → ℕ) (n : ℕ) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    ratValue
        (u * continuantNum a n + v * continuantNumPrev a n)
        (u * continuantDen a n + v * continuantDenPrev a n) =
      commonPrefixMap a n (ratValue u v) := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hv
  have hzpos : 0 < ratValue u v := by
    unfold ratValue
    exact div_pos (by exact_mod_cast hu) (by exact_mod_cast hv)
  have hscaled_den_pos :
      0 <
        (v : ℝ) *
          (ratValue u v * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ)) :=
    mul_pos (by exact_mod_cast hv) (continuant_denominator_pos a n hzpos)
  have hden_nat_ne :
      ((u * continuantDen a n +
        v * continuantDenPrev a n : ℕ) : ℝ) ≠ 0 := by
    have hscaled :
        0 <
          (u : ℝ) * (continuantDen a n : ℝ) +
            (v : ℝ) * (continuantDenPrev a n : ℝ) := by
      unfold ratValue at hscaled_den_pos
      field_simp [hvR] at hscaled_den_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled_den_pos
    exact ne_of_gt (by
      simpa using hscaled)
  have hden_exp_ne :
      (u : ℝ) * (continuantDen a n : ℝ) +
        (v : ℝ) * (continuantDenPrev a n : ℝ) ≠ 0 := by
    exact_mod_cast hden_nat_ne
  unfold ratValue commonPrefixMap
  field_simp [hvR, hden_nat_ne, hden_exp_ne]
  push_cast
  ring_nf

/-- Exact finite continued fractions only depend on the coefficients up to
their last index. -/
theorem finiteCFExact_eq_of_eq_on_prefix (a b : ℕ → ℕ) :
    ∀ n : ℕ, (∀ i : ℕ, i ≤ n → a i = b i) →
      finiteCFExact a n = finiteCFExact b n
  | 0, hprefix => by
      simp [finiteCFExact, hprefix 0 le_rfl]
  | n + 1, hprefix => by
      rw [finiteCFExact_succ_eq_head_add_inv_tail,
        finiteCFExact_succ_eq_head_add_inv_tail]
      have hhead : a 0 = b 0 := hprefix 0 (by omega)
      have htail :
          finiteCFExact (fun i : ℕ => a (i + 1)) n =
            finiteCFExact (fun i : ℕ => b (i + 1)) n :=
        finiteCFExact_eq_of_eq_on_prefix
          (fun i : ℕ => a (i + 1)) (fun i : ℕ => b (i + 1)) n
          (by
            intro i hi
            exact hprefix (i + 1) (by omega))
      rw [hhead, htail]

/-- Finite continued fractions with a variable tail only depend on the
coefficients in the displayed prefix. -/
theorem finiteCFWithTail_eq_of_eq_on_prefix (a b : ℕ → ℕ) :
    ∀ n : ℕ, ∀ x : ℝ, (∀ i : ℕ, i ≤ n → a i = b i) →
      finiteCFWithTail a n x = finiteCFWithTail b n x
  | 0, x, hprefix => by
      simp [finiteCFWithTail, hprefix 0 le_rfl]
  | n + 1, x, hprefix => by
      rw [finiteCFWithTail, finiteCFWithTail]
      have hhead : a (n + 1) = b (n + 1) := hprefix (n + 1) le_rfl
      have htail :
          finiteCFWithTail a n ((a (n + 1) : ℝ) + 1 / x) =
            finiteCFWithTail b n ((a (n + 1) : ℝ) + 1 / x) :=
        finiteCFWithTail_eq_of_eq_on_prefix a b n
          ((a (n + 1) : ℝ) + 1 / x)
          (by
            intro i hi
            exact hprefix i (by omega))
      rw [htail, hhead]

/-- Exact finite continued fractions are values of the common-prefix map at
their final coefficient. -/
theorem finiteCFExact_succ_eq_commonPrefixMap (a : ℕ → ℕ) (n : ℕ)
    (hpos : 0 < a (n + 1)) :
    finiteCFExact a (n + 1) =
      commonPrefixMap a n (a (n + 1)) := by
  dsimp [finiteCFExact, commonPrefixMap]
  exact continuant_formula a n (by exact_mod_cast hpos)

/-- The irrational tail after a common prefix lies strictly between its
integer part and the next integer. -/
theorem exists_tail_between {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    ∃ β : ℝ,
      (a (n + 1) : ℝ) < β ∧
        β < (a (n + 1) : ℝ) + 1 ∧
          α = commonPrefixMap a n β := by
  rcases hcf with ⟨_, _, htails⟩
  rcases htails n with ⟨β, hβgt, hβlt, hα⟩
  exact ⟨β, hβgt, hβlt, hα⟩

/-- The value of a positive simple continued fraction lies strictly between
its head coefficient and the next integer. -/
theorem simpleCF_head_bounds {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) :
    (a 0 : ℝ) < α ∧ α < (a 0 : ℝ) + 1 := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails 0 with ⟨β, hβgt, _, hα⟩
  have hβ_gt_one : (1 : ℝ) < β := by
    have ha1 : (1 : ℝ) ≤ a 1 := by exact_mod_cast hpos 0
    linarith
  have hβpos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hinv_pos : 0 < 1 / β := one_div_pos.mpr hβpos
  have hinv_lt_one : 1 / β < 1 :=
    (div_lt_one hβpos).mpr hβ_gt_one
  have hαeq : α = (a 0 : ℝ) + 1 / β := by
    rw [hα]
    simp [continuantNum, continuantNumPrev,
      continuantDen, continuantDenPrev]
    field_simp [ne_of_gt hβpos]
  constructor <;> rw [hαeq] <;> linarith

/-- If the finite rational expansion and the irrational expansion already
differ at the head coefficient, an integer denominator `1` lies between the
two values. -/
private theorem smaller_denominator_between_of_head_ne
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (e : CanonicalFiniteCF p q)
    (hq : 2 ≤ q)
    (hhead : e.coeff 0 ≠ a 0) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  have hαbounds := simpleCF_head_bounds hcf
  have hebounds := e.head_lt_value_lt_succ
  rcases lt_or_gt_of_ne hhead with hb_lt_ha | ha_lt_hb
  · refine ⟨e.coeff 0 + 1, 1, by norm_num, by omega, ?_⟩
    right
    constructor
    · simpa [ratValue] using hebounds.2
    · have hc_le_a : (e.coeff 0 + 1 : ℕ) ≤ a 0 := by omega
      have hc_le_aR : ((e.coeff 0 + 1 : ℕ) : ℝ) ≤ (a 0 : ℝ) := by
        exact_mod_cast hc_le_a
      simpa [ratValue] using lt_of_le_of_lt hc_le_aR hαbounds.1
  · refine ⟨e.coeff 0, 1, by norm_num, by omega, ?_⟩
    left
    constructor
    · have ha_succ_le_b : a 0 + 1 ≤ e.coeff 0 := by omega
      have ha_succ_le_bR : ((a 0 + 1 : ℕ) : ℝ) ≤ (e.coeff 0 : ℝ) := by
        exact_mod_cast ha_succ_le_b
      have hα_lt_b : α < (e.coeff 0 : ℝ) :=
        lt_of_lt_of_le hαbounds.2 (by simpa using ha_succ_le_bR)
      simpa [ratValue] using hα_lt_b
    · simpa [ratValue] using hebounds.1

/-- If the canonical finite expansion of `p / q` agrees with the expansion of
`α` through its last coefficient, then `p / q` is a convergent of `α`. -/
private theorem convergent_or_semiconvergent_of_agreesThrough
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q)
    (hagree : e.AgreesThrough a) :
    IsConvergentOrSemiconvergent α p q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  have hfinite :
      finiteCFExact e.coeff e.last = finiteCFExact a e.last := by
    exact finiteCFExact_eq_of_eq_on_prefix e.coeff a e.last
      (by
        intro i hi
        exact hagree i hi)
  have hpos_prefix :
      ∀ i : ℕ, 1 ≤ i → i ≤ e.last → 0 < a i := by
    intro i hi1 _
    cases i with
    | zero => omega
    | succ k =>
        simpa [Nat.succ_eq_add_one] using hpos k
  have hvalue :
      ratValue p q =
        ratValue (continuantNum a e.last) (continuantDen a e.last) := by
    rw [e.value_eq, hfinite,
      finiteCFExact_eq_ratValue_continuants a e.last hpos_prefix]
  have hred_conv : ReducedFraction
      (continuantNum a e.last) (continuantDen a e.last) :=
    reducedFraction_continuant a hpos e.last
  have hpq :=
    reducedFraction_eq_of_ratValue_eq hred hred_conv hvalue
  refine ⟨a, hcf', Or.inl ?_⟩
  exact ⟨e.last, hpq.1, hpq.2⟩

/-- At a first differing coefficient, the finite rational is obtained by
applying the common prefix to its finite tail. -/
private theorem ratValue_eq_commonPrefixMap_tail_of_firstDifference
    {a : ℕ → ℕ} {p q : ℕ}
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j) :
    ratValue p q = commonPrefixMap a (j - 1) (e.tailValue j) := by
  rcases hdiff with ⟨hj1, hjlast, hprefix, _⟩
  have hjpred_lt : j - 1 < e.last := by omega
  have hjpred_succ : j - 1 + 1 = j := by omega
  have htail_pos : 0 < e.tailValue j :=
    CanonicalFiniteCF.tailValue_pos e hj1 hjlast
  calc
    ratValue p q = e.tailValue 0 := by
      rw [CanonicalFiniteCF.tailValue_zero]
    _ = finiteCFWithTail e.coeff (j - 1) (e.tailValue (j - 1 + 1)) :=
      CanonicalFiniteCF.tailValue_zero_eq_finiteCFWithTail e (j - 1) hjpred_lt
    _ = finiteCFWithTail e.coeff (j - 1) (e.tailValue j) := by
      rw [hjpred_succ]
    _ = finiteCFWithTail a (j - 1) (e.tailValue j) := by
      exact finiteCFWithTail_eq_of_eq_on_prefix e.coeff a (j - 1)
        (e.tailValue j)
        (by
          intro i hi
          exact hprefix i (by omega))
    _ = commonPrefixMap a (j - 1) (e.tailValue j) :=
      finiteCFWithTail_eq_commonPrefixMap a (j - 1) htail_pos

/-- Difference formula for the common-prefix Möbius map. -/
theorem commonPrefix_sub (a : ℕ → ℕ) (n : ℕ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    commonPrefixMap a n x - commonPrefixMap a n y =
      ((x - y) *
          ((continuantNum a n : ℝ) * (continuantDenPrev a n : ℝ) -
            (continuantNumPrev a n : ℝ) * (continuantDen a n : ℝ))) /
        ((x * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) *
          (y * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ))) := by
  unfold commonPrefixMap
  have hxden :
      x * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) ≠ 0 :=
    ne_of_gt (continuant_denominator_pos a n hx)
  have hyden :
      y * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ) ≠ 0 :=
    ne_of_gt (continuant_denominator_pos a n hy)
  field_simp [hxden, hyden, mul_comm, mul_left_comm, mul_assoc]
  ring

/-- The common-prefix map sends an interior point to an interior point.  The
map may be increasing or decreasing, depending on the determinant sign, so the
statement uses `StrictBetween`. -/
theorem commonPrefix_strictBetween (a : ℕ → ℕ) (n : ℕ)
    {x z y : ℝ} (hx : 0 < x) (hz : 0 < z) (hy : 0 < y)
    (hbetween : StrictBetween x z y) :
    StrictBetween (commonPrefixMap a n x) (commonPrefixMap a n z)
      (commonPrefixMap a n y) := by
  let Δ : ℝ :=
    (continuantNum a n : ℝ) * (continuantDenPrev a n : ℝ) -
      (continuantNumPrev a n : ℝ) * (continuantDen a n : ℝ)
  have hdetR : Δ = ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [Δ]
    exact_mod_cast continuant_det a n
  have hΔne : Δ ≠ 0 := by
    rw [hdetR]
    norm_num
  rcases hbetween with ⟨hxz, hzy⟩ | ⟨hyz, hzx⟩
  · have hden_zx :
        0 <
          (z * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) *
            (x * (continuantDen a n : ℝ) +
              (continuantDenPrev a n : ℝ)) :=
      mul_pos (continuant_denominator_pos a n hz)
        (continuant_denominator_pos a n hx)
    have hden_yz :
        0 <
          (y * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) *
            (z * (continuantDen a n : ℝ) +
              (continuantDenPrev a n : ℝ)) :=
      mul_pos (continuant_denominator_pos a n hy)
        (continuant_denominator_pos a n hz)
    have hsub_zx :
        commonPrefixMap a n z - commonPrefixMap a n x =
          ((z - x) * Δ) /
            ((z * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ)) *
              (x * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ))) := by
      simpa [Δ] using commonPrefix_sub a n hz hx
    have hsub_yz :
        commonPrefixMap a n y - commonPrefixMap a n z =
          ((y - z) * Δ) /
            ((y * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ)) *
              (z * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ))) := by
      simpa [Δ] using commonPrefix_sub a n hy hz
    rcases lt_or_gt_of_ne hΔne with hΔlt | hΔgt
    · right
      have hz_lt_fx : commonPrefixMap a n z < commonPrefixMap a n x := by
        have hneg : commonPrefixMap a n z - commonPrefixMap a n x < 0 := by
          rw [hsub_zx]
          exact div_neg_of_neg_of_pos
            (mul_neg_of_pos_of_neg (sub_pos.mpr hxz) hΔlt) hden_zx
        linarith
      have fy_lt_z : commonPrefixMap a n y < commonPrefixMap a n z := by
        have hneg : commonPrefixMap a n y - commonPrefixMap a n z < 0 := by
          rw [hsub_yz]
          exact div_neg_of_neg_of_pos
            (mul_neg_of_pos_of_neg (sub_pos.mpr hzy) hΔlt) hden_yz
        linarith
      exact ⟨fy_lt_z, hz_lt_fx⟩
    · left
      have fx_lt_z : commonPrefixMap a n x < commonPrefixMap a n z := by
        have hpos : 0 < commonPrefixMap a n z - commonPrefixMap a n x := by
          rw [hsub_zx]
          exact div_pos (mul_pos (sub_pos.mpr hxz) hΔgt) hden_zx
        linarith
      have z_lt_fy : commonPrefixMap a n z < commonPrefixMap a n y := by
        have hpos : 0 < commonPrefixMap a n y - commonPrefixMap a n z := by
          rw [hsub_yz]
          exact div_pos (mul_pos (sub_pos.mpr hzy) hΔgt) hden_yz
        linarith
      exact ⟨fx_lt_z, z_lt_fy⟩
  · have hden_zy :
        0 <
          (z * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) *
            (y * (continuantDen a n : ℝ) +
              (continuantDenPrev a n : ℝ)) :=
      mul_pos (continuant_denominator_pos a n hz)
        (continuant_denominator_pos a n hy)
    have hden_xz :
        0 <
          (x * (continuantDen a n : ℝ) + (continuantDenPrev a n : ℝ)) *
            (z * (continuantDen a n : ℝ) +
              (continuantDenPrev a n : ℝ)) :=
      mul_pos (continuant_denominator_pos a n hx)
        (continuant_denominator_pos a n hz)
    have hsub_zy :
        commonPrefixMap a n z - commonPrefixMap a n y =
          ((z - y) * Δ) /
            ((z * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ)) *
              (y * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ))) := by
      simpa [Δ] using commonPrefix_sub a n hz hy
    have hsub_xz :
        commonPrefixMap a n x - commonPrefixMap a n z =
          ((x - z) * Δ) /
            ((x * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ)) *
              (z * (continuantDen a n : ℝ) +
                (continuantDenPrev a n : ℝ))) := by
      simpa [Δ] using commonPrefix_sub a n hx hz
    rcases lt_or_gt_of_ne hΔne with hΔlt | hΔgt
    · left
      have z_lt_fy : commonPrefixMap a n z < commonPrefixMap a n y := by
        have hneg : commonPrefixMap a n z - commonPrefixMap a n y < 0 := by
          rw [hsub_zy]
          exact div_neg_of_neg_of_pos
            (mul_neg_of_pos_of_neg (sub_pos.mpr hyz) hΔlt) hden_zy
        linarith
      have fx_lt_z : commonPrefixMap a n x < commonPrefixMap a n z := by
        have hneg : commonPrefixMap a n x - commonPrefixMap a n z < 0 := by
          rw [hsub_xz]
          exact div_neg_of_neg_of_pos
            (mul_neg_of_pos_of_neg (sub_pos.mpr hzx) hΔlt) hden_xz
        linarith
      exact ⟨fx_lt_z, z_lt_fy⟩
    · right
      have fy_lt_z : commonPrefixMap a n y < commonPrefixMap a n z := by
        have hpos : 0 < commonPrefixMap a n z - commonPrefixMap a n y := by
          rw [hsub_zy]
          exact div_pos (mul_pos (sub_pos.mpr hyz) hΔgt) hden_zy
        linarith
      have z_lt_fx : commonPrefixMap a n z < commonPrefixMap a n x := by
        have hpos : 0 < commonPrefixMap a n x - commonPrefixMap a n z := by
          rw [hsub_xz]
          exact div_pos (mul_pos (sub_pos.mpr hzx) hΔgt) hden_xz
        linarith
      exact ⟨fy_lt_z, z_lt_fx⟩

/-- A natural tail between two positive tails gives, after a common prefix, a
natural rational between the corresponding values. -/
private theorem commonPrefix_nat_strictBetween
    (a : ℕ → ℕ) (n δ : ℕ) {p q : ℕ} {α β γ : ℝ}
    (hα : α = commonPrefixMap a n β)
    (hpq : ratValue p q = commonPrefixMap a n γ)
    (hβpos : 0 < β)
    (hδpos : 0 < (δ : ℝ))
    (hγpos : 0 < γ)
    (hbetween : StrictBetween β (δ : ℝ) γ) :
    StrictBetween α
      (ratValue
        (δ * continuantNum a n + continuantNumPrev a n)
        (δ * continuantDen a n + continuantDenPrev a n))
      (ratValue p q) := by
  have hmap :=
    commonPrefix_strictBetween a n hβpos hδpos hγpos hbetween
  rw [hα, hpq]
  simpa [ratValue_commonPrefix_nat] using hmap

/-- A reduced rational tail remains reduced after applying a common continued
fraction prefix. -/
theorem commonPrefix_reduced (a : ℕ → ℕ) (n : ℕ) {u v : ℕ}
    (huv : Nat.Coprime u v) :
    Nat.Coprime
      (u * continuantNum a n + v * continuantNumPrev a n)
      (u * continuantDen a n + v * continuantDenPrev a n) := by
  let pn := continuantNum a n
  let ppn := continuantNumPrev a n
  let qn := continuantDen a n
  let qpn := continuantDenPrev a n
  change Nat.Coprime (u * pn + v * ppn) (u * qn + v * qpn)
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨ℓ, hℓprime, hℓA, hℓB⟩
  have hAZ : (ℓ : ℤ) ∣ ((u * pn + v * ppn : ℕ) : ℤ) := by
    exact_mod_cast hℓA
  have hBZ : (ℓ : ℤ) ∣ ((u * qn + v * qpn : ℕ) : ℤ) := by
    exact_mod_cast hℓB
  have hdet :
      (pn : ℤ) * (qpn : ℤ) - (ppn : ℤ) * (qn : ℤ) =
        (-1 : ℤ) ^ (n + 1) := by
    dsimp [pn, ppn, qn, qpn]
    exact continuant_det a n
  have hℓvZ : (ℓ : ℤ) ∣ (v : ℤ) := by
    have hcomb_div :
        (ℓ : ℤ) ∣
          ((u * pn + v * ppn : ℕ) : ℤ) * (qn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (pn : ℤ) :=
      dvd_sub (dvd_mul_of_dvd_left hAZ _) (dvd_mul_of_dvd_left hBZ _)
    have hcomb_eq :
        ((u * pn + v * ppn : ℕ) : ℤ) * (qn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (pn : ℤ) =
          -((v : ℤ) * ((-1 : ℤ) ^ (n + 1))) := by
      calc
        ((u * pn + v * ppn : ℕ) : ℤ) * (qn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (pn : ℤ)
            = (v : ℤ) * ((ppn : ℤ) * (qn : ℤ) -
                (qpn : ℤ) * (pn : ℤ)) := by
                push_cast
                ring
        _ = -((v : ℤ) * ((-1 : ℤ) ^ (n + 1))) := by
                rw [← hdet]
                ring
    rw [hcomb_eq] at hcomb_div
    rcases neg_one_pow_eq_or ℤ (n + 1) with hpow | hpow
    · rw [hpow] at hcomb_div
      simpa using (dvd_neg.mp hcomb_div)
    · rw [hpow] at hcomb_div
      simpa using hcomb_div
  have hℓuZ : (ℓ : ℤ) ∣ (u : ℤ) := by
    have hcomb_div :
        (ℓ : ℤ) ∣
          ((u * pn + v * ppn : ℕ) : ℤ) * (qpn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (ppn : ℤ) :=
      dvd_sub (dvd_mul_of_dvd_left hAZ _) (dvd_mul_of_dvd_left hBZ _)
    have hcomb_eq :
        ((u * pn + v * ppn : ℕ) : ℤ) * (qpn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (ppn : ℤ) =
          (u : ℤ) * ((-1 : ℤ) ^ (n + 1)) := by
      calc
        ((u * pn + v * ppn : ℕ) : ℤ) * (qpn : ℤ) -
            ((u * qn + v * qpn : ℕ) : ℤ) * (ppn : ℤ)
            = (u : ℤ) * ((pn : ℤ) * (qpn : ℤ) -
                (qn : ℤ) * (ppn : ℤ)) := by
                push_cast
                ring
        _ = (u : ℤ) * ((-1 : ℤ) ^ (n + 1)) := by
                rw [← hdet]
                ring
    rw [hcomb_eq] at hcomb_div
    rcases neg_one_pow_eq_or ℤ (n + 1) with hpow | hpow
    · rw [hpow] at hcomb_div
      simpa using hcomb_div
    · rw [hpow] at hcomb_div
      have hneg : (ℓ : ℤ) ∣ -(u : ℤ) := by
        simpa [mul_comm] using hcomb_div
      simpa using (dvd_neg.mp hneg)
  have hℓv : ℓ ∣ v := by
    exact_mod_cast hℓvZ
  have hℓu : ℓ ∣ u := by
    exact_mod_cast hℓuZ
  exact (Nat.not_coprime_of_dvd_of_dvd hℓprime.one_lt hℓu hℓv) huv

/-- If the first difference is the final finite coefficient, then the reduced
numerator and denominator of `p / q` are exactly obtained by applying the
common prefix to that final integer tail. -/
private theorem num_den_of_firstDifference_last
    {a : ℕ → ℕ} {p q : ℕ}
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last) :
    p = e.coeff j * continuantNum a (j - 1) +
        continuantNumPrev a (j - 1) ∧
      q = e.coeff j * continuantDen a (j - 1) +
        continuantDenPrev a (j - 1) := by
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let t : ℕ := e.coeff j
  let psemi : ℕ := t * continuantNum a n + continuantNumPrev a n
  let qsemi : ℕ := t * continuantDen a n + continuantDenPrev a n
  have htpos : 1 ≤ t := by
    dsimp [t]
    exact e.positive_after_head j hj1 hjle
  have htposR : (0 : ℝ) < t := by exact_mod_cast htpos
  have htail : e.tailValue j = (t : ℝ) := by
    dsimp [t]
    rw [hjlast]
    exact CanonicalFiniteCF.tailValue_last e
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hpq_common : ratValue p q = commonPrefixMap a n t := by
    dsimp [n]
    rw [← htail]
    exact hpq_tail
  have hvalue : ratValue p q = ratValue psemi qsemi := by
    calc
      ratValue p q = commonPrefixMap a n t := hpq_common
      _ = ratValue
            (t * continuantNum a n + continuantNumPrev a n)
            (t * continuantDen a n + continuantDenPrev a n) := by
            exact (ratValue_commonPrefix_nat a n t).symm
      _ = ratValue psemi qsemi := by rfl
  have hqsemiR : (0 : ℝ) < qsemi := by
    dsimp [qsemi]
    push_cast
    exact continuant_denominator_pos a n htposR
  have hqsemi : 0 < qsemi := by
    exact_mod_cast hqsemiR
  have hcopsemi : Nat.Coprime psemi qsemi := by
    dsimp [psemi, qsemi]
    simpa using commonPrefix_reduced a n (u := t) (v := 1)
      (Nat.coprime_one_right t)
  have hredsemi : ReducedFraction psemi qsemi := ⟨hqsemi, hcopsemi⟩
  have hpq := reducedFraction_eq_of_ratValue_eq hred hredsemi hvalue
  constructor
  · dsimp [psemi, t, n] at hpq
    simpa using hpq.1
  · dsimp [qsemi, t, n] at hpq
    simpa using hpq.2

/-- At a first difference, writing the finite tail as `u/v`, the reduced
fraction `p/q` has denominator `u q_n + v q_{n-1}` after the common prefix. -/
private theorem num_den_of_firstDifference_tail
    {a : ℕ → ℕ} {p q : ℕ}
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j) :
    let n : ℕ := j - 1
    let tail : ℕ → ℕ := fun i : ℕ => e.coeff (j + i)
    let m : ℕ := e.last - j
    let u : ℕ := continuantNum tail m
    let v : ℕ := continuantDen tail m
    p = u * continuantNum a n + v * continuantNumPrev a n ∧
      q = u * continuantDen a n + v * continuantDenPrev a n := by
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let tail : ℕ → ℕ := fun i : ℕ => e.coeff (j + i)
  let m : ℕ := e.last - j
  let u : ℕ := continuantNum tail m
  let v : ℕ := continuantDen tail m
  have htail_eq : e.tailValue j = ratValue u v := by
    dsimp [u, v, tail, m]
    exact CanonicalFiniteCF.tailValue_eq_ratValue_continuants e hj1 hjle
  have hu : 0 < u := by
    dsimp [u, tail]
    apply continuantNum_pos_of_head_pos
    exact e.positive_after_head j hj1 hjle
  have hv : 0 < v := by
    dsimp [v, tail, m]
    exact CanonicalFiniteCF.tailContinuantDen_pos e hj1 hjle
  have hzpos : 0 < ratValue u v := by
    unfold ratValue
    exact div_pos (by exact_mod_cast hu) (by exact_mod_cast hv)
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hvalue : ratValue p q =
      ratValue
        (u * continuantNum a n + v * continuantNumPrev a n)
        (u * continuantDen a n + v * continuantDenPrev a n) := by
    calc
      ratValue p q = commonPrefixMap a n (e.tailValue j) := by
        dsimp [n]
        exact hpq_tail
      _ = commonPrefixMap a n (ratValue u v) := by
        rw [htail_eq]
      _ = ratValue
            (u * continuantNum a n + v * continuantNumPrev a n)
            (u * continuantDen a n + v * continuantDenPrev a n) := by
            exact (ratValue_commonPrefix_fraction a n hu hv).symm
  have hqsemiR :
      (0 : ℝ) <
        (u * continuantDen a n + v * continuantDenPrev a n : ℕ) := by
    have hden :=
      continuant_denominator_pos a n hzpos
    unfold ratValue at hden
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hv
    have hscaled : 0 <
        (v : ℝ) *
          (((u : ℝ) / (v : ℝ)) * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ)) :=
      mul_pos (by exact_mod_cast hv) hden
    field_simp [hvR] at hscaled
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hqsemi : 0 <
      u * continuantDen a n + v * continuantDenPrev a n := by
    exact_mod_cast hqsemiR
  have hcopsemi : Nat.Coprime
      (u * continuantNum a n + v * continuantNumPrev a n)
      (u * continuantDen a n + v * continuantDenPrev a n) :=
    commonPrefix_reduced a n (continuant_coprime tail m)
  have hredsemi : ReducedFraction
      (u * continuantNum a n + v * continuantNumPrev a n)
      (u * continuantDen a n + v * continuantDenPrev a n) :=
    ⟨hqsemi, hcopsemi⟩
  exact reducedFraction_eq_of_ratValue_eq hred hredsemi hvalue

/-- Terminal first-difference case with a smaller finite coefficient: the
rational is already a semiconvergent. -/
private theorem semiconvergent_of_firstDifference_last_lt
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hb_lt_ha : e.coeff j < a j) :
    IsConvergentOrSemiconvergent α p q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let t : ℕ := e.coeff j
  let psemi : ℕ := t * continuantNum a n + continuantNumPrev a n
  let qsemi : ℕ := t * continuantDen a n + continuantDenPrev a n
  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega
  have htpos : 1 ≤ t := by
    dsimp [t]
    exact e.positive_after_head j hj1 hjle
  have htposR : (0 : ℝ) < t := by exact_mod_cast htpos
  have htlea : t ≤ a (n + 1) := by
    dsimp [t]
    rw [hn_succ]
    exact Nat.le_of_lt hb_lt_ha
  have htail : e.tailValue j = (t : ℝ) := by
    dsimp [t]
    rw [hjlast]
    exact CanonicalFiniteCF.tailValue_last e
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hpq_common : ratValue p q = commonPrefixMap a n t := by
    dsimp [n]
    rw [← htail]
    exact hpq_tail
  have hvalue : ratValue p q = ratValue psemi qsemi := by
    calc
      ratValue p q = commonPrefixMap a n t := hpq_common
      _ = ratValue
            (t * continuantNum a n + continuantNumPrev a n)
            (t * continuantDen a n + continuantDenPrev a n) := by
            exact (ratValue_commonPrefix_nat a n t).symm
      _ = ratValue psemi qsemi := by rfl
  have hqsemiR : (0 : ℝ) < qsemi := by
    dsimp [qsemi]
    push_cast
    exact continuant_denominator_pos a n htposR
  have hqsemi : 0 < qsemi := by
    exact_mod_cast hqsemiR
  have hcopsemi : Nat.Coprime psemi qsemi := by
    dsimp [psemi, qsemi]
    simpa using commonPrefix_reduced a n (u := t) (v := 1)
      (Nat.coprime_one_right t)
  have hredsemi : ReducedFraction psemi qsemi := ⟨hqsemi, hcopsemi⟩
  have hpq := reducedFraction_eq_of_ratValue_eq hred hredsemi hvalue
  refine ⟨a, hcf', Or.inr ?_⟩
  refine ⟨n, t, ?_⟩
  refine ⟨htpos, htlea, ?_, ?_⟩
  · dsimp [psemi] at hpq
    simpa [psemi, t, Nat.add_comm] using hpq.1
  · dsimp [qsemi] at hpq
    simpa [qsemi, t, Nat.add_comm] using hpq.2

/-- Terminal first-difference case with a finite coefficient at least two
larger than the irrational coefficient: choose the integer tail `b_j - 1`. -/
private theorem smaller_denominator_between_of_firstDifference_last_large
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hlarge : a j + 1 < e.coeff j) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let δ : ℕ := e.coeff j - 1
  let c : ℕ := δ * continuantNum a n + continuantNumPrev a n
  let d : ℕ := δ * continuantDen a n + continuantDenPrev a n
  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega
  have hδposNat : 0 < δ := by
    dsimp [δ]
    omega
  have hδposR : (0 : ℝ) < δ := by exact_mod_cast hδposNat
  have hδ_lt_b : δ < e.coeff j := by
    dsimp [δ]
    omega
  rcases htails n with ⟨β, hβgt, hβlt, hα⟩
  have hβpos : 0 < β := by
    have hanpos : (0 : ℝ) < a (n + 1) := by exact_mod_cast hpos n
    linarith
  have hγpos : 0 < e.tailValue j :=
    CanonicalFiniteCF.tailValue_pos e hj1 hjle
  have htail : e.tailValue j = (e.coeff j : ℝ) := by
    rw [hjlast]
    exact CanonicalFiniteCF.tailValue_last e
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hbetween_tail : StrictBetween β (δ : ℝ) (e.tailValue j) := by
    left
    constructor
    · have hle_nat : a (n + 1) + 1 ≤ δ := by
        dsimp [δ, n]
        rw [hn_succ]
        omega
      have hle_real : ((a (n + 1) + 1 : ℕ) : ℝ) ≤ (δ : ℝ) := by
        exact_mod_cast hle_nat
      have hβlt' : β < ((a (n + 1) + 1 : ℕ) : ℝ) := by
        norm_num
        exact hβlt
      exact lt_of_lt_of_le hβlt' hle_real
    · rw [htail]
      exact_mod_cast hδ_lt_b
  have hstrict :
      StrictBetween α (ratValue c d) (ratValue p q) := by
    dsimp [c, d]
    exact commonPrefix_nat_strictBetween a n δ hα hpq_tail
      hβpos hδposR hγpos hbetween_tail
  have hqform :=
    (num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩) hjlast).2
  have hqnpos : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hdpos : 0 < d := by
    dsimp [d]
    have hdenR :
        (0 : ℝ) <
          (δ : ℝ) * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ) :=
      continuant_denominator_pos a n hδposR
    exact_mod_cast hdenR
  have hdlt : d < q := by
    have hdlt_form :
        d < e.coeff j * continuantDen a (j - 1) +
          continuantDenPrev a (j - 1) := by
      dsimp [d, δ, n]
      apply Nat.add_lt_add_right
      exact Nat.mul_lt_mul_of_pos_right hδ_lt_b hqnpos
    exact lt_of_lt_of_eq hdlt_form hqform.symm
  exact ⟨c, d, hdpos, hdlt, hstrict⟩

/-- Terminal first-difference case with `b_j = a_j + 1`: the rational is the
next semiconvergent with parameter `1`. -/
private theorem semiconvergent_of_firstDifference_last_succ
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hsucc : e.coeff j = a j + 1) :
    IsConvergentOrSemiconvergent α p q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega
  have hnumden :=
    num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩) hjlast
  have hnumj :
      continuantNum a j =
        a j * continuantNum a n + continuantNumPrev a n := by
    rw [← hn_succ]
    exact continuantNum_succ a n
  have hdenj :
      continuantDen a j =
        a j * continuantDen a n + continuantDenPrev a n := by
    rw [← hn_succ]
    exact continuantDen_succ a n
  have hnumprevj : continuantNumPrev a j = continuantNum a n := by
    rw [← hn_succ]
    exact continuantNumPrev_succ a n
  have hdenprevj : continuantDenPrev a j = continuantDen a n := by
    rw [← hn_succ]
    exact continuantDenPrev_succ a n
  refine ⟨a, hcf', Or.inr ?_⟩
  refine ⟨j, 1, ?_⟩
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · exact hpos j
  · calc
      p = e.coeff j * continuantNum a n + continuantNumPrev a n :=
        hnumden.1
      _ = (a j + 1) * continuantNum a n + continuantNumPrev a n := by
        rw [hsucc]
      _ = continuantNumPrev a j + 1 * continuantNum a j := by
        rw [hnumj, hnumprevj]
        ring
  · calc
      q = e.coeff j * continuantDen a n + continuantDenPrev a n :=
        hnumden.2
      _ = (a j + 1) * continuantDen a n + continuantDenPrev a n := by
        rw [hsucc]
      _ = continuantDenPrev a j + 1 * continuantDen a j := by
        rw [hdenj, hdenprevj]
        ring

/-- Nonterminal first-difference case with `b_j < a_j`: choose the integer
tail `b_j + 1`. -/
private theorem smaller_denominator_between_of_firstDifference_nonterminal_lt
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlt : j < e.last)
    (hb_lt_ha : e.coeff j < a j) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let b : ℕ := e.coeff j
  let δ : ℕ := b + 1
  let tail : ℕ → ℕ := fun i : ℕ => e.coeff (j + i)
  let m : ℕ := e.last - j
  let u : ℕ := continuantNum tail m
  let v : ℕ := continuantDen tail m
  let c : ℕ := δ * continuantNum a n + continuantNumPrev a n
  let d : ℕ := δ * continuantDen a n + continuantDenPrev a n
  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega
  have hbpos : 0 < b := by
    dsimp [b]
    exact e.positive_after_head j hj1 hjle
  have hδposNat : 0 < δ := by
    dsimp [δ]
    omega
  have hδposR : (0 : ℝ) < δ := by exact_mod_cast hδposNat
  have hu : 0 < u := by
    dsimp [u, tail]
    apply continuantNum_pos_of_head_pos
    exact e.positive_after_head j hj1 hjle
  have hv : 0 < v := by
    dsimp [v, tail, m]
    exact CanonicalFiniteCF.tailContinuantDen_pos e hj1 hjle
  have hvge2 : 2 ≤ v := by
    dsimp [v, tail, m]
    exact CanonicalFiniteCF.two_le_tailContinuantDen e hj1 hjlt
  have htail_eq : e.tailValue j = ratValue u v := by
    dsimp [u, v, tail, m]
    exact CanonicalFiniteCF.tailValue_eq_ratValue_continuants e hj1 hjle
  have htail_bounds :=
    CanonicalFiniteCF.tailValue_between_head_and_succ e hj1 hjlt
  have hdelta_lt_u : δ < u := by
    have hb_lt_gamma : (b : ℝ) < ratValue u v := by
      rw [← htail_eq]
      simpa [b] using htail_bounds.1
    have hbv_lt_u_R : (b : ℝ) * (v : ℝ) < (u : ℝ) := by
      unfold ratValue at hb_lt_gamma
      exact (lt_div_iff₀ (by exact_mod_cast hv)).mp hb_lt_gamma
    have hbv_lt_u : b * v < u := by
      exact_mod_cast hbv_lt_u_R
    have hbv_succ_le_u : b * v + 1 ≤ u :=
      Nat.succ_le_of_lt hbv_lt_u
    have hδ_lt_bv_succ : δ < b * v + 1 := by
      have hbv_ge_2b : b * 2 ≤ b * v :=
        Nat.mul_le_mul_left b hvge2
      have hδ_le_2b : δ ≤ b * 2 := by
        dsimp [δ]
        omega
      exact Nat.lt_succ_of_le (le_trans hδ_le_2b hbv_ge_2b)
    exact lt_of_lt_of_le hδ_lt_bv_succ hbv_succ_le_u
  rcases htails n with ⟨β, hβgt, hβlt, hα⟩
  have hβpos : 0 < β := by
    have hanpos : (0 : ℝ) < a (n + 1) := by exact_mod_cast hpos n
    linarith
  have hγpos : 0 < e.tailValue j :=
    CanonicalFiniteCF.tailValue_pos e hj1 hjle
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hbetween_tail : StrictBetween β (δ : ℝ) (e.tailValue j) := by
    right
    constructor
    · have hγ_lt_delta : e.tailValue j < (δ : ℝ) := by
        dsimp [δ, b]
        simpa [Nat.cast_add, Nat.cast_one] using htail_bounds.2
      exact hγ_lt_delta
    · have hδ_le_a : δ ≤ a (n + 1) := by
        dsimp [δ, b, n]
        rw [hn_succ]
        omega
      have hδ_le_aR : (δ : ℝ) ≤ (a (n + 1) : ℝ) := by
        exact_mod_cast hδ_le_a
      exact lt_of_le_of_lt hδ_le_aR hβgt
  have hstrict :
      StrictBetween α (ratValue c d) (ratValue p q) := by
    dsimp [c, d]
    exact commonPrefix_nat_strictBetween a n δ hα hpq_tail
      hβpos hδposR hγpos hbetween_tail
  have hnumden :=
    num_den_of_firstDifference_tail hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hqform :
      q = u * continuantDen a n + v * continuantDenPrev a n := by
    simpa [n, tail, m, u, v] using hnumden.2
  have hqnpos : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hdpos : 0 < d := by
    dsimp [d]
    have hdenR :
        (0 : ℝ) <
          (δ : ℝ) * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ) :=
      continuant_denominator_pos a n hδposR
    exact_mod_cast hdenR
  have hdlt : d < q := by
    have hprev_le :
        continuantDenPrev a n ≤ v * continuantDenPrev a n := by
      have hv1 : 1 ≤ v := by omega
      calc
        continuantDenPrev a n = 1 * continuantDenPrev a n := by simp
        _ ≤ v * continuantDenPrev a n :=
          Nat.mul_le_mul_right _ hv1
    have hmul_lt :
        δ * continuantDen a n < u * continuantDen a n :=
      Nat.mul_lt_mul_of_pos_right hdelta_lt_u hqnpos
    have hdlt_form :
        d < u * continuantDen a n + v * continuantDenPrev a n := by
      dsimp [d]
      exact Nat.add_lt_add_of_lt_of_le hmul_lt hprev_le
    exact lt_of_lt_of_eq hdlt_form hqform.symm
  exact ⟨c, d, hdpos, hdlt, hstrict⟩

/-- Nonterminal first-difference case with `a_j < b_j`: choose the integer
tail `b_j`. -/
private theorem smaller_denominator_between_of_firstDifference_nonterminal_gt
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlt : j < e.last)
    (ha_lt_hb : a j < e.coeff j) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let δ : ℕ := e.coeff j
  let tail : ℕ → ℕ := fun i : ℕ => e.coeff (j + i)
  let m : ℕ := e.last - j
  let u : ℕ := continuantNum tail m
  let v : ℕ := continuantDen tail m
  let c : ℕ := δ * continuantNum a n + continuantNumPrev a n
  let d : ℕ := δ * continuantDen a n + continuantDenPrev a n
  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega
  have hδposNat : 0 < δ := by
    dsimp [δ]
    exact e.positive_after_head j hj1 hjle
  have hδposR : (0 : ℝ) < δ := by exact_mod_cast hδposNat
  have hu : 0 < u := by
    dsimp [u, tail]
    apply continuantNum_pos_of_head_pos
    exact e.positive_after_head j hj1 hjle
  have hv : 0 < v := by
    dsimp [v, tail, m]
    exact CanonicalFiniteCF.tailContinuantDen_pos e hj1 hjle
  have hvge2 : 2 ≤ v := by
    dsimp [v, tail, m]
    exact CanonicalFiniteCF.two_le_tailContinuantDen e hj1 hjlt
  have htail_eq : e.tailValue j = ratValue u v := by
    dsimp [u, v, tail, m]
    exact CanonicalFiniteCF.tailValue_eq_ratValue_continuants e hj1 hjle
  have htail_bounds :=
    CanonicalFiniteCF.tailValue_between_head_and_succ e hj1 hjlt
  have hdelta_mul_lt_u : δ * v < u := by
    have hδ_lt_gamma : (δ : ℝ) < ratValue u v := by
      rw [← htail_eq]
      simpa [δ] using htail_bounds.1
    have hδv_lt_u_R : (δ : ℝ) * (v : ℝ) < (u : ℝ) := by
      unfold ratValue at hδ_lt_gamma
      exact (lt_div_iff₀ (by exact_mod_cast hv)).mp hδ_lt_gamma
    exact_mod_cast hδv_lt_u_R
  have hdelta_lt_u : δ < u := by
    have hv1 : 1 ≤ v := by omega
    have hδ_le_δv : δ ≤ δ * v := by
      calc
        δ = δ * 1 := by simp
        _ ≤ δ * v := Nat.mul_le_mul_left δ hv1
    exact lt_of_le_of_lt hδ_le_δv hdelta_mul_lt_u
  rcases htails n with ⟨β, hβgt, hβlt, hα⟩
  have hβpos : 0 < β := by
    have hanpos : (0 : ℝ) < a (n + 1) := by exact_mod_cast hpos n
    linarith
  have hγpos : 0 < e.tailValue j :=
    CanonicalFiniteCF.tailValue_pos e hj1 hjle
  have hpq_tail :=
    ratValue_eq_commonPrefixMap_tail_of_firstDifference e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hbetween_tail : StrictBetween β (δ : ℝ) (e.tailValue j) := by
    left
    constructor
    · have hle_nat : a (n + 1) + 1 ≤ δ := by
        dsimp [δ, n]
        rw [hn_succ]
        omega
      have hle_real : ((a (n + 1) + 1 : ℕ) : ℝ) ≤ (δ : ℝ) := by
        exact_mod_cast hle_nat
      have hβlt' : β < ((a (n + 1) + 1 : ℕ) : ℝ) := by
        norm_num
        exact hβlt
      exact lt_of_lt_of_le hβlt' hle_real
    · simpa [δ] using htail_bounds.1
  have hstrict :
      StrictBetween α (ratValue c d) (ratValue p q) := by
    dsimp [c, d]
    exact commonPrefix_nat_strictBetween a n δ hα hpq_tail
      hβpos hδposR hγpos hbetween_tail
  have hnumden :=
    num_den_of_firstDifference_tail hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
  have hqform :
      q = u * continuantDen a n + v * continuantDenPrev a n := by
    simpa [n, tail, m, u, v] using hnumden.2
  have hqnpos : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hdpos : 0 < d := by
    dsimp [d]
    have hdenR :
        (0 : ℝ) <
          (δ : ℝ) * (continuantDen a n : ℝ) +
            (continuantDenPrev a n : ℝ) :=
      continuant_denominator_pos a n hδposR
    exact_mod_cast hdenR
  have hdlt : d < q := by
    have hprev_le :
        continuantDenPrev a n ≤ v * continuantDenPrev a n := by
      have hv1 : 1 ≤ v := by omega
      calc
        continuantDenPrev a n = 1 * continuantDenPrev a n := by simp
        _ ≤ v * continuantDenPrev a n :=
          Nat.mul_le_mul_right _ hv1
    have hmul_lt :
        δ * continuantDen a n < u * continuantDen a n :=
      Nat.mul_lt_mul_of_pos_right hdelta_lt_u hqnpos
    have hdlt_form :
        d < u * continuantDen a n + v * continuantDenPrev a n := by
      dsimp [d]
      exact Nat.add_lt_add_of_lt_of_le hmul_lt hprev_le
    exact lt_of_lt_of_eq hdlt_form hqform.symm
  exact ⟨c, d, hdpos, hdlt, hstrict⟩

/-- The complete first-difference branch of the finite-CF comparison proof,
assuming a project-local simple continued-fraction expansion of `α`. -/
private theorem smaller_denominator_between_of_firstDifference
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hnot : ¬ IsConvergentOrSemiconvergent α p q) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  have hdiff' : e.FirstDifference a j := ⟨hj1, hjle, hprefix, hne⟩
  rcases lt_or_gt_of_ne hne with hb_lt_ha | ha_lt_hb
  · by_cases hjlast : j = e.last
    · exact False.elim
        (hnot (semiconvergent_of_firstDifference_last_lt
          hcf hred e hdiff' hjlast hb_lt_ha))
    · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
      exact smaller_denominator_between_of_firstDifference_nonterminal_lt
        hcf hred e hdiff' hjlt hb_lt_ha
  · by_cases hjlast : j = e.last
    · by_cases hsucc : e.coeff j = a j + 1
      · exact False.elim
          (hnot (semiconvergent_of_firstDifference_last_succ
            hcf hred e hdiff' hjlast hsucc))
      · have hlarge : a j + 1 < e.coeff j := by
          omega
        exact smaller_denominator_between_of_firstDifference_last_large
          hcf hred e hdiff' hjlast hlarge
    · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
      exact smaller_denominator_between_of_firstDifference_nonterminal_gt
        hcf hred e hdiff' hjlt ha_lt_hb

/-- Lemma 3.5: the irrational lies strictly between a semiconvergent and the
adjacent convergent. -/
theorem semiconvergent_between_alpha_and_convergent {α : ℝ} {a : ℕ → ℕ}
    {n t p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hirr : IsIrrational α)
    (hsemi : IsSemiconvergentOf a n t p q) :
    StrictBetween (ratValue p q) α
      (ratValue (continuantNum a n) (continuantDen a n)) := by
  have _ : IsIrrational α := hirr
  rcases hcf with ⟨hpos, _, htails⟩
  rcases hsemi with ⟨htpos, htle, hp, hq⟩
  rcases htails n with ⟨β, hβgt, _, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let Δ : ℝ := pn * qpn - ppn * qn
  have htβ : (t : ℝ) < β := by
    have htleR : (t : ℝ) ≤ a (n + 1) := by exact_mod_cast htle
    linarith
  have hβpos : 0 < β := by
    have hanpos : (0 : ℝ) < a (n + 1) := by exact_mod_cast hpos n
    linarith
  have htRpos : (0 : ℝ) < t := by exact_mod_cast htpos
  have hqnNat : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hqnR : (0 : ℝ) < qn := by
    dsimp [qn]
    exact_mod_cast hqnNat
  have hβdenpos : 0 < β * qn + qpn := by
    dsimp [qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have htdenpos : 0 < (t : ℝ) * qn + qpn := by
    dsimp [qn, qpn]
    simpa using continuant_denominator_pos a n htRpos
  have hdetR : Δ = ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [Δ, pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hΔne : Δ ≠ 0 := by
    rw [hdetR]
    norm_num
  have hs_diff :
      α - ratValue p q =
        ((β - (t : ℝ)) * Δ) /
          ((β * qn + qpn) * ((t : ℝ) * qn + qpn)) := by
    rw [hα, hp, hq]
    unfold ratValue
    dsimp [Δ, pn, ppn, qn, qpn]
    push_cast
    field_simp [ne_of_gt hβdenpos, ne_of_gt htdenpos]
    ring
  have hc_diff :
      α - ratValue (continuantNum a n) (continuantDen a n) =
        -Δ / (qn * (β * qn + qpn)) := by
    rw [hα]
    unfold ratValue
    dsimp [Δ, pn, ppn, qn, qpn]
    field_simp [ne_of_gt hβdenpos, ne_of_gt hqnR]
    ring
  have hs_den_pos : 0 < (β * qn + qpn) * ((t : ℝ) * qn + qpn) :=
    mul_pos hβdenpos htdenpos
  have hc_den_pos : 0 < qn * (β * qn + qpn) :=
    mul_pos hqnR hβdenpos
  rcases lt_or_gt_of_ne hΔne with hΔlt | hΔgt
  · have hα_lt_s : α < ratValue p q := by
      have hsneg : α - ratValue p q < 0 := by
        rw [hs_diff]
        exact div_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (sub_pos.mpr htβ) hΔlt) hs_den_pos
      linarith
    have hc_lt_α :
        ratValue (continuantNum a n) (continuantDen a n) < α := by
      have hcpos :
          0 < α - ratValue (continuantNum a n) (continuantDen a n) := by
        rw [hc_diff]
        exact div_pos (neg_pos.mpr hΔlt) hc_den_pos
      linarith
    exact Or.inr ⟨hc_lt_α, hα_lt_s⟩
  · have hs_lt_α : ratValue p q < α := by
      have hspos : 0 < α - ratValue p q := by
        rw [hs_diff]
        exact div_pos
          (mul_pos (sub_pos.mpr htβ) hΔgt) hs_den_pos
      linarith
    have hα_lt_c :
        α < ratValue (continuantNum a n) (continuantDen a n) := by
      have hcneg :
          α - ratValue (continuantNum a n) (continuantDen a n) < 0 := by
        rw [hc_diff]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hΔgt) hc_den_pos
      linarith
    exact Or.inl ⟨hs_lt_α, hα_lt_c⟩

/-- Lemma 3.6: Farey neighbors force any reduced rational strictly between
them to have denominator at least the sum of the two denominators. -/
theorem farey_neighbor_denominator_lower_bound {a b c d x y : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hy : 0 < y)
    (hfarey : b * c = a * d + 1)
    (hbetween : ratValue a b < ratValue x y ∧ ratValue x y < ratValue c d) :
    b + d ≤ y := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hleftR : (a : ℝ) * (y : ℝ) < (x : ℝ) * (b : ℝ) := by
    have h := hbetween.1
    unfold ratValue at h
    rw [div_lt_div_iff₀ hbR hyR] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hrightR : (x : ℝ) * (d : ℝ) < (c : ℝ) * (y : ℝ) := by
    have h := hbetween.2
    unfold ratValue at h
    rw [div_lt_div_iff₀ hyR hdR] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hleftZ' : (a * y : ℤ) < (x * b : ℤ) := by
    exact_mod_cast hleftR
  have hleftZ : (a * y : ℤ) < (b * x : ℤ) := by
    simpa [mul_comm] using hleftZ'
  have hrightZ' : (x * d : ℤ) < (c * y : ℤ) := by
    exact_mod_cast hrightR
  have hrightZ : (d * x : ℤ) < (c * y : ℤ) := by
    simpa [mul_comm] using hrightZ'
  have hleft_one : (1 : ℤ) ≤ (b * x : ℤ) - (a * y : ℤ) := by omega
  have hright_one : (1 : ℤ) ≤ (c * y : ℤ) - (d * x : ℤ) := by omega
  have hmain : (y : ℤ) =
      (b : ℤ) * ((c * y : ℤ) - (d * x : ℤ)) +
        (d : ℤ) * ((b * x : ℤ) - (a * y : ℤ)) := by
    have hfareyZ : (b : ℤ) * (c : ℤ) - (a : ℤ) * (d : ℤ) = 1 := by
      have : (b * c : ℤ) = (a * d + 1 : ℕ) := by
        exact_mod_cast hfarey
      omega
    calc
      (y : ℤ) = y * ((b : ℤ) * (c : ℤ) - (a : ℤ) * (d : ℤ)) := by
        rw [hfareyZ, mul_one]
      _ = (b : ℤ) * ((c * y : ℤ) - (d * x : ℤ)) +
          (d : ℤ) * ((b * x : ℤ) - (a * y : ℤ)) := by ring
  have hbZ : (0 : ℤ) ≤ b := by exact_mod_cast Nat.zero_le b
  have hdZ : (0 : ℤ) ≤ d := by exact_mod_cast Nat.zero_le d
  have hleZ : (b : ℤ) + (d : ℤ) ≤ (y : ℤ) := by
    rw [hmain]
    nlinarith [mul_le_mul_of_nonneg_left hright_one hbZ,
      mul_le_mul_of_nonneg_left hleft_one hdZ]
  exact_mod_cast hleZ

private theorem noSmallDenominatorBetween_of_left_farey
    {α : ℝ} {p q r s : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hfarey : q * r = p * s + 1)
    (hα_between : ratValue p q < α ∧ α < ratValue r s) :
    NoSmallDenominatorBetween α p q := by
  intro x y hy hyq hbetween
  rcases hbetween with ⟨hα_lt_xy, hxy_lt_pq⟩ | ⟨hpq_lt_xy, hxy_lt_α⟩
  · have hα_lt_pq : α < ratValue p q := lt_trans hα_lt_xy hxy_lt_pq
    exact (not_lt_of_ge hα_between.1.le) hα_lt_pq
  · have hxy_between_neighbors :
        ratValue p q < ratValue x y ∧ ratValue x y < ratValue r s :=
      ⟨hpq_lt_xy, lt_trans hxy_lt_α hα_between.2⟩
    have hybound : q + s ≤ y :=
      farey_neighbor_denominator_lower_bound hq hs hy hfarey
        hxy_between_neighbors
    omega

private theorem noSmallDenominatorBetween_of_right_farey
    {α : ℝ} {p q r s : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hfarey : s * p = r * q + 1)
    (hα_between : ratValue r s < α ∧ α < ratValue p q) :
    NoSmallDenominatorBetween α p q := by
  intro x y hy hyq hbetween
  rcases hbetween with ⟨hα_lt_xy, hxy_lt_pq⟩ | ⟨hpq_lt_xy, hxy_lt_α⟩
  · have hxy_between_neighbors :
        ratValue r s < ratValue x y ∧ ratValue x y < ratValue p q :=
      ⟨lt_trans hα_between.1 hα_lt_xy, hxy_lt_pq⟩
    have hybound : s + q ≤ y :=
      farey_neighbor_denominator_lower_bound hs hq hy hfarey
        hxy_between_neighbors
    omega
  · have hpq_lt_α : ratValue p q < α := lt_trans hpq_lt_xy hxy_lt_α
    exact (not_lt_of_ge hα_between.2.le) hpq_lt_α

private theorem left_farey_of_det_and_lt {p q r s m : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hdet : (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) =
      (-1 : ℤ) ^ m)
    (hlt : ratValue p q < ratValue r s) :
    q * r = p * s + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcrossR : (p : ℝ) * (s : ℝ) < (r : ℝ) * (q : ℝ) := by
    unfold ratValue at hlt
    rw [div_lt_div_iff₀ hqR hsR] at hlt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have hcrossZ : (p * s : ℤ) < (r * q : ℤ) := by
    exact_mod_cast hcrossR
  have hDpos : 0 < (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) := by
    norm_num
    omega
  have hD_eq_one : (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) = 1 := by
    rcases neg_one_pow_eq_or ℤ m with hpow | hpow
    · rw [hdet, hpow]
    · have hneg :
          (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) = -1 := by
        rw [hdet, hpow]
      omega
  have hEqZ : (q * r : ℤ) = (p * s + 1 : ℕ) := by
    norm_num
    ring_nf at hD_eq_one ⊢
    omega
  exact_mod_cast hEqZ

private theorem right_farey_of_det_and_lt {p q r s m : ℕ}
    (hq : 0 < q) (hs : 0 < s)
    (hdet : (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) =
      (-1 : ℤ) ^ m)
    (hlt : ratValue r s < ratValue p q) :
    s * p = r * q + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcrossR : (r : ℝ) * (q : ℝ) < (p : ℝ) * (s : ℝ) := by
    unfold ratValue at hlt
    rw [div_lt_div_iff₀ hsR hqR] at hlt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have hcrossZ : (r * q : ℤ) < (p * s : ℤ) := by
    exact_mod_cast hcrossR
  have hDneg : (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) < 0 := by
    norm_num
    omega
  have hD_eq_neg_one :
      (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) = -1 := by
    rcases neg_one_pow_eq_or ℤ m with hpow | hpow
    · have hone :
          (r : ℤ) * (q : ℤ) - (p : ℤ) * (s : ℤ) = 1 := by
        rw [hdet, hpow]
      omega
    · rw [hdet, hpow]
  have hEqZ : (s * p : ℤ) = (r * q + 1 : ℕ) := by
    norm_num
    ring_nf at hD_eq_neg_one ⊢
    omega
  exact_mod_cast hEqZ

/-- A one-sided best approximation gives agreement of floors below its
denominator. -/
theorem floor_agreement_of_no_small_denominator {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hred : ReducedFraction p q)
    (hbest : NoSmallDenominatorBetween α p q) :
    FloorAgreement α p q := by
  intro k hk1 hkq
  have hqpos : 0 < q := hred.1
  have hkpos : 0 < k := by omega
  have hklt : k < q := by omega
  let xα : ℝ := (k : ℝ) * α
  let xr : ℝ := ((k : ℝ) * (p : ℝ)) / (q : ℝ)
  by_contra hne
  have hlt_or_gt :
      Int.floor xα < Int.floor xr ∨ Int.floor xr < Int.floor xα := by
    exact lt_or_gt_of_ne hne
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hqpos
  rcases hlt_or_gt with hlt | hgt
  · let mZ : ℤ := Int.floor xr
    have hmZ_nonneg : 0 ≤ mZ := by
      dsimp [mZ]
      apply Int.le_floor.mpr
      dsimp [xr]
      norm_num
      exact div_nonneg
        (mul_nonneg (le_of_lt hkRpos) (by positivity))
        (le_of_lt hqRpos)
    let m : ℕ := mZ.toNat
    have hm_cast_real : (m : ℝ) = (mZ : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hmZ_nonneg)
    have hxα_lt_m : xα < (m : ℝ) := by
      rw [hm_cast_real]
      dsimp [mZ]
      exact (Int.floor_lt).mp hlt
    have hm_lt_xr : (m : ℝ) < xr := by
      rw [hm_cast_real]
      dsimp [mZ]
      exact floor_lt_of_not_int (rat_not_int_of_coprime hqpos hred.2 hkpos hklt)
    have hα_lt_mk : α < ratValue m k := by
      unfold ratValue
      exact (lt_div_iff₀ hkRpos).mpr (by
        simpa [xα, mul_comm] using hxα_lt_m)
    have hmk_lt_pq : ratValue m k < ratValue p q := by
      unfold ratValue
      rw [div_lt_div_iff₀ hkRpos hqRpos]
      have hm_mul_q_lt : (m : ℝ) * (q : ℝ) < (k : ℝ) * (p : ℝ) := by
        exact (lt_div_iff₀ hqRpos).mp (by simpa [xr] using hm_lt_xr)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hm_mul_q_lt
    exact hbest m k hkpos hklt (Or.inl ⟨hα_lt_mk, hmk_lt_pq⟩)
  · let mZ : ℤ := Int.floor xα
    have hmZ_nonneg : 0 ≤ mZ := by
      dsimp [mZ]
      apply Int.le_floor.mpr
      dsimp [xα]
      norm_num
      exact mul_nonneg (le_of_lt hkRpos) (le_of_lt hαpos)
    let m : ℕ := mZ.toNat
    have hm_cast_real : (m : ℝ) = (mZ : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hmZ_nonneg)
    have hxr_lt_m : xr < (m : ℝ) := by
      rw [hm_cast_real]
      dsimp [mZ]
      exact (Int.floor_lt).mp hgt
    have hm_lt_xα : (m : ℝ) < xα := by
      rw [hm_cast_real]
      dsimp [mZ]
      exact floor_lt_of_not_int (mul_irrational_not_int hirr hkpos)
    have hpq_lt_mk : ratValue p q < ratValue m k := by
      unfold ratValue
      rw [div_lt_div_iff₀ hqRpos hkRpos]
      have hkp_lt_mq : (k : ℝ) * (p : ℝ) < (m : ℝ) * (q : ℝ) := by
        exact (div_lt_iff₀ hqRpos).mp (by simpa [xr] using hxr_lt_m)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hkp_lt_mq
    have hmk_lt_α : ratValue m k < α := by
      unfold ratValue
      exact (div_lt_iff₀ hkRpos).mpr (by
        simpa [xα, mul_comm] using hm_lt_xα)
    exact hbest m k hkpos hklt (Or.inr ⟨hpq_lt_mk, hmk_lt_α⟩)

/-- Classical continued-fraction fact: convergents and semiconvergents are
one-sided best approximations. -/
theorem convergent_or_semiconvergent_no_small_denominator
    {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hcf : IsConvergentOrSemiconvergent α p q)
    (hred : ReducedFraction p q) :
    NoSmallDenominatorBetween α p q := by
  have _ : 0 < α := hαpos
  rcases hcf with ⟨a, hsimple, hkind⟩
  rcases hsimple with ⟨hpos, htendsto, htails⟩
  have hsimple' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  rcases hkind with hconv | hsemiCase
  · rcases hconv with ⟨n, hp, hq⟩
    subst p
    subst q
    have hqcur : 0 < continuantDen a n :=
      continuantDen_pos_of_partials a hpos n
    have hqnext : 0 < continuantDen a (n + 1) :=
      continuantDen_pos_of_partials a hpos (n + 1)
    have hsemiNext :
        IsSemiconvergentOf a n (a (n + 1))
          (continuantNum a (n + 1)) (continuantDen a (n + 1)) := by
      refine ⟨Nat.succ_le_iff.mpr (hpos n), le_rfl, ?_, ?_⟩
      · rw [continuantNum_succ]
        ac_rfl
      · rw [continuantDen_succ]
        ac_rfl
    have hbracket :=
      semiconvergent_between_alpha_and_convergent
        (α := α) (a := a) hsimple' hirr hsemiNext
    have hdet :
        (continuantNum a (n + 1) : ℤ) * (continuantDen a n : ℤ) -
          (continuantNum a n : ℤ) * (continuantDen a (n + 1) : ℤ) =
            (-1 : ℤ) ^ (n + 2) := by
      simpa [continuantNumPrev, continuantDenPrev, Nat.add_assoc]
        using continuant_det a (n + 1)
    rcases hbracket with ⟨hnext_lt_α, hα_lt_cur⟩ | ⟨hcur_lt_α, hα_lt_next⟩
    · have hnext_lt_cur :
          ratValue (continuantNum a (n + 1)) (continuantDen a (n + 1)) <
            ratValue (continuantNum a n) (continuantDen a n) :=
        lt_trans hnext_lt_α hα_lt_cur
      have hfarey :
          continuantDen a (n + 1) * continuantNum a n =
            continuantNum a (n + 1) * continuantDen a n + 1 :=
        right_farey_of_det_and_lt
          (p := continuantNum a n) (q := continuantDen a n)
          (r := continuantNum a (n + 1)) (s := continuantDen a (n + 1))
          (m := n + 2) hqcur hqnext hdet hnext_lt_cur
      exact noSmallDenominatorBetween_of_right_farey hqcur hqnext hfarey
        ⟨hnext_lt_α, hα_lt_cur⟩
    · have hcur_lt_next :
          ratValue (continuantNum a n) (continuantDen a n) <
            ratValue (continuantNum a (n + 1)) (continuantDen a (n + 1)) :=
        lt_trans hcur_lt_α hα_lt_next
      have hfarey :
          continuantDen a n * continuantNum a (n + 1) =
            continuantNum a n * continuantDen a (n + 1) + 1 :=
        left_farey_of_det_and_lt
          (p := continuantNum a n) (q := continuantDen a n)
          (r := continuantNum a (n + 1)) (s := continuantDen a (n + 1))
          (m := n + 2) hqcur hqnext hdet hcur_lt_next
      exact noSmallDenominatorBetween_of_left_farey hqcur hqnext hfarey
        ⟨hcur_lt_α, hα_lt_next⟩
  · rcases hsemiCase with ⟨n, t, hsemi⟩
    rcases hsemi with ⟨htpos, htle, hp, hq⟩
    subst p
    subst q
    have hqsemi : 0 < continuantDenPrev a n + t * continuantDen a n := hred.1
    have hqcur : 0 < continuantDen a n :=
      continuantDen_pos_of_partials a hpos n
    have hsemi' :
        IsSemiconvergentOf a n t
          (continuantNumPrev a n + t * continuantNum a n)
          (continuantDenPrev a n + t * continuantDen a n) :=
      ⟨htpos, htle, rfl, rfl⟩
    have hbracket :=
      semiconvergent_between_alpha_and_convergent
        (α := α) (a := a) hsimple' hirr hsemi'
    have hdet :
        (continuantNum a n : ℤ) *
            ((continuantDenPrev a n + t * continuantDen a n : ℕ) : ℤ) -
          ((continuantNumPrev a n + t * continuantNum a n : ℕ) : ℤ) *
            (continuantDen a n : ℤ) =
            (-1 : ℤ) ^ (n + 1) := by
      have hbase := continuant_det a n
      push_cast
      calc
        (continuantNum a n : ℤ) *
              ((continuantDenPrev a n : ℤ) + (t : ℤ) * (continuantDen a n : ℤ)) -
            ((continuantNumPrev a n : ℤ) + (t : ℤ) * (continuantNum a n : ℤ)) *
              (continuantDen a n : ℤ)
            =
              (continuantNum a n : ℤ) * (continuantDenPrev a n : ℤ) -
                (continuantNumPrev a n : ℤ) * (continuantDen a n : ℤ) := by
              ring
        _ = (-1 : ℤ) ^ (n + 1) := hbase
    rcases hbracket with ⟨hsemi_lt_α, hα_lt_cur⟩ | ⟨hcur_lt_α, hα_lt_semi⟩
    · have hsemi_lt_cur :
          ratValue
              (continuantNumPrev a n + t * continuantNum a n)
              (continuantDenPrev a n + t * continuantDen a n) <
            ratValue (continuantNum a n) (continuantDen a n) :=
        lt_trans hsemi_lt_α hα_lt_cur
      have hfarey :
          (continuantDenPrev a n + t * continuantDen a n) *
              continuantNum a n =
            (continuantNumPrev a n + t * continuantNum a n) *
              continuantDen a n + 1 :=
        left_farey_of_det_and_lt
          (p := continuantNumPrev a n + t * continuantNum a n)
          (q := continuantDenPrev a n + t * continuantDen a n)
          (r := continuantNum a n) (s := continuantDen a n)
          (m := n + 1) hqsemi hqcur hdet hsemi_lt_cur
      exact noSmallDenominatorBetween_of_left_farey hqsemi hqcur hfarey
        ⟨hsemi_lt_α, hα_lt_cur⟩
    · have hcur_lt_semi :
          ratValue (continuantNum a n) (continuantDen a n) <
            ratValue
              (continuantNumPrev a n + t * continuantNum a n)
              (continuantDenPrev a n + t * continuantDen a n) :=
        lt_trans hcur_lt_α hα_lt_semi
      have hfarey :
          continuantDen a n *
              (continuantNumPrev a n + t * continuantNum a n) =
            continuantNum a n *
              (continuantDenPrev a n + t * continuantDen a n) + 1 :=
        right_farey_of_det_and_lt
          (p := continuantNumPrev a n + t * continuantNum a n)
          (q := continuantDenPrev a n + t * continuantDen a n)
          (r := continuantNum a n) (s := continuantDen a n)
          (m := n + 1) hqsemi hqcur hdet hcur_lt_semi
      exact noSmallDenominatorBetween_of_right_farey hqsemi hqcur hfarey
        ⟨hcur_lt_α, hα_lt_semi⟩

/-- Lemma 3.7: convergents and semiconvergents give floor agreement below
their denominator. -/
theorem convergent_or_semiconvergent_floor_agreement {α : ℝ} {p q : ℕ}
    (hirr : IsIrrational α)
    (hcf : IsConvergentOrSemiconvergent α p q)
    (hred : ReducedFraction p q) :
    FloorAgreement α p q := by
  rcases hcf with ⟨a, hsimple, hkind⟩
  have hαpos : 0 < α := by
    rcases hsimple with ⟨hpos, _, htails⟩
    rcases htails 0 with ⟨β, hβgt, _, hα⟩
    have hβpos : 0 < β := by
      have ha1pos : (0 : ℝ) < a 1 := by exact_mod_cast hpos 0
      linarith
    have hnumpos : 0 < β * (a 0 : ℝ) + 1 := by positivity
    rw [hα]
    simpa [continuantNum, continuantNumPrev,
      continuantDen, continuantDenPrev] using div_pos hnumpos hβpos
  exact floor_agreement_of_no_small_denominator hαpos hirr hred
    (convergent_or_semiconvergent_no_small_denominator hαpos hirr
      ⟨a, hsimple, hkind⟩ hred)

/-- Lemma 3.8: floor agreement excludes smaller-denominator rationals between
`α` and `p / q`. -/
theorem floor_agreement_no_small_denominator {α : ℝ} {p q : ℕ}
    (hirr : IsIrrational α)
    (hq : 2 ≤ q)
    (hred : ReducedFraction p q)
    (hagrees : FloorAgreement α p q) :
    NoSmallDenominatorBetween α p q := by
  have _ : IsIrrational α := hirr
  have _ : 2 ≤ q := hq
  intro a b hbpos hbq hbetween
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hqpos : 0 < q := hred.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hb_one : 1 ≤ b := by omega
  have hb_le_qpred : b ≤ q - 1 := by omega
  have hagree := hagrees b hb_one hb_le_qpred
  rcases hbetween with ⟨hα_lt_ab, hab_lt_pq⟩ | ⟨hpq_lt_ab, hab_lt_α⟩
  · have h_floor_alpha_lt_a : Int.floor ((b : ℝ) * α) < (a : ℤ) := by
      rw [Int.floor_lt]
      have hba_lt_a : (b : ℝ) * α < (a : ℝ) := by
        have h := hα_lt_ab
        unfold ratValue at h
        have hmul := mul_lt_mul_of_pos_left h hbR
        field_simp [ne_of_gt hbR] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact hba_lt_a
    have h_a_le_floor_rat :
        (a : ℤ) ≤ Int.floor (((b : ℝ) * (p : ℝ)) / (q : ℝ)) := by
      rw [Int.le_floor]
      have ha_lt_bpq : (a : ℝ) < ((b : ℝ) * (p : ℝ)) / (q : ℝ) := by
        have h := hab_lt_pq
        unfold ratValue at h
        have hmul := mul_lt_mul_of_pos_left h hbR
        field_simp [ne_of_gt hbR] at hmul
        exact (lt_div_iff₀ hqR).mpr
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      exact le_of_lt ha_lt_bpq
    rw [hagree] at h_floor_alpha_lt_a
    omega
  · have h_floor_rat_lt_a :
        Int.floor (((b : ℝ) * (p : ℝ)) / (q : ℝ)) < (a : ℤ) := by
      rw [Int.floor_lt]
      have hbpq_lt_a : ((b : ℝ) * (p : ℝ)) / (q : ℝ) < (a : ℝ) := by
        have h := hpq_lt_ab
        unfold ratValue at h
        have hmul := mul_lt_mul_of_pos_left h hbR
        field_simp [ne_of_gt hbR] at hmul
        exact (div_lt_iff₀ hqR).mpr
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      exact hbpq_lt_a
    have h_a_le_floor_alpha : (a : ℤ) ≤ Int.floor ((b : ℝ) * α) := by
      rw [Int.le_floor]
      have ha_lt_balpha : (a : ℝ) < (b : ℝ) * α := by
        have h := hab_lt_α
        unfold ratValue at h
        have hmul := mul_lt_mul_of_pos_left h hbR
        field_simp [ne_of_gt hbR] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact le_of_lt ha_lt_balpha
    rw [← hagree] at h_floor_rat_lt_a
    omega

private theorem floorMul_add_fracMul (α : ℝ) (q : ℕ) :
    (floorMul α q : ℝ) + fracMul α q = (q : ℝ) * α := by
  unfold floorMul fracMul
  simp [add_comm, Int.fract_add_floor]

private theorem fracMul_pos_of_irrational {α : ℝ} (hirr : IsIrrational α)
    {q : ℕ} (hq : 0 < q) :
    0 < fracMul α q := by
  have hnonneg : 0 ≤ fracMul α q := by
    unfold fracMul
    exact Int.fract_nonneg _
  have hne : fracMul α q ≠ 0 := by
    intro hzero
    have hx : (q : ℝ) * α =
        (Int.floor ((q : ℝ) * α) : ℝ) := by
      have h := Int.fract_add_floor ((q : ℝ) * α)
      unfold fracMul at hzero
      rw [hzero, zero_add] at h
      exact h.symm
    exact mul_irrational_not_int hirr hq
      (Int.floor ((q : ℝ) * α)) hx
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

private theorem floorMul_nonneg_of_pos {α : ℝ} (hαpos : 0 < α)
    {q : ℕ} (hq : 0 < q) :
    0 ≤ floorMul α q := by
  unfold floorMul
  rw [Int.floor_nonneg]
  positivity

private theorem odd_toNat_of_nonneg {z : ℤ} (hz0 : 0 ≤ z)
    (hodd : Odd z) :
    Odd z.toNat := by
  rcases hodd with ⟨m, hm⟩
  have hm0 : 0 ≤ m := by omega
  refine ⟨m.toNat, ?_⟩
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hz0, hm]
  have hmcast : (m.toNat : ℤ) = m := by
    rw [Int.toNat_of_nonneg hm0]
  rw [← hmcast]
  norm_num

private theorem odd_succ_toNat_of_even_nonneg {z : ℤ} (hz0 : 0 ≤ z)
    (heven : Even z) :
    Odd (z + 1).toNat := by
  rcases heven with ⟨m, hm⟩
  have hm0 : 0 ≤ m := by omega
  have hz10 : 0 ≤ z + 1 := by omega
  refine ⟨m.toNat, ?_⟩
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hz10, hm]
  have hmcast : (m.toNat : ℤ) = m := by
    rw [Int.toNat_of_nonneg hm0]
  rw [← hmcast]
  norm_num
  ring

private theorem noSmallDenominatorBetween_of_lowerRecord_floor
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α)
    {q : ℕ} (hq : 0 < q) (hlower : IsLowerRecord α q) :
    NoSmallDenominatorBetween α (floorMul α q).toNat q := by
  intro a b hbpos hbq hbetween
  let p : ℕ := (floorMul α q).toNat
  change StrictBetween α (ratValue a b) (ratValue p q) at hbetween
  let θ : ℝ := fracMul α q
  have hz0 : 0 ≤ floorMul α q := floorMul_nonneg_of_pos hαpos hq
  have hp_cast : (p : ℝ) = (floorMul α q : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz0)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact fracMul_pos_of_irrational hirr hq
  have hθlt1 : θ < 1 := by
    dsimp [θ, fracMul]
    exact Int.fract_lt_one _
  have hqα : (q : ℝ) * α = (p : ℝ) + θ := by
    dsimp [p, θ]
    rw [hp_cast]
    exact (floorMul_add_fracMul α q).symm
  have hpq_lt_α : ratValue p q < α := by
    unfold ratValue
    rw [div_lt_iff₀ hqR]
    nlinarith [hqα, hθpos]
  rcases hbetween with ⟨hα_lt_ab, hab_lt_pq⟩ | ⟨hpq_lt_ab, hab_lt_α⟩
  · have : α < α := lt_trans hα_lt_ab (lt_trans hab_lt_pq hpq_lt_α)
    exact (lt_irrefl α) this
  · have hbp_lt_aq_R : (b : ℝ) * (p : ℝ) < (a : ℝ) * (q : ℝ) := by
      unfold ratValue at hpq_lt_ab
      rw [div_lt_div_iff₀ hqR hbR] at hpq_lt_ab
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpq_lt_ab
    have hbp_lt_aq_N : b * p < a * q := by
      exact_mod_cast hbp_lt_aq_R
    have hgapN : b * p + 1 ≤ a * q := Nat.succ_le_of_lt hbp_lt_aq_N
    have hgapR : (b : ℝ) * (p : ℝ) + 1 ≤ (a : ℝ) * (q : ℝ) := by
      exact_mod_cast hgapN
    have ha_lt_bα : (a : ℝ) < (b : ℝ) * α := by
      unfold ratValue at hab_lt_α
      have h := (div_lt_iff₀ hbR).mp hab_lt_α
      nlinarith
    have hdelta_pos : 0 < (b : ℝ) * α - (a : ℝ) := by
      linarith
    have hdelta_lt_θ : (b : ℝ) * α - (a : ℝ) < θ := by
      have hb_lt_q_R : (b : ℝ) < (q : ℝ) := by exact_mod_cast hbq
      have hscaled_lt :
          (q : ℝ) * ((b : ℝ) * α - (a : ℝ)) < (q : ℝ) * θ := by
        nlinarith
      nlinarith [hqR]
    have hbα_lt_a1 : (b : ℝ) * α < (a : ℝ) + 1 := by
      linarith
    have hfloor_b : Int.floor ((b : ℝ) * α) = (a : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    have hfrac_b : fracMul α b = (b : ℝ) * α - (a : ℝ) := by
      unfold fracMul
      have h := Int.self_sub_floor ((b : ℝ) * α)
      rw [hfloor_b] at h
      exact h.symm
    have hrec := hlower.2 b hbpos hbq
    change θ < fracMul α b at hrec
    rw [hfrac_b] at hrec
    linarith

private theorem noSmallDenominatorBetween_of_upperRecord_ceil
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α)
    {q : ℕ} (hq : 0 < q) (hupper : IsUpperRecord α q) :
    NoSmallDenominatorBetween α (floorMul α q + 1).toNat q := by
  intro a b hbpos hbq hbetween
  let p : ℕ := (floorMul α q + 1).toNat
  change StrictBetween α (ratValue a b) (ratValue p q) at hbetween
  let θ : ℝ := fracMul α q
  have hz0 : 0 ≤ floorMul α q := floorMul_nonneg_of_pos hαpos hq
  have hz10 : 0 ≤ floorMul α q + 1 := by omega
  have hp_cast : (p : ℝ) = (floorMul α q + 1 : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz10)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact fracMul_pos_of_irrational hirr hq
  have hθlt1 : θ < 1 := by
    dsimp [θ, fracMul]
    exact Int.fract_lt_one _
  have hqα : (q : ℝ) * α = (p : ℝ) - 1 + θ := by
    dsimp [p, θ]
    rw [hp_cast]
    have h := (floorMul_add_fracMul α q).symm
    norm_num at h ⊢
    linarith
  have hα_lt_pq : α < ratValue p q := by
    unfold ratValue
    rw [lt_div_iff₀ hqR]
    nlinarith [hqα, hθlt1]
  rcases hbetween with ⟨hα_lt_ab, hab_lt_pq⟩ | ⟨hpq_lt_ab, hab_lt_α⟩
  · have haq_lt_bp_R : (a : ℝ) * (q : ℝ) < (b : ℝ) * (p : ℝ) := by
      unfold ratValue at hab_lt_pq
      rw [div_lt_div_iff₀ hbR hqR] at hab_lt_pq
      simpa [mul_comm, mul_left_comm, mul_assoc] using hab_lt_pq
    have haq_lt_bp_N : a * q < b * p := by
      exact_mod_cast haq_lt_bp_R
    have hgapN : a * q + 1 ≤ b * p := Nat.succ_le_of_lt haq_lt_bp_N
    have hgapR : (a : ℝ) * (q : ℝ) + 1 ≤ (b : ℝ) * (p : ℝ) := by
      exact_mod_cast hgapN
    have hbα_lt_a : (b : ℝ) * α < (a : ℝ) := by
      unfold ratValue at hα_lt_ab
      have h := (lt_div_iff₀ hbR).mp hα_lt_ab
      nlinarith
    have hdelta_pos : 0 < (a : ℝ) - (b : ℝ) * α := by
      linarith
    have hdelta_lt_one_sub_θ :
        (a : ℝ) - (b : ℝ) * α < 1 - θ := by
      have hb_lt_q_R : (b : ℝ) < (q : ℝ) := by exact_mod_cast hbq
      have hscaled_lt :
          (q : ℝ) * ((a : ℝ) - (b : ℝ) * α) <
            (q : ℝ) * (1 - θ) := by
        nlinarith
      nlinarith [hqR]
    have hdelta_lt_one : (a : ℝ) - (b : ℝ) * α < 1 := by
      linarith
    have hfloor_b : Int.floor ((b : ℝ) * α) = (a : ℤ) - 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    have hfrac_b :
        fracMul α b = 1 - ((a : ℝ) - (b : ℝ) * α) := by
      unfold fracMul
      have h := Int.self_sub_floor ((b : ℝ) * α)
      rw [hfloor_b] at h
      rw [← h]
      norm_num
      ring
    have hrec := hupper.2 b hbpos hbq
    change fracMul α b < θ at hrec
    rw [hfrac_b] at hrec
    linarith
  · have : α < α := lt_trans hα_lt_pq (lt_trans hpq_lt_ab hab_lt_α)
    exact (lt_irrefl α) this

private theorem coprime_floorMul_of_lowerRecord
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α)
    {q : ℕ} (hq : 0 < q) (hlower : IsLowerRecord α q) :
    Nat.Coprime (floorMul α q).toNat q := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨ℓ, hℓprime, hℓp, hℓq⟩
  let p : ℕ := (floorMul α q).toNat
  let θ : ℝ := fracMul α q
  let k : ℕ := q / ℓ
  let c : ℕ := p / ℓ
  have hℓpos : 0 < ℓ := hℓprime.pos
  have hℓone : 1 < ℓ := hℓprime.one_lt
  have hℓq' : ℓ ∣ q := hℓq
  have hℓp' : ℓ ∣ p := by simpa [p] using hℓp
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.div_pos (Nat.le_of_dvd hq hℓq') hℓpos
  have hklt : k < q := by
    dsimp [k]
    exact Nat.div_lt_self hq hℓone
  have hz0 : 0 ≤ floorMul α q := floorMul_nonneg_of_pos hαpos hq
  have hp_cast : (p : ℝ) = (floorMul α q : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz0)
  have hq_eq : k * ℓ = q := by
    dsimp [k]
    exact Nat.div_mul_cancel hℓq'
  have hp_eq : c * ℓ = p := by
    dsimp [c]
    exact Nat.div_mul_cancel hℓp'
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact fracMul_pos_of_irrational hirr hq
  have hθlt1 : θ < 1 := by
    dsimp [θ, fracMul]
    exact Int.fract_lt_one _
  have hqα : (q : ℝ) * α = (p : ℝ) + θ := by
    dsimp [p, θ]
    rw [hp_cast]
    exact (floorMul_add_fracMul α q).symm
  have hkα : (k : ℝ) * α = (c : ℝ) + θ / (ℓ : ℝ) := by
    have hscaled :
        (ℓ : ℝ) * ((k : ℝ) * α) =
          (ℓ : ℝ) * ((c : ℝ) + θ / (ℓ : ℝ)) := by
      rw [mul_add, mul_div_cancel₀ θ (ne_of_gt hℓR)]
      have hleft : (ℓ : ℝ) * ((k : ℝ) * α) = (q : ℝ) * α := by
        rw [← hq_eq]
        norm_num
        ring
      have hright : (ℓ : ℝ) * (c : ℝ) + θ = (p : ℝ) + θ := by
        rw [← hp_eq]
        norm_num
        ring
      rw [hleft, hright, hqα]
    exact mul_left_cancel₀ (ne_of_gt hℓR) hscaled
  have hθdiv_nonneg : 0 ≤ θ / (ℓ : ℝ) := by positivity
  have hθdiv_lt_one : θ / (ℓ : ℝ) < 1 := by
    have hθ_lt_ℓ : θ < (ℓ : ℝ) := by
      have hle : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓone.le
      linarith
    exact (div_lt_one hℓR).mpr hθ_lt_ℓ
  have hfrac_k : fracMul α k = θ / (ℓ : ℝ) := by
    unfold fracMul
    rw [hkα, add_comm]
    rw [Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨hθdiv_nonneg, hθdiv_lt_one⟩
  have hθdiv_lt_θ : θ / (ℓ : ℝ) < θ := by
    have hℓRone : (1 : ℝ) < ℓ := by exact_mod_cast hℓone
    rw [div_lt_iff₀ hℓR]
    nlinarith
  have hrec := hlower.2 k hkpos hklt
  change θ < fracMul α k at hrec
  rw [hfrac_k] at hrec
  linarith

private theorem coprime_floorMul_succ_of_upperRecord
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α)
    {q : ℕ} (hq : 0 < q) (hupper : IsUpperRecord α q) :
    Nat.Coprime (floorMul α q + 1).toNat q := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨ℓ, hℓprime, hℓp, hℓq⟩
  let p : ℕ := (floorMul α q + 1).toNat
  let θ : ℝ := fracMul α q
  let k : ℕ := q / ℓ
  let c : ℕ := p / ℓ
  have hℓpos : 0 < ℓ := hℓprime.pos
  have hℓone : 1 < ℓ := hℓprime.one_lt
  have hℓq' : ℓ ∣ q := hℓq
  have hℓp' : ℓ ∣ p := by simpa [p] using hℓp
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.div_pos (Nat.le_of_dvd hq hℓq') hℓpos
  have hklt : k < q := by
    dsimp [k]
    exact Nat.div_lt_self hq hℓone
  have hz0 : 0 ≤ floorMul α q := floorMul_nonneg_of_pos hαpos hq
  have hz10 : 0 ≤ floorMul α q + 1 := by omega
  have hpZpos : 0 < floorMul α q + 1 := by omega
  have hp_pos : 0 < p := by
    dsimp [p]
    apply Nat.pos_of_ne_zero
    intro hp0
    have hle := Int.toNat_eq_zero.mp hp0
    omega
  have hp_cast : (p : ℝ) = (floorMul α q + 1 : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz10)
  have hq_eq : k * ℓ = q := by
    dsimp [k]
    exact Nat.div_mul_cancel hℓq'
  have hp_eq : c * ℓ = p := by
    dsimp [c]
    exact Nat.div_mul_cancel hℓp'
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    have hp_zero : p = 0 := by
      rw [← hp_eq, hc0]
      simp
    omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact fracMul_pos_of_irrational hirr hq
  have hθlt1 : θ < 1 := by
    dsimp [θ, fracMul]
    exact Int.fract_lt_one _
  have hqα : (q : ℝ) * α = (p : ℝ) - 1 + θ := by
    dsimp [p, θ]
    rw [hp_cast]
    have h := (floorMul_add_fracMul α q).symm
    norm_num at h ⊢
    linarith
  have hkα : (k : ℝ) * α = (c : ℝ) - (1 - θ) / (ℓ : ℝ) := by
    have hscaled :
        (ℓ : ℝ) * ((k : ℝ) * α) =
          (ℓ : ℝ) * ((c : ℝ) - (1 - θ) / (ℓ : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ (1 - θ) (ne_of_gt hℓR)]
      have hleft : (ℓ : ℝ) * ((k : ℝ) * α) = (q : ℝ) * α := by
        rw [← hq_eq]
        norm_num
        ring
      have hright : (ℓ : ℝ) * (c : ℝ) - (1 - θ) =
          (p : ℝ) - 1 + θ := by
        rw [← hp_eq]
        norm_num
        ring
      rw [hleft, hright, hqα]
    exact mul_left_cancel₀ (ne_of_gt hℓR) hscaled
  have hc_cast : (c : ℝ) = ((c - 1 : ℕ) : ℝ) + 1 := by
    have hc_eq : c = (c - 1) + 1 := by omega
    conv_lhs => rw [hc_eq]
    norm_num
  have hkα' :
      (k : ℝ) * α =
        ((c - 1 : ℕ) : ℝ) + (1 - (1 - θ) / (ℓ : ℝ)) := by
    rw [hkα, hc_cast]
    ring
  have hδpos : 0 < (1 - θ) / (ℓ : ℝ) := by positivity
  have hδlt1 : (1 - θ) / (ℓ : ℝ) < 1 := by
    have hδnum_lt_ℓ : 1 - θ < (ℓ : ℝ) := by
      have hle : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓone.le
      linarith
    exact (div_lt_one hℓR).mpr hδnum_lt_ℓ
  have hγ_nonneg : 0 ≤ 1 - (1 - θ) / (ℓ : ℝ) := by linarith
  have hγ_lt_one : 1 - (1 - θ) / (ℓ : ℝ) < 1 := by linarith
  have hfrac_k :
      fracMul α k = 1 - (1 - θ) / (ℓ : ℝ) := by
    unfold fracMul
    rw [hkα', add_comm]
    rw [Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨hγ_nonneg, hγ_lt_one⟩
  have hδ_lt_one_sub_θ : (1 - θ) / (ℓ : ℝ) < 1 - θ := by
    have hℓRone : (1 : ℝ) < ℓ := by exact_mod_cast hℓone
    rw [div_lt_iff₀ hℓR]
    nlinarith
  have hθ_lt_γ : θ < 1 - (1 - θ) / (ℓ : ℝ) := by
    linarith
  have hrec := hupper.2 k hkpos hklt
  change fracMul α k < θ at hrec
  rw [hfrac_k] at hrec
  linarith

private theorem irrational_ne_int {x : ℝ} (hx : IsIrrational x) (z : ℤ) :
    x ≠ (z : ℝ) := by
  intro h
  exact hx ⟨(z : ℚ), by simp [h]⟩

private theorem fract_irrational_of_irrational {x : ℝ}
    (hx : IsIrrational x) : IsIrrational (Int.fract x) := by
  intro hrat
  rcases hrat with ⟨q, hq⟩
  apply hx
  refine ⟨q + (Int.floor x : ℚ), ?_⟩
  change ((q + (Int.floor x : ℚ) : ℚ) : ℝ) = x
  rw [Rat.cast_add, hq]
  exact Int.fract_add_floor x

private theorem inv_irrational_of_irrational {x : ℝ}
    (hx : IsIrrational x) : IsIrrational (1 / x) := by
  intro hrat
  rcases hrat with ⟨q, hq⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    exact hx ⟨0, by simp [hxzero]⟩
  apply hx
  refine ⟨q⁻¹, ?_⟩
  rw [Rat.cast_inv, hq]
  field_simp [hx0]

private theorem fract_pos_of_irrational {x : ℝ} (hx : IsIrrational x) :
    0 < Int.fract x := by
  rw [Int.fract_pos]
  exact irrational_ne_int hx (Int.floor x)

private theorem completeQuotient_irrational
    {α : ℝ}
    (hirr : IsIrrational α) :
    ∀ n : ℕ, IsIrrational (completeQuotient α n) := by
  intro n
  induction n with
  | zero => exact hirr
  | succ n ih =>
      change IsIrrational (1 / Int.fract (completeQuotient α n))
      exact inv_irrational_of_irrational (fract_irrational_of_irrational ih)

private theorem completeQuotient_pos
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α) :
    ∀ n : ℕ, 0 < completeQuotient α n := by
  intro n
  induction n with
  | zero => exact hαpos
  | succ n _ =>
      change 0 < 1 / Int.fract (completeQuotient α n)
      exact one_div_pos.mpr
        (fract_pos_of_irrational ((completeQuotient_irrational hirr) n))

private theorem one_lt_completeQuotient_succ
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    1 < completeQuotient α (n + 1) := by
  have _ : 0 < completeQuotient α n := completeQuotient_pos hαpos hirr n
  change 1 < 1 / Int.fract (completeQuotient α n)
  exact one_lt_one_div
    (fract_pos_of_irrational ((completeQuotient_irrational hirr) n))
    (Int.fract_lt_one (completeQuotient α n))

private theorem simplePartialQuotient_intCast
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    (simplePartialQuotient α n : ℤ) =
      Int.floor (completeQuotient α n) := by
  unfold simplePartialQuotient
  have hfloor_nonneg : 0 ≤ Int.floor (completeQuotient α n) := by
    rw [Int.floor_nonneg]
    exact (completeQuotient_pos hαpos hirr n).le
  exact Int.toNat_of_nonneg hfloor_nonneg

private theorem simplePartialQuotient_realCast
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    (simplePartialQuotient α n : ℝ) =
      (Int.floor (completeQuotient α n) : ℝ) := by
  exact_mod_cast simplePartialQuotient_intCast hαpos hirr n

private theorem completeQuotient_eq_coeff_add_inv_succ
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    completeQuotient α n =
      (simplePartialQuotient α n : ℝ) +
        1 / completeQuotient α (n + 1) := by
  have hfloorR :
      (simplePartialQuotient α n : ℝ) =
        (Int.floor (completeQuotient α n) : ℝ) :=
    simplePartialQuotient_realCast hαpos hirr n
  calc
    completeQuotient α n =
        Int.fract (completeQuotient α n) +
          (Int.floor (completeQuotient α n) : ℝ) := by
      exact (Int.fract_add_floor (completeQuotient α n)).symm
    _ = (simplePartialQuotient α n : ℝ) +
          1 / completeQuotient α (n + 1) := by
      rw [hfloorR]
      simp [completeQuotient, add_comm]

private theorem simplePartialQuotient_succ_pos
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    0 < simplePartialQuotient α (n + 1) := by
  unfold simplePartialQuotient
  rw [Int.lt_toNat]
  have hfloor_ge_one :
      (1 : ℤ) ≤ Int.floor (completeQuotient α (n + 1)) := by
    rw [Int.le_floor]
    norm_num
    exact (one_lt_completeQuotient_succ hαpos hirr n).le
  omega

private theorem completeQuotient_succ_between
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (n : ℕ) :
    (simplePartialQuotient α (n + 1) : ℝ) <
        completeQuotient α (n + 1) ∧
      completeQuotient α (n + 1) <
        (simplePartialQuotient α (n + 1) : ℝ) + 1 := by
  have hfloorR :
      (simplePartialQuotient α (n + 1) : ℝ) =
        (Int.floor (completeQuotient α (n + 1)) : ℝ) :=
    simplePartialQuotient_realCast hαpos hirr (n + 1)
  have hnot_int :
      completeQuotient α (n + 1) ≠
        (Int.floor (completeQuotient α (n + 1)) : ℝ) :=
    irrational_ne_int ((completeQuotient_irrational hirr) (n + 1))
      (Int.floor (completeQuotient α (n + 1)))
  constructor
  · rw [hfloorR]
    exact lt_of_le_of_ne (Int.floor_le _) hnot_int.symm
  · rw [hfloorR]
    exact Int.lt_floor_add_one _

private theorem alpha_eq_finiteCFWithTail_completeQuotient
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α) :
    ∀ n : ℕ,
      α =
        finiteCFWithTail
          (simplePartialQuotient α)
          n
          (completeQuotient α (n + 1)) := by
  intro n
  induction n with
  | zero =>
      simpa [finiteCFWithTail]
        using completeQuotient_eq_coeff_add_inv_succ hαpos hirr 0
  | succ n ih =>
      rw [finiteCFWithTail]
      rw [← completeQuotient_eq_coeff_add_inv_succ hαpos hirr (n + 1)]
      exact ih

private theorem hasContinuedFractionTails_simplePartialQuotient
    {α : ℝ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α) :
    HasContinuedFractionTails α (simplePartialQuotient α) := by
  intro n
  refine ⟨completeQuotient α (n + 1), ?_, ?_, ?_⟩
  · exact (completeQuotient_succ_between hαpos hirr n).1
  · exact (completeQuotient_succ_between hαpos hirr n).2
  · calc
      α =
          finiteCFWithTail
            (simplePartialQuotient α) n
            (completeQuotient α (n + 1)) :=
        alpha_eq_finiteCFWithTail_completeQuotient hαpos hirr n
      _ =
          (completeQuotient α (n + 1) *
                (continuantNum (simplePartialQuotient α) n : ℝ) +
              (continuantNumPrev (simplePartialQuotient α) n : ℝ)) /
            (completeQuotient α (n + 1) *
                (continuantDen (simplePartialQuotient α) n : ℝ) +
              (continuantDenPrev (simplePartialQuotient α) n : ℝ)) := by
        simpa [commonPrefixMap] using
          finiteCFWithTail_eq_commonPrefixMap (simplePartialQuotient α) n
            (completeQuotient_pos hαpos hirr (n + 1))

private theorem continuantDen_le_succ_of_partials
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ n : ℕ, continuantDen a n ≤ continuantDen a (n + 1)
  | 0 => by
      simpa [continuantDen] using hpos 0
  | n + 1 => by
      rw [continuantDen]
      have hmul :
          continuantDen a (n + 1) ≤
            a (n + 2) * continuantDen a (n + 1) :=
        Nat.le_mul_of_pos_left (continuantDen a (n + 1)) (hpos (n + 1))
      exact le_trans hmul (Nat.le_add_right _ _)

private theorem continuantDen_mono_of_partials
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Monotone (continuantDen a) :=
  monotone_nat_of_le_succ (continuantDen_le_succ_of_partials hpos)

private theorem succ_le_continuantDen_two_mul
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    ∀ k : ℕ, k + 1 ≤ continuantDen a (2 * k)
  | 0 => by
      simp [continuantDen]
  | k + 1 => by
      have ih := succ_le_continuantDen_two_mul hpos k
      have hprod_pos :
          0 <
            a (2 * k + 2) * continuantDen a (2 * k + 1) := by
        exact Nat.mul_pos (hpos (2 * k + 1))
          (continuantDen_pos_of_partials a hpos (2 * k + 1))
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, continuantDen]
      omega

private theorem continuantDen_tendsto_atTop
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto (continuantDen a) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b, ?_⟩
  intro n hn
  have hmono :
      continuantDen a (2 * b) ≤ continuantDen a n :=
    continuantDen_mono_of_partials hpos hn
  have hlower : b + 1 ≤ continuantDen a (2 * b) :=
    succ_le_continuantDen_two_mul hpos b
  exact le_trans (Nat.le_succ b) (le_trans hlower hmono)

private theorem convergent_error_le_inv_sq
    {α : ℝ} {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (htails : HasContinuedFractionTails α a)
    (n : ℕ) :
    |α - (continuantNum a n : ℝ) / (continuantDen a n : ℝ)| ≤
      1 / (continuantDen a n : ℝ) ^ 2 := by
  rcases htails n with ⟨β, hβgt, _, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  have hqnNat : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hqnpos : 0 < qn := by
    dsimp [qn]
    exact_mod_cast hqnNat
  have hqnnonnneg : 0 ≤ qn := hqnpos.le
  have htail_one : (1 : ℝ) ≤ a (n + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hpos n))
  have hβ_gt_one : (1 : ℝ) < β := lt_of_le_of_lt htail_one hβgt
  have hβpos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hdenpos : 0 < β * qn + qpn := by
    dsimp [qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hdenmulpos : 0 < (β * qn + qpn) * qn :=
    mul_pos hdenpos hqnpos
  have hdetR :
      pn * qpn - ppn * qn =
        ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hnum_abs : |ppn * qn - pn * qpn| = 1 := by
    have hneg : ppn * qn - pn * qpn = -(pn * qpn - ppn * qn) := by
      ring
    rw [hneg, hdetR, abs_neg]
    norm_num
  have hdiff :
      α - pn / qn =
        (ppn * qn - pn * qpn) / ((β * qn + qpn) * qn) := by
    have hα' : α = (β * pn + ppn) / (β * qn + qpn) := by
      simpa [pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos, ne_of_gt hqnpos]
    ring
  have hqpn_nonneg : 0 ≤ qpn := by
    dsimp [qpn]
    positivity
  have hβq_ge_q : qn ≤ β * qn := by
    calc
      qn = 1 * qn := by ring
      _ ≤ β * qn := mul_le_mul_of_nonneg_right hβ_gt_one.le hqnnonnneg
  have hden_ge_q : qn ≤ β * qn + qpn :=
    le_trans hβq_ge_q (le_add_of_nonneg_right hqpn_nonneg)
  have hsq_le_denmul : qn ^ 2 ≤ (β * qn + qpn) * qn := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hden_ge_q hqnnonnneg
  have hsqpos : 0 < qn ^ 2 := pow_pos hqnpos 2
  change |α - pn / qn| ≤ 1 / qn ^ 2
  calc
    |α - pn / qn| =
        |(ppn * qn - pn * qpn) / ((β * qn + qpn) * qn)| := by
      rw [hdiff]
    _ = 1 / ((β * qn + qpn) * qn) := by
      rw [abs_div, hnum_abs, abs_of_pos hdenmulpos]
    _ ≤ 1 / qn ^ 2 :=
      one_div_le_one_div_of_le hsqpos hsq_le_denmul

/-- Sharper standard error estimate for a continued-fraction convergent:
`|α - pₙ / qₙ| < 1 / (qₙ qₙ₊₁)`. -/
theorem convergent_error_lt_inv_mul_q_qsucc
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    |α -
        (continuantNum a n : ℝ) /
          (continuantDen a n : ℝ)| <
      1 /
        ((continuantDen a n : ℝ) *
          (continuantDen a (n + 1) : ℝ)) := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails n with ⟨β, hβgt, _, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let qnext : ℝ := continuantDen a (n + 1)
  have hqnNat : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hqnpos : 0 < qn := by
    dsimp [qn]
    exact_mod_cast hqnNat
  have hqnextNat : 0 < continuantDen a (n + 1) :=
    continuantDen_pos_of_partials a hpos (n + 1)
  have hqnextpos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast hqnextNat
  have htail_one : (1 : ℝ) ≤ a (n + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hpos n))
  have hβ_gt_one : (1 : ℝ) < β := lt_of_le_of_lt htail_one hβgt
  have hβpos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hdenpos : 0 < β * qn + qpn := by
    dsimp [qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hdenmulpos : 0 < (β * qn + qpn) * qn :=
    mul_pos hdenpos hqnpos
  have hdetR :
      pn * qpn - ppn * qn =
        ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hnum_abs : |ppn * qn - pn * qpn| = 1 := by
    have hneg : ppn * qn - pn * qpn = -(pn * qpn - ppn * qn) := by
      ring
    rw [hneg, hdetR, abs_neg]
    norm_num
  have hdiff :
      α - pn / qn =
        (ppn * qn - pn * qpn) / ((β * qn + qpn) * qn) := by
    have hα' : α = (β * pn + ppn) / (β * qn + qpn) := by
      simpa [pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos, ne_of_gt hqnpos]
    ring
  have hqnext_eq :
      qnext = (a (n + 1) : ℝ) * qn + qpn := by
    dsimp [qnext, qn, qpn]
    rw [continuantDen_succ]
    norm_num
  have hqnext_lt_den : qnext < β * qn + qpn := by
    rw [hqnext_eq]
    have hmul : (a (n + 1) : ℝ) * qn < β * qn :=
      mul_lt_mul_of_pos_right hβgt hqnpos
    linarith
  have htargetpos : 0 < qn * qnext := mul_pos hqnpos hqnextpos
  have htarget_lt_actual : qn * qnext < (β * qn + qpn) * qn := by
    have hmul := mul_lt_mul_of_pos_right hqnext_lt_den hqnpos
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  change |α - pn / qn| < 1 / (qn * qnext)
  calc
    |α - pn / qn| =
        |(ppn * qn - pn * qpn) / ((β * qn + qpn) * qn)| := by
      rw [hdiff]
    _ = 1 / ((β * qn + qpn) * qn) := by
      rw [abs_div, hnum_abs, abs_of_pos hdenmulpos]
    _ < 1 / (qn * qnext) :=
      one_div_lt_one_div_of_lt htargetpos htarget_lt_actual

/-- Integer-form lower bound for the `n`-th convergent error:
`|qₙ α - pₙ| > 1 / (qₙ + qₙ₊₁)`. -/
theorem convergent_integer_error_gt_inv_sum_q_qsucc
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    |(continuantDen a n : ℝ) * α -
        (continuantNum a n : ℝ)| >
      1 /
        ((continuantDen a n : ℝ) +
          (continuantDen a (n + 1) : ℝ)) := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails n with ⟨β, _, hβlt, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let qnext : ℝ := continuantDen a (n + 1)
  have hqnNat : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hqnpos : 0 < qn := by
    dsimp [qn]
    exact_mod_cast hqnNat
  have htail_one : (1 : ℝ) ≤ a (n + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hpos n))
  have hβpos : 0 < β := by
    have hnonneg : (0 : ℝ) ≤ a (n + 1) := by positivity
    linarith
  have hdenpos : 0 < β * qn + qpn := by
    dsimp [qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hdetR :
      pn * qpn - ppn * qn =
        ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hnum_abs : |qn * ppn - pn * qpn| = 1 := by
    have hbase : |ppn * qn - pn * qpn| = 1 := by
      have hneg :
          ppn * qn - pn * qpn = -(pn * qpn - ppn * qn) := by
        ring
      rw [hneg, hdetR, abs_neg]
      norm_num
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hdiff :
      qn * α - pn =
        (qn * ppn - pn * qpn) / (β * qn + qpn) := by
    have hα' : α = (β * pn + ppn) / (β * qn + qpn) := by
      simpa [pn, ppn, qn, qpn] using hα
    have hdenpos' : 0 < qn * β + qpn := by
      simpa [mul_comm] using hdenpos
    rw [hα']
    field_simp [ne_of_gt hdenpos, ne_of_gt hdenpos']
    ring
  have hqnext_eq :
      qnext = (a (n + 1) : ℝ) * qn + qpn := by
    dsimp [qnext, qn, qpn]
    rw [continuantDen_succ]
    norm_num
  have hden_lt_target : β * qn + qpn < qn + qnext := by
    have hβq_lt : β * qn < ((a (n + 1) : ℝ) + 1) * qn :=
      mul_lt_mul_of_pos_right hβlt hqnpos
    calc
      β * qn + qpn < ((a (n + 1) : ℝ) + 1) * qn + qpn := by
        linarith
      _ = qn + qnext := by
        rw [hqnext_eq]
        ring
  change |qn * α - pn| > 1 / (qn + qnext)
  calc
    |qn * α - pn| =
        |(qn * ppn - pn * qpn) / (β * qn + qpn)| := by
      rw [hdiff]
    _ = 1 / (β * qn + qpn) := by
      rw [abs_div, hnum_abs, abs_of_pos hdenpos]
    _ > 1 / (qn + qnext) :=
      one_div_lt_one_div_of_lt hdenpos hden_lt_target

/-- A weaker but handier integer-form lower bound:
`|qₙ α - pₙ| > 1 / (2 qₙ₊₁)`. -/
theorem convergent_integer_error_gt_inv_two_qsucc
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    |(continuantDen a n : ℝ) * α -
        (continuantNum a n : ℝ)| >
      1 / (2 * (continuantDen a (n + 1) : ℝ)) := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  let qn : ℝ := continuantDen a n
  let qnext : ℝ := continuantDen a (n + 1)
  have hmain :
      |qn * α - (continuantNum a n : ℝ)| > 1 / (qn + qnext) := by
    simpa [qn, qnext] using
      convergent_integer_error_gt_inv_sum_q_qsucc hcf' n
  have hqnextNat : 0 < continuantDen a (n + 1) :=
    continuantDen_pos_of_partials a hpos (n + 1)
  have hqnextpos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast hqnextNat
  have hleNat : continuantDen a n ≤ continuantDen a (n + 1) :=
    continuantDen_le_succ_of_partials hpos n
  have hle : qn ≤ qnext := by
    dsimp [qn, qnext]
    exact_mod_cast hleNat
  have hsumpos : 0 < qn + qnext := by
    have hqn_nonneg : 0 ≤ qn := by positivity
    positivity
  have hsum_le_two : qn + qnext ≤ 2 * qnext := by
    linarith
  have hrecip : 1 / (2 * qnext) ≤ 1 / (qn + qnext) :=
    one_div_le_one_div_of_le hsumpos hsum_le_two
  change
    |qn * α - (continuantNum a n : ℝ)| >
      1 / (2 * qnext)
  linarith

/-- The current and previous convergent integer errors have opposite signs. -/
theorem convergent_error_mul_prev_error_lt_zero
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    ((continuantDen a n : ℝ) * α -
      (continuantNum a n : ℝ)) *
    ((continuantDenPrev a n : ℝ) * α -
      (continuantNumPrev a n : ℝ)) < 0 := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails n with ⟨β, hβgt, _, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let Δ : ℝ := pn * qpn - ppn * qn
  let D : ℝ := β * qn + qpn
  have htail_one : (1 : ℝ) ≤ a (n + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hpos n))
  have hβ_gt_one : (1 : ℝ) < β := lt_of_le_of_lt htail_one hβgt
  have hβpos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hdenpos : 0 < D := by
    dsimp [D, qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hdetR : Δ = ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [Δ, pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hΔne : Δ ≠ 0 := by
    rw [hdetR]
    norm_num
  have hcur : qn * α - pn = -Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  have hprev : qpn * α - ppn = β * Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  have hDsqpos : 0 < D ^ 2 := pow_pos hdenpos 2
  have hΔsqpos : 0 < Δ ^ 2 := sq_pos_of_ne_zero hΔne
  have hfrac_pos : 0 < β * Δ ^ 2 / D ^ 2 :=
    div_pos (mul_pos hβpos hΔsqpos) hDsqpos
  have hprod_eq :
      (-Δ / D) * (β * Δ / D) = -(β * Δ ^ 2 / D ^ 2) := by
    field_simp [ne_of_gt hdenpos]
  change (qn * α - pn) * (qpn * α - ppn) < 0
  calc
    (qn * α - pn) * (qpn * α - ppn)
        = (-Δ / D) * (β * Δ / D) := by
      rw [hcur, hprev]
    _ = -(β * Δ ^ 2 / D ^ 2) := hprod_eq
    _ < 0 := by
      linarith

/-- The current convergent integer error is strictly smaller in magnitude than
the previous convergent integer error. -/
theorem abs_convergent_error_lt_abs_prev_error
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    |(continuantDen a n : ℝ) * α -
      (continuantNum a n : ℝ)| <
    |(continuantDenPrev a n : ℝ) * α -
      (continuantNumPrev a n : ℝ)| := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails n with ⟨β, hβgt, _, hα⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let Δ : ℝ := pn * qpn - ppn * qn
  let D : ℝ := β * qn + qpn
  have htail_one : (1 : ℝ) ≤ a (n + 1) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (hpos n))
  have hβ_gt_one : (1 : ℝ) < β := lt_of_le_of_lt htail_one hβgt
  have hβpos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hdenpos : 0 < D := by
    dsimp [D, qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hdetR : Δ = ((-1 : ℤ) ^ (n + 1) : ℝ) := by
    dsimp [Δ, pn, ppn, qn, qpn]
    exact_mod_cast continuant_det a n
  have hΔabs : |Δ| = 1 := by
    rw [hdetR]
    norm_num
  have hcur : qn * α - pn = -Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  have hprev : qpn * α - ppn = β * Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  have hcur_abs : |qn * α - pn| = 1 / D := by
    rw [hcur, abs_div, abs_neg, hΔabs, abs_of_pos hdenpos]
  have hprev_abs : |qpn * α - ppn| = β / D := by
    rw [hprev, abs_div, abs_mul, abs_of_pos hβpos, hΔabs,
      abs_of_pos hdenpos]
    ring
  change |qn * α - pn| < |qpn * α - ppn|
  calc
    |qn * α - pn| = 1 / D := hcur_abs
    _ < β / D := div_lt_div_of_pos_right hβ_gt_one hdenpos
    _ = |qpn * α - ppn| := hprev_abs.symm

/-- Once the second-kind best-approximation inequality is available, the
standard rational lower bound between consecutive convergent denominators is
only algebra plus the convergent integer-error estimate. -/
theorem rational_approx_lower_bound_between_convergents_of_best
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (n q : ℕ) (p : ℤ)
    (hqpos : 0 < q)
    (hbest :
      |(q : ℝ) * α - (p : ℝ)| ≥
        |(continuantDen a n : ℝ) * α -
          (continuantNum a n : ℝ)|) :
    |α - (p : ℝ) / (q : ℝ)| ≥
      1 / (2 * (q : ℝ) * (continuantDen a (n + 1) : ℝ)) := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  let qnext : ℝ := continuantDen a (n + 1)
  have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hqnextNat : 0 < continuantDen a (n + 1) :=
    continuantDen_pos_of_partials a hpos (n + 1)
  have hqnextpos : 0 < qnext := by
    dsimp [qnext]
    exact_mod_cast hqnextNat
  have hconv :
      |(continuantDen a n : ℝ) * α -
        (continuantNum a n : ℝ)| >
      1 / (2 * qnext) := by
    simpa [qnext] using
      convergent_integer_error_gt_inv_two_qsucc hcf' n
  have hnum_lower :
      1 / (2 * qnext) < |(q : ℝ) * α - (p : ℝ)| :=
    lt_of_lt_of_le hconv hbest
  have hscaled :
      1 / (2 * qnext) / (q : ℝ) <
        |(q : ℝ) * α - (p : ℝ)| / (q : ℝ) :=
    div_lt_div_of_pos_right hnum_lower hqRpos
  have htarget :
      1 / (2 * qnext) / (q : ℝ) =
        1 / (2 * (q : ℝ) * qnext) := by
    field_simp [ne_of_gt hqRpos, ne_of_gt hqnextpos]
  have herror :
      |α - (p : ℝ) / (q : ℝ)| =
        |(q : ℝ) * α - (p : ℝ)| / (q : ℝ) := by
    have hdiff :
        α - (p : ℝ) / (q : ℝ) =
          ((q : ℝ) * α - (p : ℝ)) / (q : ℝ) := by
      field_simp [ne_of_gt hqRpos]
    rw [hdiff, abs_div, abs_of_pos hqRpos]
  change |α - (p : ℝ) / (q : ℝ)| ≥
      1 / (2 * (q : ℝ) * qnext)
  rw [herror]
  rw [← htarget]
  exact le_of_lt hscaled

/-- Exact relation between consecutive integer errors at the tail `β`:
`qₙ₋₁ α - pₙ₋₁ = -β (qₙ α - pₙ)`. -/
theorem prev_error_eq_neg_tail_mul_error
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a) (n : ℕ) :
    ∃ β : ℝ,
      (a (n + 1) : ℝ) < β ∧
        β < (a (n + 1) : ℝ) + 1 ∧
        ((continuantDenPrev a n : ℝ) * α -
          (continuantNumPrev a n : ℝ)) =
        -β *
          ((continuantDen a n : ℝ) * α -
            (continuantNum a n : ℝ)) := by
  rcases hcf with ⟨hpos, _, htails⟩
  rcases htails n with ⟨β, hβgt, hβlt, hα⟩
  refine ⟨β, hβgt, hβlt, ?_⟩
  let pn : ℝ := continuantNum a n
  let ppn : ℝ := continuantNumPrev a n
  let qn : ℝ := continuantDen a n
  let qpn : ℝ := continuantDenPrev a n
  let Δ : ℝ := pn * qpn - ppn * qn
  let D : ℝ := β * qn + qpn
  have hβpos : 0 < β := by
    have hanonneg : (0 : ℝ) ≤ a (n + 1) := by positivity
    linarith
  have hdenpos : 0 < D := by
    dsimp [D, qn, qpn]
    simpa using continuant_denominator_pos a n hβpos
  have hcur : qn * α - pn = -Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  have hprev : qpn * α - ppn = β * Δ / D := by
    have hα' : α = (β * pn + ppn) / D := by
      simpa [D, pn, ppn, qn, qpn] using hα
    rw [hα']
    field_simp [ne_of_gt hdenpos]
    ring
  change qpn * α - ppn = -β * (qn * α - pn)
  calc
    qpn * α - ppn = β * Δ / D := hprev
    _ = -β * (-Δ / D) := by
      field_simp [ne_of_gt hdenpos]
    _ = -β * (qn * α - pn) := by rw [hcur]

/-- Consecutive continuant vectors form a `ℤ`-basis of `ℤ²`. -/
theorem exists_convergent_zbasis_coeffs
    (a : ℕ → ℕ) (n : ℕ) (p q : ℤ) :
    ∃ r s : ℤ,
      p =
        r * (continuantNum a n : ℤ) +
          s * (continuantNumPrev a n : ℤ) ∧
      q =
        r * (continuantDen a n : ℤ) +
          s * (continuantDenPrev a n : ℤ) := by
  let pn : ℤ := continuantNum a n
  let ppn : ℤ := continuantNumPrev a n
  let qn : ℤ := continuantDen a n
  let qpn : ℤ := continuantDenPrev a n
  have hdet :
      pn * qpn - ppn * qn = (-1 : ℤ) ^ (n + 1) := by
    dsimp [pn, ppn, qn, qpn]
    exact continuant_det a n
  rcases neg_one_pow_eq_or ℤ (n + 1) with hpow | hpow
  · have hdet_one : pn * qpn - ppn * qn = 1 := by
      rw [hdet, hpow]
    refine ⟨p * qpn - ppn * q, pn * q - p * qn, ?_, ?_⟩
    · dsimp [pn, ppn, qn, qpn] at hdet_one ⊢
      calc
        p = p * (pn * qpn - ppn * qn) := by
          rw [hdet_one]
          ring
        _ =
            (p * qpn - ppn * q) * pn +
              (pn * q - p * qn) * ppn := by
          ring
    · dsimp [pn, ppn, qn, qpn] at hdet_one ⊢
      calc
        q = q * (pn * qpn - ppn * qn) := by
          rw [hdet_one]
          ring
        _ =
            (p * qpn - ppn * q) * qn +
              (pn * q - p * qn) * qpn := by
          ring
  · have hdet_neg_one : pn * qpn - ppn * qn = -1 := by
      rw [hdet, hpow]
    refine ⟨-(p * qpn - ppn * q), -(pn * q - p * qn), ?_, ?_⟩
    · dsimp [pn, ppn, qn, qpn] at hdet_neg_one ⊢
      calc
        p = -p * (pn * qpn - ppn * qn) := by
          rw [hdet_neg_one]
          ring
        _ =
            -(p * qpn - ppn * q) * pn +
              -(pn * q - p * qn) * ppn := by
          ring
    · dsimp [pn, ppn, qn, qpn] at hdet_neg_one ⊢
      calc
        q = -q * (pn * qpn - ppn * qn) := by
          rw [hdet_neg_one]
          ring
        _ =
            -(p * qpn - ppn * q) * qn +
              -(pn * q - p * qn) * qpn := by
          ring

/-- Coefficient restriction underlying the second-kind best-approximation
property. If `0 < r qₙ + s qₙ₋₁ < A qₙ + qₙ₋₁` and `β > A`, then
`|r - s β| ≥ 1`. -/
theorem abs_int_coeff_sub_tail_ge_one_of_den_lt_qsucc
    {β : ℝ} {A qn qp : ℕ} {r s : ℤ}
    (hApos : 0 < A)
    (hβA : (A : ℝ) < β)
    (hqn : 0 < qn)
    (hqpos :
      0 <
        r * (qn : ℤ) + s * (qp : ℤ))
    (hqhi :
      r * (qn : ℤ) + s * (qp : ℤ) <
        (A : ℤ) * (qn : ℤ) + (qp : ℤ)) :
    1 ≤ |(r : ℝ) - (s : ℝ) * β| := by
  have hβpos : 0 < β := by
    have hAnonneg : (0 : ℝ) ≤ A := by positivity
    linarith
  have hqnZpos : (0 : ℤ) < (qn : ℤ) := by exact_mod_cast hqn
  have hqpZnonneg : (0 : ℤ) ≤ (qp : ℤ) := by exact_mod_cast Nat.zero_le qp
  by_cases hs_nonpos : s ≤ 0
  · have hsqp_nonpos : s * (qp : ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hs_nonpos hqpZnonneg
    have hrqn_pos : 0 < r * (qn : ℤ) := by
      linarith
    have hrpos : 0 < r := by
      by_contra hrnot
      have hrnonpos : r ≤ 0 := le_of_not_gt hrnot
      have hprod_nonpos : r * (qn : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hrnonpos hqnZpos.le
      linarith
    have hrge1 : (1 : ℤ) ≤ r := by omega
    have hrge1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrge1
    have hsR_nonpos : (s : ℝ) ≤ 0 := by exact_mod_cast hs_nonpos
    have hnegterm_nonneg : 0 ≤ -(s : ℝ) * β :=
      mul_nonneg (neg_nonneg.mpr hsR_nonpos) hβpos.le
    have hexpr_ge : 1 ≤ (r : ℝ) - (s : ℝ) * β := by
      nlinarith
    exact le_trans hexpr_ge (le_abs_self _)
  · have hspos : 0 < s := lt_of_not_ge hs_nonpos
    have hsge1 : (1 : ℤ) ≤ s := by omega
    have hright_nonpos : (1 - s) * (qp : ℤ) ≤ 0 := by
      have hones_nonpos : 1 - s ≤ 0 := by omega
      exact mul_nonpos_of_nonpos_of_nonneg hones_nonpos hqpZnonneg
    have hineq :
        (r - (A : ℤ)) * (qn : ℤ) < (1 - s) * (qp : ℤ) := by
      nlinarith
    have hmul_neg : (r - (A : ℤ)) * (qn : ℤ) < 0 :=
      lt_of_lt_of_le hineq hright_nonpos
    have hr_lt_A : r < (A : ℤ) := by
      by_contra hnot
      have hdiff_nonneg : 0 ≤ r - (A : ℤ) := by omega
      have hprod_nonneg :
          0 ≤ (r - (A : ℤ)) * (qn : ℤ) :=
        mul_nonneg hdiff_nonneg hqnZpos.le
      linarith
    have hr_le_A_sub_one : r ≤ (A : ℤ) - 1 := by omega
    have hsRge1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsge1
    have hr_le_A_sub_one_R : (r : ℝ) ≤ (A : ℝ) - 1 := by
      exact_mod_cast hr_le_A_sub_one
    have hβ_le_sβ : β ≤ (s : ℝ) * β := by
      calc
        β = 1 * β := by ring
        _ ≤ (s : ℝ) * β :=
          mul_le_mul_of_nonneg_right hsRge1 hβpos.le
    have hgt : 1 < (s : ℝ) * β - (r : ℝ) := by
      nlinarith
    have hnonpos : (r : ℝ) - (s : ℝ) * β ≤ 0 := by
      linarith
    rw [abs_of_nonpos hnonpos]
    linarith

/-- Best approximation of the second kind for project-local simple continued
fractions: no positive denominator below `qₙ₊₁` gives smaller integer error
than the `n`-th convergent. -/
theorem convergent_best_approx_second_kind
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (n q : ℕ) (p : ℤ)
    (hqpos : 0 < q)
    (hqhi : q < continuantDen a (n + 1)) :
    |(q : ℝ) * α - (p : ℝ)| ≥
      |(continuantDen a n : ℝ) * α -
        (continuantNum a n : ℝ)| := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hcf' : IsSimpleCFExpansion α a := ⟨hpos, htendsto, htails⟩
  rcases prev_error_eq_neg_tail_mul_error hcf' n with
    ⟨β, hβgt, _, hprev_rel⟩
  rcases exists_convergent_zbasis_coeffs a n p (q : ℤ) with
    ⟨r, s, hp, hq⟩
  let E : ℝ :=
    (continuantDen a n : ℝ) * α - (continuantNum a n : ℝ)
  let Ep : ℝ :=
    (continuantDenPrev a n : ℝ) * α - (continuantNumPrev a n : ℝ)
  have hqposZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
  have hqhiZ : (q : ℤ) < (continuantDen a (n + 1) : ℤ) := by
    exact_mod_cast hqhi
  have hq_coeff_pos :
      0 <
        r * (continuantDen a n : ℤ) +
          s * (continuantDenPrev a n : ℤ) := by
    simpa [hq] using hqposZ
  have hnext_eqZ :
      (continuantDen a (n + 1) : ℤ) =
        (a (n + 1) : ℤ) * (continuantDen a n : ℤ) +
          (continuantDenPrev a n : ℤ) := by
    rw [continuantDen_succ]
    norm_num
  have hq_coeff_hi :
      r * (continuantDen a n : ℤ) +
          s * (continuantDenPrev a n : ℤ) <
        (a (n + 1) : ℤ) * (continuantDen a n : ℤ) +
          (continuantDenPrev a n : ℤ) := by
    simpa [hq, hnext_eqZ] using hqhiZ
  have hqnpos : 0 < continuantDen a n :=
    continuantDen_pos_of_partials a hpos n
  have hcoeff :
      1 ≤ |(r : ℝ) - (s : ℝ) * β| :=
    abs_int_coeff_sub_tail_ge_one_of_den_lt_qsucc
      (hApos := hpos n) (hβA := hβgt) (hqn := hqnpos)
      hq_coeff_pos hq_coeff_hi
  have hpR :
      (p : ℝ) =
        (r : ℝ) * (continuantNum a n : ℝ) +
          (s : ℝ) * (continuantNumPrev a n : ℝ) := by
    exact_mod_cast hp
  have hqR :
      (q : ℝ) =
        (r : ℝ) * (continuantDen a n : ℝ) +
          (s : ℝ) * (continuantDenPrev a n : ℝ) := by
    exact_mod_cast hq
  have hlin :
      (q : ℝ) * α - (p : ℝ) =
        (r : ℝ) * E + (s : ℝ) * Ep := by
    dsimp [E, Ep]
    rw [hpR, hqR]
    ring
  have hprev_rel' : Ep = -β * E := by
    simpa [E, Ep] using hprev_rel
  have hmain :
      (q : ℝ) * α - (p : ℝ) =
        ((r : ℝ) - (s : ℝ) * β) * E := by
    rw [hlin, hprev_rel']
    ring
  have habs :
      |(q : ℝ) * α - (p : ℝ)| =
        |(r : ℝ) - (s : ℝ) * β| * |E| := by
    rw [hmain, abs_mul]
  change |E| ≤ |(q : ℝ) * α - (p : ℝ)|
  rw [habs]
  simpa [one_mul] using
    mul_le_mul_of_nonneg_right hcoeff (abs_nonneg E)

/-- Rational lower bound between consecutive convergent denominators. -/
theorem rational_approx_lower_bound_between_convergents
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (n q : ℕ) (p : ℤ)
    (_hqlo : continuantDen a n ≤ q)
    (hqhi : q < continuantDen a (n + 1))
    (hqpos : 0 < q) :
    |α - (p : ℝ) / (q : ℝ)| ≥
      1 / (2 * (q : ℝ) * (continuantDen a (n + 1) : ℝ)) :=
  rational_approx_lower_bound_between_convergents_of_best
    hcf n q p hqpos
    (convergent_best_approx_second_kind hcf n q p hqpos hqhi)

private theorem inv_sq_continuantDen_tendsto_zero
    {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1)) :
    Tendsto
      (fun n : ℕ => 1 / (continuantDen a n : ℝ) ^ 2)
      atTop
      (𝓝 0) := by
  have hqR :
      Tendsto (fun n : ℕ => (continuantDen a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (continuantDen_tendsto_atTop hpos)
  have hinv :
      Tendsto (fun n : ℕ => ((continuantDen a n : ℝ)⁻¹))
        atTop (𝓝 0) :=
    hqR.inv_tendsto_atTop
  have hinv2 := hinv.mul hinv
  simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hinv2

private theorem convergents_tendsto_of_tails
    {α : ℝ} {a : ℕ → ℕ}
    (hpos : ∀ n : ℕ, 0 < a (n + 1))
    (htails : HasContinuedFractionTails α a) :
    Tendsto
      (fun n : ℕ =>
        (continuantNum a n : ℝ) / (continuantDen a n : ℝ))
      atTop
      (𝓝 α) := by
  rw [← tendsto_sub_nhds_zero_iff]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero
    (fun n : ℕ => norm_nonneg _)
    (fun n : ℕ => by
      have herror := convergent_error_le_inv_sq hpos htails n
      simpa [Real.norm_eq_abs, sub_zero, abs_sub_comm] using herror)
    (inv_sq_continuantDen_tendsto_zero hpos)

/-- Standard continued-fraction existence bridge needed to connect mathlib's
`GenContFract.of` API with this project's local `IsSimpleCFExpansion` record.

Mathematically this is the classical theorem that every positive irrational
real has an infinite simple continued-fraction expansion, with convergents
tending to the real and with the usual tail identities. -/
theorem exists_simpleCFExpansion_of_irrational
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α) :
    ∃ a : ℕ → ℕ, IsSimpleCFExpansion α a := by
  let a : ℕ → ℕ := simplePartialQuotient α
  refine ⟨a, ?_, ?_, ?_⟩
  · intro n
    exact simplePartialQuotient_succ_pos hαpos hirr n
  · exact convergents_tendsto_of_tails
      (fun n => simplePartialQuotient_succ_pos hαpos hirr n)
      (hasContinuedFractionTails_simplePartialQuotient hαpos hirr)
  · exact hasContinuedFractionTails_simplePartialQuotient hαpos hirr

/-- Contrapositive form of the remaining classical continued-fraction bridge.

This is the exact finite-CF/first-difference theorem isolated in the write-up:
if a reduced rational is not one of the convergents or semiconvergents of
`α`, then the finite continued-fraction comparison produces a rational with
strictly smaller denominator between it and `α`. -/
theorem smaller_denominator_between_of_not_convergent_or_semiconvergent
    {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hq : 2 ≤ q)
    (hred : ReducedFraction p q)
    (hnot : ¬ IsConvergentOrSemiconvergent α p q) :
    ∃ c d : ℕ,
      0 < d ∧ d < q ∧
        StrictBetween α (ratValue c d) (ratValue p q) := by
  rcases exists_simpleCFExpansion_of_irrational hαpos hirr with ⟨a, hcf⟩
  rcases canonicalFiniteCF_exists hred hq with ⟨e⟩
  rcases CanonicalFiniteCF.head_ne_or_agreesThrough_or_firstDifference e a with
    hhead | hagree | hdiff
  · exact smaller_denominator_between_of_head_ne hcf e hq hhead
  · exact False.elim
      (hnot (convergent_or_semiconvergent_of_agreesThrough
        hcf hred e hagree))
  · rcases hdiff with ⟨j, hdiffj⟩
    exact smaller_denominator_between_of_firstDifference
      hcf hred e hdiffj hnot

/-- Lemma 3.9: the best-approximation property is equivalent to being a
convergent or semiconvergent. -/
theorem no_small_denominator_iff_convergent_or_semiconvergent
    {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hq : 2 ≤ q)
    (hred : ReducedFraction p q) :
    NoSmallDenominatorBetween α p q ↔
      IsConvergentOrSemiconvergent α p q := by
  constructor
  · intro hbest
    by_contra hnot
    rcases smaller_denominator_between_of_not_convergent_or_semiconvergent
        hαpos hirr hq hred hnot with
      ⟨c, d, hdpos, hdlt, hbetween⟩
    exact (hbest c d hdpos hdlt) hbetween
  · intro hcf
    exact convergent_or_semiconvergent_no_small_denominator
      hαpos hirr hcf hred

/-- Forward inclusion for Theorem 3.10: odd reduced convergents and
semiconvergents produce elements of `A_α`. -/
theorem mem_A_of_odd_convergent_or_semiconvergent {α : ℝ} {p q : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hq : 2 ≤ q)
    (hred : ReducedFraction p q)
    (hcf : IsConvergentOrSemiconvergent α p q)
    (hpodd : Odd p) :
    q - 1 ∈ A α := by
  have _ : 0 < α := hαpos
  have hagrees : FloorAgreement α p q :=
    convergent_or_semiconvergent_floor_agreement hirr hcf hred
  have hfloor_eq : floorSum α (q - 1) = rationalFloorSum p q := by
    unfold floorSum rationalFloorSum
    apply Finset.sum_congr rfl
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkq⟩
    unfold floorMul
    exact hagrees k hk1 hkq
  have hp : 0 < p := by
    rcases hpodd with ⟨m, hm⟩
    omega
  have hrat := coprime_rationalFloorSum (p := p) (q := q) hp hred.1 hred.2
  refine (mem_A_iff).mpr ⟨by omega, ?_⟩
  rw [hfloor_eq, hrat]
  rcases hpodd with ⟨m, hm⟩
  refine ⟨(m : ℤ), ?_⟩
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  have hpminus : (p : ℤ) - 1 = 2 * (m : ℤ) := by
    rw [hm]
    omega
  rw [hqsub, hpminus]
  have hdiv :
      (2 * (m : ℤ) * ((q : ℤ) - 1)) / 2 =
        (m : ℤ) * ((q : ℤ) - 1) := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num)
    ring
  rw [hdiv]
  ring

/-- Reverse inclusion for Theorem 3.10: membership in `A_α` gives an odd
best approximation at denominator `n + 1`. -/
theorem exists_odd_best_approx_of_mem_A {α : ℝ} {n : ℕ}
    (hαpos : 0 < α)
    (hirr : IsIrrational α)
    (hA : n ∈ A α) :
    ∃ p : ℕ,
      Odd p ∧ ReducedFraction p (n + 1) ∧
        NoSmallDenominatorBetween α p (n + 1) := by
  have hnpos : 0 < n := (mem_A_iff.mp hA).1
  have hqpos : 0 < n + 1 := by omega
  rcases (mem_A_iff_record_extreme (r := α) hirr (n := n) hnpos).mp hA with
    ⟨hlower, hodd⟩ | ⟨hupper, heven⟩
  · refine ⟨(floorMul α (n + 1)).toNat, ?_, ?_, ?_⟩
    · exact odd_toNat_of_nonneg
        (floorMul_nonneg_of_pos hαpos hqpos) hodd
    · exact ⟨hqpos,
        coprime_floorMul_of_lowerRecord hαpos hirr hqpos hlower⟩
    · exact noSmallDenominatorBetween_of_lowerRecord_floor
        hαpos hirr hqpos hlower
  · refine ⟨(floorMul α (n + 1) + 1).toNat, ?_, ?_, ?_⟩
    · exact odd_succ_toNat_of_even_nonneg
        (floorMul_nonneg_of_pos hαpos hqpos) heven
    · exact ⟨hqpos,
        coprime_floorMul_succ_of_upperRecord hαpos hirr hqpos hupper⟩
    · exact noSmallDenominatorBetween_of_upperRecord_ceil
        hαpos hirr hqpos hupper

/-- Theorem 3.10: the continued-fraction classification of `A_α`. -/
theorem A_eq_odd_convergent_or_semiconvergent {α : ℝ}
    (hαpos : 0 < α) (hirr : IsIrrational α) :
    A α =
      {n : ℕ | ∃ p q : ℕ,
        n = q - 1 ∧ 2 ≤ q ∧ ReducedFraction p q ∧
          IsConvergentOrSemiconvergent α p q ∧ Odd p} := by
  ext n
  constructor
  · intro hA
    rcases exists_odd_best_approx_of_mem_A hαpos hirr hA with
      ⟨p, hpodd, hred, hbest⟩
    have hnpos : 0 < n := (mem_A_iff.mp hA).1
    have hnq : 2 ≤ n + 1 := by omega
    have hcf : IsConvergentOrSemiconvergent α p (n + 1) :=
      (no_small_denominator_iff_convergent_or_semiconvergent
        hαpos hirr hnq hred).mp hbest
    refine ⟨p, n + 1, ?_, ?_, hred, hcf, hpodd⟩ <;> omega
  · rintro ⟨p, q, rfl, hq, hred, hcf, hpodd⟩
    exact mem_A_of_odd_convergent_or_semiconvergent hαpos hirr hq hred hcf hpodd

/-- The canonical sequence `simplePartialQuotient α` is itself a simple
continued-fraction expansion of a positive irrational `α`.

This exports the concrete witness used by
`exists_simpleCFExpansion_of_irrational`. -/
theorem simplePartialQuotient_isSimpleCFExpansion
    {α : ℝ} (hαpos : 0 < α) (hirr : IsIrrational α) :
    IsSimpleCFExpansion α (simplePartialQuotient α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact simplePartialQuotient_succ_pos hαpos hirr n
  · exact convergents_tendsto_of_tails
      (fun n => simplePartialQuotient_succ_pos hαpos hirr n)
      (hasContinuedFractionTails_simplePartialQuotient hαpos hirr)
  · exact hasContinuedFractionTails_simplePartialQuotient hαpos hirr

/-- Continuant numerators only depend on the coefficient sequence. -/
theorem continuantNum_eq_of_coeff_eq {a b : ℕ → ℕ}
    (h : ∀ n : ℕ, a n = b n) :
    ∀ n : ℕ, continuantNum a n = continuantNum b n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [continuantNum, h 0]
  | one =>
      simp [continuantNum, h 0, h 1]
  | more n ih0 ih1 =>
      rw [continuantNum, continuantNum]
      rw [h (n + 2), ih1, ih0]

/-- Continuant denominators only depend on the coefficient sequence. -/
theorem continuantDen_eq_of_coeff_eq {a b : ℕ → ℕ}
    (h : ∀ n : ℕ, a n = b n) :
    ∀ n : ℕ, continuantDen a n = continuantDen b n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [continuantDen]
  | one =>
      simp [continuantDen, h 1]
  | more n ih0 ih1 =>
      rw [continuantDen, continuantDen]
      rw [h (n + 2), ih1, ih0]

/-- Positive irrational real numbers are determined by all of their canonical
simple continued-fraction partial quotients. -/
theorem eq_of_simplePartialQuotient_eq
    {x y : ℝ}
    (hxpos : 0 < x) (hypos : 0 < y)
    (hxirr : IsIrrational x) (hyirr : IsIrrational y)
    (hcoeff : ∀ n : ℕ,
      simplePartialQuotient x n = simplePartialQuotient y n) :
    x = y := by
  let ax : ℕ → ℕ := simplePartialQuotient x
  let ay : ℕ → ℕ := simplePartialQuotient y
  have hxcf : IsSimpleCFExpansion x ax := by
    simpa [ax] using simplePartialQuotient_isSimpleCFExpansion hxpos hxirr
  have hycf : IsSimpleCFExpansion y ay := by
    simpa [ay] using simplePartialQuotient_isSimpleCFExpansion hypos hyirr
  have hcoeff' : ∀ n : ℕ, ax n = ay n := by
    intro n
    exact hcoeff n
  have hnum : ∀ n : ℕ, continuantNum ax n = continuantNum ay n :=
    continuantNum_eq_of_coeff_eq hcoeff'
  have hden : ∀ n : ℕ, continuantDen ax n = continuantDen ay n :=
    continuantDen_eq_of_coeff_eq hcoeff'
  have hseq :
      (fun n : ℕ =>
        (continuantNum ax n : ℝ) / (continuantDen ax n : ℝ)) =
      (fun n : ℕ =>
        (continuantNum ay n : ℝ) / (continuantDen ay n : ℝ)) := by
    funext n
    rw [hnum n, hden n]
  have hxlim :
      Tendsto
        (fun n : ℕ =>
          (continuantNum ax n : ℝ) / (continuantDen ax n : ℝ))
        atTop (𝓝 x) := hxcf.2.1
  have hylim_on_xseq :
      Tendsto
        (fun n : ℕ =>
          (continuantNum ax n : ℝ) / (continuantDen ax n : ℝ))
        atTop (𝓝 y) := by
    simpa [hseq] using hycf.2.1
  exact tendsto_nhds_unique hxlim hylim_on_xseq

/-- If two positive irrational reals are unequal, their canonical simple
continued-fraction partial quotient sequences have a first differing index. -/
theorem exists_firstDiff_simplePartialQuotient_of_ne
    {x y : ℝ}
    (hxpos : 0 < x) (hypos : 0 < y)
    (hxirr : IsIrrational x) (hyirr : IsIrrational y)
    (hxy : x ≠ y) :
    ∃ j : ℕ,
      (∀ i : ℕ, i < j →
        simplePartialQuotient x i = simplePartialQuotient y i) ∧
      simplePartialQuotient x j ≠ simplePartialQuotient y j := by
  classical
  by_contra hno
  have hall : ∀ i : ℕ,
      simplePartialQuotient x i = simplePartialQuotient y i := by
    intro i
    by_contra hi
    let P : ℕ → Prop := fun n =>
      simplePartialQuotient x n ≠ simplePartialQuotient y n
    have hex : ∃ n : ℕ, P n := ⟨i, hi⟩
    let j : ℕ := Nat.find hex
    have hjdiff : P j := Nat.find_spec hex
    have hprefix : ∀ k : ℕ, k < j →
        simplePartialQuotient x k = simplePartialQuotient y k := by
      intro k hk
      by_contra hkdiff
      exact (Nat.find_min hex hk) hkdiff
    exact hno ⟨j, hprefix, hjdiff⟩
  exact hxy (eq_of_simplePartialQuotient_eq
    hxpos hypos hxirr hyirr hall)

/-- If the canonical finite expansion of `p / q` agrees with the expansion
`a` through its last coefficient, then the denominator `q` lies in the
principal/intermediate denominator path of `a`.

Since `q ≥ 2`, the finite continued fraction has positive length, and the
last principal denominator is the last semiconvergent in the previous block. -/
private theorem CFDenominatorPath_of_agreesThrough
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q)
    (hagree : e.AgreesThrough a) :
    CFDenominatorPath a q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hfinite :
      finiteCFExact e.coeff e.last = finiteCFExact a e.last := by
    exact finiteCFExact_eq_of_eq_on_prefix e.coeff a e.last
      (by
        intro i hi
        exact hagree i hi)

  have hpos_prefix :
      ∀ i : ℕ, 1 ≤ i → i ≤ e.last → 0 < a i := by
    intro i hi1 _
    cases i with
    | zero => omega
    | succ k =>
        simpa [Nat.succ_eq_add_one] using hpos k

  have hvalue :
      ratValue p q =
        ratValue (continuantNum a e.last) (continuantDen a e.last) := by
    rw [e.value_eq, hfinite,
      finiteCFExact_eq_ratValue_continuants a e.last hpos_prefix]

  have hred_conv : ReducedFraction
      (continuantNum a e.last) (continuantDen a e.last) :=
    reducedFraction_continuant a hpos e.last

  have hpq :=
    reducedFraction_eq_of_ratValue_eq hred hred_conv hvalue

  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt e.last_pos) with
    ⟨n, hlast⟩
  refine ⟨n, a (n + 1), ?_, le_rfl, ?_⟩
  · exact Nat.succ_le_iff.mpr (hpos n)
  · calc
      q = continuantDen a (n + 1) := by
            simpa [hlast, Nat.succ_eq_add_one] using hpq.2
      _ = a (n + 1) * continuantDen a n +
            continuantDenPrev a n := by
            exact continuantDen_succ a n
      _ = continuantDenPrev a n +
            a (n + 1) * continuantDen a n := by
            omega

/-- Terminal first-difference case with a smaller finite coefficient:
the denominator lies in the canonical semiconvergent path. -/
private theorem CFDenominatorPath_of_firstDifference_last_lt
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hb_lt_ha : e.coeff j < a j) :
    CFDenominatorPath a q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let t : ℕ := e.coeff j

  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega

  have htpos : 1 ≤ t := by
    dsimp [t]
    exact e.positive_after_head j hj1 hjle

  have htlea : t ≤ a (n + 1) := by
    dsimp [t]
    rw [hn_succ]
    exact Nat.le_of_lt hb_lt_ha

  have hqform :=
    (num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
      hjlast).2

  refine ⟨n, t, htpos, htlea, ?_⟩
  calc
    q = e.coeff j * continuantDen a (j - 1) +
          continuantDenPrev a (j - 1) := hqform
    _ = continuantDenPrev a n + t * continuantDen a n := by
          dsimp [n, t]
          omega

/-- Terminal first-difference case with `e.coeff j = a j + 1`:
the denominator is the first semiconvergent in the next block. -/
private theorem CFDenominatorPath_of_firstDifference_last_succ
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hsucc : e.coeff j = a j + 1) :
    CFDenominatorPath a q := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1

  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega

  have hnumden :=
    num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
      hjlast

  have hdenj :
      continuantDen a j =
        a j * continuantDen a n + continuantDenPrev a n := by
    rw [← hn_succ]
    exact continuantDen_succ a n

  have hdenprevj : continuantDenPrev a j = continuantDen a n := by
    rw [← hn_succ]
    exact continuantDenPrev_succ a n

  refine ⟨j, 1, by norm_num, ?_, ?_⟩
  · exact Nat.succ_le_iff.mpr (hpos j)
  · calc
      q = e.coeff j * continuantDen a n +
            continuantDenPrev a n := hnumden.2
      _ = (a j + 1) * continuantDen a n +
            continuantDenPrev a n := by
            rw [hsucc]
      _ = continuantDenPrev a j + 1 * continuantDen a j := by
            rw [hdenj, hdenprevj]
            ring
      _ = continuantDenPrev a j + 1 * continuantDen a j := rfl

/-- Pair-path version of `CFDenominatorPath_of_agreesThrough`.

If the canonical finite expansion of `p / q` agrees with `a` through its last
coefficient, then the whole reduced pair `(p,q)` is the last semiconvergent in
the previous canonical block. -/
private theorem CFPathPair_of_agreesThrough
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q)
    (hagree : e.AgreesThrough a) :
    ∃ n t : ℕ,
      1 ≤ t ∧ t ≤ a (n + 1) ∧
        p = continuantNumPrev a n + t * continuantNum a n ∧
        q = continuantDenPrev a n + t * continuantDen a n := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  have hfinite :
      finiteCFExact e.coeff e.last = finiteCFExact a e.last := by
    exact finiteCFExact_eq_of_eq_on_prefix e.coeff a e.last
      (by
        intro i hi
        exact hagree i hi)

  have hpos_prefix :
      ∀ i : ℕ, 1 ≤ i → i ≤ e.last → 0 < a i := by
    intro i hi1 _
    cases i with
    | zero => omega
    | succ k =>
        simpa [Nat.succ_eq_add_one] using hpos k

  have hvalue :
      ratValue p q =
        ratValue (continuantNum a e.last) (continuantDen a e.last) := by
    rw [e.value_eq, hfinite,
      finiteCFExact_eq_ratValue_continuants a e.last hpos_prefix]

  have hred_conv : ReducedFraction
      (continuantNum a e.last) (continuantDen a e.last) :=
    reducedFraction_continuant a hpos e.last

  have hpq :=
    reducedFraction_eq_of_ratValue_eq hred hred_conv hvalue

  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt e.last_pos) with
    ⟨n, hlast⟩
  refine ⟨n, a (n + 1), ?_, le_rfl, ?_, ?_⟩
  · exact Nat.succ_le_iff.mpr (hpos n)
  · calc
      p = continuantNum a (n + 1) := by
            simpa [hlast, Nat.succ_eq_add_one] using hpq.1
      _ = a (n + 1) * continuantNum a n +
            continuantNumPrev a n := by
            exact continuantNum_succ a n
      _ = continuantNumPrev a n +
            a (n + 1) * continuantNum a n := by
            omega
  · calc
      q = continuantDen a (n + 1) := by
            simpa [hlast, Nat.succ_eq_add_one] using hpq.2
      _ = a (n + 1) * continuantDen a n +
            continuantDenPrev a n := by
            exact continuantDen_succ a n
      _ = continuantDenPrev a n +
            a (n + 1) * continuantDen a n := by
            omega

/-- Pair-path version of `CFDenominatorPath_of_firstDifference_last_lt`. -/
private theorem CFPathPair_of_firstDifference_last_lt
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hb_lt_ha : e.coeff j < a j) :
    ∃ n t : ℕ,
      1 ≤ t ∧ t ≤ a (n + 1) ∧
        p = continuantNumPrev a n + t * continuantNum a n ∧
        q = continuantDenPrev a n + t * continuantDen a n := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1
  let t : ℕ := e.coeff j

  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega

  have htpos : 1 ≤ t := by
    dsimp [t]
    exact e.positive_after_head j hj1 hjle

  have htlea : t ≤ a (n + 1) := by
    dsimp [t]
    rw [hn_succ]
    exact Nat.le_of_lt hb_lt_ha

  have hnumden :=
    num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
      hjlast

  refine ⟨n, t, htpos, htlea, ?_, ?_⟩
  · calc
      p = e.coeff j * continuantNum a (j - 1) +
            continuantNumPrev a (j - 1) := hnumden.1
      _ = continuantNumPrev a n + t * continuantNum a n := by
            dsimp [n, t]
            omega
  · calc
      q = e.coeff j * continuantDen a (j - 1) +
            continuantDenPrev a (j - 1) := hnumden.2
      _ = continuantDenPrev a n + t * continuantDen a n := by
            dsimp [n, t]
            omega

/-- Pair-path version of `CFDenominatorPath_of_firstDifference_last_succ`. -/
private theorem CFPathPair_of_firstDifference_last_succ
    {α : ℝ} {a : ℕ → ℕ} {p q : ℕ}
    (hcf : IsSimpleCFExpansion α a)
    (hred : ReducedFraction p q)
    (e : CanonicalFiniteCF p q) {j : ℕ}
    (hdiff : e.FirstDifference a j)
    (hjlast : j = e.last)
    (hsucc : e.coeff j = a j + 1) :
    ∃ n t : ℕ,
      1 ≤ t ∧ t ≤ a (n + 1) ∧
        p = continuantNumPrev a n + t * continuantNum a n ∧
        q = continuantDenPrev a n + t * continuantDen a n := by
  rcases hcf with ⟨hpos, htendsto, htails⟩
  rcases hdiff with ⟨hj1, hjle, hprefix, hne⟩
  let n : ℕ := j - 1

  have hn_succ : n + 1 = j := by
    dsimp [n]
    omega

  have hnumden :=
    num_den_of_firstDifference_last hred e
      (show e.FirstDifference a j from ⟨hj1, hjle, hprefix, hne⟩)
      hjlast

  have hnumj :
      continuantNum a j =
        a j * continuantNum a n + continuantNumPrev a n := by
    rw [← hn_succ]
    exact continuantNum_succ a n

  have hdenj :
      continuantDen a j =
        a j * continuantDen a n + continuantDenPrev a n := by
    rw [← hn_succ]
    exact continuantDen_succ a n

  have hnumpredj : continuantNumPrev a j = continuantNum a n := by
    rw [← hn_succ]
    exact continuantNumPrev_succ a n

  have hdenprevj : continuantDenPrev a j = continuantDen a n := by
    rw [← hn_succ]
    exact continuantDenPrev_succ a n

  refine ⟨j, 1, by norm_num, ?_, ?_, ?_⟩
  · exact Nat.succ_le_iff.mpr (hpos j)
  · calc
      p = e.coeff j * continuantNum a n +
            continuantNumPrev a n := hnumden.1
      _ = (a j + 1) * continuantNum a n +
            continuantNumPrev a n := by
            rw [hsucc]
      _ = continuantNumPrev a j + 1 * continuantNum a j := by
            rw [hnumj, hnumpredj]
            ring
      _ = continuantNumPrev a j + 1 * continuantNum a j := rfl
  · calc
      q = e.coeff j * continuantDen a n +
            continuantDenPrev a n := hnumden.2
      _ = (a j + 1) * continuantDen a n +
            continuantDenPrev a n := by
            rw [hsucc]
      _ = continuantDenPrev a j + 1 * continuantDen a j := by
            rw [hdenj, hdenprevj]
            ring
      _ = continuantDenPrev a j + 1 * continuantDen a j := rfl

/-- Direct canonical pair-path recovery for a reduced principal/intermediate
convergent witness.

This is the strengthened version of `oddCFDenoms_subset_canonical_path`: it
recovers the numerator attached to the canonical path denominator, not just the
denominator itself. -/
private theorem canonical_pair_path_of_convergent_or_semiconvergent
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    {P Q : ℕ}
    (hQ2 : 2 ≤ Q)
    (hred : ReducedFraction P Q)
    (hcf_any : IsConvergentOrSemiconvergent α P Q) :
    ∃ n t : ℕ,
      1 ≤ t ∧ t ≤ simplePartialQuotient α (n + 1) ∧
        P = continuantNumPrev (simplePartialQuotient α) n +
              t * continuantNum (simplePartialQuotient α) n ∧
        Q = continuantDenPrev (simplePartialQuotient α) n +
              t * continuantDen (simplePartialQuotient α) n := by
  let a : ℕ → ℕ := simplePartialQuotient α

  have hcf : IsSimpleCFExpansion α a := by
    simpa [a] using simplePartialQuotient_isSimpleCFExpansion hαpos hαirr

  have hbest : NoSmallDenominatorBetween α P Q :=
    convergent_or_semiconvergent_no_small_denominator
      hαpos hαirr hcf_any hred

  rcases canonicalFiniteCF_exists hred hQ2 with ⟨e⟩

  rcases CanonicalFiniteCF.head_ne_or_agreesThrough_or_firstDifference e a with
    hhead | hagree | hdiff
  · rcases smaller_denominator_between_of_head_ne hcf e hQ2 hhead with
      ⟨c, d, hdpos, hdlt, hbetween⟩
    exact False.elim ((hbest c d hdpos hdlt) hbetween)

  · simpa [a] using CFPathPair_of_agreesThrough hcf hred e hagree

  · rcases hdiff with ⟨j, hdiffj⟩
    rcases hdiffj with ⟨hj1, hjle, hprefix, hne⟩
    have hdiffj' : e.FirstDifference a j :=
      ⟨hj1, hjle, hprefix, hne⟩

    rcases lt_or_gt_of_ne hne with hb_lt_ha | ha_lt_hb
    · by_cases hjlast : j = e.last
      · simpa [a] using CFPathPair_of_firstDifference_last_lt
          hcf hred e hdiffj' hjlast hb_lt_ha
      · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
        rcases smaller_denominator_between_of_firstDifference_nonterminal_lt
            hcf hred e hdiffj' hjlt hb_lt_ha with
          ⟨c, d, hdpos, hdlt, hbetween⟩
        exact False.elim ((hbest c d hdpos hdlt) hbetween)

    · by_cases hjlast : j = e.last
      · by_cases hsucc : e.coeff j = a j + 1
        · simpa [a] using CFPathPair_of_firstDifference_last_succ
            hcf hred e hdiffj' hjlast hsucc
        · have hlarge : a j + 1 < e.coeff j := by
            omega
          rcases smaller_denominator_between_of_firstDifference_last_large
              hcf hred e hdiffj' hjlast hlarge with
            ⟨c, d, hdpos, hdlt, hbetween⟩
          exact False.elim ((hbest c d hdpos hdlt) hbetween)
      · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
        rcases smaller_denominator_between_of_firstDifference_nonterminal_gt
            hcf hred e hdiffj' hjlt ha_lt_hb with
          ⟨c, d, hdpos, hdlt, hbetween⟩
        exact False.elim ((hbest c d hdpos hdlt) hbetween)

/-- The canonical coefficient sequence recovers the numerator-denominator pair
for any parity-selected principal/intermediate denominator witness. -/
theorem oddCFDenoms_subset_canonical_pair_path
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    {P Q : ℕ}
    (hQ :
      ∃ P0 : ℕ,
        P0 = P ∧
          2 ≤ Q ∧ ReducedFraction P0 Q ∧
          IsConvergentOrSemiconvergent α P0 Q ∧ Odd P0) :
    ∃ n t : ℕ,
      1 ≤ t ∧ t ≤ simplePartialQuotient α (n + 1) ∧
        P = continuantNumPrev (simplePartialQuotient α) n +
              t * continuantNum (simplePartialQuotient α) n ∧
        Q = continuantDenPrev (simplePartialQuotient α) n +
              t * continuantDen (simplePartialQuotient α) n := by
  rcases hQ with ⟨P0, hP0, hQ2, hred, hcf_any, hodd⟩
  subst P0
  exact canonical_pair_path_of_convergent_or_semiconvergent
    hαpos hαirr hQ2 hred hcf_any

/-- The canonical coefficient sequence exhausts all principal/intermediate
denominators for `α`.

This turns the existential definition of `IsConvergentOrSemiconvergent`
into membership in the canonical denominator path. -/
theorem oddCFDenoms_subset_canonical_path
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    {Q : ℕ}
    (hQ : Q ∈ oddCFDenoms α) :
    CFDenominatorPath (simplePartialQuotient α) Q := by
  rcases hQ with ⟨p, hQ2, hred, hcf_any, hodd⟩

  let a : ℕ → ℕ := simplePartialQuotient α

  have hcf : IsSimpleCFExpansion α a := by
    simpa [a] using simplePartialQuotient_isSimpleCFExpansion hαpos hαirr

  have hbest : NoSmallDenominatorBetween α p Q :=
    convergent_or_semiconvergent_no_small_denominator
      hαpos hαirr hcf_any hred

  rcases canonicalFiniteCF_exists hred hQ2 with ⟨e⟩

  rcases CanonicalFiniteCF.head_ne_or_agreesThrough_or_firstDifference e a with
    hhead | hagree | hdiff
  · rcases smaller_denominator_between_of_head_ne hcf e hQ2 hhead with
      ⟨c, d, hdpos, hdlt, hbetween⟩
    exact False.elim ((hbest c d hdpos hdlt) hbetween)

  · exact CFDenominatorPath_of_agreesThrough hcf hred e hagree

  · rcases hdiff with ⟨j, hdiffj⟩
    rcases hdiffj with ⟨hj1, hjle, hprefix, hne⟩
    have hdiffj' : e.FirstDifference a j :=
      ⟨hj1, hjle, hprefix, hne⟩

    rcases lt_or_gt_of_ne hne with hb_lt_ha | ha_lt_hb
    · by_cases hjlast : j = e.last
      · exact CFDenominatorPath_of_firstDifference_last_lt
          hcf hred e hdiffj' hjlast hb_lt_ha
      · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
        rcases smaller_denominator_between_of_firstDifference_nonterminal_lt
            hcf hred e hdiffj' hjlt hb_lt_ha with
          ⟨c, d, hdpos, hdlt, hbetween⟩
        exact False.elim ((hbest c d hdpos hdlt) hbetween)

    · by_cases hjlast : j = e.last
      · by_cases hsucc : e.coeff j = a j + 1
        · exact CFDenominatorPath_of_firstDifference_last_succ
            hcf hred e hdiffj' hjlast hsucc
        · have hlarge : a j + 1 < e.coeff j := by
            omega
          rcases smaller_denominator_between_of_firstDifference_last_large
              hcf hred e hdiffj' hjlast hlarge with
            ⟨c, d, hdpos, hdlt, hbetween⟩
          exact False.elim ((hbest c d hdpos hdlt) hbetween)
      · have hjlt : j < e.last := lt_of_le_of_ne hjle hjlast
        rcases smaller_denominator_between_of_firstDifference_nonterminal_gt
            hcf hred e hdiffj' hjlt ha_lt_hb with
          ⟨c, d, hdpos, hdlt, hbetween⟩
        exact False.elim ((hbest c d hdpos hdlt) hbetween)

/-- Gap exclusion for the canonical principal/intermediate denominator path.

If a natural number lies strictly between two consecutive path denominators,
then it cannot be in `oddCFDenoms`. -/
theorem not_mem_oddCFDenoms_of_between_consecutive_canonical_denoms
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    {Q₁ Q Q₂ : ℕ}
    (hQ₁path : CFDenominatorPath (simplePartialQuotient α) Q₁)
    (hQ₂path : CFDenominatorPath (simplePartialQuotient α) Q₂)
    (hconsec :
      ∀ R : ℕ,
        CFDenominatorPath (simplePartialQuotient α) R →
        Q₁ < R → R < Q₂ → False)
    (hgap : Q₁ < Q ∧ Q < Q₂) :
    Q ∉ oddCFDenoms α := by
  have _ := hQ₁path
  have _ := hQ₂path
  intro hQmem
  have hQpath :
      CFDenominatorPath (simplePartialQuotient α) Q :=
    oddCFDenoms_subset_canonical_path hαpos hαirr hQmem
  exact hconsec Q hQpath hgap.1 hgap.2

/-- If every canonical path representation of `Q` has even numerator, then
`Q` is not in the parity-selected denominator set. -/
private theorem not_mem_oddCFDenoms_of_all_path_reprs_even
    {α : ℝ}
    (hαpos : 0 < α)
    (hαirr : IsIrrational α)
    {Q : ℕ}
    (heven :
      ∀ P : ℕ,
        (∃ n t : ℕ,
          1 ≤ t ∧ t ≤ simplePartialQuotient α (n + 1) ∧
            P = continuantNumPrev (simplePartialQuotient α) n +
                t * continuantNum (simplePartialQuotient α) n ∧
            Q = continuantDenPrev (simplePartialQuotient α) n +
                t * continuantDen (simplePartialQuotient α) n) →
          Even P) :
    Q ∉ oddCFDenoms α := by
  intro hQ
  rcases hQ with ⟨P, hQ2, hred, hcf_any, hodd⟩
  have hpair :
      ∃ n t : ℕ,
        1 ≤ t ∧ t ≤ simplePartialQuotient α (n + 1) ∧
          P = continuantNumPrev (simplePartialQuotient α) n +
              t * continuantNum (simplePartialQuotient α) n ∧
          Q = continuantDenPrev (simplePartialQuotient α) n +
              t * continuantDen (simplePartialQuotient α) n :=
    oddCFDenoms_subset_canonical_pair_path hαpos hαirr
      ⟨P, rfl, hQ2, hred, hcf_any, hodd⟩
  exact (Nat.not_even_iff_odd.mpr hodd) (heven P hpair)

private theorem simplePartialQuotient_zero_eq_one_of_mem_Icc
    {α : ℝ} (hαirr : IsIrrational α)
    (hαI : α ∈ Set.Icc (1 : ℝ) 2) :
    simplePartialQuotient α 0 = 1 := by
  have hαge1 : (1 : ℝ) ≤ α := hαI.1
  have hαlt2 : α < 2 := by
    refine lt_of_le_of_ne hαI.2 ?_
    intro hα2
    exact hαirr ⟨2, by norm_num [hα2]⟩
  unfold simplePartialQuotient completeQuotient
  have hfloor : Int.floor α = 1 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  simp [hfloor]

private theorem pathPair_reduced
    (a : ℕ → ℕ) {n t : ℕ} (ht : 1 ≤ t) :
    ReducedFraction
      (continuantNumPrev a n + t * continuantNum a n)
      (continuantDenPrev a n + t * continuantDen a n) := by
  have hcop :
      Nat.Coprime
        (t * continuantNum a n + 1 * continuantNumPrev a n)
        (t * continuantDen a n + 1 * continuantDenPrev a n) :=
    commonPrefix_reduced a n (u := t) (v := 1)
      (Nat.coprime_one_right t)
  have hdenR :
      (0 : ℝ) <
        (t : ℝ) * (continuantDen a n : ℝ) +
          (continuantDenPrev a n : ℝ) :=
    continuant_denominator_pos a n (by exact_mod_cast ht)
  have hden :
      0 <
        continuantDenPrev a n + t * continuantDen a n := by
    have hdenR' :
        (0 : ℝ) <
          ((continuantDenPrev a n + t * continuantDen a n : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_mul, add_comm, mul_comm] using hdenR
    exact_mod_cast hdenR'
  refine ⟨hden, ?_⟩
  simpa [add_comm, mul_comm, one_mul] using hcop

private theorem mem_oddCFDenoms_of_canonical_path_odd
    {α : ℝ} {a : ℕ → ℕ}
    (hcf : IsSimpleCFExpansion α a)
    {n t : ℕ}
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (n + 1))
    (hodd :
      Odd (continuantNumPrev a n + t * continuantNum a n))
    (hQ2 :
      2 ≤ continuantDenPrev a n + t * continuantDen a n) :
    continuantDenPrev a n + t * continuantDen a n ∈ oddCFDenoms α := by
  refine oddCFDenoms_mem_of_oddCFPathPair
    (α := α) (a := a)
    (P := continuantNumPrev a n + t * continuantNum a n)
    (Q := continuantDenPrev a n + t * continuantDen a n)
    hcf ?_ hQ2 ?_
  · refine ⟨n, t, ht1, htle, rfl, rfl, hodd⟩
  · exact pathPair_reduced a ht1

private theorem continuantNum_eq_of_eq_on_prefix {a b : ℕ → ℕ} :
    ∀ n : ℕ,
      (∀ i : ℕ, i ≤ n → a i = b i) →
        continuantNum a n = continuantNum b n
  | 0, hprefix => by
      simp [continuantNum, hprefix 0 le_rfl]
  | 1, hprefix => by
      simp [continuantNum, hprefix 0 (by omega), hprefix 1 le_rfl]
  | n + 2, hprefix => by
      rw [continuantNum, continuantNum]
      rw [hprefix (n + 2) le_rfl]
      rw [continuantNum_eq_of_eq_on_prefix (n + 1)
        (by
          intro i hi
          exact hprefix i (by omega))]
      rw [continuantNum_eq_of_eq_on_prefix n
        (by
          intro i hi
          exact hprefix i (by omega))]

private theorem continuantDen_eq_of_eq_on_prefix {a b : ℕ → ℕ} :
    ∀ n : ℕ,
      (∀ i : ℕ, i ≤ n → a i = b i) →
        continuantDen a n = continuantDen b n
  | 0, _ => by
      simp [continuantDen]
  | 1, hprefix => by
      simp [continuantDen, hprefix 1 le_rfl]
  | n + 2, hprefix => by
      rw [continuantDen, continuantDen]
      rw [hprefix (n + 2) le_rfl]
      rw [continuantDen_eq_of_eq_on_prefix (n + 1)
        (by
          intro i hi
          exact hprefix i (by omega))]
      rw [continuantDen_eq_of_eq_on_prefix n
        (by
          intro i hi
          exact hprefix i (by omega))]

private theorem continuantNumPrev_eq_of_eq_on_prefix {a b : ℕ → ℕ}
    {n : ℕ}
    (hprefix : ∀ i : ℕ, i ≤ n → a i = b i) :
    continuantNumPrev a n = continuantNumPrev b n := by
  cases n with
  | zero =>
      simp [continuantNumPrev]
  | succ n =>
      simp [continuantNumPrev]
      exact continuantNum_eq_of_eq_on_prefix n
        (by
          intro i hi
          exact hprefix i (by omega))

private theorem continuantDenPrev_eq_of_eq_on_prefix {a b : ℕ → ℕ}
    {n : ℕ}
    (hprefix : ∀ i : ℕ, i ≤ n → a i = b i) :
    continuantDenPrev a n = continuantDenPrev b n := by
  cases n with
  | zero =>
      simp [continuantDenPrev]
  | succ n =>
      simp [continuantDenPrev]
      exact continuantDen_eq_of_eq_on_prefix n
        (by
          intro i hi
          exact hprefix i (by omega))

private theorem continuantDenPrev_eq_zero_iff_of_partials
    (a : ℕ → ℕ)
    (hpos : ∀ k : ℕ, 0 < a (k + 1)) :
    ∀ n : ℕ, continuantDenPrev a n = 0 ↔ n = 0
  | 0 => by
      simp [continuantDenPrev]
  | n + 1 => by
      have hdenpos : 0 < continuantDen a n :=
        continuantDen_pos_of_partials a hpos n
      simp [continuantDenPrev, Nat.ne_of_gt hdenpos]

private theorem continuantDenPrev_lt_den_of_two_le
    (a : ℕ → ℕ)
    (hpos : ∀ k : ℕ, 0 < a (k + 1))
    {n : ℕ} (hn : 2 ≤ n) :
    continuantDenPrev a n < continuantDen a n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  subst n
  rw [show 2 + k = k + 2 by omega]
  rw [continuantDenPrev_succ, continuantDen]
  have hcoefpos : 0 < a (k + 2) := by
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hpos (k + 1)
  have hdenpos : 0 < continuantDen a k :=
    continuantDen_pos_of_partials a hpos k
  have hmul_ge :
      continuantDen a (k + 1) ≤
        a (k + 2) * continuantDen a (k + 1) :=
    Nat.le_mul_of_pos_left (continuantDen a (k + 1)) hcoefpos
  omega

private theorem path_den_le_next_principal
    {a : ℕ → ℕ}
    (hpos : ∀ k : ℕ, 0 < a (k + 1))
    {r t : ℕ}
    (ht1 : 1 ≤ t)
    (htle : t ≤ a (r + 1)) :
    continuantDenPrev a r + t * continuantDen a r
      ≤ continuantDen a (r + 1) := by
  have _ := hpos
  have _ := ht1
  rw [continuantDen_succ]
  simpa [add_comm] using
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (continuantDen a r) htle)
      (continuantDenPrev a r)

private theorem path_den_ge_first_of_block
    {a : ℕ → ℕ} {r t : ℕ}
    (ht1 : 1 ≤ t) :
    continuantDenPrev a r + continuantDen a r
      ≤ continuantDenPrev a r + t * continuantDen a r := by
  simpa using
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (continuantDen a r) ht1)
      (continuantDenPrev a r)

/-- After a block with previous/current denominators `q'`, `q` and digit `A`,
the first two later path denominators are `(A + 1) * q + q'` and
`(2 * A + 1) * q + 2 * q'`; there is no canonical path denominator strictly
between them. -/
private theorem no_path_between_next1_next2
    {a : ℕ → ℕ} {n A q q' R : ℕ}
    (hpos : ∀ k : ℕ, 0 < a (k + 1))
    (hA : A = a (n + 1))
    (hq : q = continuantDen a n)
    (hq' : q' = continuantDenPrev a n)
    (hR : CFDenominatorPath a R)
    (hgap :
      (A + 1) * q + q' < R ∧
        R < (2 * A + 1) * q + 2 * q') :
    False := by
  rcases hR with ⟨r, t, ht1, htle, hReq⟩
  by_cases hr_le_n : r ≤ n
  · have hR_le_principal :
        R ≤ A * q + q' := by
      rw [hReq]
      have hle_next :
          continuantDenPrev a r + t * continuantDen a r
            ≤ continuantDen a (r + 1) :=
        path_den_le_next_principal hpos ht1 htle
      have hmono :
          continuantDen a (r + 1) ≤ continuantDen a (n + 1) :=
        continuantDen_mono_of_partials hpos (by omega)
      have hprincipal :
          continuantDen a (n + 1) = A * q + q' := by
        rw [continuantDen_succ]
        subst A
        subst q
        subst q'
        rfl
      omega
    have hqpos : 0 < q := by
      subst q
      exact continuantDen_pos_of_partials a hpos n
    have hstep : A * q + q' < (A + 1) * q + q' := by
      rw [show (A + 1) * q = A * q + q by ring]
      omega
    omega
  · have hn_lt_r : n < r := Nat.lt_of_not_ge hr_le_n
    by_cases hr_eq_succ : r = n + 1
    · subst r
      rw [hReq] at hgap
      have hprev :
          continuantDenPrev a (n + 1) = q := by
        subst q
        exact continuantDenPrev_succ a n
      have hden :
          continuantDen a (n + 1) = A * q + q' := by
        rw [continuantDen_succ]
        subst A
        subst q
        subst q'
        rfl
      by_cases ht_eq_one : t = 1
      · subst t
        rw [hprev, hden] at hgap
        have hsame : q + 1 * (A * q + q') = (A + 1) * q + q' := by
          ring
        omega
      · have ht_ge_two : 2 ≤ t := by omega
        have hlower :
            (2 * A + 1) * q + 2 * q'
              ≤ continuantDenPrev a (n + 1) +
                  t * continuantDen a (n + 1) := by
          rw [hprev, hden]
          have hqpos : 0 < q := by
            subst q
            exact continuantDen_pos_of_partials a hpos n
          have hmul :
              2 * (A * q + q') ≤ t * (A * q + q') :=
            Nat.mul_le_mul_right (A * q + q') ht_ge_two
          rw [show (2 * A + 1) * q + 2 * q' =
              q + 2 * (A * q + q') by ring]
          exact Nat.add_le_add_left hmul q
        omega
    · have hsucc_lt_r : n + 1 < r := by omega
      rw [hReq] at hgap
      have hfirst_block :
          (2 * A + 1) * q + 2 * q'
            ≤ continuantDenPrev a r + t * continuantDen a r := by
        have hbase_den :
            continuantDen a (n + 1) = A * q + q' := by
          rw [continuantDen_succ]
          subst A
          subst q
          subst q'
          rfl
        have hbase_prev :
            continuantDenPrev a (n + 1) = q := by
          subst q
          exact continuantDenPrev_succ a n
        have hden_succ_ge :
            continuantDen a (n + 2)
              ≥ continuantDen a (n + 1) + continuantDen a n := by
          rw [continuantDen_succ]
          have hpos_digit : 0 < a (n + 2) := hpos (n + 1)
          have hqpos : 0 < continuantDen a (n + 1) :=
            continuantDen_pos_of_partials a hpos (n + 1)
          nlinarith [Nat.succ_le_iff.mp hpos_digit]
        have hden_r_ge :
            continuantDen a r ≥ continuantDen a (n + 2) :=
          continuantDen_mono_of_partials hpos (by omega)
        have hprev_r_ge :
            continuantDenPrev a r ≥ continuantDen a (n + 1) := by
          cases r with
          | zero => omega
          | succ r' =>
              have hr'ge : n + 1 ≤ r' := by omega
              rw [continuantDenPrev_succ]
              exact continuantDen_mono_of_partials hpos hr'ge
        have hpath_ge :
            continuantDenPrev a r + continuantDen a r
              ≤ continuantDenPrev a r + t * continuantDen a r :=
          path_den_ge_first_of_block ht1
        have htarget :
            (2 * A + 1) * q + 2 * q'
              ≤ continuantDenPrev a r + continuantDen a r := by
          have htarget_base :
              (2 * A + 1) * q + 2 * q'
                ≤ continuantDen a (n + 1) + continuantDen a (n + 2) := by
            rw [hbase_den]
            subst q
            subst q'
            subst A
            nlinarith
          nlinarith
        exact le_trans htarget hpath_ge
      omega

/-- In one fixed block, there is no path denominator strictly between two
adjacent current-block denominators. -/
private theorem no_path_between_same_block_adjacent
    {a : ℕ → ℕ} {n m R : ℕ}
    (hpos : ∀ k : ℕ, 0 < a (k + 1))
    (hm1 : 1 ≤ m)
    (hmnext : m + 1 ≤ a (n + 1))
    (hR : CFDenominatorPath a R)
    (hgap :
      continuantDenPrev a n + m * continuantDen a n < R ∧
        R < continuantDenPrev a n + (m + 1) * continuantDen a n) :
    False := by
  rcases hR with ⟨r, t, ht1, htle, hReq⟩
  by_cases hr_lt : r < n
  · have hR_le_prev :
        R ≤ continuantDen a n := by
      rw [hReq]
      have hle_next :
          continuantDenPrev a r + t * continuantDen a r
            ≤ continuantDen a (r + 1) :=
        path_den_le_next_principal hpos ht1 htle
      have hmono :
          continuantDen a (r + 1) ≤ continuantDen a n :=
        continuantDen_mono_of_partials hpos (by omega)
      exact le_trans hle_next hmono
    have hleft_ge :
        continuantDen a n
          ≤ continuantDenPrev a n + m * continuantDen a n := by
      have hmul :
          continuantDen a n ≤ m * continuantDen a n :=
        Nat.le_mul_of_pos_left (continuantDen a n) hm1
      omega
    omega
  · by_cases hr_eq : r = n
    · subst r
      rw [hReq] at hgap
      have ht_le_m_or_ge : t ≤ m ∨ m + 1 ≤ t := by omega
      rcases ht_le_m_or_ge with htm | hmt
      · have hle :
            continuantDenPrev a n + t * continuantDen a n
              ≤ continuantDenPrev a n + m * continuantDen a n :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_right (continuantDen a n) htm)
            _
        omega
      · have hge :
            continuantDenPrev a n + (m + 1) * continuantDen a n
              ≤ continuantDenPrev a n + t * continuantDen a n :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_right (continuantDen a n) hmt)
            _
        omega
    · have hn_lt_r : n < r := by omega
      rw [hReq] at hgap
      have hR_ge_next :
          continuantDen a (n + 1)
            ≤ continuantDenPrev a r + t * continuantDen a r := by
        have hden_next_le_r :
            continuantDen a (n + 1) ≤ continuantDen a r :=
          continuantDen_mono_of_partials hpos (by omega)
        have hden_r_le_path :
            continuantDen a r ≤
              continuantDenPrev a r + t * continuantDen a r := by
          have hmul :
              continuantDen a r ≤ t * continuantDen a r :=
            Nat.le_mul_of_pos_left (continuantDen a r) ht1
          omega
        exact le_trans hden_next_le_r hden_r_le_path
      have hright_le_next :
          continuantDenPrev a n + (m + 1) * continuantDen a n
            ≤ continuantDen a (n + 1) := by
        rw [continuantDen_succ]
        simpa [add_comm] using
          Nat.add_le_add_left
            (Nat.mul_le_mul_right (continuantDen a n) hmnext)
            (continuantDenPrev a n)
      omega

/-- There is no path denominator strictly between a principal denominator
`A*q+q'` and the first denominator in the next local block `(A+1)*q+q'`. -/
private theorem no_path_between_principal_and_next1
    {a : ℕ → ℕ} {n A q q' R : ℕ}
    (hpos : ∀ k : ℕ, 0 < a (k + 1))
    (hA : A = a (n + 1))
    (hq : q = continuantDen a n)
    (hq' : q' = continuantDenPrev a n)
    (hR : CFDenominatorPath a R)
    (hgap : A * q + q' < R ∧ R < (A + 1) * q + q') :
    False := by
  rcases hR with ⟨r, t, ht1, htle, hReq⟩
  by_cases hr_le_n : r ≤ n
  · have hR_le :
        R ≤ A * q + q' := by
      rw [hReq]
      have hle_next :
          continuantDenPrev a r + t * continuantDen a r
            ≤ continuantDen a (r + 1) :=
        path_den_le_next_principal hpos ht1 htle
      have hmono :
          continuantDen a (r + 1) ≤ continuantDen a (n + 1) :=
        continuantDen_mono_of_partials hpos (by omega)
      have hprincipal :
          continuantDen a (n + 1) = A * q + q' := by
        rw [continuantDen_succ]
        subst A
        subst q
        subst q'
        rfl
      omega
    omega
  · have hn_lt_r : n < r := Nat.lt_of_not_ge hr_le_n
    by_cases hr_eq_succ : r = n + 1
    · subst r
      rw [hReq] at hgap
      have hprev :
          continuantDenPrev a (n + 1) = q := by
        subst q
        exact continuantDenPrev_succ a n
      have hden :
          continuantDen a (n + 1) = A * q + q' := by
        rw [continuantDen_succ]
        subst A
        subst q
        subst q'
        rfl
      have ht_cases : t = 1 ∨ 2 ≤ t := by omega
      rcases ht_cases with ht | ht
      · subst t
        rw [hprev, hden] at hgap
        have hsame : q + 1 * (A * q + q') = (A + 1) * q + q' := by
          ring
        omega
      · rw [hprev, hden] at hgap
        have hqpos : 0 < q := by
          subst q
          exact continuantDen_pos_of_partials a hpos n
        have htwomul :
            2 * (A * q + q') ≤ t * (A * q + q') :=
          Nat.mul_le_mul_right (A * q + q') ht
        have htarget :
            (A + 1) * q + q' ≤ q + 2 * (A * q + q') := by
          nlinarith
        have hlower :
            (A + 1) * q + q' ≤ q + t * (A * q + q') := by
          exact le_trans htarget (Nat.add_le_add_left htwomul q)
        omega
    · have hsucc_lt_r : n + 1 < r := by omega
      rw [hReq] at hgap
      have hge_next1 :
          (A + 1) * q + q'
            ≤ continuantDenPrev a r + t * continuantDen a r := by
        have hbase_den :
            continuantDen a (n + 1) = A * q + q' := by
          rw [continuantDen_succ]
          subst A
          subst q
          subst q'
          rfl
        have hprev_r_ge :
            continuantDenPrev a r ≥ continuantDen a (n + 1) := by
          cases r with
          | zero => omega
          | succ r' =>
              have hr'ge : n + 1 ≤ r' := by omega
              rw [continuantDenPrev_succ]
              exact continuantDen_mono_of_partials hpos hr'ge
        have hpath_ge :
            continuantDenPrev a r + continuantDen a r
              ≤ continuantDenPrev a r + t * continuantDen a r :=
          path_den_ge_first_of_block ht1
        have hden_r_ge_q :
            q ≤ continuantDen a r := by
          subst q
          exact continuantDen_mono_of_partials hpos (by omega)
        have htarget_eq :
            (A + 1) * q + q' = (A * q + q') + q := by
          ring
        rw [htarget_eq]
        have hbase_le_prev :
            A * q + q' ≤ continuantDenPrev a r := by
          rw [← hbase_den]
          exact hprev_r_ge
        exact le_trans (Nat.add_le_add hbase_le_prev hden_r_ge_q) hpath_ge
      omega

/-- Ordered first-deviation case for the parity-filtered continued-fraction
denominator set. This is the local two-denominator argument: the first
different canonical partial quotient of `x` is strictly smaller than that of
`y`. -/
private theorem oddCFDenoms_ne_of_firstDiff_lt
    {x y : ℝ}
    (hxirr : IsIrrational x) (hyirr : IsIrrational y)
    (hxI : x ∈ Set.Icc (1 : ℝ) 2)
    (hyI : y ∈ Set.Icc (1 : ℝ) 2)
    {j : ℕ}
    (hprefix : ∀ i : ℕ, i < j →
      simplePartialQuotient x i = simplePartialQuotient y i)
    (hlt :
      simplePartialQuotient x j < simplePartialQuotient y j) :
    oddCFDenoms x ≠ oddCFDenoms y := by
  have hx0 : simplePartialQuotient x 0 = 1 :=
    simplePartialQuotient_zero_eq_one_of_mem_Icc hxirr hxI
  have hy0 : simplePartialQuotient y 0 = 1 :=
    simplePartialQuotient_zero_eq_one_of_mem_Icc hyirr hyI
  have hjpos : 0 < j := by
    by_contra hj0
    have hj : j = 0 := Nat.eq_zero_of_not_pos hj0
    subst j
    rw [hx0, hy0] at hlt
    omega
  let n : ℕ := j - 1
  have hn1 : n + 1 = j := by
    dsimp [n]
    omega
  let ax : ℕ → ℕ := simplePartialQuotient x
  let ay : ℕ → ℕ := simplePartialQuotient y
  let a : ℕ := ax j
  let b : ℕ := ay j
  let p : ℕ := continuantNum ax n
  let p' : ℕ := continuantNumPrev ax n
  let q : ℕ := continuantDen ax n
  let q' : ℕ := continuantDenPrev ax n
  let X₁ : ℕ := (a + 1) * q + q'
  let Y : ℕ := (a + 2) * q + q'
  let X₂ : ℕ := (2 * a + 1) * q + 2 * q'
  let PY : ℕ := (a + 2) * p + p'
  let PX₂ : ℕ := (2 * a + 1) * p + 2 * p'
  have hab : a < b := by
    dsimp [a, b, ax, ay]
    simpa using hlt
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxI.1
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hyI.1
  have hxcf : IsSimpleCFExpansion x ax := by
    simpa [ax] using simplePartialQuotient_isSimpleCFExpansion hxpos hxirr
  have hycf : IsSimpleCFExpansion y ay := by
    simpa [ay] using simplePartialQuotient_isSimpleCFExpansion hypos hyirr
  have hprefix_to_n : ∀ i : ℕ, i ≤ n → ax i = ay i := by
    intro i hi
    dsimp [ax, ay]
    exact hprefix i (by omega)
  have hnum_eq : continuantNum ax n = continuantNum ay n :=
    continuantNum_eq_of_eq_on_prefix n hprefix_to_n
  have hden_eq : continuantDen ax n = continuantDen ay n :=
    continuantDen_eq_of_eq_on_prefix n hprefix_to_n
  have hnumPrev_eq : continuantNumPrev ax n = continuantNumPrev ay n :=
    continuantNumPrev_eq_of_eq_on_prefix hprefix_to_n
  have hdenPrev_eq : continuantDenPrev ax n = continuantDenPrev ay n :=
    continuantDenPrev_eq_of_eq_on_prefix hprefix_to_n
  by_cases hPYodd : Odd PY
  · have hb_ge_or_eq : a + 2 ≤ b ∨ b = a + 1 := by omega
    have hY_mem_y : Y ∈ oddCFDenoms y := by
      rcases hb_ge_or_eq with hbge | hbeq
      · have hYeq :
            Y = continuantDenPrev ay n + (a + 2) * continuantDen ay n := by
          dsimp [Y, q, q']
          rw [← hdenPrev_eq, ← hden_eq]
          ring
        rw [hYeq]
        refine mem_oddCFDenoms_of_canonical_path_odd
          (α := y) (a := ay) hycf
          (n := n) (t := a + 2)
          ?_ ?_ ?_ ?_
        · omega
        · rw [hn1]
          dsimp [b] at hbge
          exact hbge
        · have hnumexpr :
              continuantNumPrev ay n + (a + 2) * continuantNum ay n = PY := by
            dsimp [PY, p, p']
            rw [← hnumPrev_eq, ← hnum_eq]
            ring
          rw [hnumexpr]
          exact hPYodd
        · have hdenpos : 0 < continuantDen ay n :=
            continuantDen_pos_of_partials ay hycf.1 n
          have hmul : 2 ≤ (a + 2) * continuantDen ay n := by
            nlinarith
          omega
      · have hdenPrev_j : continuantDenPrev ay j = q := by
          rw [← hn1]
          dsimp [q]
          rw [continuantDenPrev_succ]
          exact hden_eq.symm
        have hden_j : continuantDen ay j = b * q + q' := by
          rw [← hn1]
          rw [continuantDen_succ]
          dsimp [b, q, q']
          rw [← hn1]
          rw [← hden_eq, ← hdenPrev_eq]
        have hYeq :
            Y = continuantDenPrev ay j + 1 * continuantDen ay j := by
          rw [hdenPrev_j, hden_j, hbeq]
          dsimp [Y]
          ring
        rw [hYeq]
        refine mem_oddCFDenoms_of_canonical_path_odd
          (α := y) (a := ay) hycf
          (n := j) (t := 1)
          (by norm_num) ?_ ?_ ?_
        · exact Nat.succ_le_iff.mpr (hycf.1 j)
        · have hnumPrev_j : continuantNumPrev ay j = p := by
            rw [← hn1]
            dsimp [p]
            rw [continuantNumPrev_succ]
            exact hnum_eq.symm
          have hnum_j : continuantNum ay j = b * p + p' := by
            rw [← hn1]
            rw [continuantNum_succ]
            dsimp [b, p, p']
            rw [← hn1]
            rw [← hnum_eq, ← hnumPrev_eq]
          have hnumexpr :
              continuantNumPrev ay j + 1 * continuantNum ay j = PY := by
            rw [hnumPrev_j, hnum_j, hbeq]
            dsimp [PY]
            ring
          rw [hnumexpr]
          exact hPYodd
        · have hqpos : 0 < q := by
            dsimp [q]
            exact continuantDen_pos_of_partials ax hxcf.1 n
          have hprevpos : 0 < continuantDenPrev ay j := by
            rw [hdenPrev_j]
            exact hqpos
          have hdenpos : 0 < continuantDen ay j :=
            continuantDen_pos_of_partials ay hycf.1 j
          omega
    have hY_not_x : Y ∉ oddCFDenoms x := by
      refine not_mem_oddCFDenoms_of_between_consecutive_canonical_denoms
        (Q₁ := X₁) (Q := Y) (Q₂ := X₂)
        hxpos hxirr ?hX1path ?hX2path ?hconsec ?hgap
      · refine ⟨j, 1, by norm_num, ?_, ?_⟩
        · exact Nat.succ_le_iff.mpr (hxcf.1 j)
        · dsimp [X₁, a, q, q']
          rw [← hn1]
          rw [continuantDenPrev_succ, continuantDen_succ]
          ring
      · by_cases hnext2 : 2 ≤ ax (j + 1)
        · refine ⟨j, 2, by norm_num, hnext2, ?_⟩
          dsimp [X₂, a, q, q']
          rw [← hn1]
          rw [continuantDenPrev_succ, continuantDen_succ]
          ring
        · have hnext1 : ax (j + 1) = 1 := by
            have hposnext : 0 < ax (j + 1) := hxcf.1 j
            omega
          refine ⟨j + 1, 1, by norm_num, ?_, ?_⟩
          · exact Nat.succ_le_iff.mpr (hxcf.1 (j + 1))
          · have hprev_j : continuantDenPrev ax j = q := by
              rw [← hn1]
              dsimp [q]
              rw [continuantDenPrev_succ]
            have hden_j : continuantDen ax j = a * q + q' := by
              rw [← hn1]
              rw [continuantDen_succ]
              dsimp [a, q, q']
              rw [hn1]
            have hprev_j1 : continuantDenPrev ax (j + 1) = continuantDen ax j := by
              rw [continuantDenPrev_succ]
            have hden_j1 :
                continuantDen ax (j + 1) =
                  continuantDen ax j + continuantDenPrev ax j := by
              rw [continuantDen_succ, hnext1]
              ring
            rw [hprev_j1, hden_j1, hden_j, hprev_j]
            dsimp [X₂]
            ring
      · intro R hR hRX1 hRX2
        exact no_path_between_next1_next2
          (a := ax) (n := n) (A := a) (q := q) (q' := q')
          hxcf.1 (by dsimp [a]; rw [hn1]) rfl rfl hR ⟨hRX1, hRX2⟩
      · have hqpos : 0 < q := by
          dsimp [q]
          exact continuantDen_pos_of_partials ax hxcf.1 n
        have hstrict : Y < X₂ := by
          by_cases hex : a = 1 ∧ q' = 0
          · rcases hex with ⟨ha1, hq0⟩
            exfalso
            have hn0 : n = 0 := by
              exact (continuantDenPrev_eq_zero_iff_of_partials ax hxcf.1 n).mp
                (by simpa [q'] using hq0)
            have hp : p = 1 := by
              dsimp [p, ax]
              rw [hn0]
              simpa [continuantNum] using hx0
            have hp' : p' = 1 := by
              dsimp [p']
              rw [hn0]
              simp [continuantNumPrev]
            have hpy : PY = 4 := by
              dsimp [PY]
              rw [ha1, hp, hp']
            rw [hpy] at hPYodd
            norm_num at hPYodd
          · dsimp [Y, X₂]
            by_cases ha1 : a = 1
            · have hq'pos : 0 < q' := by
                by_contra hq'not
                have hq'0 : q' = 0 := Nat.eq_zero_of_not_pos hq'not
                exact hex ⟨ha1, hq'0⟩
              rw [ha1]
              norm_num
              omega
            · have hapos : 0 < a := by
                dsimp [a]
                rw [← hn1]
                exact hxcf.1 n
              have ha2 : 2 ≤ a := by omega
              have hmul_lt : (a + 2) * q < (2 * a + 1) * q := by
                have hcoef_lt : a + 2 < 2 * a + 1 := by omega
                exact Nat.mul_lt_mul_of_pos_right hcoef_lt hqpos
              omega
        constructor
        · dsimp [X₁, Y]
          rw [show (a + 2) * q = (a + 1) * q + q by ring]
          omega
        · exact hstrict
    intro hsets
    exact hY_not_x (by simpa [hsets] using hY_mem_y)
  · -- Even `PY` case: prove `X₂ ∈ oddCFDenoms x` and `X₂ ∉ oddCFDenoms y`.
    have hPYeven : Even PY := Nat.not_odd_iff_even.mp hPYodd
    have hpodd : Odd p := by
      by_contra hpnot
      have hpeven : Even p := Nat.not_odd_iff_even.mp hpnot
      have hcop : Nat.Coprime p p' := by
        dsimp [p, p']
        exact continuantNum_coprime_prev ax n
      have hp'not_even : ¬ Even p' := by
        intro hp'even
        have hbad : ¬ Nat.Coprime p p' :=
          Nat.not_coprime_of_dvd_of_dvd
            (d := 2) (by norm_num)
            (even_iff_two_dvd.mp hpeven)
            (even_iff_two_dvd.mp hp'even)
        exact hbad hcop
      have hp'odd : Odd p' := Nat.not_even_iff_odd.mp hp'not_even
      have hterm_even : Even ((a + 2) * p) :=
        Even.mul_left hpeven (a + 2)
      have hpy_odd : Odd PY := by
        dsimp [PY]
        exact hterm_even.add_odd hp'odd
      exact hPYodd hpy_odd
    have hPX₂odd : Odd PX₂ := by
      have hcoefodd : Odd (2 * a + 1) := ⟨a, rfl⟩
      have hmainodd : Odd ((2 * a + 1) * p) :=
        hcoefodd.mul hpodd
      have htail_even : Even (2 * p') := even_two_mul p'
      dsimp [PX₂]
      exact hmainodd.add_even htail_even
    have hX₂_mem_x : X₂ ∈ oddCFDenoms x := by
      by_cases hnext2 : 2 ≤ ax (j + 1)
      · have hX₂eq :
            X₂ = continuantDenPrev ax j + 2 * continuantDen ax j := by
          dsimp [X₂, a, q, q']
          rw [← hn1]
          rw [continuantDenPrev_succ, continuantDen_succ]
          ring
        rw [hX₂eq]
        refine mem_oddCFDenoms_of_canonical_path_odd
          (α := x) (a := ax) hxcf
          (n := j) (t := 2)
          (by norm_num) hnext2 ?_ ?_
        · have hnumPrev_j : continuantNumPrev ax j = p := by
            rw [← hn1]
            dsimp [p]
            rw [continuantNumPrev_succ]
          have hnum_j : continuantNum ax j = a * p + p' := by
            rw [← hn1]
            rw [continuantNum_succ]
            dsimp [a, p, p']
            rw [hn1]
          have hnumexpr :
              continuantNumPrev ax j + 2 * continuantNum ax j = PX₂ := by
            rw [hnumPrev_j, hnum_j]
            dsimp [PX₂]
            ring
          rw [hnumexpr]
          exact hPX₂odd
        · have hqpos : 0 < q := by
            dsimp [q]
            exact continuantDen_pos_of_partials ax hxcf.1 n
          have hapos : 0 < a := by
            dsimp [a]
            rw [← hn1]
            exact hxcf.1 n
          have hcoef : 2 ≤ 2 * a + 1 := by omega
          have hmul : 2 ≤ (2 * a + 1) * q :=
            le_trans hcoef (Nat.le_mul_of_pos_right (2 * a + 1) hqpos)
          rw [← hX₂eq]
          dsimp [X₂]
          omega
      · have hnext1 : ax (j + 1) = 1 := by
          have hposnext : 0 < ax (j + 1) := hxcf.1 j
          omega
        have hX₂eq :
            X₂ = continuantDenPrev ax (j + 1) +
                1 * continuantDen ax (j + 1) := by
          have hprev_j : continuantDenPrev ax j = q := by
            rw [← hn1]
            dsimp [q]
            rw [continuantDenPrev_succ]
          have hden_j : continuantDen ax j = a * q + q' := by
            rw [← hn1]
            rw [continuantDen_succ]
            dsimp [a, q, q']
            rw [hn1]
          have hprev_j1 : continuantDenPrev ax (j + 1) = continuantDen ax j := by
            rw [continuantDenPrev_succ]
          have hden_j1 :
              continuantDen ax (j + 1) =
                continuantDen ax j + continuantDenPrev ax j := by
            rw [continuantDen_succ, hnext1]
            ring
          rw [hprev_j1, hden_j1, hden_j, hprev_j]
          dsimp [X₂]
          ring
        rw [hX₂eq]
        refine mem_oddCFDenoms_of_canonical_path_odd
          (α := x) (a := ax) hxcf
          (n := j + 1) (t := 1)
          (by norm_num) ?_ ?_ ?_
        · exact Nat.succ_le_iff.mpr (hxcf.1 (j + 1))
        · have hnumPrev_j : continuantNumPrev ax j = p := by
            rw [← hn1]
            dsimp [p]
            rw [continuantNumPrev_succ]
          have hnum_j : continuantNum ax j = a * p + p' := by
            rw [← hn1]
            rw [continuantNum_succ]
            dsimp [a, p, p']
            rw [hn1]
          have hnumPrev_j1 : continuantNumPrev ax (j + 1) = continuantNum ax j := by
            rw [continuantNumPrev_succ]
          have hnum_j1 :
              continuantNum ax (j + 1) =
                continuantNum ax j + continuantNumPrev ax j := by
            rw [continuantNum_succ, hnext1]
            ring
          have hnumexpr :
              continuantNumPrev ax (j + 1) +
                  1 * continuantNum ax (j + 1) = PX₂ := by
            rw [hnumPrev_j1, hnum_j1, hnum_j, hnumPrev_j]
            dsimp [PX₂]
            ring
          rw [hnumexpr]
          exact hPX₂odd
        · have hqpos : 0 < q := by
            dsimp [q]
            exact continuantDen_pos_of_partials ax hxcf.1 n
          have hapos : 0 < a := by
            dsimp [a]
            rw [← hn1]
            exact hxcf.1 n
          have hcoef : 2 ≤ 2 * a + 1 := by omega
          have hmul : 2 ≤ (2 * a + 1) * q :=
            le_trans hcoef (Nat.le_mul_of_pos_right (2 * a + 1) hqpos)
          rw [← hX₂eq]
          dsimp [X₂]
          omega
    have hX₂_all_y_reprs_even :
        ∀ P : ℕ,
          (∃ r t : ℕ,
            1 ≤ t ∧ t ≤ simplePartialQuotient y (r + 1) ∧
              P = continuantNumPrev (simplePartialQuotient y) r +
                  t * continuantNum (simplePartialQuotient y) r ∧
              X₂ = continuantDenPrev (simplePartialQuotient y) r +
                  t * continuantDen (simplePartialQuotient y) r) →
            Even P := by
      intro P hpair
      rcases hpair with ⟨r, t, ht1, htle, hP, hQ⟩
      by_cases hq0 : q' = 0
      · have hn0 : n = 0 := by
          exact (continuantDenPrev_eq_zero_iff_of_partials ax hxcf.1 n).mp
            (by simpa [q'] using hq0)
        have hj1' : j = 1 := by
          omega
        have hp0 : p = 1 := by
          dsimp [p]
          rw [hn0]
          simpa [ax, continuantNum] using hx0
        have hp0' : p' = 1 := by
          dsimp [p']
          rw [hn0]
          simp [continuantNumPrev]
        have hq0val : q = 1 := by
          dsimp [q]
          rw [hn0]
          simp [continuantDen]
        have hX₂val : X₂ = 2 * a + 1 := by
          dsimp [X₂]
          rw [hq0val, hq0]
          ring
        cases r with
        | zero =>
            have ht_eq : t = 2 * a + 1 := by
              rw [hX₂val] at hQ
              simp [continuantDenPrev, continuantDen] at hQ
              omega
            rw [hP]
            simp [continuantNumPrev, continuantNum, ht_eq, hy0]
            exact ⟨a + 1, by omega⟩
        | succ r' =>
            by_cases hr0 : r' = 0
            · subst r'
              have hb_y : ay 1 = b := by
                dsimp [b, ay]
                rw [hj1']
              have hden_block1 :
                  continuantDenPrev ay 1 + t * continuantDen ay 1 =
                    1 + t * b := by
                simp [continuantDenPrev, continuantDen, hb_y]
              have hden_eq_local : 2 * a + 1 = 1 + t * b := by
                rw [hX₂val] at hQ
                rw [hden_block1] at hQ
                exact hQ
              have ht_cases : t = 1 ∨ 2 ≤ t := by omega
              rcases ht_cases with ht_eq_one | ht_ge_two
              · subst t
                have hb_eq_2a : b = 2 * a := by
                  omega
                rw [hP]
                simp [continuantNumPrev, continuantNum, hb_y, hb_eq_2a, ay, hy0]
                exact ⟨a + 1, by omega⟩
              · have hcontr : 2 * a < t * b := by
                  have h2a_lt_2b : 2 * a < 2 * b :=
                    Nat.mul_lt_mul_of_pos_left hab (by norm_num)
                  have h2b_le_tb : 2 * b ≤ t * b :=
                    Nat.mul_le_mul_right b ht_ge_two
                  exact lt_of_lt_of_le h2a_lt_2b h2b_le_tb
                omega
            · exfalso
              have hr'pos : 0 < r' := Nat.pos_of_ne_zero hr0
              have hden1 : continuantDen ay 1 = b := by
                simp [continuantDen]
                dsimp [b, ay]
                rw [hj1']
              have hprev_ge_b :
                  b ≤ continuantDenPrev ay (Nat.succ r') := by
                rw [continuantDenPrev_succ]
                rw [← hden1]
                exact continuantDen_mono_of_partials hycf.1 (by omega)
              have hden_ge_b :
                  b ≤ continuantDen ay (Nat.succ r') := by
                rw [← hden1]
                exact continuantDen_mono_of_partials hycf.1 (by omega)
              have hden_le_tden :
                  continuantDen ay (Nat.succ r') ≤
                    t * continuantDen ay (Nat.succ r') :=
                Nat.le_mul_of_pos_left
                  (continuantDen ay (Nat.succ r')) ht1
              have hpath_ge_2b :
                  2 * b ≤
                    continuantDenPrev ay (Nat.succ r') +
                      t * continuantDen ay (Nat.succ r') := by
                omega
              have hX₂_lt_2b : X₂ < 2 * b := by
                rw [hX₂val]
                omega
              rw [← hQ] at hpath_ge_2b
              omega
      · have hq'pos : 0 < q' := by omega
        have hqpos : 0 < q := by
          dsimp [q]
          exact continuantDen_pos_of_partials ax hxcf.1 n
        have hq'_lt_q : q' < q := by
          by_cases hn1case : n = 1
          · by_contra hnot
            have hnot' : ¬ (1 < ax 1) := by
              intro hlt1
              apply hnot
              dsimp [q, q']
              rw [hn1case]
              simpa [continuantDen, continuantDenPrev] using hlt1
            have hax1pos : 0 < ax 1 := by
              simpa using hxcf.1 0
            have hax1le : ax 1 ≤ 1 := Nat.le_of_not_gt hnot'
            have hax1 : ax 1 = 1 :=
              le_antisymm hax1le hax1pos
            have hax0 : ax 0 = 1 := by
              dsimp [ax]
              exact hx0
            have hp_eq_two : p = 2 := by
              dsimp [p]
              rw [hn1case]
              simp [continuantNum, hax0, hax1]
            have hp'_eq_one : p' = 1 := by
              dsimp [p']
              rw [hn1case]
              simp [continuantNumPrev, continuantNum, hax0]
            have hPY_odd : Odd PY := by
              dsimp [PY]
              rw [hp_eq_two, hp'_eq_one]
              exact ⟨a + 2, by omega⟩
            exact hPYodd hPY_odd
          · have hn0_ne : n ≠ 0 := by
              intro hn0
              have hq'0 : q' = 0 := by
                dsimp [q']
                rw [hn0]
                simp [continuantDenPrev]
              omega
            have hn_ge_two : 2 ≤ n := by omega
            dsimp [q, q']
            exact continuantDenPrev_lt_den_of_two_le ax hxcf.1 hn_ge_two
        have hdenpos_ay : 0 < continuantDen ay n := by
          rw [← hden_eq]
          exact hqpos
        have hprev_lt_den_ay :
            continuantDenPrev ay n < continuantDen ay n := by
          rw [← hdenPrev_eq, ← hden_eq]
          exact hq'_lt_q
        have hpath : CFDenominatorPath ay X₂ := by
          refine ⟨r, t, ht1, htle, ?_⟩
          exact hQ
        by_cases hb_big : 2 * a + 2 ≤ b
        · exfalso
          have hgap :
              continuantDenPrev ay n + (2 * a + 1) * continuantDen ay n < X₂ ∧
                X₂ < continuantDenPrev ay n + (2 * a + 2) * continuantDen ay n := by
            constructor
            · dsimp [X₂, q, q']
              rw [hden_eq, hdenPrev_eq]
              omega
            · have hcoef_lt : 2 * a + 1 < 2 * a + 2 := by omega
              have hmul_lt :
                  (2 * a + 1) * continuantDen ay n <
                    (2 * a + 2) * continuantDen ay n :=
                Nat.mul_lt_mul_of_pos_right hcoef_lt hdenpos_ay
              have hupper_nat :
                  (2 * a + 1) * continuantDen ay n +
                      2 * continuantDenPrev ay n <
                    continuantDenPrev ay n +
                      (2 * a + 2) * continuantDen ay n := by
                have htwoprev :
                    2 * continuantDenPrev ay n <
                      continuantDen ay n + continuantDenPrev ay n := by
                  omega
                calc
                  (2 * a + 1) * continuantDen ay n +
                      2 * continuantDenPrev ay n
                      < (2 * a + 1) * continuantDen ay n +
                          (continuantDen ay n + continuantDenPrev ay n) :=
                        Nat.add_lt_add_left htwoprev _
                  _ = continuantDenPrev ay n +
                        (2 * a + 2) * continuantDen ay n := by
                        ring
              dsimp [X₂, q, q']
              rw [hden_eq, hdenPrev_eq]
              exact hupper_nat
          exact no_path_between_same_block_adjacent
            hycf.1
            (m := 2 * a + 1)
            (by omega)
            (by
              have hb_big' : 2 * a + 2 ≤ ay (n + 1) := by
                dsimp [b] at hb_big
                rwa [hn1]
              omega)
            hpath hgap
        · have hb_le_big : b ≤ 2 * a + 1 := by omega
          by_cases hb_eq : b = 2 * a + 1
          · exfalso
            have hgap :
                b * q + q' < X₂ ∧ X₂ < (b + 1) * q + q' := by
              constructor
              · dsimp [X₂]
                rw [hb_eq]
                omega
              · have hcoef_lt : b < b + 1 := Nat.lt_succ_self b
                have hmul_lt : b * q < (b + 1) * q :=
                  Nat.mul_lt_mul_of_pos_right hcoef_lt hqpos
                have hupper_nat :
                    (2 * a + 1) * q + 2 * q' <
                      (2 * a + 1 + 1) * q + q' := by
                  have htwoprev : 2 * q' < q + q' := by
                    omega
                  calc
                    (2 * a + 1) * q + 2 * q'
                        < (2 * a + 1) * q + (q + q') :=
                          Nat.add_lt_add_left htwoprev _
                    _ = (2 * a + 1 + 1) * q + q' := by
                          ring
                dsimp [X₂]
                rw [hb_eq]
                exact hupper_nat
            exact no_path_between_principal_and_next1
              (a := ay) (n := n) (A := b) (q := q) (q' := q')
              hycf.1
              (by dsimp [b]; rw [hn1])
              (by dsimp [q]; exact hden_eq)
              (by dsimp [q']; exact hdenPrev_eq)
              hpath hgap
          · have hb_le_2a : b ≤ 2 * a := by omega
            by_cases heqF1 : X₂ = (b + 1) * q + q'
            · exfalso

              have hcoef_le : b + 1 ≤ 2 * a + 1 := by
                omega

              have hmul_le : (b + 1) * q ≤ (2 * a + 1) * q :=
                Nat.mul_le_mul_right q hcoef_le

              have hF1_lt_X₂ : (b + 1) * q + q' < X₂ := by
                dsimp [X₂]
                omega

              have hbad : (b + 1) * q + q' < (b + 1) * q + q' := by
                calc
                  (b + 1) * q + q' < X₂ := hF1_lt_X₂
                  _ = (b + 1) * q + q' := heqF1

              exact (lt_irrefl ((b + 1) * q + q')) hbad
            · exfalso
              have hgap :
                  (b + 1) * q + q' < X₂ ∧
                    X₂ < (2 * b + 1) * q + 2 * q' := by
                constructor
                · have hcoef_le : b + 1 ≤ 2 * a + 1 := by
                    omega

                  have hmul_le : (b + 1) * q ≤ (2 * a + 1) * q :=
                    Nat.mul_le_mul_right q hcoef_le

                  have hle : (b + 1) * q + q' ≤ X₂ := by
                    dsimp [X₂]
                    omega

                  have hne : (b + 1) * q + q' ≠ X₂ := by
                    intro h
                    exact heqF1 h.symm

                  exact lt_of_le_of_ne hle hne

                · have hcoef_lt : 2 * a + 1 < 2 * b + 1 := by
                    omega

                  have hmul_lt : (2 * a + 1) * q < (2 * b + 1) * q :=
                    Nat.mul_lt_mul_of_pos_right hcoef_lt hqpos

                  dsimp [X₂]
                  omega
              exact no_path_between_next1_next2
                (a := ay) (n := n) (A := b) (q := q) (q' := q')
                hycf.1
                (by dsimp [b]; rw [hn1])
                (by dsimp [q]; exact hden_eq)
                (by dsimp [q']; exact hdenPrev_eq)
                hpath hgap

    have hX₂_not_y : X₂ ∉ oddCFDenoms y := by
      exact not_mem_oddCFDenoms_of_all_path_reprs_even
        hypos hyirr hX₂_all_y_reprs_even
    intro hsets
    exact hX₂_not_y (by simpa [hsets] using hX₂_mem_x)

/-- If two irrational numbers in `[1,2]` have the same canonical continued
fraction coefficients before index `j`, but differ at index `j`, then their
parity-filtered principal/intermediate denominator sets differ.

This is the first-deviation lemma for the equivalence-class problem. -/
theorem oddCFDenoms_ne_of_firstDiff_simplePartialQuotient
    {x y : ℝ}
    (hxirr : IsIrrational x) (hyirr : IsIrrational y)
    (hxI : x ∈ Set.Icc (1 : ℝ) 2)
    (hyI : y ∈ Set.Icc (1 : ℝ) 2)
    {j : ℕ}
    (hprefix : ∀ i : ℕ, i < j →
      simplePartialQuotient x i = simplePartialQuotient y i)
    (hdiff :
      simplePartialQuotient x j ≠ simplePartialQuotient y j) :
    oddCFDenoms x ≠ oddCFDenoms y := by
  rcases lt_or_gt_of_ne hdiff with hlt | hgt
  · exact oddCFDenoms_ne_of_firstDiff_lt
      hxirr hyirr hxI hyI hprefix hlt
  · have hprefix_symm : ∀ i : ℕ, i < j →
        simplePartialQuotient y i = simplePartialQuotient x i := by
      intro i hi
      exact (hprefix i hi).symm
    have hne :
        oddCFDenoms y ≠ oddCFDenoms x :=
      oddCFDenoms_ne_of_firstDiff_lt
        hyirr hxirr hyI hxI hprefix_symm hgt
    intro hxy
    exact hne hxy.symm

end IrrationalityAr
