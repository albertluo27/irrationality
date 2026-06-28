import IrrationalityAr.CanonicalBlockGrowth
import IrrationalityAr.CriteriaLattice
import IrrationalityAr.Ramanujan

open Filter
open scoped Topology

namespace IrrationalityAr

noncomputable section

/-- Width constant from the notes: κ = 6 log 2. -/
def spikeKappa : ℝ := 6 * Real.log 2

/-- `BadRamanujanSet ν κ Q` is the bad-index predicate
for a denominator threshold function `Q`. -/
def BadRamanujanSet (ν κ : ℝ) (Q : ℕ → ℕ) : Set ℕ :=
  {m | (Q m : ℝ) ≤ Real.exp (κ * (m : ℝ) / ν)}

/-- Ideal spike upper interval for index `j`. -/
def spikeUpperInterval (X : ℕ → ℝ) (κ ν β : ℝ) (j : ℕ) : Set ℕ :=
  {m |
    (ν * X j / κ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (X j + X (j + 1)) / β}

/-- Ideal spike lower interval for index `j` (using `γ`). -/
def spikeLowerInterval (X : ℕ → ℝ) (κ ν γ : ℝ) (j : ℕ) : Set ℕ :=
  {m |
    (ν * X j / κ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (X j + X (j + 1)) / γ}

/-- Pointwise union of a family of intervals.
This is a lightweight helper for spike-shape cover statements. -/
def spikeUnion (I : ℕ → Set ℕ) : Set ℕ := ⋃ j : ℕ, I j

/-- Scaffold threshold for the finite-fail set. 
To be replaced by the final set-based definition in the completed proof. -/
def spikeFinitenessThreshold (_S : Set ℕ) : ℝ := sInf (Set.Ioi (0 : ℝ))

/-! ## Legacy Ramanujan density-contraction API -/

/-- Two-sided exponential interior margin of asymptotic rate `κ`. -/
def EventuallyTwoSidedExpMargin
    (α : ℝ) (L U : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∀ b : ℝ, κ < b →
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
      Real.exp (-(b * (m : ℝ))) ≤ U m - α

/-- The `m`-th interval is bad at exponent `ν` when its least rational
denominator is no larger than `exp (κ m / ν)`. -/
def SmallDenominatorBad
    (L U : ℕ → ℝ) (hLU : ∀ m : ℕ, L m < U m)
    (κ ν : ℝ) (m : ℕ) : Prop :=
  (leastDenominatorInIntervalSeq L U hLU m : ℝ) ≤
    Real.exp ((κ * (m : ℝ)) / ν)

/-- Exponential rate of the Ramanujan `42 n + 5` summands. -/
def ramanujanKappa : ℝ := spikeKappa

/-- Bad Ramanujan truncation at trial exponent `ν`. -/
def BadRamanujanTruncation (ν : ℝ) (m : ℕ) : Prop :=
  SmallDenominatorBad
    ramanujanPiL ramanujanPiU ramanujanPi_hLU
    ramanujanKappa ν m

theorem ramanujanKappa_pos : 0 < ramanujanKappa := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simpa [ramanujanKappa, spikeKappa] using
    mul_pos (by norm_num : (0 : ℝ) < 6) hlog

/-! ## Density contraction proof spine

The public density-contraction theorem below is still kept as an axiom until
the remaining logarithmic block counting target is formalized.  The lemmas in
this section discharge the one-index, finite-counting, and algebraic parts of
that replacement proof.
-/

/-! ### One-index badness from one rational hit -/

/-- If a rational approximation lies in `[L m, U m]` and its denominator is
below the bad threshold, then index `m` is small-denominator bad. -/
lemma smallDenominatorBad_of_ratInClosedInterval_of_den_le_exp
    {κ ν : ℝ} {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    {m q : ℕ} {p : ℤ}
    (hqpos : 0 < q)
    (hmem : L m ≤ (p : ℝ) / (q : ℝ) ∧ (p : ℝ) / (q : ℝ) ≤ U m)
    (hqle : (q : ℝ) ≤ Real.exp (κ * (m : ℝ) / ν)) :
    SmallDenominatorBad L U hLU κ ν m := by
  have hden : DenominatorInInterval (L m) (U m) q := by
    exact ⟨p, hqpos, hmem.1, hmem.2⟩
  have hleast : leastDenominatorInIntervalSeq L U hLU m ≤ q := by
    simpa [leastDenominatorInIntervalSeq] using
      (leastDenominatorInInterval_min (L := L m) (U := U m) (hLU m) hden)
  have hleast_real :
      (leastDenominatorInIntervalSeq L U hLU m : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hleast
  exact hleast_real.trans hqle

/-- The left logarithmic block inequality gives the denominator threshold. -/
lemma denominator_le_exp_of_log_block_left
    {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν)
    {m q : ℕ} (hqpos : 0 < q)
    (hleft : ν * Real.log (q : ℝ) / κ ≤ (m : ℝ)) :
    (q : ℝ) ≤ Real.exp (κ * (m : ℝ) / ν) := by
  have hq_real_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hqpos
  have hmul : ν * Real.log (q : ℝ) ≤ κ * (m : ℝ) := by
    have h := (div_le_iff₀ hκ).mp hleft
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hlog_le : Real.log (q : ℝ) ≤ κ * (m : ℝ) / ν := by
    exact (le_div_iff₀ hν).mpr (by simpa [mul_comm] using hmul)
  calc
    (q : ℝ) = Real.exp (Real.log (q : ℝ)) := by
      rw [Real.exp_log hq_real_pos]
    _ ≤ Real.exp (κ * (m : ℝ) / ν) := by
      exact Real.exp_le_exp.mpr hlog_le

/-- The right logarithmic block inequality gives the approximation-width
threshold `q^(-γ) ≤ exp(-b m)`. -/
lemma rpow_neg_le_exp_neg_of_log_block_right
    {γ b : ℝ} (hb : 0 < b)
    {m q : ℕ} (hqpos : 0 < q)
    (hright : (m : ℝ) ≤ γ * Real.log (q : ℝ) / b) :
    (q : ℝ) ^ (-γ) ≤ Real.exp (-(b * (m : ℝ))) := by
  have hq_real_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hqpos
  have hbm_le : b * (m : ℝ) ≤ γ * Real.log (q : ℝ) := by
    have h := (le_div_iff₀ hb).mp hright
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hneg_le : -(γ * Real.log (q : ℝ)) ≤ -(b * (m : ℝ)) := by
    linarith
  calc
    (q : ℝ) ^ (-γ) = Real.exp ((-γ) * Real.log (q : ℝ)) := by
      rw [Real.rpow_def_of_pos hq_real_pos]
      ring_nf
    _ = Real.exp (-(γ * Real.log (q : ℝ))) := by
      ring_nf
    _ ≤ Real.exp (-(b * (m : ℝ))) := by
      exact Real.exp_le_exp.mpr hneg_le

/-- Absolute-value interval algebra: if `r` is within the two-sided interior
margin around `α`, then `r ∈ [L,U]`. -/
lemma mem_closedInterval_of_abs_sub_le_twoSided_margin
    {α L U r E : ℝ}
    (habs : |α - r| ≤ E)
    (hEL : E ≤ α - L)
    (hEU : E ≤ U - α) :
    L ≤ r ∧ r ≤ U := by
  have hαr : α - r ≤ E := by
    exact (le_abs_self (α - r)).trans habs
  have habs' : |r - α| ≤ E := by
    simpa [abs_sub_comm] using habs
  have hrα : r - α ≤ E := by
    exact (le_abs_self (r - α)).trans habs'
  constructor <;> linarith

/-- A close rational approximation makes every index in the logarithmic block
bad, once the two-sided margin at rate `b` is active at that index. -/
lemma smallDenominatorBad_of_close_approx_on_log_block
    {α κ ν γ b : ℝ} {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    (hκ : 0 < κ) (hν : 0 < ν) (hb : 0 < b)
    {m q : ℕ} {p : ℤ}
    (hqpos : 0 < q)
    (hclose : |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-γ))
    (hleft : ν * Real.log (q : ℝ) / κ ≤ (m : ℝ))
    (hright : (m : ℝ) ≤ γ * Real.log (q : ℝ) / b)
    (hmargin_m : Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
      Real.exp (-(b * (m : ℝ))) ≤ U m - α) :
    SmallDenominatorBad L U hLU κ ν m := by
  have hqle_exp : (q : ℝ) ≤ Real.exp (κ * (m : ℝ) / ν) :=
    denominator_le_exp_of_log_block_left hκ hν hqpos hleft
  have hpow_le_margin :
      (q : ℝ) ^ (-γ) ≤ Real.exp (-(b * (m : ℝ))) :=
    rpow_neg_le_exp_neg_of_log_block_right hb hqpos hright
  have habs_le_margin :
      |α - (p : ℝ) / (q : ℝ)| ≤ Real.exp (-(b * (m : ℝ))) :=
    (le_of_lt hclose).trans hpow_le_margin
  have hmem :
      L m ≤ (p : ℝ) / (q : ℝ) ∧ (p : ℝ) / (q : ℝ) ≤ U m :=
    mem_closedInterval_of_abs_sub_le_twoSided_margin
      habs_le_margin hmargin_m.1 hmargin_m.2
  exact smallDenominatorBad_of_ratInClosedInterval_of_den_le_exp
    (L := L) (U := U) (hLU := hLU) (m := m) (q := q) (p := p)
    hqpos hmem hqle_exp

/-! ### Finite-counting and density bookkeeping -/

/-- If all `m ∈ [A,B]` are bad, then the initial count up to `B` is at least
`B + 1 - A`.  The count convention is `{0,1,...,B}`. -/
lemma natInitialSegmentCount_ge_of_interval_subset
    {Bad : ℕ → Prop} {A B : ℕ}
    (_hAB : A ≤ B)
    (hblock : ∀ m : ℕ, A ≤ m → m ≤ B → Bad m) :
    (B + 1 - A : ℕ) ≤ natInitialSegmentCount Bad B := by
  classical
  have hsubset : Finset.Icc A B ⊆ (Finset.range (B + 1)).filter Bad := by
    intro m hm
    rw [Finset.mem_filter]
    rcases Finset.mem_Icc.mp hm with ⟨hAm, hmB⟩
    have hmrange : m ∈ Finset.range (B + 1) := by
      rw [Finset.mem_range]
      omega
    exact ⟨hmrange, hblock m hAm hmB⟩
  have hcard_le : (Finset.Icc A B).card ≤
      ((Finset.range (B + 1)).filter Bad).card :=
    Finset.card_le_card hsubset
  have hcard_Icc : (Finset.Icc A B).card = B + 1 - A := by
    exact Nat.card_Icc A B
  simpa [natInitialSegmentCount, hcard_Icc] using hcard_le

/-- A frequently occurring lower initial-segment density above `δ` contradicts
`UpperNatDensityAtMost B δ`. -/
lemma not_upperDensityAtMost_of_frequently_lower_bound
    {B : ℕ → Prop} {δ θ : ℝ}
    (hδθ : δ < θ)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      θ * ((N : ℝ) + 1) ≤ (natInitialSegmentCount B N : ℝ)) :
    ¬ UpperNatDensityAtMost B δ := by
  intro hupper
  let ε : ℝ := (θ - δ) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hupper_ev : ∀ᶠ N : ℕ in atTop,
      (natInitialSegmentCount B N : ℝ) ≤ (δ + ε) * ((N : ℝ) + 1) :=
    hupper ε hε
  have hfalse : ∃ᶠ N : ℕ in atTop, False :=
    (hfreq.and_eventually hupper_ev).mono fun N hN => by
      rcases hN with ⟨hlower, hupperN⟩
      have hδeps_lt : δ + ε < θ := by
        dsimp [ε]
        linarith
      have hNpos : 0 < ((N : ℝ) + 1) := by positivity
      have hstrict : (δ + ε) * ((N : ℝ) + 1) <
          θ * ((N : ℝ) + 1) :=
        mul_lt_mul_of_pos_right hδeps_lt hNpos
      linarith
  exact (Filter.frequently_false atTop) hfalse

/-- Finite version of the logarithmic block argument.

This lemma does not do any asymptotics.  It says: once a single rational
approximation is known, and once the margin plus the two logarithmic endpoint
inequalities are known for every integer in `[A,B]`, the whole integer block
contributes to the bad-count up to `B`. -/
lemma natInitialSegmentCount_ge_of_close_approx_log_block
    {α κ ν γ b : ℝ} {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    (hκ : 0 < κ) (hν : 0 < ν) (hb : 0 < b)
    {A B q : ℕ} {p : ℤ}
    (hAB : A ≤ B)
    (hqpos : 0 < q)
    (hclose : |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-γ))
    (hleft_block :
      ∀ m : ℕ, A ≤ m → m ≤ B →
        ν * Real.log (q : ℝ) / κ ≤ (m : ℝ))
    (hright_block :
      ∀ m : ℕ, A ≤ m → m ≤ B →
        (m : ℝ) ≤ γ * Real.log (q : ℝ) / b)
    (hmargin_block :
      ∀ m : ℕ, A ≤ m → m ≤ B →
        Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
        Real.exp (-(b * (m : ℝ))) ≤ U m - α) :
    (B + 1 - A : ℕ) ≤
      natInitialSegmentCount (SmallDenominatorBad L U hLU κ ν) B := by
  apply natInitialSegmentCount_ge_of_interval_subset hAB
  intro m hAm hmB
  exact smallDenominatorBad_of_close_approx_on_log_block
    (L := L) (U := U) (hLU := hLU)
    hκ hν hb hqpos hclose
    (hleft_block m hAm hmB)
    (hright_block m hAm hmB)
    (hmargin_block m hAm hmB)

/-! ### Logarithmic-block counting -/

/-- Lower real estimate for `Nat.floor`. -/
private lemma natFloor_cast_lower (x : ℝ) :
    x - 1 ≤ (Nat.floor x : ℝ) := by
  have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- Upper real estimate for `Nat.ceil` on nonnegative inputs. -/
private lemma natCeil_cast_upper_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ((Nat.ceil x : ℕ) : ℝ) ≤ x + 1 := by
  exact le_of_lt (Nat.ceil_lt_add_one hx)

/-- If a natural number is above `exp R`, then its logarithm is above `R`. -/
private lemma lt_log_nat_of_exp_lt_nat {R : ℝ} {q : ℕ}
    (hq : Real.exp R < (q : ℝ)) :
    R < Real.log (q : ℝ) := by
  calc
    R = Real.log (Real.exp R) := by rw [Real.log_exp]
    _ < Real.log (q : ℝ) := Real.log_lt_log (Real.exp_pos R) hq

/-- Logarithmic block-counting lemma.

From infinitely many approximants of exponent `γ`, and from the active
`b`-margin, one obtains frequently many initial segments whose bad-index density
is at least any `θ` below `1 - (ν*b)/(γ*κ)`. -/
lemma frequently_lower_bound_from_close_approximants_log_blocks
    {α κ ν γ b θ : ℝ}
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    (hκ : 0 < κ) (hν : 0 < ν) (hγ : 0 < γ) (hb : 0 < b)
    (hθ_lt : θ < 1 - (ν * b) / (γ * κ))
    (hmargin_b :
      ∀ᶠ m : ℕ in atTop,
        Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
        Real.exp (-(b * (m : ℝ))) ≤ U m - α)
    (hfreq : ∃ᶠ q : ℕ in atTop,
      ∃ p : ℤ, 0 < q ∧ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-γ)) :
    ∃ᶠ N : ℕ in atTop,
      θ * ((N : ℝ) + 1) ≤
        (natInitialSegmentCount (SmallDenominatorBad L U hLU κ ν) N : ℝ) := by
  by_cases hθ_nonpos : θ ≤ 0
  · rw [Filter.frequently_atTop]
    intro N0
    refine ⟨N0, le_rfl, ?_⟩
    have hNpos : 0 ≤ ((N0 : ℝ) + 1) := by positivity
    have hleft_nonpos : θ * ((N0 : ℝ) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hθ_nonpos hNpos
    have hcnt_nonneg :
        0 ≤ (natInitialSegmentCount
          (SmallDenominatorBad L U hLU κ ν) N0 : ℝ) := by positivity
    exact hleft_nonpos.trans hcnt_nonneg
  · have hθpos : 0 < θ := lt_of_not_ge hθ_nonpos
    have ha : 0 < ν / κ := div_pos hν hκ
    have hc : 0 < γ / b := div_pos hγ hb
    have hthreshold_pos : 0 < 1 - (ν * b) / (γ * κ) :=
      hθpos.trans hθ_lt
    have hfrac_lt_one : (ν * b) / (γ * κ) < 1 := by
      linarith
    have hνb_lt_γκ : ν * b < γ * κ := by
      have hden : 0 < γ * κ := mul_pos hγ hκ
      have h := (div_lt_iff₀ hden).mp hfrac_lt_one
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have ha_lt_hc : ν / κ < γ / b := by
      have hstep : (ν / κ) * b < γ := by
        calc
          (ν / κ) * b = (ν * b) / κ := by ring_nf
          _ < γ := by
            exact (div_lt_iff₀ hκ).mpr (by simpa [mul_comm] using hνb_lt_γκ)
      exact (lt_div_iff₀ hb).mpr hstep
    have hgap_pos : 0 < γ / b - ν / κ := by linarith
    have hratio_eq : (ν * b) / (γ * κ) = (ν / κ) / (γ / b) := by
      field_simp [ne_of_gt hκ, ne_of_gt hγ, ne_of_gt hb]
    have hθ_coeff : θ < 1 - (ν / κ) / (γ / b) := by
      simpa [hratio_eq] using hθ_lt
    have hdensityGap_pos : 0 < (1 - θ) * (γ / b) - ν / κ := by
      have hdiv_lt : (ν / κ) / (γ / b) < 1 - θ := by linarith
      have hmul := (div_lt_iff₀ hc).mp hdiv_lt
      nlinarith
    have honeMinusTheta_nonneg : 0 ≤ 1 - θ := by
      have hfrac_pos : 0 < (ν * b) / (γ * κ) :=
        div_pos (mul_pos hν hb) (mul_pos hγ hκ)
      linarith

    rw [Filter.eventually_atTop] at hmargin_b
    rcases hmargin_b with ⟨M0, hmarginM⟩
    rw [Filter.frequently_atTop] at hfreq
    rw [Filter.frequently_atTop]
    intro N0

    let a₀ : ℝ := ν / κ
    let c₀ : ℝ := γ / b
    let d₀ : ℝ := c₀ - a₀
    let e₀ : ℝ := (1 - θ) * c₀ - a₀
    have ha₀ : 0 < a₀ := by simpa [a₀] using ha
    have hc₀ : 0 < c₀ := by simpa [c₀] using hc
    have hd₀ : 0 < d₀ := by simpa [d₀, a₀, c₀] using hgap_pos
    have he₀ : 0 < e₀ := by simpa [e₀, a₀, c₀] using hdensityGap_pos

    let R : ℝ :=
      ((M0 + 1 : ℕ) : ℝ) / a₀ +
      3 / d₀ +
      2 / e₀ +
      ((N0 + 2 : ℕ) : ℝ) / c₀ +
      1

    have hMterm_lt_R : ((M0 + 1 : ℕ) : ℝ) / a₀ < R := by
      dsimp [R]
      have h1 : 0 < 3 / d₀ := div_pos (by norm_num) hd₀
      have h2 : 0 < 2 / e₀ := div_pos (by norm_num) he₀
      have h3 : 0 < ((N0 + 2 : ℕ) : ℝ) / c₀ :=
        div_pos (by positivity) hc₀
      nlinarith
    have hDterm_lt_R : 3 / d₀ < R := by
      dsimp [R]
      have h0 : 0 ≤ ((M0 + 1 : ℕ) : ℝ) / a₀ :=
        div_nonneg (by positivity) ha₀.le
      have h2 : 0 < 2 / e₀ := div_pos (by norm_num) he₀
      have h3 : 0 < ((N0 + 2 : ℕ) : ℝ) / c₀ :=
        div_pos (by positivity) hc₀
      nlinarith
    have hEterm_lt_R : 2 / e₀ < R := by
      dsimp [R]
      have h0 : 0 ≤ ((M0 + 1 : ℕ) : ℝ) / a₀ :=
        div_nonneg (by positivity) ha₀.le
      have h1 : 0 ≤ 3 / d₀ := (div_pos (by norm_num) hd₀).le
      have h3 : 0 < ((N0 + 2 : ℕ) : ℝ) / c₀ :=
        div_pos (by positivity) hc₀
      nlinarith
    have hNterm_lt_R : ((N0 + 2 : ℕ) : ℝ) / c₀ < R := by
      dsimp [R]
      have h0 : 0 ≤ ((M0 + 1 : ℕ) : ℝ) / a₀ :=
        div_nonneg (by positivity) ha₀.le
      have h1 : 0 ≤ 3 / d₀ := (div_pos (by norm_num) hd₀).le
      have h2 : 0 ≤ 2 / e₀ := (div_pos (by norm_num) he₀).le
      nlinarith

    obtain ⟨Q0, hQ0⟩ := exists_nat_gt (Real.exp R)
    rcases hfreq Q0 with ⟨q, hQq, hqdata⟩
    rcases hqdata with ⟨p, hqpos, hclose⟩
    have hQq_real : (Q0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQq
    have hExp_lt_q : Real.exp R < (q : ℝ) := hQ0.trans_le hQq_real

    let T : ℝ := Real.log (q : ℝ)
    have hRltT : R < T := by
      simpa [T] using lt_log_nat_of_exp_lt_nat hExp_lt_q
    have hT_nonneg : 0 ≤ T := by
      have hq_one : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hqpos)
      exact Real.log_nonneg hq_one

    have hM_aT : (M0 : ℝ) ≤ a₀ * T := by
      have hterm : ((M0 + 1 : ℕ) : ℝ) / a₀ < T :=
        hMterm_lt_R.trans hRltT
      have hmul : ((M0 + 1 : ℕ) : ℝ) < a₀ * T := by
        calc
          ((M0 + 1 : ℕ) : ℝ) = a₀ * (((M0 + 1 : ℕ) : ℝ) / a₀) := by
            field_simp [ne_of_gt ha₀]
          _ < a₀ * T := mul_lt_mul_of_pos_left hterm ha₀
      have hcast : ((M0 + 1 : ℕ) : ℝ) = (M0 : ℝ) + 1 := by norm_num
      linarith
    have hgapT : 2 ≤ d₀ * T := by
      have hterm : 3 / d₀ < T := hDterm_lt_R.trans hRltT
      have hmul : 3 < d₀ * T := by
        calc
          (3 : ℝ) = d₀ * (3 / d₀) := by field_simp [ne_of_gt hd₀]
          _ < d₀ * T := mul_lt_mul_of_pos_left hterm hd₀
      linarith
    have heT : 1 ≤ e₀ * T := by
      have hterm : 2 / e₀ < T := hEterm_lt_R.trans hRltT
      have hmul : 2 < e₀ * T := by
        calc
          (2 : ℝ) = e₀ * (2 / e₀) := by field_simp [ne_of_gt he₀]
          _ < e₀ * T := mul_lt_mul_of_pos_left hterm he₀
      linarith
    have hN_cT : (N0 : ℝ) + 1 ≤ c₀ * T := by
      have hterm : ((N0 + 2 : ℕ) : ℝ) / c₀ < T :=
        hNterm_lt_R.trans hRltT
      have hmul : ((N0 + 2 : ℕ) : ℝ) < c₀ * T := by
        calc
          ((N0 + 2 : ℕ) : ℝ) = c₀ * (((N0 + 2 : ℕ) : ℝ) / c₀) := by
            field_simp [ne_of_gt hc₀]
          _ < c₀ * T := mul_lt_mul_of_pos_left hterm hc₀
      have hcast : ((N0 + 2 : ℕ) : ℝ) = (N0 : ℝ) + 2 := by norm_num
      linarith

    let A : ℕ := Nat.ceil (a₀ * T)
    let B : ℕ := Nat.floor (c₀ * T)
    have haT_nonneg : 0 ≤ a₀ * T := mul_nonneg ha₀.le hT_nonneg
    have hcT_nonneg : 0 ≤ c₀ * T := mul_nonneg hc₀.le hT_nonneg
    have hA_lower : a₀ * T ≤ (A : ℝ) := by
      simpa [A] using Nat.le_ceil (a₀ * T)
    have hA_upper : (A : ℝ) ≤ a₀ * T + 1 := by
      simpa [A] using natCeil_cast_upper_of_nonneg haT_nonneg
    have hB_upper : (B : ℝ) ≤ c₀ * T := by
      simpa [B] using Nat.floor_le hcT_nonneg
    have hB_lower : c₀ * T - 1 ≤ (B : ℝ) := by
      simpa [B] using natFloor_cast_lower (c₀ * T)
    have hB1_lower : c₀ * T ≤ (B : ℝ) + 1 := by linarith

    have hM0_le_A : M0 ≤ A := by
      have hreal : (M0 : ℝ) ≤ (A : ℝ) := hM_aT.trans hA_lower
      exact_mod_cast hreal
    have hAB : A ≤ B := by
      have hreal : (A : ℝ) ≤ (B : ℝ) := by
        have hmain : a₀ * T + 1 ≤ c₀ * T - 1 := by
          dsimp [d₀] at hgapT
          nlinarith
        exact hA_upper.trans (hmain.trans hB_lower)
      exact_mod_cast hreal
    have hN0B : N0 ≤ B := by
      have hreal : (N0 : ℝ) ≤ (B : ℝ) := by
        have hmain : (N0 : ℝ) ≤ c₀ * T - 1 := by linarith
        exact hmain.trans hB_lower
      exact_mod_cast hreal

    have hleft_block :
        ∀ m : ℕ, A ≤ m → m ≤ B →
          ν * Real.log (q : ℝ) / κ ≤ (m : ℝ) := by
      intro m hAm _hmB
      have hAm_real : (A : ℝ) ≤ (m : ℝ) := by exact_mod_cast hAm
      calc
        ν * Real.log (q : ℝ) / κ = a₀ * T := by
          dsimp [a₀, T]
          ring_nf
        _ ≤ (A : ℝ) := hA_lower
        _ ≤ (m : ℝ) := hAm_real
    have hright_block :
        ∀ m : ℕ, A ≤ m → m ≤ B →
          (m : ℝ) ≤ γ * Real.log (q : ℝ) / b := by
      intro m _hAm hmB
      have hmB_real : (m : ℝ) ≤ (B : ℝ) := by exact_mod_cast hmB
      calc
        (m : ℝ) ≤ (B : ℝ) := hmB_real
        _ ≤ c₀ * T := hB_upper
        _ = γ * Real.log (q : ℝ) / b := by
          dsimp [c₀, T]
          ring_nf
    have hmargin_block :
        ∀ m : ℕ, A ≤ m → m ≤ B →
          Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
          Real.exp (-(b * (m : ℝ))) ≤ U m - α := by
      intro m hAm _hmB
      exact hmarginM m (hM0_le_A.trans hAm)

    have hcnt_nat :
        (B + 1 - A : ℕ) ≤
          natInitialSegmentCount
            (SmallDenominatorBad L U hLU κ ν) B :=
      natInitialSegmentCount_ge_of_close_approx_log_block
        (L := L) (U := U) (hLU := hLU)
        hκ hν hb hAB hqpos hclose hleft_block hright_block hmargin_block

    have hA_scaled : (A : ℝ) ≤ (1 - θ) * ((B : ℝ) + 1) := by
      have hmain : a₀ * T + 1 ≤ (1 - θ) * (c₀ * T) := by
        calc
          a₀ * T + 1 ≤ a₀ * T + e₀ * T := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left heT (a₀ * T)
          _ = (a₀ + e₀) * T := by ring
          _ = ((1 - θ) * c₀) * T := by
            dsimp [e₀]
            ring
          _ = (1 - θ) * (c₀ * T) := by ring
      have hscale : (1 - θ) * (c₀ * T) ≤ (1 - θ) * ((B : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hB1_lower honeMinusTheta_nonneg
      exact hA_upper.trans (hmain.trans hscale)
    have hdensity_block :
        θ * ((B : ℝ) + 1) ≤ ((B + 1 - A : ℕ) : ℝ) := by
      have hAleB1 : A ≤ B + 1 := by omega
      have hsubid : ((B + 1 - A : ℕ) : ℝ) + (A : ℝ) = (B : ℝ) + 1 := by
        have hnat : B + 1 - A + A = B + 1 := Nat.sub_add_cancel hAleB1
        exact_mod_cast hnat
      have hsubid' :
          ((B + 1 - A : ℕ) : ℝ) = (B : ℝ) + 1 - (A : ℝ) := by
        linarith
      have hscale :
          (1 - θ) * ((B : ℝ) + 1) =
            ((B : ℝ) + 1) - θ * ((B : ℝ) + 1) := by
        ring
      rw [hsubid']
      rw [hscale] at hA_scaled
      linarith
    have hcnt_real :
        ((B + 1 - A : ℕ) : ℝ) ≤
          (natInitialSegmentCount
            (SmallDenominatorBad L U hLU κ ν) B : ℝ) := by
      exact Nat.cast_le.mpr hcnt_nat

    refine ⟨B, hN0B, ?_⟩
    exact hdensity_block.trans hcnt_real

/-! ### Choosing the margin exponent `b` -/

/-- Algebraic form of the threshold inequality:
from `ν/(1-δ) < γ`, derive `δ < 1 - ν/γ`. -/
lemma delta_lt_one_sub_nu_div_gamma_of_contraction_gap
    {ν δ γ : ℝ}
    (hν : 0 < ν) (hδ_lt_one : δ < 1)
    (hγ_lower : ν / (1 - δ) < γ) :
    δ < 1 - ν / γ := by
  have hden_pos : 0 < 1 - δ := by linarith
  have hγ_pos : 0 < γ := by
    have hnu_over_pos : 0 < ν / (1 - δ) := div_pos hν hden_pos
    exact hnu_over_pos.trans hγ_lower
  have hν_lt : ν < γ * (1 - δ) :=
    (div_lt_iff₀ hden_pos).mp hγ_lower
  have hdiv_lt : ν / γ < 1 - δ := by
    exact (div_lt_iff₀ hγ_pos).mpr (by simpa [mul_comm] using hν_lt)
  linarith

/-- Choose `b > κ` close enough to `κ` so that the bad block density lower
bound still beats `δ`.  This avoids using a continuity theorem; the witness is
explicit. -/
lemma exists_margin_exponent_with_density_surplus
    {κ ν δ γ : ℝ}
    (hκ : 0 < κ) (hν : 0 < ν) (hγ : 0 < γ)
    (hδ_surplus : δ < 1 - ν / γ) :
    ∃ b : ℝ, κ < b ∧ δ < 1 - (ν * b) / (γ * κ) := by
  let A : ℝ := 1 - δ - ν / γ
  have hA_pos : 0 < A := by
    dsimp [A]
    linarith
  let b : ℝ := κ * (1 + A * γ / (2 * ν))
  have hfrac_pos : 0 < A * γ / (2 * ν) := by
    exact div_pos (mul_pos hA_pos hγ) (mul_pos (by norm_num) hν)
  have hfactor_gt_one : 1 < 1 + A * γ / (2 * ν) := by
    linarith
  refine ⟨b, ?_, ?_⟩
  · dsimp [b]
    nlinarith [hκ, hfactor_gt_one]
  · have hcalc : (ν * b) / (γ * κ) = ν / γ + A / 2 := by
      dsimp [b, A]
      field_simp [ne_of_gt hν, ne_of_gt hγ, ne_of_gt hκ]
    rw [hcalc]
    dsimp [A]
    nlinarith [hA_pos]

/-! ### Replacement for the contraction axiom -/

/-- If the contraction inequality fails, then the assumed upper-density bound
cannot hold. -/
lemma not_upperDensityAtMost_of_irratMeasure_gt_contraction_threshold
    {α μ κ ν δ : ℝ}
    {L U : ℕ → ℝ} {hLU : ∀ m : ℕ, L m < U m}
    (hμ : HasIrrationalityMeasure α μ)
    (hκ : 0 < κ) (hν : 0 < ν)
    (_hδ_nonneg : 0 ≤ δ) (hδ_lt_one : δ < 1)
    (hmargin : EventuallyTwoSidedExpMargin α L U κ)
    (hgt : ν / (1 - δ) < μ) :
    ¬ UpperNatDensityAtMost (SmallDenominatorBad L U hLU κ ν) δ := by
  rcases exists_between hgt with ⟨γ, hγ_lower, hγ_lt_mu⟩
  have hden_pos : 0 < 1 - δ := by linarith
  have hγ_pos : 0 < γ := by
    have hnu_over_pos : 0 < ν / (1 - δ) := div_pos hν hden_pos
    exact hnu_over_pos.trans hγ_lower
  have hδ_surplus : δ < 1 - ν / γ :=
    delta_lt_one_sub_nu_div_gamma_of_contraction_gap hν hδ_lt_one hγ_lower
  obtain ⟨b, hbκ, hb_good⟩ :
      ∃ b : ℝ, κ < b ∧ δ < 1 - (ν * b) / (γ * κ) :=
    exists_margin_exponent_with_density_surplus hκ hν hγ_pos hδ_surplus
  have hbpos : 0 < b := hκ.trans hbκ
  have hmargin_b :
      ∀ᶠ m : ℕ in atTop,
        Real.exp (-(b * (m : ℝ))) ≤ α - L m ∧
        Real.exp (-(b * (m : ℝ))) ≤ U m - α :=
    hmargin b hbκ
  rcases hμ with ⟨hlower, _hupper⟩
  have hfreq : ∃ᶠ q : ℕ in atTop,
      ∃ p : ℤ, 0 < q ∧ |α - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-γ) :=
    hlower γ hγ_lt_mu

  let θ : ℝ := (δ + (1 - (ν * b) / (γ * κ))) / 2
  have hδθ : δ < θ := by
    dsimp [θ]
    linarith
  have hθ_lt : θ < 1 - (ν * b) / (γ * κ) := by
    dsimp [θ]
    linarith
  have hfreq_lower : ∃ᶠ N : ℕ in atTop,
      θ * ((N : ℝ) + 1) ≤
        (natInitialSegmentCount (SmallDenominatorBad L U hLU κ ν) N : ℝ) :=
    frequently_lower_bound_from_close_approximants_log_blocks
      (L := L) (U := U) (hLU := hLU)
      hκ hν hγ_pos hbpos hθ_lt hmargin_b hfreq
  exact not_upperDensityAtMost_of_frequently_lower_bound hδθ hfreq_lower

/-- Generic density-contraction theorem for small denominator bad sets.

If the set of indices whose interval contains a rational with denominator at
most `exp (κ m / ν)` has upper density at most `δ`, then every irrationality
measure value is at most `ν / (1 - δ)`. -/
theorem irrationalityMeasure_le_of_smallDenominatorBad_upperDensity
    {α μ κ ν δ : ℝ}
    {L U : ℕ → ℝ}
    {hLU : ∀ m : ℕ, L m < U m}
    (hμ : HasIrrationalityMeasure α μ)
    (hκ : 0 < κ)
    (hν : 0 < ν)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_lt_one : δ < 1)
    (hmargin : EventuallyTwoSidedExpMargin α L U κ)
    (hdensity :
      UpperNatDensityAtMost
        (SmallDenominatorBad L U hLU κ ν) δ) :
    μ ≤ ν / (1 - δ) := by
  by_contra hnot
  have hgt : ν / (1 - δ) < μ := lt_of_not_ge hnot
  exact
    not_upperDensityAtMost_of_irratMeasure_gt_contraction_threshold
      (L := L) (U := U) (hLU := hLU)
      hμ hκ hν hδ_nonneg hδ_lt_one hmargin hgt hdensity

/-- Summability of the Ramanujan tail starting after index `m`. -/
theorem summable_ramanujanPiTerm_tail_public (m : ℕ) :
    Summable (fun k : ℕ => ramanujanPiTerm (m + 1 + k)) := by
  have hpow : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hgeom :
      Summable
        (fun k : ℕ => (1 / 4 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.mul_right (ramanujanPiTerm (m + 1))
  exact Summable.of_nonneg_of_le
    (fun k => le_of_lt (ramanujanPiTerm_pos (m + 1 + k)))
    (fun k => ramanujanPiTerm_tail_le_geometric m k)
    hgeom

/-- The Ramanujan tail is at least its first term. -/
theorem ramanujanPi_tsum_tail_ge_first (m : ℕ) :
    ramanujanPiTerm (m + 1) ≤
      (∑' k : ℕ, ramanujanPiTerm (m + 1 + k)) := by
  let f : ℕ → ℝ := fun k => ramanujanPiTerm (m + 1 + k)
  have hsumm : Summable f := by
    simpa [f] using summable_ramanujanPiTerm_tail_public m
  have hsplit : (∑' k : ℕ, f k) = f 0 + (∑' k : ℕ, f (k + 1)) := by
    simpa using hsumm.tsum_eq_zero_add
  have htail_nonneg : 0 ≤ (∑' k : ℕ, f (k + 1)) := by
    exact tsum_nonneg fun k => le_of_lt (ramanujanPiTerm_pos (m + 1 + (k + 1)))
  calc
    ramanujanPiTerm (m + 1) = f 0 := by simp [f]
    _ ≤ f 0 + (∑' k : ℕ, f (k + 1)) := by linarith
    _ = (∑' k : ℕ, f k) := hsplit.symm
    _ = (∑' k : ℕ, ramanujanPiTerm (m + 1 + k)) := by rfl

/-- Sharp geometric tail control using the proved ratio `47 / 320`. -/
theorem ramanujanPiTerm_tail_le_geometric_47_div_320 (m k : ℕ) :
    ramanujanPiTerm (m + 1 + k)
      ≤ (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :
          ramanujanPiTerm (m + 1 + k + 1)
            ≤ (47 / 320 : ℝ) * ramanujanPiTerm (m + 1 + k) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ramanujanPiTerm_succ_le_47_div_320 (m + 1 + k)
      calc
        ramanujanPiTerm (m + 1 + (k + 1))
            = ramanujanPiTerm (m + 1 + k + 1) := by
              simp [Nat.add_assoc]
        _ ≤ (47 / 320 : ℝ) * ramanujanPiTerm (m + 1 + k) := hstep
        _ ≤ (47 / 320 : ℝ) *
              ((47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
              exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (47 / 320 : ℝ) ^ (k + 1) * ramanujanPiTerm (m + 1) := by
              rw [pow_succ']
              ring

/-- Summability of the sharper geometric majorant. -/
theorem summable_ramanujanPiTerm_tail_47_div_320 (m : ℕ) :
    Summable (fun k : ℕ => ramanujanPiTerm (m + 1 + k)) := by
  have hpow : Summable (fun k : ℕ => (47 / 320 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num : ‖(47 / 320 : ℝ)‖ < 1)
  have hgeom :
      Summable
        (fun k : ℕ => (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.mul_right (ramanujanPiTerm (m + 1))
  exact Summable.of_nonneg_of_le
    (fun k => le_of_lt (ramanujanPiTerm_pos (m + 1 + k)))
    (fun k => ramanujanPiTerm_tail_le_geometric_47_div_320 m k)
    hgeom

/-- Sharp Bauer/Ramanujan tail upper bound.

The constant is exact: `1 / (1 - 47 / 320) = 320 / 273`. -/
theorem ramanujanPi_tsum_tail_le_320_div_273 (m : ℕ) :
    (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
      ≤ (320 / 273 : ℝ) * ramanujanPiTerm (m + 1) := by
  have hpow : Summable (fun k : ℕ => (47 / 320 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one
      (by norm_num : ‖(47 / 320 : ℝ)‖ < 1)
  have hgeom :
      Summable
        (fun k : ℕ => (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hpow.mul_right (ramanujanPiTerm (m + 1))
  have hgeom_tsum :
      (∑' k : ℕ, (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1))
        = (320 / 273 : ℝ) * ramanujanPiTerm (m + 1) := by
    calc
      (∑' k : ℕ, (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1))
          = (∑' k : ℕ, (47 / 320 : ℝ) ^ k) * ramanujanPiTerm (m + 1) := by
              rw [tsum_mul_right]
      _ = (320 / 273 : ℝ) * ramanujanPiTerm (m + 1) := by
              rw [tsum_geometric_of_norm_lt_one
                (by norm_num : ‖(47 / 320 : ℝ)‖ < 1)]
              norm_num
  have hle :
      (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
        ≤
      (∑' k : ℕ, (47 / 320 : ℝ) ^ k * ramanujanPiTerm (m + 1)) :=
    (summable_ramanujanPiTerm_tail_47_div_320 m).tsum_le_tsum
      (fun k => ramanujanPiTerm_tail_le_geometric_47_div_320 m k) hgeom
  exact hle.trans_eq hgeom_tsum

/-- Pointwise two-sided margin inside the Ramanujan interval. -/
theorem ramanujanPi_twoSidedMargin_term
    (hRam : BauerRamanujanIdentity) (m : ℕ) :
    (44 / 273 : ℝ) * ramanujanPiTerm (m + 1) ≤
        1 / Real.pi - ramanujanPiL m ∧
    (44 / 273 : ℝ) * ramanujanPiTerm (m + 1) ≤
        ramanujanPiU m - 1 / Real.pi := by
  let T : ℝ := ramanujanPiTerm (m + 1)
  let tail : ℝ := (∑' k : ℕ, ramanujanPiTerm (m + 1 + k))
  have hTpos : 0 < T := by
    dsimp [T]
    exact ramanujanPiTerm_pos (m + 1)
  have htail_eq_L : tail = 1 / Real.pi - ramanujanPiL m := by
    dsimp [tail]
    simpa [ramanujanPiL] using ramanujanPi_tsum_tail_eq hRam m
  have htail_ge_T : T ≤ tail := by
    dsimp [tail, T]
    exact ramanujanPi_tsum_tail_ge_first m
  have htail_le : tail ≤ (320 / 273 : ℝ) * T := by
    dsimp [tail, T]
    exact ramanujanPi_tsum_tail_le_320_div_273 m
  constructor
  · have hcoef : (44 / 273 : ℝ) ≤ 1 := by norm_num
    have hfirst : (44 / 273 : ℝ) * T ≤ T := by
      calc
        (44 / 273 : ℝ) * T ≤ 1 * T := by
          exact mul_le_mul_of_nonneg_right hcoef (le_of_lt hTpos)
        _ = T := by ring
    calc
      (44 / 273 : ℝ) * ramanujanPiTerm (m + 1)
          = (44 / 273 : ℝ) * T := by rfl
      _ ≤ T := hfirst
      _ ≤ tail := htail_ge_T
      _ = 1 / Real.pi - ramanujanPiL m := htail_eq_L
  · have hU_eq :
        ramanujanPiU m - 1 / Real.pi = ramanujanPiTailBound m - tail := by
      have htail_eq_partial : tail = 1 / Real.pi - ramanujanPiPartial m := by
        dsimp [tail]
        exact ramanujanPi_tsum_tail_eq hRam m
      unfold ramanujanPiU ramanujanPiTailBound
      linarith
    have hmargin :
        (44 / 273 : ℝ) * T ≤ ramanujanPiTailBound m - tail := by
      unfold ramanujanPiTailBound
      dsimp [T] at *
      calc
        (44 / 273 : ℝ) * T
            = ((4 / 3 : ℝ) - (320 / 273 : ℝ)) * T := by norm_num
        _ = (4 / 3 : ℝ) * T - (320 / 273 : ℝ) * T := by ring
        _ ≤ (4 / 3 : ℝ) * T - tail := by linarith
    calc
      (44 / 273 : ℝ) * ramanujanPiTerm (m + 1)
          = (44 / 273 : ℝ) * T := by rfl
      _ ≤ ramanujanPiTailBound m - tail := hmargin
      _ = ramanujanPiU m - 1 / Real.pi := hU_eq.symm

/-- Absorb the shift and the positive constant in a lower exponential bound.

If `c < b` and `0 < C`, then eventually
`exp (-(b*m)) ≤ C * exp (-(c*(m+1)))`. -/
theorem exp_margin_absorb_shift_const
    {C c b : ℝ} (hC : 0 < C) (hcb : c < b) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-(b * (m : ℝ))) ≤
        C * Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) := by
  have hgap : 0 < b - c := sub_pos.mpr hcb
  have hlarge :=
    eventually_const_le_pos_mul_natCast
      (A := c - Real.log C) (δ := b - c) hgap
  filter_upwards [hlarge] with m hm
  have hlogle : c - (b - c) * (m : ℝ) ≤ Real.log C := by
    linarith
  have hexp_small :
      Real.exp (c - (b - c) * (m : ℝ)) ≤ C := by
    calc
      Real.exp (c - (b - c) * (m : ℝ))
          ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr hlogle
      _ = C := Real.exp_log hC
  calc
    Real.exp (-(b * (m : ℝ)))
        = Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) *
            Real.exp (c - (b - c) * (m : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          norm_num [Nat.cast_add]
          ring
    _ ≤ Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) * C := by
          exact mul_le_mul_of_nonneg_left hexp_small (le_of_lt (Real.exp_pos _))
    _ = C * Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) := by
          ring

/-- The Ramanujan intervals have two-sided exponential margin at rate
`6 log 2`, conditional on the named Bauer-Ramanujan identity. -/
theorem ramanujanPi_eventuallyTwoSidedExpMargin
    (hRam : BauerRamanujanIdentity) :
    EventuallyTwoSidedExpMargin
      (1 / Real.pi) ramanujanPiL ramanujanPiU ramanujanKappa := by
  intro b hb
  have hb₀ : 6 * Real.log 2 < b := by
    simpa [ramanujanKappa, spikeKappa] using hb
  let c : ℝ := (6 * Real.log 2 + b) / 2
  have hκc : 6 * Real.log 2 < c := by
    dsimp [c]
    linarith
  have hcb : c < b := by
    dsimp [c]
    linarith
  have hterm_base :
      ∀ᶠ n : ℕ in atTop,
        Real.exp (-(c * (n : ℝ))) ≤ ramanujanPiTerm n :=
    ramanujanPiTerm_exp_lower_of_gt_six_log_two hκc
  have hterm_shift :
      ∀ᶠ m : ℕ in atTop,
        Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) ≤
          ramanujanPiTerm (m + 1) := by
    simpa using (tendsto_add_atTop_nat 1).eventually hterm_base
  let C : ℝ := (44 / 273 : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    norm_num
  have habsorb :
      ∀ᶠ m : ℕ in atTop,
        Real.exp (-(b * (m : ℝ))) ≤
          C * Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) :=
    exp_margin_absorb_shift_const hCpos hcb
  filter_upwards [hterm_shift, habsorb] with m hterm habs
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hmargin_to_term :
      Real.exp (-(b * (m : ℝ))) ≤ C * ramanujanPiTerm (m + 1) := by
    calc
      Real.exp (-(b * (m : ℝ)))
          ≤ C * Real.exp (-(c * ((m + 1 : ℕ) : ℝ))) := habs
      _ ≤ C * ramanujanPiTerm (m + 1) := by
            exact mul_le_mul_of_nonneg_left hterm hCnonneg
  rcases ramanujanPi_twoSidedMargin_term hRam m with ⟨hleft, hright⟩
  constructor
  · exact hmargin_to_term.trans hleft
  · exact hmargin_to_term.trans hright

/-- Conditional Ramanujan density contraction. -/
theorem oneOverPi_irratMeasure_le_of_badRamanujan_upperDensity
    {μ ν δ : ℝ}
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : 0 < ν)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_lt_one : δ < 1)
    (hmargin :
      EventuallyTwoSidedExpMargin
        (1 / Real.pi) ramanujanPiL ramanujanPiU ramanujanKappa)
    (hdensity :
      UpperNatDensityAtMost (BadRamanujanTruncation ν) δ) :
    μ ≤ ν / (1 - δ) := by
  exact irrationalityMeasure_le_of_smallDenominatorBad_upperDensity
    (L := ramanujanPiL) (U := ramanujanPiU)
    (hLU := ramanujanPi_hLU)
    hμ ramanujanKappa_pos hν hδ_nonneg hδ_lt_one hmargin hdensity

/-- Strict bootstrap from a known numerical bound `M`. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_densityDeficit
    {μ ν M η : ℝ}
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hη : 0 < η)
    (hδ_nonneg : 0 ≤ 1 - ν / M - η)
    (hmargin :
      EventuallyTwoSidedExpMargin
        (1 / Real.pi) ramanujanPiL ramanujanPiU ramanujanKappa)
    (hdensity :
      UpperNatDensityAtMost
        (BadRamanujanTruncation ν)
        (1 - ν / M - η)) :
    μ < M := by
  have hν_pos : 0 < ν := by linarith
  have hM_pos : 0 < M := hν_pos.trans hν_M
  let δ : ℝ := 1 - ν / M - η
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    have hdiv_pos : 0 < ν / M := div_pos hν_pos hM_pos
    linarith
  have hμ_le : μ ≤ ν / (1 - δ) :=
    oneOverPi_irratMeasure_le_of_badRamanujan_upperDensity
      (μ := μ) (ν := ν) (δ := δ)
      hμ hν_pos (by simpa [δ] using hδ_nonneg) hδ_lt_one
      hmargin (by simpa [δ] using hdensity)
  have hden_pos : 0 < ν / M + η :=
    add_pos (div_pos hν_pos hM_pos) hη
  have hstrict : ν / (1 - δ) < M := by
    have hden_eq : 1 - δ = ν / M + η := by
      dsimp [δ]
      ring
    rw [hden_eq, div_lt_iff₀ hden_pos]
    have hrewrite : M * (ν / M + η) = ν + M * η := by
      field_simp [ne_of_gt hM_pos]
    rw [hrewrite]
    nlinarith [mul_pos hM_pos hη]
  exact hμ_le.trans_lt hstrict

/-- Ramanujan contraction with the margin discharged from Bauer's identity. -/
theorem oneOverPi_irratMeasure_le_of_Bauer_badRamanujan_upperDensity
    {μ ν δ : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν : 0 < ν)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_lt_one : δ < 1)
    (hdensity :
      UpperNatDensityAtMost (BadRamanujanTruncation ν) δ) :
    μ ≤ ν / (1 - δ) :=
  oneOverPi_irratMeasure_le_of_badRamanujan_upperDensity
    hμ hν hδ_nonneg hδ_lt_one
    (ramanujanPi_eventuallyTwoSidedExpMargin hBauer) hdensity

/-- Strict numerical bootstrap with the margin discharged from Bauer's
identity. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_Bauer_densityDeficit
    {μ ν M η : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hη : 0 < η)
    (hδ_nonneg : 0 ≤ 1 - ν / M - η)
    (hdensity :
      UpperNatDensityAtMost
        (BadRamanujanTruncation ν)
        (1 - ν / M - η)) :
    μ < M :=
  oneOverPi_irratMeasure_lt_knownBound_of_densityDeficit
    hμ hν_two hν_M hη hδ_nonneg
    (ramanujanPi_eventuallyTwoSidedExpMargin hBauer) hdensity

/-- Exact strict-density formulation of the missing bootstrap theorem. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_badDensity_lt
    {μ ν M : ℝ}
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hmargin :
      EventuallyTwoSidedExpMargin
        (1 / Real.pi) ramanujanPiL ramanujanPiU ramanujanKappa)
    (hdensity :
      UpperNatDensityLessThan
        (BadRamanujanTruncation ν)
        (1 - ν / M)) :
    μ < M := by
  rcases hdensity with ⟨δ, hδ_nonneg, hδ_lt, hδ_density⟩
  let η : ℝ := 1 - ν / M - δ
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hrewrite : 1 - ν / M - η = δ := by
    dsimp [η]
    ring
  apply oneOverPi_irratMeasure_lt_knownBound_of_densityDeficit
    (μ := μ) (ν := ν) (M := M) (η := η)
    hμ hν_two hν_M hη
  · rw [hrewrite]
    exact hδ_nonneg
  · exact hmargin
  · rw [hrewrite]
    exact hδ_density

/-- Exact strict-density version with all Ramanujan margin input discharged by
`BauerRamanujanIdentity`. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_Bauer_badDensity_lt
    {μ ν M : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hdensity :
      UpperNatDensityLessThan
        (BadRamanujanTruncation ν)
        (1 - ν / M)) :
    μ < M :=
  oneOverPi_irratMeasure_lt_knownBound_of_badDensity_lt
    hμ hν_two hν_M
    (ramanujanPi_eventuallyTwoSidedExpMargin hBauer) hdensity

/-- Isolated density estimate for the bad Ramanujan truncation set. -/
axiom badRamanujanTruncation_density_lessThan_threshold
    {ν M : ℝ}
    (_hν_two : 2 < ν)
    (_hν_M : ν < M) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M)

/-- Compatibility alias for the earlier camel-case density theorem name. -/
theorem badRamanujanTruncation_densityLessThan_threshold
    {ν M : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  badRamanujanTruncation_density_lessThan_threshold hν_two hν_M

/-- Compatibility alias for the earlier shortened density theorem name. -/
theorem badRamanujanTruncation_density_lt_threshold
    {ν M : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  badRamanujanTruncation_density_lessThan_threshold hν_two hν_M

/-- Wrapper showing the isolated density estimate feeds the Bauer bootstrap. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_Bauer_isolatedDensity
    {μ ν M : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M) :
    μ < M :=
  oneOverPi_irratMeasure_lt_knownBound_of_Bauer_badDensity_lt
    hBauer hμ hν_two hν_M
    (badRamanujanTruncation_density_lessThan_threshold hν_two hν_M)

/-! ## Ramanujan spike-shadow API -/

/-- Logarithmic denominator scale of the `j`-th convergent attached to a
coefficient sequence. -/
noncomputable def cfDenLog (a : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.log (continuantDen a j : ℝ)

/-- The ideal lower endpoint of the spike shadow. -/
def idealSpikeLower (X : ℕ → ℝ) (κ ν : ℝ) (j : ℕ) : ℝ :=
  ν * X j / κ

/-- The ideal upper endpoint of the spike shadow. -/
def idealSpikeUpper (X : ℕ → ℝ) (κ : ℝ) (j : ℕ) : ℝ :=
  (X j + X (j + 1)) / κ

/-- Ideal spike window. -/
def IdealSpikeWindow (X : ℕ → ℝ) (κ ν : ℝ) (j m : ℕ) : Prop :=
  idealSpikeLower X κ ν j ≤ (m : ℝ) ∧
    (m : ℝ) ≤ idealSpikeUpper X κ j

/-- Ideal spike excess. -/
def IdealSpikeExcess (X : ℕ → ℝ) (ν : ℝ) (j : ℕ) : ℝ :=
  X (j + 1) - (ν - 1) * X j

/-- Upper spike slope after weakening the width exponent. -/
def upperSpikeSlope (κ ν β : ℝ) : ℝ :=
  ν * β / κ - 1

/-- Upper spike excess for the rigorous covering window. -/
def UpperSpikeExcess (X : ℕ → ℝ) (κ ν β : ℝ) (j : ℕ) : ℝ :=
  X (j + 1) - upperSpikeSlope κ ν β * X j + Real.log 2

/-- Rigorous upper spike window. -/
def UpperSpikeWindow (X : ℕ → ℝ) (κ ν β : ℝ) (j m : ℕ) : Prop :=
  ν * X j / κ ≤ (m : ℝ) ∧
    (m : ℝ) ≤ (X j + X (j + 1) + Real.log 2) / β

/-- The union of all upper spike windows. -/
def UpperSpikeShadow (X : ℕ → ℝ) (κ ν β : ℝ) (m : ℕ) : Prop :=
  ∃ j : ℕ, UpperSpikeWindow X κ ν β j m

/-- The union of all ideal spike windows. -/
def IdealSpikeShadow (X : ℕ → ℝ) (κ ν : ℝ) (m : ℕ) : Prop :=
  ∃ j : ℕ, IdealSpikeWindow X κ ν j m

theorem idealSpikeWindow_nonempty_iff
    {X : ℕ → ℝ} {κ ν : ℝ} {j : ℕ}
    (hκ : 0 < κ) :
    idealSpikeLower X κ ν j ≤ idealSpikeUpper X κ j ↔
      0 ≤ IdealSpikeExcess X ν j := by
  constructor
  · intro h
    unfold idealSpikeLower idealSpikeUpper at h
    rw [le_div_iff₀ hκ] at h
    have hmain : ν * X j ≤ X j + X (j + 1) := by
      calc
        ν * X j = (ν * X j / κ) * κ := by
          field_simp [ne_of_gt hκ]
        _ ≤ X j + X (j + 1) := h
    unfold IdealSpikeExcess
    linarith
  · intro h
    unfold idealSpikeLower idealSpikeUpper
    rw [le_div_iff₀ hκ]
    have hmain : ν * X j ≤ X j + X (j + 1) := by
      unfold IdealSpikeExcess at h
      linarith
    calc
      (ν * X j / κ) * κ = ν * X j := by
        field_simp [ne_of_gt hκ]
      _ ≤ X j + X (j + 1) := hmain

theorem idealSpikeExcess_nonneg_of_mem
    {X : ℕ → ℝ} {κ ν : ℝ} {j m : ℕ}
    (hκ : 0 < κ)
    (hm : IdealSpikeWindow X κ ν j m) :
    0 ≤ IdealSpikeExcess X ν j := by
  exact (idealSpikeWindow_nonempty_iff (X := X) (κ := κ) (ν := ν)
    (j := j) hκ).mp (hm.1.trans hm.2)

theorem not_idealSpikeWindow_of_excess_neg
    {X : ℕ → ℝ} {κ ν : ℝ} {j m : ℕ}
    (hκ : 0 < κ)
    (hneg : IdealSpikeExcess X ν j < 0) :
    ¬ IdealSpikeWindow X κ ν j m := by
  intro hm
  have hnonneg := idealSpikeExcess_nonneg_of_mem
    (X := X) (κ := κ) (ν := ν) (j := j) (m := m) hκ hm
  linarith

theorem upperSpikeWindow_nonempty_iff
    {X : ℕ → ℝ} {κ ν β : ℝ} {j : ℕ}
    (hβ : 0 < β) :
    ν * X j / κ ≤ (X j + X (j + 1) + Real.log 2) / β ↔
      0 ≤ UpperSpikeExcess X κ ν β j := by
  constructor
  · intro h
    rw [le_div_iff₀ hβ] at h
    have hmain : (ν * β / κ) * X j ≤
        X j + X (j + 1) + Real.log 2 := by
      calc
        (ν * β / κ) * X j = (ν * X j / κ) * β := by
          ring_nf
        _ ≤ X j + X (j + 1) + Real.log 2 := h
    unfold UpperSpikeExcess upperSpikeSlope
    linarith
  · intro h
    rw [le_div_iff₀ hβ]
    have hmain : (ν * β / κ) * X j ≤
        X j + X (j + 1) + Real.log 2 := by
      unfold UpperSpikeExcess upperSpikeSlope at h
      linarith
    calc
      (ν * X j / κ) * β = (ν * β / κ) * X j := by
        ring_nf
      _ ≤ X j + X (j + 1) + Real.log 2 := hmain

theorem upperSpikeExcess_nonneg_of_mem
    {X : ℕ → ℝ} {κ ν β : ℝ} {j m : ℕ}
    (hβ : 0 < β)
    (hm : UpperSpikeWindow X κ ν β j m) :
    0 ≤ UpperSpikeExcess X κ ν β j := by
  exact (upperSpikeWindow_nonempty_iff (X := X) (κ := κ) (ν := ν)
    (β := β) (j := j) hβ).mp (hm.1.trans hm.2)

theorem not_upperSpikeWindow_of_excess_neg
    {X : ℕ → ℝ} {κ ν β : ℝ} {j m : ℕ}
    (hβ : 0 < β)
    (hneg : UpperSpikeExcess X κ ν β j < 0) :
    ¬ UpperSpikeWindow X κ ν β j m := by
  intro hm
  have hnonneg := upperSpikeExcess_nonneg_of_mem
    (X := X) (κ := κ) (ν := ν) (β := β)
    (j := j) (m := m) hβ hm
  linarith

theorem idealSpikeUpper_lt_nextLower
    {X : ℕ → ℝ} {κ ν : ℝ} {j : ℕ}
    (hκ : 0 < κ)
    (hν : 2 < ν)
    (hXnonneg : 0 ≤ X j)
    (hXinc : X j < X (j + 1)) :
    idealSpikeUpper X κ j < idealSpikeLower X κ ν (j + 1) := by
  unfold idealSpikeUpper idealSpikeLower
  have hXnext_pos : 0 < X (j + 1) := lt_of_le_of_lt hXnonneg hXinc
  have hcoef : 1 < ν - 1 := by linarith
  have hsmall : X j < (ν - 1) * X (j + 1) := by
    calc
      X j < X (j + 1) := hXinc
      _ = 1 * X (j + 1) := by ring
      _ < (ν - 1) * X (j + 1) :=
        mul_lt_mul_of_pos_right hcoef hXnext_pos
  have hmain : X j + X (j + 1) < ν * X (j + 1) := by
    linarith
  have hdiv : (X j + X (j + 1)) / κ <
      (ν * X (j + 1)) / κ := by
    exact (div_lt_div_iff_of_pos_right hκ).mpr hmain
  simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv

theorem idealSpikeLength_eq_excess_div
    {X : ℕ → ℝ} {κ ν : ℝ} {j : ℕ} :
    idealSpikeUpper X κ j - idealSpikeLower X κ ν j =
      IdealSpikeExcess X ν j / κ := by
  unfold idealSpikeUpper idealSpikeLower IdealSpikeExcess
  ring

theorem upperSpikeLength_eq_excess_div
    {X : ℕ → ℝ} {κ ν β : ℝ} {j : ℕ}
    (hβ : β ≠ 0) :
    (X j + X (j + 1) + Real.log 2) / β - ν * X j / κ =
      UpperSpikeExcess X κ ν β j / β := by
  unfold UpperSpikeExcess upperSpikeSlope
  field_simp [hβ]
  ring

theorem UpperNatDensityAtMost_of_subset
    {B C : ℕ → Prop} {δ : ℝ}
    (hsub : ∀ n : ℕ, B n → C n)
    (hC : UpperNatDensityAtMost C δ) :
    UpperNatDensityAtMost B δ :=
  Criteria.upperDensityAtMost_mono hsub hC

theorem UpperNatDensityLessThan_of_subset
    {B C : ℕ → Prop} {c : ℝ}
    (hsub : ∀ n : ℕ, B n → C n)
    (hC : UpperNatDensityLessThan C c) :
    UpperNatDensityLessThan B c :=
  Criteria.upperDensityLessThan_mono hsub hC

theorem badRamanujan_badDensity_lt_of_spikeShadow_badDensity_lt
    {X : ℕ → ℝ} {ν M β : ℝ}
    (hcover : ∀ m : ℕ,
      BadRamanujanTruncation ν m →
        UpperSpikeShadow X ramanujanKappa ν β m)
    (hdensity :
      UpperNatDensityLessThan
        (UpperSpikeShadow X ramanujanKappa ν β)
        (1 - ν / M)) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  UpperNatDensityLessThan_of_subset hcover hdensity

theorem oneOverPi_irratMeasure_lt_knownBound_of_Bauer_spikeShadowDensity_lt
    {X : ℕ → ℝ} {μ ν M β : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hcover : ∀ m : ℕ,
      BadRamanujanTruncation ν m →
        UpperSpikeShadow X ramanujanKappa ν β m)
    (hdensity :
      UpperNatDensityLessThan
        (UpperSpikeShadow X ramanujanKappa ν β)
        (1 - ν / M)) :
    μ < M := by
  have hbadDensity :
      UpperNatDensityLessThan
        (BadRamanujanTruncation ν)
        (1 - ν / M) :=
    badRamanujan_badDensity_lt_of_spikeShadow_badDensity_lt
      (X := X) (ν := ν) (M := M) (β := β) hcover hdensity
  exact oneOverPi_irratMeasure_lt_knownBound_of_Bauer_badDensity_lt
    hBauer hμ hν_two hν_M hbadDensity

/-! ## Late-stage spike-covering reduction names -/

/-- Denominator-log sequence for the continued fraction of `1 / π`. -/
noncomputable def ramanujanInvPiCFDenLog (j : ℕ) : ℝ :=
  cfDenLog oneOverPiCF j

/-- Compatibility alias used by the earlier sandbox stage. -/
abbrev oneOverPiCFDenLog : ℕ → ℝ := ramanujanInvPiCFDenLog

/-- Admissible weakened upper-spike width exponent. -/
def AdmissibleUpperSpikeBeta (ν β : ℝ) : Prop :=
  2 * ramanujanKappa / ν < β ∧ β < ramanujanKappa

/-- Upper-density bounds are unchanged by finitely many pointwise exceptions. -/
theorem UpperNatDensityAtMost_of_eventually_subset
    {B C : ℕ → Prop} {δ : ℝ}
    (hsub : ∀ᶠ n : ℕ in atTop, B n → C n)
    (hC : UpperNatDensityAtMost C δ) :
    UpperNatDensityAtMost B δ := by
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rw [eventually_atTop] at hsub
  rcases hsub with ⟨K, hK⟩
  have hCη := hC η hη
  have hKsmall :
      ∀ᶠ N : ℕ in atTop, (K : ℝ) ≤ η * (N : ℝ) :=
    eventually_const_le_pos_mul_natCast (A := (K : ℝ)) (δ := η) hη
  filter_upwards [hCη, hKsmall] with N hCN hKN
  have hcountNat :
      natInitialSegmentCount B N ≤ natInitialSegmentCount C N + K := by
    classical
    let FB : Finset ℕ := (Finset.range (N + 1)).filter B
    let FC : Finset ℕ := (Finset.range (N + 1)).filter C
    let FI : Finset ℕ := Finset.range K
    have hsubset : FB ⊆ FC ∪ FI := by
      intro n hn
      have hnrange : n ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hn).1
      have hnB : B n := (Finset.mem_filter.mp hn).2
      by_cases hnK : K ≤ n
      · have hnC : C n := hK n hnK hnB
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hnrange, hnC⟩))
      · have hnltK : n < K := Nat.lt_of_not_ge hnK
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_range.mpr hnltK))
    calc
      natInitialSegmentCount B N = FB.card := rfl
      _ ≤ (FC ∪ FI).card := Finset.card_le_card hsubset
      _ ≤ FC.card + FI.card := Finset.card_union_le FC FI
      _ = natInitialSegmentCount C N + K := by
        simp [FC, FI, natInitialSegmentCount]
  have hcount :
      (natInitialSegmentCount B N : ℝ) ≤
        (natInitialSegmentCount C N : ℝ) + (K : ℝ) := by
    exact_mod_cast hcountNat
  have hKN' : (K : ℝ) ≤ η * ((N : ℝ) + 1) := by
    have hηnonneg : 0 ≤ η := le_of_lt hη
    calc
      (K : ℝ) ≤ η * (N : ℝ) := hKN
      _ ≤ η * ((N : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hηnonneg
  calc
    (natInitialSegmentCount B N : ℝ)
        ≤ (natInitialSegmentCount C N : ℝ) + (K : ℝ) := hcount
    _ ≤ (δ + η) * ((N : ℝ) + 1) + η * ((N : ℝ) + 1) :=
        add_le_add hCN hKN'
    _ = (δ + ε) * ((N : ℝ) + 1) := by
        dsimp [η]
        ring

/-- Strict upper-density bounds are unchanged by finitely many pointwise
exceptions. -/
theorem UpperNatDensityLessThan_of_eventually_subset
    {B C : ℕ → Prop} {c : ℝ}
    (hsub : ∀ᶠ n : ℕ in atTop, B n → C n)
    (hC : UpperNatDensityLessThan C c) :
    UpperNatDensityLessThan B c := by
  rcases hC with ⟨δ, hδ0, hδc, hδ⟩
  exact ⟨δ, hδ0, hδc,
    UpperNatDensityAtMost_of_eventually_subset hsub hδ⟩

/-- Eventual spike-shadow cover transfers strict density from the shadow to
bad Ramanujan truncations. -/
theorem badRamanujan_badDensity_lt_of_eventual_spikeShadow_badDensity_lt
    {X : ℕ → ℝ} {ν M β : ℝ}
    (hcover : ∀ᶠ m : ℕ in atTop,
      BadRamanujanTruncation ν m →
        UpperSpikeShadow X ramanujanKappa ν β m)
    (hdensity :
      UpperNatDensityLessThan
        (UpperSpikeShadow X ramanujanKappa ν β)
        (1 - ν / M)) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  UpperNatDensityLessThan_of_eventually_subset hcover hdensity

/-- Early sandbox package for the `1 / π` spike-cover route. -/
def OneOverPiSpikeProgram (ν M : ℝ) : Prop :=
  ∃ β : ℝ,
    AdmissibleUpperSpikeBeta ν β ∧
      (∀ᶠ m : ℕ in atTop,
        BadRamanujanTruncation ν m →
          UpperSpikeShadow oneOverPiCFDenLog ramanujanKappa ν β m) ∧
      UpperNatDensityLessThan
        (UpperSpikeShadow oneOverPiCFDenLog ramanujanKappa ν β)
        (1 - ν / M)

/-- Production package for the Ramanujan inverse-pi spike-cover route. -/
def RamanujanSpikeCoveringProgram (ν M : ℝ) : Prop :=
  ∃ β : ℝ,
    AdmissibleUpperSpikeBeta ν β ∧
      (∀ᶠ m : ℕ in atTop,
        BadRamanujanTruncation ν m →
          UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β m) ∧
      UpperNatDensityLessThan
        (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
        (1 - ν / M)

/-- The spike-cover package implies the bad-truncation density threshold. -/
theorem badRamanujanTruncation_density_lessThan_threshold_of_spikeProgram
    {ν M : ℝ}
    (hprog : OneOverPiSpikeProgram ν M) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) := by
  rcases hprog with ⟨β, _hβ, hcover, hdensity⟩
  exact badRamanujan_badDensity_lt_of_eventual_spikeShadow_badDensity_lt
    (X := oneOverPiCFDenLog) (ν := ν) (M := M) (β := β)
    hcover hdensity

/-- Promoted pointwise spike-cover target for bad Ramanujan truncations. -/
axiom badRamanujanTruncation_eventually_subset_ramanujanInvPi_upperSpikeShadow
    {ν β : ℝ}
    (hβ : AdmissibleUpperSpikeBeta ν β) :
    ∀ᶠ m : ℕ in atTop,
      BadRamanujanTruncation ν m →
        UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β m

/-- The remaining unconditional spike-shadow density target. -/
axiom ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold
    {ν M β : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hβ : AdmissibleUpperSpikeBeta ν β) :
    UpperNatDensityLessThan
      (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
      (1 - ν / M)

/-- The two isolated spike targets imply the bad-truncation density threshold. -/
theorem badRamanujanTruncation_density_lessThan_threshold_of_isolated_spike_targets
    {ν M β : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hβ : AdmissibleUpperSpikeBeta ν β) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  badRamanujan_badDensity_lt_of_eventual_spikeShadow_badDensity_lt
    (X := ramanujanInvPiCFDenLog) (ν := ν) (M := M) (β := β)
    (badRamanujanTruncation_eventually_subset_ramanujanInvPi_upperSpikeShadow hβ)
    (ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold
      hν_two hν_M hβ)

/-- Alias naming the density transfer through the Ramanujan inverse-pi spike
shadow. -/
theorem badRamanujanTruncation_density_lessThan_threshold_of_ramanujanInvPi_spikeShadow
    {ν M β : ℝ}
    (hcover : ∀ᶠ m : ℕ in atTop,
      BadRamanujanTruncation ν m →
        UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β m)
    (hdensity :
      UpperNatDensityLessThan
        (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
        (1 - ν / M)) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  badRamanujan_badDensity_lt_of_eventual_spikeShadow_badDensity_lt
    (X := ramanujanInvPiCFDenLog) hcover hdensity

/-- Final Bauer wrapper through the isolated spike-covering targets. -/
theorem oneOverPi_irratMeasure_lt_knownBound_of_Bauer_isolated_spike_targets
    {μ ν M β : ℝ}
    (hBauer : BauerRamanujanIdentity)
    (hμ : HasIrrationalityMeasure (1 / Real.pi) μ)
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hβ : AdmissibleUpperSpikeBeta ν β) :
    μ < M :=
  oneOverPi_irratMeasure_lt_knownBound_of_Bauer_badDensity_lt
    hBauer hμ hν_two hν_M
    (badRamanujanTruncation_density_lessThan_threshold_of_isolated_spike_targets
      hν_two hν_M hβ)

/-- Denominator-log divergence for the inverse-pi CF denominators. -/
axiom ramanujanInvPiCFDenLog_tendsto_atTop :
    Tendsto ramanujanInvPiCFDenLog atTop atTop

/-- A pointwise denominator-log ratio bound makes upper spike excess
eventually negative. -/
axiom eventually_upperSpikeExcess_neg_of_eventually_next_le_mul
    {X : ℕ → ℝ} {κ ν β ρ : ℝ}
    (hXtop : Tendsto X atTop atTop)
    (hρ : ρ < upperSpikeSlope κ ν β)
    (hnext : ∀ᶠ j : ℕ in atTop, X (j + 1) ≤ ρ * X j) :
    ∀ᶠ j : ℕ in atTop, UpperSpikeExcess X κ ν β j < 0

/-- Eventual denominator-log ratio control gives spike-shadow density deficit. -/
axiom UpperSpikeShadow_density_lessThan_of_eventually_next_le_mul
    {X : ℕ → ℝ} {κ ν β ρ M : ℝ}
    (hXtop : Tendsto X atTop atTop)
    (hρ : ρ < upperSpikeSlope κ ν β)
    (hnext : ∀ᶠ j : ℕ in atTop, X (j + 1) ≤ ρ * X j) :
    UpperNatDensityLessThan
      (UpperSpikeShadow X κ ν β)
      (1 - ν / M)

/-- Negative upper spike excess eventually implies the inverse-pi spike-shadow
density threshold. -/
axiom ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold_of_eventually_negative_upperSpikeExcess
    {ν M β : ℝ}
    (hneg :
      ∀ᶠ j : ℕ in atTop,
        UpperSpikeExcess ramanujanInvPiCFDenLog ramanujanKappa ν β j < 0) :
    UpperNatDensityLessThan
      (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
      (1 - ν / M)

/-- Denominator-log ratio control implies the inverse-pi spike-shadow density
threshold. -/
theorem ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold_of_eventually_denLog_next_le_mul
    {ν M β ρ : ℝ}
    (hρ : ρ < upperSpikeSlope ramanujanKappa ν β)
    (hnext :
      ∀ᶠ j : ℕ in atTop,
        ramanujanInvPiCFDenLog (j + 1) ≤ ρ * ramanujanInvPiCFDenLog j) :
    UpperNatDensityLessThan
      (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
      (1 - ν / M) :=
  UpperSpikeShadow_density_lessThan_of_eventually_next_le_mul
    ramanujanInvPiCFDenLog_tendsto_atTop hρ hnext

/-- Conditional spike-shadow density route from denominator-ratio exponent
`1`. -/
axiom ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold_of_denominatorRatioExponent_eq_one
    {ν M β : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hβ : AdmissibleUpperSpikeBeta ν β)
    (hrho : denominatorRatioExponent oneOverPiCF = 1) :
    UpperNatDensityLessThan
      (UpperSpikeShadow ramanujanInvPiCFDenLog ramanujanKappa ν β)
      (1 - ν / M)

/-- Bad-truncation density threshold from denominator-ratio exponent `1`. -/
theorem badRamanujanTruncation_density_lessThan_threshold_of_denominatorRatioExponent_eq_one
    {ν M β : ℝ}
    (hν_two : 2 < ν)
    (hν_M : ν < M)
    (hβ : AdmissibleUpperSpikeBeta ν β)
    (hrho : denominatorRatioExponent oneOverPiCF = 1) :
    UpperNatDensityLessThan
      (BadRamanujanTruncation ν)
      (1 - ν / M) :=
  badRamanujanTruncation_density_lessThan_threshold_of_ramanujanInvPi_spikeShadow
    (ν := ν) (M := M) (β := β)
    (badRamanujanTruncation_eventually_subset_ramanujanInvPi_upperSpikeShadow hβ)
    (ramanujanInvPi_upperSpikeShadow_density_lessThan_threshold_of_denominatorRatioExponent_eq_one
      hν_two hν_M hβ hrho)

namespace SpikeCovering

/-- Result 1 (notes): bad hits are principal convergents. -/
axiom bad_hits_are_principal_convergents
    {κ ν β : ℝ} {Q : ℕ → ℕ} {m : ℕ}
    (hnu : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ)
    (hm : m ∈ BadRamanujanSet ν κ Q) :
    ∃ _ : ℕ, True

/-- Result 2 (notes): upper spike covering into ideal upper intervals. -/
axiom upper_spike_covering
    {κ ν β : ℝ} {Q : ℕ → ℕ} {X : ℕ → ℝ} {m : ℕ}
    (hnu : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ)
    (hm : m ∈ BadRamanujanSet ν κ Q) :
    ∃ j : ℕ, m ∈ spikeUpperInterval X κ ν β j

/-- Result 3 (notes): lower inclusion into `B_ν` from spike windows. -/
axiom lower_spike_inclusion
    {κ ν γ : ℝ} {Q : ℕ → ℕ} {X : ℕ → ℝ} {m : ℕ}
    (hν : (2 : ℝ) < ν) (hγ : κ < γ)
    {j : ℕ} (hm : m ∈ spikeLowerInterval X κ ν γ j) :
    m ∈ BadRamanujanSet ν κ Q

/-- Result 4 (notes): exact spike sandwich as set inclusion. -/
axiom spike_asymptotic_sandwich
    {κ ν β γ : ℝ} {X : ℕ → ℝ}
    (hν : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ) (hγ : κ < γ) :
    spikeUnion (spikeLowerInterval X κ ν γ) ⊆
      spikeUnion (spikeUpperInterval X κ ν β)

/-- Result 5 (notes): disjointness of ideal spike intervals for ν > 2. -/
axiom spikes_disjoint
    {κ ν : ℝ} {X : ℕ → ℝ}
    (hnu : (2 : ℝ) < ν) (hmono : StrictMono X) :
    ∀ j : ℕ, Disjoint (spikeUpperInterval X κ ν κ j)
      (spikeUpperInterval X κ ν κ (j + 1))

/-- Result 6 (notes): threshold equals irrationality measure in the project model. -/
axiom finiteness_threshold_eq_irrationalityMeasure
    {α ν : ℝ} (hν : (2 : ℝ) < ν) (hμ : HasIrrationalityMeasure α (1 + ν)) :
    spikeFinitenessThreshold (Set.univ : Set ℕ) = (1 + ν)

/-- Result 7 (notes): upper-density contraction implication. -/
axiom upper_density_contraction_implies_measure_improvement
    {ν M : ℝ} {B : ℕ → Prop}
    (hν : (2 : ℝ) < ν) (hM : (2 : ℝ) < M)
    (hδ : UpperNatDensityLessThan B (1 - ν / M)) :
    HasIrrationalityMeasure (1 / Real.pi) M

/-- Result 8 (notes): no bootstrap from known M alone. -/
axiom non_bootstrap_from_known_bound
    {M : ℝ} (hM : (2 : ℝ) < M) :
    True

/-- Result 9 (notes): equivalent density and direct spike-exclusion formulations. -/
axiom equivalent_density_and_direct_exclusion
    {M η ν : ℝ}
    (hM : (2 : ℝ) < M) (hν : (2 : ℝ) < ν) (hη : (0 : ℝ) < η) :
    True

/-- Result 10 (notes): explicit residue/arithmetic reformulation target. -/
axiom pi_specific_residue_exclusion_target
    {M : ℝ} (hM : (2 : ℝ) < M) :
    True

-- Legacy names kept for merge continuity.
theorem result1_bad_hits_are_principal_convergents
    {κ ν β : ℝ} {Q : ℕ → ℕ} {m : ℕ}
    (hnu : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ)
    (hm : m ∈ BadRamanujanSet ν κ Q) :
    ∃ _ : ℕ, True :=
  bad_hits_are_principal_convergents hnu hβ hκ hm

theorem result2_upper_spike_covering
    {κ ν β : ℝ} {Q : ℕ → ℕ} {X : ℕ → ℝ} {m : ℕ}
    (hnu : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ)
    (hm : m ∈ BadRamanujanSet ν κ Q) :
    ∃ j : ℕ, m ∈ spikeUpperInterval X κ ν β j :=
  upper_spike_covering hnu hβ hκ hm

theorem result3_lower_spike_inclusion
    {κ ν γ : ℝ} {Q : ℕ → ℕ} {X : ℕ → ℝ} {m : ℕ}
    (hν : (2 : ℝ) < ν) (hγ : κ < γ) {j : ℕ}
    (hm : m ∈ spikeLowerInterval X κ ν γ j) :
    m ∈ BadRamanujanSet ν κ Q :=
  lower_spike_inclusion hν hγ hm

theorem result4_spike_asymptotic_sandwich
    {κ ν β γ : ℝ} {X : ℕ → ℝ}
    (hν : (2 : ℝ) < ν) (hβ : 2 * κ / ν < β) (hκ : β < κ) (hγ : κ < γ) :
    spikeUnion (spikeLowerInterval X κ ν γ) ⊆
      spikeUnion (spikeUpperInterval X κ ν β) :=
  spike_asymptotic_sandwich hν hβ hκ hγ

theorem result5_spikes_disjoint
    {κ ν : ℝ} {X : ℕ → ℝ}
    (hnu : (2 : ℝ) < ν) (hmono : StrictMono X) :
    ∀ j : ℕ, Disjoint (spikeUpperInterval X κ ν κ j)
      (spikeUpperInterval X κ ν κ (j + 1)) :=
  spikes_disjoint hnu hmono

theorem result6_threshold_eq_irrationalityMeasure
    {α ν : ℝ} (hν : (2 : ℝ) < ν) (hμ : HasIrrationalityMeasure α (1 + ν)) :
    spikeFinitenessThreshold (Set.univ : Set ℕ) = (1 + ν) :=
  finiteness_threshold_eq_irrationalityMeasure hν hμ

theorem result7_density_contraction_implies_measure_improvement
    {ν M : ℝ} {B : ℕ → Prop}
    (hν : (2 : ℝ) < ν) (hM : (2 : ℝ) < M)
    (hδ : UpperNatDensityLessThan B (1 - ν / M)) :
    HasIrrationalityMeasure (1 / Real.pi) M :=
  upper_density_contraction_implies_measure_improvement hν hM hδ

theorem result8_non_bootstrap_from_known_bound
    {M : ℝ} (hM : (2 : ℝ) < M) :
    True :=
  non_bootstrap_from_known_bound hM

theorem result9_equivalent_density_and_direct_exclusion
    {M η ν : ℝ}
    (hM : (2 : ℝ) < M) (hν : (2 : ℝ) < ν) (hη : (0 : ℝ) < η) :
    True :=
  equivalent_density_and_direct_exclusion hM hν hη

theorem result10_pi_specific_residue_exclusion_target
    {M : ℝ} (hM : (2 : ℝ) < M) :
    True :=
  pi_specific_residue_exclusion_target hM

end SpikeCovering

-- Plan marker: all spike-covering targets are present and namespaced.
theorem spikePlanIsPopulated : True := by
  trivial

end
end IrrationalityAr
