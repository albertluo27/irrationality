import IrrationalityAr.Basic

namespace IrrationalityAr

/-- The fractional part of `q r`. -/
noncomputable def fracMul (r : ℝ) (q : ℕ) : ℝ :=
  Int.fract ((q : ℝ) * r)

/-- `q` produces a new strict minimum among the positive-index fractional
parts up to `q`. -/
def IsLowerRecord (r : ℝ) (q : ℕ) : Prop :=
  0 < q ∧ ∀ k : ℕ, 0 < k → k < q → fracMul r q < fracMul r k

/-- `q` produces a new strict maximum among the positive-index fractional
parts up to `q`. -/
def IsUpperRecord (r : ℝ) (q : ℕ) : Prop :=
  0 < q ∧ ∀ k : ℕ, 0 < k → k < q → fracMul r k < fracMul r q

end IrrationalityAr
