import IrrationalityAr.CountingConsequencesCorollaries

open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# External Diophantine input for `1 / π`

This file intentionally isolates the external fact that `1 / π` has finite
irrationality measure.  The rest of the project proves the structural and
Ramanujan-certification pipeline; importing this file makes exactly this
Diophantine input available as an axiom.
-/

/-- External Diophantine input: this project does not reproduce a proof that
`1 / π` has finite irrationality measure. -/
axiom oneOverPi_hasFiniteIrrationalityMeasure :
    HasFiniteIrrationalityMeasure (1 / Real.pi)

/-- Bauer-interface certified production with the finite-measure input supplied
by the isolated external axiom. -/
theorem exists_eventually_AOneOverPiBelowExp_card_lower_of_Bauer
    (hBauer : BauerRamanujanIdentity) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧
      3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤
          ((AOneOverPiBelowExp Λ m).card : ℝ) :=
  exists_eventually_AOneOverPiBelowExp_card_lower_of_Bauer_finiteMeasure
    hBauer
    oneOverPi_hasFiniteIrrationalityMeasure

/-- `ACount` checkpoint form of the Bauer-interface certified production, with
the finite-measure input supplied by the isolated external axiom. -/
theorem exists_eventually_ACount_oneOverPi_floorExp_lower_of_Bauer
    (hBauer : BauerRamanujanIdentity) :
    ∃ ρ Λ : ℝ,
      0 < ρ ∧
      3 * Real.log 2 < Λ ∧
      ∀ᶠ m : ℕ in atTop,
        ρ * (m : ℝ) ≤
          (ACount (1 / Real.pi)
            (Nat.floor (Real.exp (Λ * (m : ℝ)))) : ℝ) :=
  exists_eventually_ACount_oneOverPi_floorExp_lower_of_Bauer_finiteMeasure
    hBauer
    oneOverPi_hasFiniteIrrationalityMeasure

end IrrationalityAr
