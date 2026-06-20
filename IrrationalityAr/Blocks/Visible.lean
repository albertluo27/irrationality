import IrrationalityAr.Blocks.Selected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace IrrationalityAr

/-!
# Visible canonical denominator sets and exponents

This module defines the finite denominator truncations and exponent functionals
used by the canonical block-growth layer.  The asymptotic estimates proving
their values remain in `CanonicalBlockGrowth`.
-/

/-- The visible part of a canonical denominator block, using the true
denominator cap `N`.  Since `canonicalOddDenominatorBlock` stores `Q - 1`, the
filter is `q + 1 ≤ N`. -/
def visibleCanonicalOddDenominatorBlock
    (a : ℕ → ℕ) (N j : ℕ) : Finset ℕ :=
  (canonicalOddDenominatorBlock a j).filter fun q => q + 1 ≤ N

/-- The largest visible local canonical block below denominator cap `N`, with a
logarithmic index cap. -/
def visibleCanonicalBlockMax
    (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  max 1 <| (Finset.range (2 * Nat.log 2 N + 3)).sup fun j =>
    (visibleCanonicalOddDenominatorBlock a N j).card

/-- Visible canonical block exponent, using the logarithmic visible block
maximum rather than the older endpoint-counting `canonicalBlockGrowth`. -/
noncomputable def visibleCanonicalBlockExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (visibleCanonicalBlockMax a N : ℝ) / Real.log (N : ℝ))
    atTop

/-- All visible canonical parity-selected denominator elements `Q - 1` below
the true denominator cap `N`. -/
def visibleCanonicalDenominatorSet
    (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * Nat.log 2 N + 3)).biUnion fun j =>
    visibleCanonicalOddDenominatorBlock a N j

/-- The positive part of the visible canonical denominator set.

The full shifted denominator set can contain the harmless initial value
`0 = 1 - 1`; this version is the one that matches the floor-sum set `A`. -/
def positiveVisibleCanonicalDenominatorSet
    (a : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (visibleCanonicalDenominatorSet a N).erase 0

noncomputable def visiblePopularDifferenceExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (popularDifferenceUpTo (visibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisiblePopularDifferenceExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (popularDifferenceUpTo
          (positiveVisibleCanonicalDenominatorSet a N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def visibleAdditiveEnergyExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (additiveEnergy (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisibleAdditiveEnergyExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log
        (additiveEnergy (positiveVisibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def properHilbertCubeDimension (S : Finset ℕ) : ℕ :=
  by
    classical
    exact (Finset.range (S.card + 1)).sup fun h : ℕ =>
      if HasProperHilbertCube S h then h else 0

noncomputable def visibleHilbertCubeExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension
        (visibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def positiveVisibleHilbertCubeExponent (a : ℕ → ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension
        (positiveVisibleCanonicalDenominatorSet a N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def popularDifferenceExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (popularDifferenceUpTo (S N) N : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def additiveEnergyExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      Real.log (additiveEnergy (S N) : ℝ) /
        Real.log (N : ℝ))
    atTop

noncomputable def hilbertCubeExponentOf (S : ℕ → Finset ℕ) : ℝ :=
  limsup
    (fun N : ℕ =>
      (properHilbertCubeDimension (S N) : ℝ) /
        Real.log (N : ℝ))
    atTop

theorem popularDifferenceExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    popularDifferenceExponentOf S =
      popularDifferenceExponentOf T := by
  unfold popularDifferenceExponentOf
  congr
  ext N
  rw [hST N]

theorem additiveEnergyExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    additiveEnergyExponentOf S =
      additiveEnergyExponentOf T := by
  unfold additiveEnergyExponentOf
  congr
  ext N
  rw [hST N]

theorem hilbertCubeExponent_congr
    {S T : ℕ → Finset ℕ}
    (hST : ∀ N, S N = T N) :
    hilbertCubeExponentOf S =
      hilbertCubeExponentOf T := by
  unfold hilbertCubeExponentOf
  congr
  ext N
  rw [hST N]

end IrrationalityAr
