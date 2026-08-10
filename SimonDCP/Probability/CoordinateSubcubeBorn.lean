import SimonDCP.Probability.CoordinateSubcubeProjection
import SimonDCP.Probability.LabelledBornProbability

/-!
# Exact labelled Born mass on coordinate-subcube residue fibres

Projection injectivity removes every off-diagonal term from restricted
labelled Parseval.  After dividing by the Step-4 Born denominator, the
all-zero event on a coordinate set `A` therefore has exactly its uniform
baseline mass `2 ^ (-|A|)`.

The second theorem applies the same identity to two disjoint groups.  Their
joint all-zero mass is the product of their individual uniform baselines; no
probabilistic independence assumption is needed beyond subset-sum
injectivity on the union.
-/

namespace SimonDCP.Probability.CoordinateSubcubeBorn

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.LabelledBornProbability

variable {I G Label : Type*}
  [Fintype I] [DecidableEq I]
  [AddCommGroup G] [DecidableEq G]
  [DecidableEq Label]

/-- Exact normalized all-zero mass for a nonempty coordinate-subcube residue
fibre whose local free subset sums are injective. -/
theorem labelledZeroEventMass_maskCoordinateSubcubeResidueFibre_eq
    (free A : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hinjective : SubsetSumInjectiveWithin (free ∩ A) sample) :
    labelledZeroEventMass A
        (maskCoordinateSubcubeResidueFibre free fixed sample residue) label =
      (1 / 2 : ℚ) ^ A.card := by
  have hsupportCard :
      ((maskCoordinateSubcubeResidueFibre
        free fixed sample residue).card : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hsupport)
  rw [labelledZeroEventMass,
    maskCoordinateSubcubeResidueFibre_labelled_parseval_eq_diagonal
      free A fixed sample residue label hinjective]
  rw [← uniformZeroBaseline_eq A]
  simp only [labelledBornDenominator, uniformZeroBaseline]
  push_cast
  field_simp

/-- For disjoint coordinate groups, injectivity on their union makes the
joint all-zero mass equal to the product of the two uniform baselines. -/
theorem labelledZeroEventMass_disjoint_union_eq_mul
    (free A B : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hdisjoint : Disjoint A B)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ (A ∪ B)) sample) :
    labelledZeroEventMass (A ∪ B)
        (maskCoordinateSubcubeResidueFibre free fixed sample residue) label =
      (1 / 2 : ℚ) ^ A.card * (1 / 2 : ℚ) ^ B.card := by
  rw [labelledZeroEventMass_maskCoordinateSubcubeResidueFibre_eq
    free (A ∪ B) fixed sample residue label hsupport hinjective]
  rw [Finset.card_union_of_disjoint hdisjoint, pow_add]

end SimonDCP.Probability.CoordinateSubcubeBorn
