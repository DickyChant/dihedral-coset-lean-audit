import SimonDCP.Probability.ProjectionInjectivity

/-!
# Projection injectivity for coordinate-subcube residue supports

This file gives the `ZMod 2` mask version of a coordinate-subcube support.
Coordinates in `free` may vary, while every other coordinate agrees with a
fixed mask.  Filtering this subcube by one Boolean subset-sum residue gives the
hidden support relevant to restricted Parseval.

The main theorem reduces projection injectivity on a local set `A` to subset-
sum injectivity on `free ∩ A`.  Indeed, two supported masks agree on `Aᶜ` by
the projection hypothesis and on `freeᶜ` because the subcube fixes both masks
there.  They therefore agree outside `free ∩ A`, where local subset-sum
injectivity applies.

`CoordinateSubcubeSupport.lean` contains the parallel counting development for
`I → Bool`.  This module deliberately stays in the Walsh-analysis mask type
`Mask I = I → ZMod 2`; a transport equivalence between the two support
representations has not yet been added.
-/

namespace SimonDCP.Probability.CoordinateSubcubeProjection

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval
open SimonDCP.Probability.ProjectionInjectivity

variable {I G Label : Type*}
  [Fintype I] [DecidableEq I]

/-- `ZMod 2` masks that agree with `fixed` away from the free coordinates. -/
noncomputable def maskCoordinateSubcube
    (free : Finset I) (fixed : Mask I) : Finset (Mask I) := by
  classical
  exact Finset.univ.filter fun selection =>
    ∀ i, i ∉ free → selection i = fixed i

@[simp]
theorem mem_maskCoordinateSubcube_iff
    {free : Finset I} {fixed selection : Mask I} :
    selection ∈ maskCoordinateSubcube free fixed ↔
      ∀ i, i ∉ free → selection i = fixed i := by
  classical
  simp [maskCoordinateSubcube]

/-- The part of a mask coordinate subcube having one prescribed subset-sum
residue. -/
noncomputable def maskCoordinateSubcubeResidueFibre
    [AddCommGroup G] [DecidableEq G]
    (free : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G) : Finset (Mask I) :=
  (maskCoordinateSubcube free fixed).filter fun selection =>
    booleanSubsetSum sample selection = residue

@[simp]
theorem mem_maskCoordinateSubcubeResidueFibre_iff
    [AddCommGroup G] [DecidableEq G]
    {free : Finset I} {fixed : Mask I}
    {sample : I → G} {residue : G} {selection : Mask I} :
    selection ∈
        maskCoordinateSubcubeResidueFibre free fixed sample residue ↔
      selection ∈ maskCoordinateSubcube free fixed ∧
        booleanSubsetSum sample selection = residue := by
  classical
  simp [maskCoordinateSubcubeResidueFibre]

/-- Agreement outside `A`, together with the fixed coordinates of a subcube,
implies agreement outside `free ∩ A`. -/
theorem agreeOutside_inter_of_mem_maskCoordinateSubcube
    {free A : Finset I} {fixed left right : Mask I}
    (hleft : left ∈ maskCoordinateSubcube free fixed)
    (hright : right ∈ maskCoordinateSubcube free fixed)
    (hagree : AgreeOutside A left right) :
    AgreeOutside (free ∩ A) left right := by
  intro i hi
  by_cases hiA : i ∈ A
  · have hiFree : i ∉ free := by
      intro hiFree
      exact hi (Finset.mem_inter.mpr ⟨hiFree, hiA⟩)
    exact
      ((mem_maskCoordinateSubcube_iff.mp hleft) i hiFree).trans
        ((mem_maskCoordinateSubcube_iff.mp hright) i hiFree).symm
  · exact hagree i hiA

/-- Local subset-sum injectivity on the free coordinates in `A` makes the
coordinate-subcube residue fibre projection-injective on `A`. -/
theorem projectionInjective_maskCoordinateSubcubeResidueFibre
    [AddCommGroup G] [DecidableEq G]
    (free A : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (hinjective : SubsetSumInjectiveWithin (free ∩ A) sample) :
    ProjectionInjective A
      (maskCoordinateSubcubeResidueFibre free fixed sample residue) := by
  intro left hleft right hright hagree
  have hleftData :=
    mem_maskCoordinateSubcubeResidueFibre_iff.mp hleft
  have hrightData :=
    mem_maskCoordinateSubcubeResidueFibre_iff.mp hright
  have hagreeLocal : AgreeOutside (free ∩ A) left right :=
    agreeOutside_inter_of_mem_maskCoordinateSubcube
      hleftData.1 hrightData.1 hagree
  apply
    (subsetSumInjectiveOn_of_injectiveWithin
      (free ∩ A) sample hinjective) hagreeLocal
  exact hleftData.2.trans hrightData.2.symm

section Labels

variable [DecidableEq Label]

omit [Fintype I] [DecidableEq I] in
/-- Projection injectivity of a support is inherited by every complete-label
fibre. -/
theorem labelwiseProjectionInjective_of_projectionInjective
    (A : Finset I) (support : Finset (Mask I))
    (label : Mask I → Label)
    (hinjective : ProjectionInjective A support) :
    LabelwiseProjectionInjective A support label := by
  intro labelValue hlabelValue
  apply hinjective.mono
  intro selection hselection
  exact (Finset.mem_filter.mp hselection).1

/-- Exact labelled restricted Parseval for a coordinate-subcube residue
support.  The only injectivity hypothesis concerns the genuinely free
coordinates in `A`. -/
theorem maskCoordinateSubcubeResidueFibre_labelled_parseval_eq_diagonal
    [AddCommGroup G] [DecidableEq G]
    (free A : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hinjective : SubsetSumInjectiveWithin (free ∩ A) sample) :
    (∑ mask : MasksVanishingOn A,
        labelledSquaredAmplitude
          (maskCoordinateSubcubeResidueFibre free fixed sample residue)
          label mask) =
      (2 : ℤ) ^ (Fintype.card I - A.card) *
        (maskCoordinateSubcubeResidueFibre
          free fixed sample residue).card := by
  apply labelled_restricted_parseval_eq_diagonal
  exact labelwiseProjectionInjective_of_projectionInjective
    A (maskCoordinateSubcubeResidueFibre free fixed sample residue) label
      (projectionInjective_maskCoordinateSubcubeResidueFibre
        free A fixed sample residue hinjective)

end Labels

end SimonDCP.Probability.CoordinateSubcubeProjection
