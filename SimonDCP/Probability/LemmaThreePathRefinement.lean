import SimonDCP.Probability.LemmaThreeBornBounds

/-!
# Path refinements for the repaired Lemma 3

This file supplies the finite partition identity behind the incoherent-energy
hypothesis in `LemmaThreeBornBounds`.  A path may be sent to an arbitrary
complete transcript and branch; in particular, the transcript map may include
a measured mask `D` and an adaptively selected set `A(D)`.

Retaining the path as an orthogonal refinement partitions the finite path
space.  Consequently the sum of the fibre path counts, weighted by their
common squared path magnitudes, is exactly the total path energy.  No
independence property of the transcript map is required.
-/

namespace SimonDCP.Probability.LemmaThreePathRefinement

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeBornBounds

variable {Path Transcript Branch : Type*}

/-- Paths producing one complete transcript and one residual branch. -/
def transcriptBranchFibre
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (transcript : Transcript) (branch : Branch) : Finset Path :=
  Finset.univ.filter fun path =>
    transcriptOf path = transcript ∧ branchOf path = branch

/-- Positive-sign paths in one transcript/branch fibre. -/
def positivePathCount
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (transcript : Transcript) (branch : Branch) : Nat :=
  ((transcriptBranchFibre transcriptOf branchOf transcript branch).filter
    fun path => positive path = true).card

/-- Negative-sign paths in one transcript/branch fibre. -/
def negativePathCount
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (transcript : Transcript) (branch : Branch) : Nat :=
  ((transcriptBranchFibre transcriptOf branchOf transcript branch).filter
    fun path => positive path = false).card

/-- The positive and negative classes partition a transcript/branch fibre. -/
theorem positivePathCount_add_negativePathCount
    [Fintype Path] [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (transcript : Transcript) (branch : Branch) :
    positivePathCount transcriptOf branchOf positive transcript branch +
        negativePathCount transcriptOf branchOf positive transcript branch =
      (transcriptBranchFibre transcriptOf branchOf transcript branch).card := by
  classical
  simpa [positivePathCount, negativePathCount, Bool.not_eq_true] using
    (Finset.card_filter_add_card_filter_not
      (s := transcriptBranchFibre transcriptOf branchOf transcript branch)
      (fun path => positive path = true))

/--
Weighted fibre cardinalities sum to the weight of every path in its unique
transcript/branch fibre.
-/
theorem sum_scale_mul_transcriptBranchFibre_card
    [Fintype Path] [Fintype Transcript] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (scale : Transcript -> Branch -> Real) :
    (∑ transcript, ∑ branch,
      scale transcript branch *
        ((transcriptBranchFibre transcriptOf branchOf transcript branch).card : Real)) =
      ∑ path, scale (transcriptOf path) (branchOf path) := by
  classical
  let key : Path -> Transcript × Branch := fun path =>
    (transcriptOf path, branchOf path)
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_fiberwise key
    (fun path => scale (transcriptOf path) (branchOf path))]
  apply Finset.sum_congr rfl
  rintro ⟨transcript, branch⟩ _
  have hCard :
      Fintype.card {path : Path // key path = (transcript, branch)} =
        (transcriptBranchFibre transcriptOf branchOf transcript branch).card := by
    simpa [key, transcriptBranchFibre, Prod.mk.injEq] using
      (Fintype.card_subtype
        (fun path : Path => key path = (transcript, branch)))
  symm
  calc
    (∑ path : {path : Path // key path = (transcript, branch)},
        scale (transcriptOf path) (branchOf path)) =
        ∑ _path : {path : Path // key path = (transcript, branch)},
          scale transcript branch := by
      apply Finset.sum_congr rfl
      intro path _
      have hPath := path.property
      simp only [key, Prod.mk.injEq] at hPath
      rw [hPath.1, hPath.2]
    _ = (Fintype.card {path : Path // key path = (transcript, branch)} : Real) *
        scale transcript branch := by simp
    _ = scale transcript branch *
        ((transcriptBranchFibre transcriptOf branchOf transcript branch).card : Real) := by
      rw [hCard]
      ring

/--
The total incoherent fibre energy is exactly the total energy of the refined
paths.  This is the normalization bridge needed by the small-branch Born
bound.
-/
theorem totalIncoherentPathEnergy_eq
    [Fintype Path] [Fintype Transcript] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (scale : Transcript -> Branch -> Real) :
    (∑ transcript, ∑ branch,
      scale transcript branch *
        pathCount
          (positivePathCount transcriptOf branchOf positive transcript branch)
          (negativePathCount transcriptOf branchOf positive transcript branch)) =
      ∑ path, scale (transcriptOf path) (branchOf path) := by
  classical
  calc
    (∑ transcript, ∑ branch,
      scale transcript branch *
        pathCount
          (positivePathCount transcriptOf branchOf positive transcript branch)
          (negativePathCount transcriptOf branchOf positive transcript branch)) =
        ∑ transcript, ∑ branch,
          scale transcript branch *
            ((transcriptBranchFibre transcriptOf branchOf transcript branch).card : Real) := by
      apply Finset.sum_congr rfl
      intro transcript _
      apply Finset.sum_congr rfl
      intro branch _
      rw [pathCount]
      congr 1
      exact_mod_cast positivePathCount_add_negativePathCount
        transcriptOf branchOf positive transcript branch
    _ = ∑ path, scale (transcriptOf path) (branchOf path) :=
      sum_scale_mul_transcriptBranchFibre_card transcriptOf branchOf scale

/--
Paper-facing path-model form of the first repaired Lemma 3 bound.  The
transcript assignment is completely arbitrary, so this theorem remains valid
when the transcript records an adaptive choice such as `A(D)`.
-/
theorem pathModel_smallBranchMass_le_paperThreshold
    [Fintype Path] [Fintype Transcript] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (scale : Transcript -> Branch -> Real)
    (n : Nat)
    (hScale : forall transcript branch, 0 <= scale transcript branch)
    (hTotalPathEnergy :
      (∑ path, scale (transcriptOf path) (branchOf path)) <= 1) :
    realFiniteMass
        (fun transcript => ∑ branch,
          scale transcript branch *
            signedCountSq
              (positivePathCount transcriptOf branchOf positive transcript branch)
              (negativePathCount transcriptOf branchOf positive transcript branch))
        (countSmallBranchEvent
          (positivePathCount transcriptOf branchOf positive)
          (negativePathCount transcriptOf branchOf positive)
          ((2 : Real)⁻¹ ^ n)) <=
      (2 : Real)⁻¹ ^ n := by
  apply countSmallBranchMass_le_paperThreshold
  · exact hScale
  · rw [totalIncoherentPathEnergy_eq
      transcriptOf branchOf positive scale]
    exact hTotalPathEnergy

end SimonDCP.Probability.LemmaThreePathRefinement
