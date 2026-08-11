import SimonDCP.Probability.LemmaThreeTranscriptModel
import SimonDCP.Probability.LemmaThreeSectorRefinement
import SimonDCP.Probability.LemmaThreePostselection
import SimonDCP.Probability.LemmaThreeUniformWalshPaths

/-!
# Combined abstract finite bounds for the Lemma 3 audit

This module combines two independent Born-energy estimates that replace
invalid inference patterns in the published proof.  It does **not** prove a
repaired decoder: the word `repaired` retained in theorem names refers only to
these conditional finite inequalities.  Its outcomes are complete transcripts
and its fine paths are defined
by an arbitrary compatibility relation.  Thus the transcript, and in
particular a selected set such as `A(D)`, may depend on the measured outcome
`D`.

There are two independent analytic premises:

* the total energy of compatible fine paths is at most one;
* the total energy of the refined sectors is at most an explicit budget `C`.

The second premise is substantive.  It does not follow merely from
completeness of the coarse measurement when the sector label depends on the
outcome.  `LemmaThreeSectorRefinement` contains finite counterexamples with
normalized coarse Born mass and refined energy `3 / 2`.  Consequently, an
application to the paper's adaptive implicit label `z*(D)` must prove this
energy budget separately.

The statements below are a finite probabilistic core, not an instantiation of
the paper's Steps 3--7.  Such an instantiation must still identify the actual
common path amplitudes, prove the two displayed energy premises, and account
for every normalization and postselection factor.  In particular, the supplied
`sectorAmplitude` is otherwise arbitrary: the paper-facing bridge must prove
that it is the path-restricted contribution `u(M,z)` belonging to the same
transcript Born weight.  Choosing unrelated or zero sectors would make the
abstract conjunction true but say nothing about the paper.
-/

namespace SimonDCP.Probability.LemmaThreeFiniteRepair

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePathRefinement
open SimonDCP.Probability.LemmaThreeTranscriptModel
open SimonDCP.Probability.LemmaThreeSectorRefinement
open SimonDCP.Probability.LemmaThreePostselection
open SimonDCP.Probability.LemmaThreeUniformWalshPaths

/--
Equal-amplitude Step-2/Walsh specialization of the joint repair.  The first
energy premise is discharged by counting all surviving `(hidden, hadamard)`
paths inside the normalized product space.  Only the adaptive sector budget
remains explicit.
-/
theorem repairedUniformWalshJointBounds
    {Hidden Hadamard Outcome Branch Fine : Type*}
    [Fintype Hidden] [Fintype Hadamard]
    [Fintype Outcome] [Fintype Branch] [Fintype Fine]
    [Nonempty Hidden] [Nonempty Hadamard]
    [DecidableEq Outcome] [DecidableEq Branch]
    (survives : Hidden -> Hadamard -> Prop)
    [DecidablePred fun pair : Hidden × Hadamard => survives pair.1 pair.2]
    (transcriptOf : UniformWalshPath Hidden Hadamard survives -> Outcome)
    (branchOf : UniformWalshPath Hidden Hadamard survives -> Branch)
    (positive : UniformWalshPath Hidden Hadamard survives -> Bool)
    (sectorAmplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (thresholdSq budget : Real)
    (hThreshold : 0 < thresholdSq)
    (hSectorEnergy : totalSectorEnergy sectorAmplitude <= budget) :
    let weight : Outcome -> Real := fun outcome => ∑ branch,
      uniformWalshPathScale Hidden Hadamard *
        signedCountSq
          (positivePathCount transcriptOf branchOf positive outcome branch)
          (negativePathCount transcriptOf branchOf positive outcome branch)
    realFiniteMass weight
          (countSmallBranchEvent
            (positivePathCount transcriptOf branchOf positive)
            (negativePathCount transcriptOf branchOf positive)
            ((2 : Real)⁻¹ ^ n)) <=
        (2 : Real)⁻¹ ^ n
      ∧
    realFiniteMass weight
          (largeNormalizedSectorEvent weight sectorAmplitude thresholdSq) <=
        budget / thresholdSq := by
  dsimp only
  constructor
  · exact uniformWalshPaths_smallBranchMass_le
      survives transcriptOf branchOf positive n
  · exact largeNormalizedSectorMass_le_budget
      (fun outcome => ∑ branch,
        uniformWalshPathScale Hidden Hadamard *
          signedCountSq
            (positivePathCount transcriptOf branchOf positive outcome branch)
            (negativePathCount transcriptOf branchOf positive outcome branch))
      sectorAmplitude thresholdSq budget hThreshold hSectorEnergy

/--
The joint finite repair before postselection.  The first conclusion is the
relational compatible-path small-branch bound.  The second is the adaptive
sector bound `C / L^2`, with both `C` and `L^2` explicit.
-/
theorem repairedJointBounds
    {Outcome Hidden Branch Fine : Type*}
    [Fintype Outcome] [Fintype Hidden] [Fintype Branch] [Fintype Fine]
    [DecidableEq Outcome] [DecidableEq Branch]
    (compatible : Outcome -> Hidden -> Prop)
    [DecidablePred fun pair : Outcome × Hidden => compatible pair.1 pair.2]
    (branchOf : CompatibleStepSevenPath Outcome Hidden compatible -> Branch)
    (positive : CompatibleStepSevenPath Outcome Hidden compatible -> Bool)
    (commonAmplitude : Outcome -> Branch -> Complex)
    (sectorAmplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (thresholdSq budget : Real)
    (hPathEnergy :
      (∑ path : CompatibleStepSevenPath Outcome Hidden compatible,
        Complex.normSq
          (commonAmplitude path.transcript (branchOf path))) <= 1)
    (hThreshold : 0 < thresholdSq)
    (hSectorEnergy : totalSectorEnergy sectorAmplitude <= budget) :
    realFiniteMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          (allStepSevenBranchesSmall CompatibleStepSevenPath.transcript
            branchOf positive n) <=
        (2 : Real)⁻¹ ^ n
      ∧
    realFiniteMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          (largeNormalizedSectorEvent
            (transcriptBornWeight CompatibleStepSevenPath.transcript
              branchOf positive commonAmplitude)
            sectorAmplitude thresholdSq) <=
        budget / thresholdSq := by
  constructor
  · exact compatiblePaths_allBranchesSmall_mass_le
      compatible branchOf positive commonAmplitude n hPathEnergy
  · exact largeNormalizedSectorMass_le_budget
      (transcriptBornWeight CompatibleStepSevenPath.transcript
        branchOf positive commonAmplitude)
      sectorAmplitude thresholdSq budget hThreshold hSectorEnergy

/--
Dyadic specialization of the joint repair.  A sector-energy budget `C` with
`C <= 2^(2n)` and squared threshold `2^(3n)` gives sector bad mass at most
`2^(-n)`.  The hypothesis bounding `C` remains explicit; it is not inferred
from coarse completeness.
-/
theorem repairedDyadicJointBounds_of_budget
    {Outcome Hidden Branch Fine : Type*}
    [Fintype Outcome] [Fintype Hidden] [Fintype Branch] [Fintype Fine]
    [DecidableEq Outcome] [DecidableEq Branch]
    (compatible : Outcome -> Hidden -> Prop)
    [DecidablePred fun pair : Outcome × Hidden => compatible pair.1 pair.2]
    (branchOf : CompatibleStepSevenPath Outcome Hidden compatible -> Branch)
    (positive : CompatibleStepSevenPath Outcome Hidden compatible -> Bool)
    (commonAmplitude : Outcome -> Branch -> Complex)
    (sectorAmplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (budget : Real)
    (hPathEnergy :
      (∑ path : CompatibleStepSevenPath Outcome Hidden compatible,
        Complex.normSq
          (commonAmplitude path.transcript (branchOf path))) <= 1)
    (hSectorEnergy : totalSectorEnergy sectorAmplitude <= budget)
    (hBudget : budget <= (2 : Real) ^ (2 * n)) :
    realFiniteMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          (allStepSevenBranchesSmall CompatibleStepSevenPath.transcript
            branchOf positive n) <=
        (2 : Real)⁻¹ ^ n
      ∧
    realFiniteMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          (largeNormalizedSectorEvent
            (transcriptBornWeight CompatibleStepSevenPath.transcript
              branchOf positive commonAmplitude)
            sectorAmplitude ((2 : Real) ^ (3 * n))) <=
        1 / ((2 : Real) ^ n) := by
  constructor
  · exact compatiblePaths_allBranchesSmall_mass_le
      compatible branchOf positive commonAmplitude n hPathEnergy
  · apply exactSectorMass_le_of_dyadicBudget
    exact hSectorEnergy.trans hBudget

/-- The Born weight of a complete transcript is nonnegative. -/
theorem transcriptBornWeight_nonneg
    {Path Outcome Branch : Type*}
    [Fintype Path] [Fintype Branch]
    [DecidableEq Outcome] [DecidableEq Branch]
    (transcriptOf : Path -> Outcome) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Outcome -> Branch -> Complex)
    (outcome : Outcome) :
    0 <= transcriptBornWeight transcriptOf branchOf positive commonAmplitude outcome := by
  unfold transcriptBornWeight
  exact Finset.sum_nonneg fun branch _ =>
    Complex.normSq_nonneg
      (rawBranchAmplitude transcriptOf branchOf positive commonAmplitude
        outcome branch)

/-- Intersecting an event with a postselection event cannot increase its mass
when all point weights are nonnegative. -/
theorem finiteJointBadMass_le_eventMass
    {Outcome : Type*} [Fintype Outcome]
    (weight : Outcome -> Real) (accept bad : Outcome -> Prop)
    (hWeight : ∀ outcome, 0 <= weight outcome) :
    finiteJointBadMass weight accept bad <= realFiniteMass weight bad := by
  classical
  unfold finiteJointBadMass realFiniteMass
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hAccept : accept outcome <;>
    by_cases hBad : bad outcome <;>
      simp [hAccept, hBad, hWeight outcome]

/--
Postselection version of the finite repair.  Conditioning on an event of mass
at least `rho > 0` loses exactly the factor `1 / rho` in both estimates.
-/
theorem repairedConditionalBounds
    {Outcome Hidden Branch Fine : Type*}
    [Fintype Outcome] [Fintype Hidden] [Fintype Branch] [Fintype Fine]
    [DecidableEq Outcome] [DecidableEq Branch]
    (compatible : Outcome -> Hidden -> Prop)
    [DecidablePred fun pair : Outcome × Hidden => compatible pair.1 pair.2]
    (branchOf : CompatibleStepSevenPath Outcome Hidden compatible -> Branch)
    (positive : CompatibleStepSevenPath Outcome Hidden compatible -> Bool)
    (commonAmplitude : Outcome -> Branch -> Complex)
    (sectorAmplitude : SectorAmplitude Outcome Fine)
    (accept : Outcome -> Prop)
    (n : Nat) (thresholdSq budget rho : Real)
    (hPathEnergy :
      (∑ path : CompatibleStepSevenPath Outcome Hidden compatible,
        Complex.normSq
          (commonAmplitude path.transcript (branchOf path))) <= 1)
    (hThreshold : 0 < thresholdSq)
    (hSectorEnergy : totalSectorEnergy sectorAmplitude <= budget)
    (hRho : 0 < rho)
    (hAccept : rho <=
      finiteAcceptanceMass
        (transcriptBornWeight CompatibleStepSevenPath.transcript
          branchOf positive commonAmplitude)
        accept) :
    finiteConditionalBadMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          accept
          (allStepSevenBranchesSmall CompatibleStepSevenPath.transcript
            branchOf positive n) <=
        ((2 : Real)⁻¹ ^ n) / rho
      ∧
    finiteConditionalBadMass
          (transcriptBornWeight CompatibleStepSevenPath.transcript
            branchOf positive commonAmplitude)
          accept
          (largeNormalizedSectorEvent
            (transcriptBornWeight CompatibleStepSevenPath.transcript
              branchOf positive commonAmplitude)
            sectorAmplitude thresholdSq) <=
        (budget / thresholdSq) / rho := by
  let weight : Outcome -> Real :=
    transcriptBornWeight CompatibleStepSevenPath.transcript
      branchOf positive commonAmplitude
  let small : Outcome -> Prop :=
    allStepSevenBranchesSmall CompatibleStepSevenPath.transcript
      branchOf positive n
  let large : Outcome -> Prop :=
    largeNormalizedSectorEvent weight sectorAmplitude thresholdSq
  have hWeight : ∀ outcome, 0 <= weight outcome := by
    intro outcome
    exact transcriptBornWeight_nonneg
      CompatibleStepSevenPath.transcript branchOf positive commonAmplitude outcome
  have hJoint :
      realFiniteMass weight small <= (2 : Real)⁻¹ ^ n
        ∧ realFiniteMass weight large <= budget / thresholdSq := by
    simpa [weight, small, large] using
      repairedJointBounds compatible branchOf positive commonAmplitude
        sectorAmplitude n thresholdSq budget hPathEnergy hThreshold hSectorEnergy
  constructor
  · apply finiteConditionalBadMass_le_bound_div_rho
    · exact hWeight
    · exact (finiteJointBadMass_le_eventMass weight accept small hWeight).trans
        hJoint.1
    · exact hRho
    · simpa [weight] using hAccept
  · apply finiteConditionalBadMass_le_bound_div_rho
    · exact hWeight
    · exact (finiteJointBadMass_le_eventMass weight accept large hWeight).trans
        hJoint.2
    · exact hRho
    · simpa [weight] using hAccept

end SimonDCP.Probability.LemmaThreeFiniteRepair
