import SimonDCP.Probability.LemmaThreePaperPathEnergy
import SimonDCP.Probability.LemmaThreePostselectionSlack

/-!
# Conditional first clause in the paper-shaped finite model

This module combines the paper-shaped common-path energy estimate with exact
postselection bookkeeping.  The acceptance predicate is `True`, so its mass
is the total unnormalized mass of the retained finite analytic model.  If that
mass is at least `n^(-degree)`, the joint `2^(-n)` small-branch estimate yields
a conditional `2^(-floor(n / 2))` estimate under the explicit premise
`n^degree <= 2^(n - floor(n / 2))`.

The theorem is conditional on the paper-shaped finite model.  Identifying its
`transcriptBornWeight` with the actual circuit Born distribution, and proving
that its residual branch labels are orthogonal, remain external bridge
obligations; neither fact follows from finite postselection arithmetic.
-/

namespace SimonDCP.Probability.LemmaThreePaperFirstClause

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePaperPathBridge
open SimonDCP.Probability.LemmaThreePaperPathEnergy
open SimonDCP.Probability.LemmaThreePostselection
open SimonDCP.Probability.LemmaThreePostselectionSlack
open SimonDCP.Probability.LemmaThreeTranscriptModel

variable {Hidden Y D W S Low : Type*}

/--
Paper-shaped conditional form of the repaired first clause.  Here acceptance
means membership in the retained analytic model itself, so
`finiteAcceptanceMass weight (fun _ => True)` is its total mass.
-/
theorem paperFirstClause_conditional_small_mass_le_halfExponent
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    [Nonempty D] [Nonempty Low]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (n degree : Nat) (hn : 0 < n)
    (hStepTwoEnergy :
      (∑ phi : Hidden,
        Complex.normSq (stepTwoAmplitude (model.yOf phi))) <= 1)
    (hAcceptedTotalMass :
      1 / (n : Real) ^ degree <=
        finiteAcceptanceMass
          (transcriptBornWeight
            CompatibleStepSevenPath.transcript
            (paperBranch model) (paperPositive model)
            (fun transcript (_hStar : Bool) =>
              paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript))
          (fun _transcript => True))
    (hPolynomial :
      (n : Real) ^ degree <= (2 : Real) ^ (n - n / 2)) :
    finiteConditionalBadMass
        (transcriptBornWeight
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model)
          (fun transcript (_hStar : Bool) =>
            paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript))
        (fun _transcript => True)
        (allStepSevenBranchesSmall
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model) n) <=
      1 / (2 : Real) ^ (n / 2) := by
  let weight : StepSevenTranscript Y D W S -> Real :=
    transcriptBornWeight
      CompatibleStepSevenPath.transcript
      (paperBranch model) (paperPositive model)
      (fun transcript (_hStar : Bool) =>
        paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript)
  let bad : StepSevenTranscript Y D W S -> Prop :=
    allStepSevenBranchesSmall
      CompatibleStepSevenPath.transcript
      (paperBranch model) (paperPositive model) n
  have hWeight : forall transcript, 0 <= weight transcript := by
    intro transcript
    unfold weight transcriptBornWeight
    exact Finset.sum_nonneg fun branch _ =>
      Complex.normSq_nonneg
        (rawBranchAmplitude
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model)
          (fun transcript (_hStar : Bool) =>
            paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript)
          transcript branch)
  have hPaperJoint :
      realFiniteMass weight bad <= (2 : Real)⁻¹ ^ n := by
    simpa [weight, bad] using
      paperPaths_allBranchesSmall_mass_le
        (Low := Low) model stepTwoAmplitude n hStepTwoEnergy
  have hJoint :
      finiteJointBadMass weight (fun _transcript => True) bad <=
        1 / (2 : Real) ^ n := by
    simpa [finiteJointBadMass, one_div] using hPaperJoint
  apply finiteConditionalBadMass_le_halfExponent
    weight (fun _transcript => True) bad n degree hn hWeight
  · simpa [weight] using hAcceptedTotalMass
  · exact hJoint
  · exact hPolynomial

end SimonDCP.Probability.LemmaThreePaperFirstClause
