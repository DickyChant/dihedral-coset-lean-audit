import SimonDCP.Probability.ActualStepFourBorn
import SimonDCP.Probability.LemmaOneFiniteModel
import SimonDCP.Probability.StepTwoJointKernel

/-!
# Lemma 1 for one fixed fault environment

This module instantiates the finite Lemma 1 estimate with the analytic
Step-2 joint kernel for one fixed coordinate-subcube fault environment.  An
outer outcome records the complete Fourier vector and the measured low
residue.  Its reduced sample is obtained coordinatewise through `lowBitsHom`.

The inner rational weight is the labelled Walsh law on the corresponding
Step-2 residue fibre, with the complete paper-style Step-4 label
`(h, s_1, ..., s_g)`.  `mixedStepFourBornWeight_eq_fixedEnvironmentWeight_cast`
identifies its real cast pointwise with the defined mixed-state Step-4
conditional kernel.  The resulting estimate is therefore for the composed
analytic fixed-environment kernel.  The raw-normalization bridge below further
identifies this conditional kernel with the ratio of the explicit projected
output mass to its total mass.  Gate-level circuit identification and the
paper's rounded parameter arithmetic remain outside this module.
-/

namespace SimonDCP.Probability.LemmaOneFixedEnvironment

open SimonDCP.Probability.TernarySubsetSumBound
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepTwoJointKernel
open SimonDCP.Probability.StepFourLabelPhaseBridge
open SimonDCP.Probability.FaultyHighBitCarry
open SimonDCP.Probability.ActualStepFourBorn
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.LemmaOneOuterAveraging
open SimonDCP.Probability.RectangularGroupPartition
open SimonDCP.Probability.LemmaOneFiniteModel
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

open scoped BigOperators

noncomputable section

variable {wordWidth groupCount groupWidth : Nat}

/-- The rational conditional Step-4 output law for one fixed fault
environment and one realized Step-2 joint outcome. -/
def fixedEnvironmentStepFourWeight
    {S : Type*} [DecidableEq S]
    (wordWidth groupCount groupWidth : Nat)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (outcome : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth)
    (output : Mask (Fin groupCount × Fin groupWidth)) : Rat :=
  labelledBornWeight
    (maskCoordinateSubcubeResidueFibre free
      (boolMaskEquiv (Fin groupCount × Fin groupWidth) fixed)
      (fun coordinate => lowBitsHom wordWidth (outcome.1 coordinate))
      outcome.2)
    (paperStepFourLabel (fullSumHighBit wordWidth outcome.1)
      (groupSummary outcome))
    output

/-- The inner rational law used by the finite estimate is exactly the defined
mixed-state Step-4 conditional weight after casting to `Real`.  This is
pointwise in the complete Step-2 outcome and in the Hadamard output. -/
theorem mixedStepFourBornWeight_eq_fixedEnvironmentWeight_cast
    {S : Type*} [DecidableEq S]
    (hWordWidth : 0 < wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (outcome : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth)
    (output : Mask (Fin groupCount × Fin groupWidth)) :
    mixedStepFourBornWeight wordWidth secret free fixed outcome.1 outcome.2
        (groupSummary outcome) output =
      (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
        fixed groupSummary outcome output : Real) := by
  rw [mixedStepFourBornWeight_eq_labelled hWordWidth]
  rw [mixedStepTwoMaskSupport_eq_maskCoordinateSubcubeResidueFibre]
  simp only [fixedEnvironmentStepFourWeight]

/-- For a reachable Step-2 outcome, normalizing the explicit raw projected
mass gives exactly the real cast of the rational fixed-environment kernel. -/
theorem mixedStepFourRawOutputMass_div_total_eq_fixedEnvironmentWeight_cast
    {S : Type*} [DecidableEq S]
    (hWordWidth : 0 < wordWidth)
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (outcome : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth)
    (hSupport :
      (boolStepTwoMeasuredFibre wordWidth free fixed outcome.1
        outcome.2).Nonempty)
    (output : Mask (Fin groupCount × Fin groupWidth)) :
    mixedStepFourRawOutputMass wordWidth positions secret free fixed outcome.1
          outcome.2 (groupSummary outcome) output /
        mixedStepFourRawTotalMass wordWidth positions secret free fixed
          outcome.1 outcome.2 (groupSummary outcome) =
      (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
        fixed groupSummary outcome output : Real) := by
  rw [mixedStepFourRawOutputMass_div_total_eq_bornWeight hWordWidth positions
    secret free fixed outcome.1 outcome.2 (groupSummary outcome) hSupport
    output]
  exact mixedStepFourBornWeight_eq_fixedEnvironmentWeight_cast
    hWordWidth secret free fixed groupSummary outcome output

/-- On every positive-mass Step-2 outcome, the defined mixed Step-4
conditional kernel has total mass one.  This follows from the labelled
Parseval normalization; the preceding theorem identifies the same kernel with
the normalized explicit projected-amplitude mass. -/
theorem sum_mixedStepFourBornWeight_eq_one_of_stepTwoWeight_ne_zero
    {S : Type*} [DecidableEq S]
    (hWordWidth : 0 < wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (outcome : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth)
    (hOutcome : stepTwoJointWeight wordWidth free fixed outcome ≠ 0) :
    (∑ output : Mask (Fin groupCount × Fin groupWidth),
      mixedStepFourBornWeight wordWidth secret free fixed outcome.1 outcome.2
        (groupSummary outcome) output) = 1 := by
  let I := Fin groupCount × Fin groupWidth
  have hBooleanSupport :
      (boolStepTwoMeasuredFibre wordWidth free fixed outcome.1
        outcome.2).Nonempty :=
    (stepTwoJointWeight_ne_zero_iff wordWidth free fixed outcome).mp hOutcome
  have hSupport :
      (maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun coordinate => lowBitsHom wordWidth (outcome.1 coordinate))
        outcome.2).Nonempty := by
    rw [← image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
    exact hBooleanSupport.image (boolMaskEquiv I)
  have hRationalSum :
      (∑ output : Mask I,
        fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
          fixed groupSummary outcome output) = 1 := by
    unfold fixedEnvironmentStepFourWeight
    exact sum_labelledBornWeight_eq_one
      (maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun coordinate => lowBitsHom wordWidth (outcome.1 coordinate))
        outcome.2)
      (paperStepFourLabel (fullSumHighBit wordWidth outcome.1)
        (groupSummary outcome)) hSupport
  calc
    (∑ output : Mask I,
      mixedStepFourBornWeight wordWidth secret free fixed outcome.1 outcome.2
        (groupSummary outcome) output) =
        ∑ output : Mask I,
          (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
            fixed groupSummary outcome output : Real) := by
      apply Finset.sum_congr rfl
      intro output _
      exact mixedStepFourBornWeight_eq_fixedEnvironmentWeight_cast
        hWordWidth secret free fixed groupSummary outcome output
    _ = 1 := by exact_mod_cast hRationalSum

/-- The real-valued lower-tail mass of the composed analytic kernel.
The outer factor is the Step-2 Born mass summed over the measured selection
fibre, and the inner factor is the defined Step-4 conditional weight. -/
def mixedFixedEnvironmentLowerTailMass
    {S : Type*} [DecidableEq S]
    (wordWidth groupCount groupWidth : Nat)
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) : Real :=
  ∑ outcome : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth,
    (∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
        outcome.1 outcome.2,
      ‖mixedPostPositionDftProductAmplitude free fixed positions secret
        (selection, outcome.1)‖ ^ 2) *
      ∑ output : Mask (Fin groupCount × Fin groupWidth),
        if indicatorSum groupCount
              (groupZeroIndicator
                (rectangularGroups groupCount groupWidth)) output < target then
          mixedStepFourBornWeight wordWidth secret free fixed outcome.1
            outcome.2 (groupSummary outcome) output
        else 0

/-- The composed real-valued analytic mass is exactly the real cast of the
rational nested kernel used by the finite-model estimate. -/
theorem mixedFixedEnvironmentLowerTailMass_eq_cast_nestedFiniteMass
    {S : Type*} [DecidableEq S]
    (hWordWidth : 0 < wordWidth)
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) :
    mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        positions secret free fixed groupSummary target =
      (nestedFiniteMass
        (stepTwoJointWeight wordWidth free fixed)
        (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
          fixed groupSummary)
        (fun _ output =>
          indicatorSum groupCount
              (groupZeroIndicator
                (rectangularGroups groupCount groupWidth)) output < target) :
        Real) := by
  classical
  unfold mixedFixedEnvironmentLowerTailMass nestedFiniteMass finiteMass
  push_cast
  apply Finset.sum_congr rfl
  intro outcome _
  rw [← cast_stepTwoJointWeight_eq_sum_fibre_mixedBorn wordWidth free fixed
    positions secret outcome.1 outcome.2]
  apply congrArg
  apply Finset.sum_congr rfl
  intro output _
  by_cases hEvent :
      indicatorSum groupCount
          (groupZeroIndicator
            (rectangularGroups groupCount groupWidth)) output < target
  · simp only [hEvent, if_true]
    exact mixedStepFourBornWeight_eq_fixedEnvironmentWeight_cast
      hWordWidth secret free fixed groupSummary outcome output
  · simp only [hEvent, if_false, Rat.cast_zero]

/--
The fixed-fault-environment Lemma 1 estimate.

The first summand bounds failure of subset-sum injectivity for some one- or
two-group set.  The second is the conditional Chebyshev lower-tail bound.
No independence between the Step-2 outcome and the Step-4 output is assumed.
-/
theorem lowerTailMass_fixedEnvironment_rectangular_le
    {S : Type*} [DecidableEq S]
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWordWidth : 0 < wordWidth)
    (hGroupWidth : 0 < groupWidth)
    (hExactMean :
      (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth = mean)
    (hMeanParameters : mean = (k / c) * (paperN / logN))
    (hTargetParameters : target = paperN / logN)
    (hc : 0 < c) (hPaperN : 0 < paperN) (hLogN : 0 < logN)
    (hck : c < k) :
    nestedFiniteMass
        (stepTwoJointWeight wordWidth free fixed)
        (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
          fixed groupSummary)
        (fun _ output =>
          indicatorSum groupCount
              (groupZeroIndicator
                (rectangularGroups groupCount groupWidth)) output < target) <=
      (groupCount ^ 2 : Rat) *
          (((3 ^ (2 * groupWidth) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (wordWidth - 1))) : Rat)) +
        (k * c / (k - c) ^ 2) * (logN / paperN) := by
  let I := Fin groupCount × Fin groupWidth
  have hSupport : forall outcome : StepTwoJointOutcome I wordWidth,
      stepTwoJointWeight wordWidth free fixed outcome ≠ 0 ->
        (maskCoordinateSubcubeResidueFibre free
          (boolMaskEquiv I fixed)
          (fun coordinate => lowBitsHom wordWidth (outcome.1 coordinate))
          outcome.2).Nonempty := by
    intro outcome hOutcome
    have hBooleanSupport :
        (boolStepTwoMeasuredFibre wordWidth free fixed outcome.1
          outcome.2).Nonempty :=
      (stepTwoJointWeight_ne_zero_iff wordWidth free fixed outcome).mp hOutcome
    rw [← image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
    exact hBooleanSupport.image (boolMaskEquiv I)
  exact nested_lowerTailMass_rectangular_le
    (Outer := StepTwoJointOutcome I wordWidth)
    (G := ZMod (2 ^ (wordWidth - 1)))
    (Label := StepFourLabel (Fin groupCount) S)
    (N := groupCount) (m := groupWidth)
    (outerWeight := stepTwoJointWeight wordWidth free fixed)
    (sample := fun outcome coordinate =>
      lowBitsHom wordWidth (outcome.1 coordinate))
    (free := fun _ => free)
    (fixed := fun _ => boolMaskEquiv I fixed)
    (residue := fun outcome => outcome.2)
    (label := fun outcome =>
      paperStepFourLabel (fullSumHighBit wordWidth outcome.1)
        (groupSummary outcome))
    target mean k c paperN logN
    (stepTwoJointWeight_nonneg wordWidth free fixed)
    (sum_stepTwoJointWeight_eq_one wordWidth free fixed)
    (hasUniformLocalMarginals_stepTwoJointWeight_lowBits wordWidth
      hWordWidth free fixed
      (groupUnionFamily (rectangularGroups groupCount groupWidth)))
    hSupport hGroupWidth hExactMean hMeanParameters hTargetParameters
    hc hPaperN hLogN hck

/-- The composed real-valued analytic kernel inherits the same collision plus
Chebyshev bound.  The positions and secret are explicit in the outer and inner
amplitudes, although the resulting bound is independent of their values. -/
theorem mixedFixedEnvironmentLowerTailMass_rectangular_le
    {S : Type*} [DecidableEq S]
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWordWidth : 0 < wordWidth)
    (hGroupWidth : 0 < groupWidth)
    (hExactMean :
      (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth = mean)
    (hMeanParameters : mean = (k / c) * (paperN / logN))
    (hTargetParameters : target = paperN / logN)
    (hc : 0 < c) (hPaperN : 0 < paperN) (hLogN : 0 < logN)
    (hck : c < k) :
    mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        positions secret free fixed groupSummary target <=
      ((groupCount ^ 2 : Rat) *
          (((3 ^ (2 * groupWidth) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (wordWidth - 1))) : Rat)) +
        (k * c / (k - c) ^ 2) * (logN / paperN) : Real) := by
  rw [mixedFixedEnvironmentLowerTailMass_eq_cast_nestedFiniteMass
    hWordWidth positions secret free fixed groupSummary target]
  exact_mod_cast lowerTailMass_fixedEnvironment_rectangular_le free fixed
    groupSummary target mean k c paperN logN hWordWidth hGroupWidth
    hExactMean hMeanParameters hTargetParameters hc hPaperN hLogN hck

/-- If the collision and Chebyshev summands are each budgeted by `1/4`, the
fixed-environment lower-tail failure mass is at most `1/2`. -/
theorem lowerTailMass_fixedEnvironment_rectangular_le_half
    {S : Type*} [DecidableEq S]
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWordWidth : 0 < wordWidth)
    (hGroupWidth : 0 < groupWidth)
    (hExactMean :
      (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth = mean)
    (hMeanParameters : mean = (k / c) * (paperN / logN))
    (hTargetParameters : target = paperN / logN)
    (hc : 0 < c) (hPaperN : 0 < paperN) (hLogN : 0 < logN)
    (hck : c < k)
    (hCollisionBudget :
      4 * groupCount ^ 2 * (3 ^ (2 * groupWidth) - 1) <=
        2 ^ (wordWidth - 1))
    (hTailBudget :
      4 * k * c * logN <= (k - c) ^ 2 * paperN) :
    nestedFiniteMass
        (stepTwoJointWeight wordWidth free fixed)
        (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
          fixed groupSummary)
        (fun _ output =>
          indicatorSum groupCount
              (groupZeroIndicator
                (rectangularGroups groupCount groupWidth)) output < target) <=
      1 / 2 := by
  calc
    nestedFiniteMass
        (stepTwoJointWeight wordWidth free fixed)
        (fixedEnvironmentStepFourWeight wordWidth groupCount groupWidth free
          fixed groupSummary)
        (fun _ output =>
          indicatorSum groupCount
              (groupZeroIndicator
                (rectangularGroups groupCount groupWidth)) output < target) <=
        (groupCount ^ 2 : Rat) *
            (((3 ^ (2 * groupWidth) - 1 : Nat) : Rat) /
              (Fintype.card (ZMod (2 ^ (wordWidth - 1))) : Rat)) +
          (k * c / (k - c) ^ 2) * (logN / paperN) :=
      lowerTailMass_fixedEnvironment_rectangular_le free fixed groupSummary
        target mean k c paperN logN hWordWidth hGroupWidth hExactMean
        hMeanParameters hTargetParameters hc hPaperN hLogN hck
    _ <= 1 / 4 + 1 / 4 := add_le_add
      (rectangularCollisionBound_zmod_le_quarter
        (N := groupCount) (m := groupWidth) (wordWidth - 1)
        hCollisionBudget)
      (paperTailBound_le_quarter k c paperN logN hPaperN hck hTailBudget)
    _ = 1 / 2 := by norm_num

/-- The same explicit budgets give the `1/2` bound directly for the composed
real-valued analytic kernel. -/
theorem mixedFixedEnvironmentLowerTailMass_rectangular_le_half
    {S : Type*} [DecidableEq S]
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWordWidth : 0 < wordWidth)
    (hGroupWidth : 0 < groupWidth)
    (hExactMean :
      (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth = mean)
    (hMeanParameters : mean = (k / c) * (paperN / logN))
    (hTargetParameters : target = paperN / logN)
    (hc : 0 < c) (hPaperN : 0 < paperN) (hLogN : 0 < logN)
    (hck : c < k)
    (hCollisionBudget :
      4 * groupCount ^ 2 * (3 ^ (2 * groupWidth) - 1) <=
        2 ^ (wordWidth - 1))
    (hTailBudget :
      4 * k * c * logN <= (k - c) ^ 2 * paperN) :
    mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        positions secret free fixed groupSummary target <= 1 / 2 := by
  rw [mixedFixedEnvironmentLowerTailMass_eq_cast_nestedFiniteMass
    hWordWidth positions secret free fixed groupSummary target]
  have hRational :=
    lowerTailMass_fixedEnvironment_rectangular_le_half free fixed
    groupSummary target mean k c paperN logN hWordWidth hGroupWidth
    hExactMean hMeanParameters hTargetParameters hc hPaperN hLogN hck
    hCollisionBudget hTailBudget
  have hHalfCast : (1 / 2 : Real) = ((1 / 2 : Rat) : Real) := by
    norm_num
  rw [hHalfCast]
  exact_mod_cast hRational

end

end SimonDCP.Probability.LemmaOneFixedEnvironment
