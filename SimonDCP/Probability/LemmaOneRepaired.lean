import SimonDCP.Probability.LemmaOneRoundedFixedEnvironment

/-!
# Public repaired Lemma 1 interface

This module packages the completed analytic repair of Lemma 1 as a direct
success-probability statement.  Success means that the number of all-zero
groups is at least the target `n / floor(log_2 n)`.

The success mass below is an event sum under the actual Step-2 Born marginal
and the normalized analytic Step-4 conditional kernel.  It is not defined as
`1 - failure`.  The complement identity is proved separately from the
normalization theorems for those kernels.

For the repaired rounded schedule with `k = 24`, `c = 12`, and `n >= 1024`,
the success mass is at least `1/2`, both for a fixed fault environment and for
an arbitrary normalized finite classical mixture of fault environments.
-/

namespace SimonDCP.Probability.LemmaOneRepaired

open scoped BigOperators

open SimonDCP.Probability.ActualStepFourBorn
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.FaultyHighBitCarry
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.LemmaOneFaultEnvironmentAveraging
open SimonDCP.Probability.LemmaOneFixedEnvironment
open SimonDCP.Probability.LemmaOneRoundedFixedEnvironment
open SimonDCP.Probability.LemmaOneRoundedParameters
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.RectangularGroupPartition
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepTwoJointKernel
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

noncomputable section

/-- The repaired Lemma 1 success event: at least `target` rectangular groups
have the all-zero Step-4 output. -/
def repairedLemmaOneSuccessEvent
    (groupCount groupWidth : Nat) (target : Rat)
    (output : Mask (Fin groupCount × Fin groupWidth)) : Prop :=
  target <=
    indicatorSum groupCount
      (groupZeroIndicator (rectangularGroups groupCount groupWidth)) output

/-- The success event is exactly the complement of the lower-tail event used
in the failure estimate. -/
theorem repairedLemmaOneSuccessEvent_iff_not_lowerTail
    (groupCount groupWidth : Nat) (target : Rat)
    (output : Mask (Fin groupCount × Fin groupWidth)) :
    repairedLemmaOneSuccessEvent groupCount groupWidth target output ↔
      ¬ indicatorSum groupCount
          (groupZeroIndicator (rectangularGroups groupCount groupWidth))
          output < target := by
  simp [repairedLemmaOneSuccessEvent]

/-- The analytic fixed-environment success mass.

The outer factor is the actual Step-2 Born mass of a measured outcome.  The
inner factor is the normalized analytic Step-4 kernel restricted to the
success event. -/
def mixedFixedEnvironmentSuccessMass
    {S : Type*} [DecidableEq S]
    (wordWidth groupCount groupWidth : Nat)
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) : Real := by
  classical
  exact
    ∑ outcome : StepTwoJointOutcome
        (Fin groupCount × Fin groupWidth) wordWidth,
      (∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
          outcome.1 outcome.2,
        ‖mixedPostPositionDftProductAmplitude free fixed positions secret
          (selection, outcome.1)‖ ^ 2) *
        ∑ output : Mask (Fin groupCount × Fin groupWidth),
          if repairedLemmaOneSuccessEvent groupCount groupWidth target output then
            mixedStepFourBornWeight wordWidth secret free fixed outcome.1
              outcome.2 (groupSummary outcome) output
          else 0

/-- The fixed-environment success and lower-tail failure masses form a
partition of the normalized analytic experiment. -/
theorem mixedFixedEnvironmentSuccessMass_add_lowerTailMass_eq_one
    {S : Type*} [DecidableEq S]
    {wordWidth groupCount groupWidth : Nat}
    (positions : (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Finset (Fin groupCount × Fin groupWidth))
    (fixed : (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) (hWordWidth : 0 < wordWidth) :
    mixedFixedEnvironmentSuccessMass wordWidth groupCount groupWidth
        positions secret free fixed groupSummary target +
      mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        positions secret free fixed groupSummary target = 1 := by
  classical
  unfold mixedFixedEnvironmentSuccessMass
    mixedFixedEnvironmentLowerTailMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ outcome : StepTwoJointOutcome
        (Fin groupCount × Fin groupWidth) wordWidth,
      ((∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
            outcome.1 outcome.2,
          ‖mixedPostPositionDftProductAmplitude free fixed positions secret
            (selection, outcome.1)‖ ^ 2) *
            (∑ output : Mask (Fin groupCount × Fin groupWidth),
              if repairedLemmaOneSuccessEvent groupCount groupWidth target output
              then
                mixedStepFourBornWeight wordWidth secret free fixed outcome.1
                  outcome.2 (groupSummary outcome) output
              else 0) +
          (∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
              outcome.1 outcome.2,
            ‖mixedPostPositionDftProductAmplitude free fixed positions secret
              (selection, outcome.1)‖ ^ 2) *
            (∑ output : Mask (Fin groupCount × Fin groupWidth),
              if indicatorSum groupCount
                    (groupZeroIndicator
                      (rectangularGroups groupCount groupWidth)) output < target
              then
                mixedStepFourBornWeight wordWidth secret free fixed outcome.1
                  outcome.2 (groupSummary outcome) output
              else 0))) =
        ∑ outcome : StepTwoJointOutcome
            (Fin groupCount × Fin groupWidth) wordWidth,
          ∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
              outcome.1 outcome.2,
            ‖mixedPostPositionDftProductAmplitude free fixed positions secret
              (selection, outcome.1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [← mul_add]
      by_cases hOutcome :
          stepTwoJointWeight wordWidth free fixed outcome = 0
      · have hOuter :
            (∑ selection ∈ boolStepTwoMeasuredFibre wordWidth free fixed
                outcome.1 outcome.2,
              ‖mixedPostPositionDftProductAmplitude free fixed positions secret
                (selection, outcome.1)‖ ^ 2) = 0 := by
          rw [← cast_stepTwoJointWeight_eq_sum_fibre_mixedBorn wordWidth free
            fixed positions secret outcome.1 outcome.2]
          simp [hOutcome]
        simp [hOuter]
      · have hPartition :
            (∑ output : Mask (Fin groupCount × Fin groupWidth),
              if repairedLemmaOneSuccessEvent groupCount groupWidth target
                  output then
                mixedStepFourBornWeight wordWidth secret free fixed outcome.1
                  outcome.2 (groupSummary outcome) output
              else 0) +
              (∑ output : Mask (Fin groupCount × Fin groupWidth),
                if indicatorSum groupCount
                      (groupZeroIndicator
                        (rectangularGroups groupCount groupWidth)) output <
                    target then
                  mixedStepFourBornWeight wordWidth secret free fixed outcome.1
                    outcome.2 (groupSummary outcome) output
                else 0) =
              ∑ output : Mask (Fin groupCount × Fin groupWidth),
                mixedStepFourBornWeight wordWidth secret free fixed outcome.1
                  outcome.2 (groupSummary outcome) output := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro output _
          by_cases hSuccess :
              repairedLemmaOneSuccessEvent groupCount groupWidth target output
          · have hNotLower :
                ¬ indicatorSum groupCount
                    (groupZeroIndicator
                      (rectangularGroups groupCount groupWidth)) output <
                  target :=
              (repairedLemmaOneSuccessEvent_iff_not_lowerTail groupCount
                groupWidth target output).mp hSuccess
            simp [hSuccess, hNotLower]
          · have hLower :
                indicatorSum groupCount
                    (groupZeroIndicator
                      (rectangularGroups groupCount groupWidth)) output <
                  target := by
              exact lt_of_not_ge hSuccess
            simp [hSuccess, hLower]
        rw [hPartition,
          sum_mixedStepFourBornWeight_eq_one_of_stepTwoWeight_ne_zero
            hWordWidth secret free fixed groupSummary outcome hOutcome,
          mul_one]
    _ = ∑ outcome : StepTwoJointOutcome
          (Fin groupCount × Fin groupWidth) wordWidth,
        (stepTwoJointWeight wordWidth free fixed outcome : Real) := by
      apply Finset.sum_congr rfl
      intro outcome _
      exact (cast_stepTwoJointWeight_eq_sum_fibre_mixedBorn wordWidth free
        fixed positions secret outcome.1 outcome.2).symm
    _ = 1 := by
      rw [← Rat.cast_sum, sum_stepTwoJointWeight_eq_one]
      norm_num

/-- Direct repaired Lemma 1 for one fixed fault environment.  With the
concrete constants and rounded schedule, analytic success mass is at least
`1/2`. -/
theorem mixedFixedEnvironmentSuccessMass_paperConstants_ge_half
    {S : Type*} [DecidableEq S] {n : Nat}
    (positions :
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) ->
        Word n)
    (secret : Word n)
    (free : Finset
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)))
    (fixed :
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) ->
        Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) n ->
        Mask
          (Fin (roundedGroupCount 24 12 n) ×
            Fin (roundedGroupWidth 12 n)) ->
        Fin (roundedGroupCount 24 12 n) -> S)
    (hn : 1024 <= n) :
    (1 / 2 : Real) <=
      mixedFixedEnvironmentSuccessMass n (roundedGroupCount 24 12 n)
        (roundedGroupWidth 12 n) positions secret free fixed groupSummary
        ((n : Rat) / (roundedLog n : Rat)) := by
  have hComplement :=
    mixedFixedEnvironmentSuccessMass_add_lowerTailMass_eq_one
      positions secret free fixed groupSummary
      ((n : Rat) / (roundedLog n : Rat)) (by omega)
  have hFailure :=
    mixedFixedEnvironmentLowerTailMass_paperConstants_le_half
      positions secret free fixed groupSummary hn
  linarith

variable {Environment : Type*} [Fintype Environment]

/-- The repaired Lemma 1 success mass after averaging over a finite classical
fault environment.  This is again an event sum, now additionally weighted by
the normalized environment distribution. -/
def mixedFaultEnvironmentSuccessMass
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (wordWidth groupCount groupWidth : Nat)
    (positions : Environment ->
      (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Environment -> Finset (Fin groupCount × Fin groupWidth))
    (fixed : Environment -> (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : (environment : Environment) ->
      StepTwoJointOutcome (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) : Real :=
  ∑ environment,
    environmentWeight environment *
      mixedFixedEnvironmentSuccessMass wordWidth groupCount groupWidth
        (positions environment) secret (free environment) (fixed environment)
        (groupSummary environment) target

/-- Averaged success and lower-tail failure masses are complementary for
every normalized finite classical environment distribution. -/
theorem mixedFaultEnvironmentSuccessMass_add_lowerTailMass_eq_one
    {S : Type*} [DecidableEq S]
    {wordWidth groupCount groupWidth : Nat}
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Environment -> Finset (Fin groupCount × Fin groupWidth))
    (fixed : Environment -> (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : (environment : Environment) ->
      StepTwoJointOutcome (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hWordWidth : 0 < wordWidth) :
    mixedFaultEnvironmentSuccessMass environmentWeight wordWidth groupCount
        groupWidth positions secret free fixed groupSummary target +
      mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary target = 1 := by
  classical
  unfold mixedFaultEnvironmentSuccessMass
    mixedFaultEnvironmentLowerTailMass environmentAveragedFailureMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ environment,
      (environmentWeight environment *
            mixedFixedEnvironmentSuccessMass wordWidth groupCount groupWidth
              (positions environment) secret (free environment)
              (fixed environment) (groupSummary environment) target +
          environmentWeight environment *
            mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
              (positions environment) secret (free environment)
              (fixed environment) (groupSummary environment) target)) =
        ∑ environment, environmentWeight environment := by
      apply Finset.sum_congr rfl
      intro environment _
      rw [← mul_add,
        mixedFixedEnvironmentSuccessMass_add_lowerTailMass_eq_one
          (positions environment) secret (free environment)
          (fixed environment) (groupSummary environment) target hWordWidth,
        mul_one]
    _ = 1 := hWeightNormalized

/-- Direct repaired Lemma 1 for an arbitrary normalized finite classical
mixture of fault environments.  No independence assumption is imposed on the
environment-dependent positions, free coordinates, fixed bits, or summaries.
-/
theorem mixedFaultEnvironmentSuccessMass_paperConstants_ge_half
    {S : Type*} [DecidableEq S] {n : Nat}
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) ->
        Word n)
    (secret : Word n)
    (free : Environment -> Finset
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)))
    (fixed : Environment ->
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) ->
        Bool)
    (groupSummary : (environment : Environment) -> StepTwoJointOutcome
      (Fin (roundedGroupCount 24 12 n) × Fin (roundedGroupWidth 12 n)) n ->
        Mask
          (Fin (roundedGroupCount 24 12 n) ×
            Fin (roundedGroupWidth 12 n)) ->
        Fin (roundedGroupCount 24 12 n) -> S)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hn : 1024 <= n) :
    (1 / 2 : Real) <=
      mixedFaultEnvironmentSuccessMass environmentWeight n
        (roundedGroupCount 24 12 n) (roundedGroupWidth 12 n) positions secret
        free fixed groupSummary ((n : Rat) / (roundedLog n : Rat)) := by
  have hComplement :=
    mixedFaultEnvironmentSuccessMass_add_lowerTailMass_eq_one
      environmentWeight positions secret free fixed groupSummary
      ((n : Rat) / (roundedLog n : Rat)) hWeightNormalized (by omega)
  have hFailure :=
    mixedFaultEnvironmentLowerTailMass_paperConstants_le_half
      environmentWeight positions secret free fixed groupSummary
      hWeightNonneg hWeightNormalized hn
  linarith

end

end SimonDCP.Probability.LemmaOneRepaired
