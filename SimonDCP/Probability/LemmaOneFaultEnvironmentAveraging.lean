import SimonDCP.Probability.LemmaOneFixedEnvironment

/-!
# Classical averaging over fault environments

This module passes the fixed-fault-environment estimate through an arbitrary
finite classical mixture.  Environment weights are nonnegative and normalized,
and no independence assumption is made: the positions, free coordinates,
fixed bits, and Step-4 summaries may all depend on the environment.

This is only a probability-level averaging result.  It does not construct a
density matrix, a quantum channel, or a gate-level implementation of the
fault distribution.
-/

namespace SimonDCP.Probability.LemmaOneFaultEnvironmentAveraging

open scoped BigOperators

open SimonDCP.Probability.LemmaOneFixedEnvironment
open SimonDCP.Probability.StepTwoJointKernel
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.FaultyHighBitCarry
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

noncomputable section

variable {Environment : Type*} [Fintype Environment]

/-- The weighted average of a real-valued failure mass over a finite classical
environment space. -/
def environmentAveragedFailureMass
    (environmentWeight : Environment -> Real)
    (failureMass : Environment -> Real) : Real :=
  ∑ environment, environmentWeight environment * failureMass environment

/-- A uniform pointwise failure bound is preserved by every nonnegative,
normalized finite classical mixture. -/
theorem environmentAveragedFailureMass_le
    (environmentWeight : Environment -> Real)
    (failureMass : Environment -> Real)
    (bound : Real)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hFailure : ∀ environment, failureMass environment <= bound) :
    environmentAveragedFailureMass environmentWeight failureMass <= bound := by
  calc
    environmentAveragedFailureMass environmentWeight failureMass <=
        ∑ environment, environmentWeight environment * bound := by
      unfold environmentAveragedFailureMass
      apply Finset.sum_le_sum
      intro environment _
      exact mul_le_mul_of_nonneg_left
        (hFailure environment) (hWeightNonneg environment)
    _ = (∑ environment, environmentWeight environment) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by rw [hWeightNormalized, one_mul]

variable {wordWidth groupCount groupWidth : Nat}

/-- The lower-tail failure mass after classically averaging the analytic
fixed-environment kernels.  The secret and numerical parameters are shared,
while all data describing the realized fault environment may vary. -/
def mixedFaultEnvironmentLowerTailMass
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Environment -> Finset (Fin groupCount × Fin groupWidth))
    (fixed : Environment -> (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : (environment : Environment) ->
      StepTwoJointOutcome (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target : Rat) : Real :=
  environmentAveragedFailureMass environmentWeight fun environment =>
    mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
      (positions environment) secret (free environment) (fixed environment)
      (groupSummary environment) target

/-- The collision-plus-Chebyshev fixed-environment estimate is unchanged by
an arbitrary normalized classical mixture of fault environments. -/
theorem mixedFaultEnvironmentLowerTailMass_rectangular_le
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Environment -> Finset (Fin groupCount × Fin groupWidth))
    (fixed : Environment -> (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : (environment : Environment) ->
      StepTwoJointOutcome (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hWordWidth : 0 < wordWidth)
    (hGroupWidth : 0 < groupWidth)
    (hExactMean :
      (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth = mean)
    (hMeanParameters : mean = (k / c) * (paperN / logN))
    (hTargetParameters : target = paperN / logN)
    (hc : 0 < c) (hPaperN : 0 < paperN) (hLogN : 0 < logN)
    (hck : c < k) :
    mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary target <=
      ((groupCount ^ 2 : Rat) *
          (((3 ^ (2 * groupWidth) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (wordWidth - 1))) : Rat)) +
        (k * c / (k - c) ^ 2) * (logN / paperN) : Real) := by
  apply environmentAveragedFailureMass_le environmentWeight
    (fun environment =>
      mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        (positions environment) secret (free environment) (fixed environment)
        (groupSummary environment) target)
    _ hWeightNonneg hWeightNormalized
  intro environment
  exact mixedFixedEnvironmentLowerTailMass_rectangular_le
    (positions environment) secret (free environment) (fixed environment)
    (groupSummary environment) target mean k c paperN logN hWordWidth
    hGroupWidth hExactMean hMeanParameters hTargetParameters hc hPaperN hLogN
    hck

/-- If both fixed-environment error summands have budget `1/4`, then every
normalized classical mixture has lower-tail failure mass at most `1/2`. -/
theorem mixedFaultEnvironmentLowerTailMass_rectangular_le_half
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin groupCount × Fin groupWidth) -> Word wordWidth)
    (secret : Word wordWidth)
    (free : Environment -> Finset (Fin groupCount × Fin groupWidth))
    (fixed : Environment -> (Fin groupCount × Fin groupWidth) -> Bool)
    (groupSummary : (environment : Environment) ->
      StepTwoJointOutcome (Fin groupCount × Fin groupWidth) wordWidth ->
        Mask (Fin groupCount × Fin groupWidth) -> Fin groupCount -> S)
    (target mean k c paperN logN : Rat)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
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
    mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary target <= 1 / 2 := by
  apply environmentAveragedFailureMass_le environmentWeight
    (fun environment =>
      mixedFixedEnvironmentLowerTailMass wordWidth groupCount groupWidth
        (positions environment) secret (free environment) (fixed environment)
        (groupSummary environment) target)
    (1 / 2) hWeightNonneg hWeightNormalized
  intro environment
  exact mixedFixedEnvironmentLowerTailMass_rectangular_le_half
    (positions environment) secret (free environment) (fixed environment)
    (groupSummary environment) target mean k c paperN logN hWordWidth
    hGroupWidth hExactMean hMeanParameters hTargetParameters hc hPaperN hLogN
    hck hCollisionBudget hTailBudget

end

end SimonDCP.Probability.LemmaOneFaultEnvironmentAveraging
