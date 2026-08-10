import SimonDCP.Probability.LemmaOneFaultEnvironmentAveraging
import SimonDCP.Probability.LemmaOneRoundedParameters

/-!
# Rounded parameters in the fixed-environment Lemma 1 chain

This module removes the exact-mean, power-of-two, and exact-divisibility
hypotheses from the analytic fixed-fault-environment estimate.  For natural
parameters `k`, `c`, and `n`, it uses

* `ell = floor(log_2 n)`,
* `m = c * ell`,
* `K = ceil((k * n^(c+1)) / m)`, and
* target `n / ell`.

The experiment therefore contains `K * m` coordinate samples.  The theorems
`nominalSampleCount_le_roundedSampleCount` and
`roundedSampleCount_lt_nominal_add_width` show that this count is the nominal
`k * n^(c+1)` rounded up by less than one complete group.

The proof uses a lower bound on the actual Bernoulli mean, rather than an
exact mean identity.  The final `1/2` statements retain two explicit,
checkable arithmetic budgets: a logarithmic collision budget and the usual
Chebyshev tail budget.  No gate-level circuit or quantum fault-channel claim
is made here.
-/

namespace SimonDCP.Probability.LemmaOneRoundedFixedEnvironment

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernarySubsetSumBound
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.RectangularGroupPartition
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.LemmaOneOuterAveraging
open SimonDCP.Probability.LemmaOneFiniteModel
open SimonDCP.Probability.LemmaOneRoundedParameters
open SimonDCP.Probability.LemmaOneFixedEnvironment
open SimonDCP.Probability.LemmaOneFaultEnvironmentAveraging
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepTwoJointKernel
open SimonDCP.Probability.StepTwoUniformMarginals
open SimonDCP.Probability.StepFourLabelPhaseBridge
open SimonDCP.Probability.FaultyHighBitCarry
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

noncomputable section

variable {Outer G Label : Type*} {N m : Nat}
  [Fintype Outer]
  [Fintype G] [DecidableEq G] [AddCommGroup G]
  [DecidableEq Label]

/-- The rectangular finite-model estimate when the actual all-zero-group
mean is only bounded below by the paper's reference mean. -/
theorem nested_lowerTailMass_rectangular_lowerMean_le
    (outerWeight : Outer -> Rat)
    (sample : Outer -> (Fin N × Fin m) -> G)
    (free : Outer -> Finset (Fin N × Fin m))
    (fixed : Outer -> Mask (Fin N × Fin m))
    (residue : Outer -> G)
    (label : Outer -> Mask (Fin N × Fin m) -> Label)
    (target k c n L : Rat)
    (hOuterWeight : forall outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hUniform :
      HasUniformLocalMarginals
        (groupUnionFamily (rectangularGroups N m)) outerWeight sample)
    (hSupport : forall outer, outerWeight outer ≠ 0 ->
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer)).Nonempty)
    (hm : 0 < m)
    (hMeanLower :
      (k / c) * (n / L) <= (N : Rat) * (1 / 2 : Rat) ^ m)
    (hTargetParameters : target = n / L)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    nestedFiniteMass outerWeight
        (fun outer =>
          labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              (free outer) (fixed outer) (sample outer) (residue outer))
            (label outer))
        (fun _ output =>
          indicatorSum N
              (groupZeroIndicator (rectangularGroups N m)) output < target) <=
      (N ^ 2 : Rat) *
          (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)) +
        (k * c / (k - c) ^ 2) * (L / n) := by
  classical
  let collisionBound : Rat :=
    (N ^ 2 : Rat) *
      (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat))
  let tailBound : Rat := (k * c / (k - c) ^ 2) * (L / n)
  apply nestedFiniteMass_le_simultaneousLocalFailure_add
    (groupUnionFamily (rectangularGroups N m)) sample outerWeight
    (fun outer =>
      labelledBornWeight
        (maskCoordinateSubcubeResidueFibre
          (free outer) (fixed outer) (sample outer) (residue outer))
        (label outer))
    (fun _ output =>
      indicatorSum N
          (groupZeroIndicator (rectangularGroups N m)) output < target)
    collisionBound tailBound
  · exact hOuterWeight
  · exact hOuterNormalized
  · intro outer _ output
    exact labelledBornWeight_nonneg
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer))
      (label outer) output
  · intro outer hOuter
    exact sum_labelledBornWeight_eq_one
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer))
      (label outer) (hSupport outer hOuter)
  · dsimp [tailBound]
    have hk : 0 < k := lt_trans hc hkc
    have hdiff : 0 < k - c := sub_pos.mpr hkc
    exact (mul_pos
      (div_pos (mul_pos hk hc) (pow_pos hdiff 2))
      (div_pos hL hn)).le
  · dsimp [collisionBound]
    exact mass_rectangularGroupUnionFailure_le
      outerWeight sample hOuterWeight hUniform hm
  · intro outer hOuter hGood
    have hInjectiveOne : forall index,
        SubsetSumInjectiveWithin
          (free outer ∩ rectangularGroups N m index) (sample outer) := by
      intro index
      exact subsetSumInjectiveWithin_free_inter_of_goodOuter
        (groupUnionFamily (rectangularGroups N m)) sample outer
        (free outer) (rectangularGroups N m index) hGood
        (group_mem_groupUnionFamily (rectangularGroups N m) index)
    have hInjectivePair : forall left right, left ≠ right ->
        SubsetSumInjectiveWithin
          (free outer ∩
            (rectangularGroups N m left ∪ rectangularGroups N m right))
          (sample outer) := by
      intro left right _
      exact subsetSumInjectiveWithin_free_inter_of_goodOuter
        (groupUnionFamily (rectangularGroups N m)) sample outer
        (free outer)
        (rectangularGroups N m left ∪ rectangularGroups N m right) hGood
        (union_mem_groupUnionFamily (rectangularGroups N m) left right)
    have hTail := lowerTailMass_le_paper_bound_of_mean_ge N
      (labelledBornWeight
        (maskCoordinateSubcubeResidueFibre
          (free outer) (fixed outer) (sample outer) (residue outer))
        (label outer))
      (groupZeroIndicator (rectangularGroups N m))
      ((1 / 2 : Rat) ^ m) target k c n L
      (fun output => labelledBornWeight_nonneg
        (maskCoordinateSubcubeResidueFibre
          (free outer) (fixed outer) (sample outer) (residue outer))
        (label outer) output)
      (sum_labelledBornWeight_eq_one
        (maskCoordinateSubcubeResidueFibre
          (free outer) (fixed outer) (sample outer) (residue outer))
        (label outer) (hSupport outer hOuter))
      (fun index output =>
        zeroOnIndicator_idempotent (rectangularGroups N m index) output)
      (groupZeroIndicator_mean_eq
        (rectangularGroups N m) (free outer) (fixed outer)
        (sample outer) (residue outer) (label outer) (hSupport outer hOuter)
        rectangularGroups_card_eq hInjectiveOne)
      (groupZeroIndicator_pair_mean_eq
        (rectangularGroups N m) (free outer) (fixed outer)
        (sample outer) (residue outer) (label outer) (hSupport outer hOuter)
        rectangularGroups_card_eq rectangularGroups_pairwiseDisjoint
        hInjectivePair)
      (by positivity) hTargetParameters hMeanLower hc hn hL hkc
    dsimp [tailBound]
    unfold finiteMass
    unfold eventMass at hTail
    convert hTail using 1
    apply Finset.sum_congr rfl
    intro output _
    by_cases hEvent :
        indicatorSum N
            (groupZeroIndicator (rectangularGroups N m)) output < target <;>
      simp [hEvent]

variable {k c n : Nat}

set_option maxHeartbeats 800000 in
/-- The rational fixed-environment estimate with floor-logarithmic group
width and ceiling-rounded group count. -/
theorem lowerTailMass_fixedEnvironment_rounded_le
    {S : Type*} [DecidableEq S]
    (free : Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k) :
    nestedFiniteMass
        (stepTwoJointWeight n free fixed)
        (fixedEnvironmentStepFourWeight n (roundedGroupCount k c n)
          (roundedGroupWidth c n) free fixed groupSummary)
        (fun _ output =>
          indicatorSum (roundedGroupCount k c n)
              (groupZeroIndicator
                (rectangularGroups (roundedGroupCount k c n)
                  (roundedGroupWidth c n))) output <
            (n : Rat) / (roundedLog n : Rat)) <=
      (roundedGroupCount k c n ^ 2 : Rat) *
          (((3 ^ (2 * roundedGroupWidth c n) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (n - 1))) : Rat)) +
        (((k : Rat) * (c : Rat)) /
            ((k : Rat) - (c : Rat)) ^ 2) *
          ((roundedLog n : Rat) / (n : Rat)) := by
  let I := Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)
  have hWordWidth : 0 < n := by omega
  have hGroupWidth : 0 < roundedGroupWidth c n :=
    roundedGroupWidth_pos c n hc hn
  have hSupport : forall outcome : StepTwoJointOutcome I n,
      stepTwoJointWeight n free fixed outcome ≠ 0 ->
        (maskCoordinateSubcubeResidueFibre free
          (boolMaskEquiv I fixed)
          (fun coordinate => lowBitsHom n (outcome.1 coordinate))
          outcome.2).Nonempty := by
    intro outcome hOutcome
    have hBooleanSupport :
        (boolStepTwoMeasuredFibre n free fixed outcome.1 outcome.2).Nonempty :=
      (stepTwoJointWeight_ne_zero_iff n free fixed outcome).mp hOutcome
    rw [← image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
    exact hBooleanSupport.image (boolMaskEquiv I)
  exact nested_lowerTailMass_rectangular_lowerMean_le
    (Outer := StepTwoJointOutcome I n)
    (G := ZMod (2 ^ (n - 1)))
    (Label := StepFourLabel (Fin (roundedGroupCount k c n)) S)
    (N := roundedGroupCount k c n) (m := roundedGroupWidth c n)
    (outerWeight := stepTwoJointWeight n free fixed)
    (sample := fun outcome coordinate => lowBitsHom n (outcome.1 coordinate))
    (free := fun _ => free)
    (fixed := fun _ => boolMaskEquiv I fixed)
    (residue := fun outcome => outcome.2)
    (label := fun outcome =>
      paperStepFourLabel (fullSumHighBit n outcome.1) (groupSummary outcome))
    ((n : Rat) / (roundedLog n : Rat)) (k : Rat) (c : Rat) (n : Rat)
    (roundedLog n : Rat)
    (stepTwoJointWeight_nonneg n free fixed)
    (sum_stepTwoJointWeight_eq_one n free fixed)
    (hasUniformLocalMarginals_stepTwoJointWeight_lowBits n hWordWidth free
      fixed
      (groupUnionFamily
        (rectangularGroups (roundedGroupCount k c n)
          (roundedGroupWidth c n))))
    hSupport hGroupWidth (roundedMean_ge_reference k c n hc hn) rfl
    (by exact_mod_cast hc) (by exact_mod_cast hWordWidth)
    (by exact_mod_cast Nat.log_pos (by norm_num) hn)
    (by exact_mod_cast hck)

/-- The composed analytic fixed-environment kernel inherits the rounded
collision-plus-Chebyshev estimate. -/
theorem mixedFixedEnvironmentLowerTailMass_rounded_le
    {S : Type*} [DecidableEq S]
    (positions :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Word n)
    (secret : Word n)
    (free : Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k) :
    mixedFixedEnvironmentLowerTailMass n (roundedGroupCount k c n)
        (roundedGroupWidth c n) positions secret free fixed groupSummary
        ((n : Rat) / (roundedLog n : Rat)) <=
      ((roundedGroupCount k c n ^ 2 : Rat) *
          (((3 ^ (2 * roundedGroupWidth c n) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (n - 1))) : Rat)) +
        (((k : Rat) * (c : Rat)) /
            ((k : Rat) - (c : Rat)) ^ 2) *
          ((roundedLog n : Rat) / (n : Rat)) : Real) := by
  rw [mixedFixedEnvironmentLowerTailMass_eq_cast_nestedFiniteMass
    (by omega) positions secret free fixed groupSummary
    ((n : Rat) / (roundedLog n : Rat))]
  exact_mod_cast lowerTailMass_fixedEnvironment_rounded_le free fixed
    groupSummary hc hn hck

/-- The two explicit rounded arithmetic budgets imply a rational
fixed-environment failure bound of `1/2`. -/
theorem lowerTailMass_fixedEnvironment_rounded_le_half
    {S : Type*} [DecidableEq S]
    (free : Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k)
    (hCollisionBudget :
      3 + 2 * Nat.clog 2 k + (6 * c + 2) * Nat.clog 2 n <= n)
    (hTailBudget :
      4 * k * c * roundedLog n <= (k - c) ^ 2 * n) :
    nestedFiniteMass
        (stepTwoJointWeight n free fixed)
        (fixedEnvironmentStepFourWeight n (roundedGroupCount k c n)
          (roundedGroupWidth c n) free fixed groupSummary)
        (fun _ output =>
          indicatorSum (roundedGroupCount k c n)
              (groupZeroIndicator
                (rectangularGroups (roundedGroupCount k c n)
                  (roundedGroupWidth c n))) output <
            (n : Rat) / (roundedLog n : Rat)) <= 1 / 2 := by
  have hTailBudgetRat :
      (4 : Rat) * (k : Rat) * (c : Rat) * (roundedLog n : Rat) <=
        ((k : Rat) - (c : Rat)) ^ 2 * (n : Rat) := by
    have hCast :
        ((4 * k * c * roundedLog n : Nat) : Rat) <=
          (((k - c) ^ 2 * n : Nat) : Rat) := by
      exact_mod_cast hTailBudget
    simpa [Nat.cast_sub (Nat.le_of_lt hck)] using hCast
  calc
    nestedFiniteMass
        (stepTwoJointWeight n free fixed)
        (fixedEnvironmentStepFourWeight n (roundedGroupCount k c n)
          (roundedGroupWidth c n) free fixed groupSummary)
        (fun _ output =>
          indicatorSum (roundedGroupCount k c n)
              (groupZeroIndicator
                (rectangularGroups (roundedGroupCount k c n)
                  (roundedGroupWidth c n))) output <
            (n : Rat) / (roundedLog n : Rat)) <=
        (roundedGroupCount k c n ^ 2 : Rat) *
            (((3 ^ (2 * roundedGroupWidth c n) - 1 : Nat) : Rat) /
              (Fintype.card (ZMod (2 ^ (n - 1))) : Rat)) +
          (((k : Rat) * (c : Rat)) /
              ((k : Rat) - (c : Rat)) ^ 2) *
            ((roundedLog n : Rat) / (n : Rat)) :=
      lowerTailMass_fixedEnvironment_rounded_le free fixed groupSummary
        hc hn hck
    _ <= 1 / 4 + 1 / 4 := add_le_add
      (rectangularCollisionBound_zmod_le_quarter
        (N := roundedGroupCount k c n) (m := roundedGroupWidth c n) (n - 1)
        (roundedCollisionBudget_of_clogBudget k c n hc hn hCollisionBudget))
      (paperTailBound_le_quarter (k : Rat) (c : Rat) (n : Rat)
        (roundedLog n : Rat) (by positivity) (by exact_mod_cast hck)
        hTailBudgetRat)
    _ = 1 / 2 := by norm_num

/-- The same rounded budgets bound the composed analytic fixed-environment
failure mass by `1/2`. -/
theorem mixedFixedEnvironmentLowerTailMass_rounded_le_half
    {S : Type*} [DecidableEq S]
    (positions :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Word n)
    (secret : Word n)
    (free : Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed :
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k)
    (hCollisionBudget :
      3 + 2 * Nat.clog 2 k + (6 * c + 2) * Nat.clog 2 n <= n)
    (hTailBudget :
      4 * k * c * roundedLog n <= (k - c) ^ 2 * n) :
    mixedFixedEnvironmentLowerTailMass n (roundedGroupCount k c n)
        (roundedGroupWidth c n) positions secret free fixed groupSummary
        ((n : Rat) / (roundedLog n : Rat)) <= 1 / 2 := by
  rw [mixedFixedEnvironmentLowerTailMass_eq_cast_nestedFiniteMass
    (by omega) positions secret free fixed groupSummary
    ((n : Rat) / (roundedLog n : Rat))]
  have hRational := lowerTailMass_fixedEnvironment_rounded_le_half free fixed
    groupSummary hc hn hck hCollisionBudget hTailBudget
  have hHalfCast : (1 / 2 : Real) = ((1 / 2 : Rat) : Real) := by norm_num
  rw [hHalfCast]
  exact_mod_cast hRational

/-- With the concrete paper-compatible constants `k = 24` and `c = 12`,
the explicit arithmetic budgets hold automatically for every `n >= 1024`. -/
theorem mixedFixedEnvironmentLowerTailMass_paperConstants_le_half
    {S : Type*} [DecidableEq S]
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
    mixedFixedEnvironmentLowerTailMass n (roundedGroupCount 24 12 n)
        (roundedGroupWidth 12 n) positions secret free fixed groupSummary
        ((n : Rat) / (roundedLog n : Rat)) <= 1 / 2 := by
  exact mixedFixedEnvironmentLowerTailMass_rounded_le_half
    positions secret free fixed groupSummary (by norm_num) (by omega)
    (by norm_num) (paperConstants_clogBudget n hn)
    (paperConstants_tailBudget n hn)

variable {Environment : Type*} [Fintype Environment]

/-- Classical averaging preserves the rounded fixed-environment estimate.
All realized fault data may depend on the environment. -/
theorem mixedFaultEnvironmentLowerTailMass_rounded_le
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Word n)
    (secret : Word n)
    (free : Environment -> Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed : Environment ->
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : (environment : Environment) -> StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k) :
    mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary ((n : Rat) / (roundedLog n : Rat)) <=
      ((roundedGroupCount k c n ^ 2 : Rat) *
          (((3 ^ (2 * roundedGroupWidth c n) - 1 : Nat) : Rat) /
            (Fintype.card (ZMod (2 ^ (n - 1))) : Rat)) +
        (((k : Rat) * (c : Rat)) /
            ((k : Rat) - (c : Rat)) ^ 2) *
          ((roundedLog n : Rat) / (n : Rat)) : Real) := by
  apply environmentAveragedFailureMass_le environmentWeight
    (fun environment =>
      mixedFixedEnvironmentLowerTailMass n (roundedGroupCount k c n)
        (roundedGroupWidth c n) (positions environment) secret
        (free environment) (fixed environment) (groupSummary environment)
        ((n : Rat) / (roundedLog n : Rat))) _ hWeightNonneg hWeightNormalized
  intro environment
  exact mixedFixedEnvironmentLowerTailMass_rounded_le
    (positions environment) secret (free environment) (fixed environment)
    (groupSummary environment) hc hn hck

/-- The rounded `1/2` bound is uniform over every normalized finite
classical mixture of fault environments. -/
theorem mixedFaultEnvironmentLowerTailMass_rounded_le_half
    {S : Type*} [DecidableEq S]
    (environmentWeight : Environment -> Real)
    (positions : Environment ->
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Word n)
    (secret : Word n)
    (free : Environment -> Finset
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)))
    (fixed : Environment ->
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) -> Bool)
    (groupSummary : (environment : Environment) -> StepTwoJointOutcome
      (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) n ->
        Mask
          (Fin (roundedGroupCount k c n) × Fin (roundedGroupWidth c n)) ->
        Fin (roundedGroupCount k c n) -> S)
    (hWeightNonneg : ∀ environment, 0 <= environmentWeight environment)
    (hWeightNormalized : (∑ environment, environmentWeight environment) = 1)
    (hc : 0 < c) (hn : 2 <= n) (hck : c < k)
    (hCollisionBudget :
      3 + 2 * Nat.clog 2 k + (6 * c + 2) * Nat.clog 2 n <= n)
    (hTailBudget :
      4 * k * c * roundedLog n <= (k - c) ^ 2 * n) :
    mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary ((n : Rat) / (roundedLog n : Rat)) <= 1 / 2 := by
  apply environmentAveragedFailureMass_le environmentWeight
    (fun environment =>
      mixedFixedEnvironmentLowerTailMass n (roundedGroupCount k c n)
        (roundedGroupWidth c n) (positions environment) secret
        (free environment) (fixed environment) (groupSummary environment)
        ((n : Rat) / (roundedLog n : Rat))) (1 / 2) hWeightNonneg
    hWeightNormalized
  intro environment
  exact mixedFixedEnvironmentLowerTailMass_rounded_le_half
    (positions environment) secret (free environment) (fixed environment)
    (groupSummary environment) hc hn hck hCollisionBudget hTailBudget

/-- The concrete `k = 24`, `c = 12`, `n >= 1024` bound also survives every
normalized finite classical mixture of fault environments. -/
theorem mixedFaultEnvironmentLowerTailMass_paperConstants_le_half
    {S : Type*} [DecidableEq S]
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
    mixedFaultEnvironmentLowerTailMass environmentWeight positions secret
        free fixed groupSummary ((n : Rat) / (roundedLog n : Rat)) <= 1 / 2 := by
  exact mixedFaultEnvironmentLowerTailMass_rounded_le_half
    environmentWeight positions secret free fixed groupSummary hWeightNonneg
    hWeightNormalized (by norm_num) (by omega) (by norm_num)
    (paperConstants_clogBudget n hn) (paperConstants_tailBudget n hn)

end

end SimonDCP.Probability.LemmaOneRoundedFixedEnvironment
