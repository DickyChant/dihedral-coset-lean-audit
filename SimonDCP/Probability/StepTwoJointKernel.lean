import SimonDCP.Probability.StepTwoUniformMarginals
import SimonDCP.Quantum.MixedFaultPatternFourierProduct

/-!
# The finite Step-2 joint measurement kernel

Fix a fault environment, represented by the free selection coordinates and
the Boolean values outside them.  Before Step 2, choose a selection uniformly
from this coordinate subcube and choose the full Fourier vector uniformly.
The weight below is the resulting joint law of the Fourier vector and the
measured low residue.  It is defined directly by counting the compatible
selection fibre.

This is primarily a finite classical measurement-law theorem.  The final
bridges identify both its pointwise joint weight and its Fourier-vector
marginal with the analytic mixed fault-pattern amplitude already formalized
in `MixedFaultPatternFourierProduct`.  They do not identify the complete
gate-level circuit preparation with that analytic amplitude model; that
state-level equality remains a separate statement.
-/

namespace SimonDCP.Probability.StepTwoJointKernel

open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepTwoUniformMarginals
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The joint outcome space consisting of the full Fourier vector and the
Step-2 low-residue measurement. -/
abbrev StepTwoJointOutcome (I : Type*) (n : Nat) :=
  (I -> ZMod (2 ^ n)) × ZMod (2 ^ (n - 1))

/-- The exact number of equally weighted pre-Step-2 pairs consisting of a
coordinate-subcube selection and a full Fourier vector. -/
def stepTwoJointDenominator (n : Nat) (free : Finset I) : Nat :=
  2 ^ free.card * (2 ^ n) ^ Fintype.card I

/-- The rational joint weight of a full Fourier vector and its measured
Step-2 low residue, for one fixed fault environment. -/
noncomputable def stepTwoJointWeight
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (outcome : StepTwoJointOutcome I n) : Rat :=
  (boolStepTwoMeasuredFibre n free fixed outcome.1 outcome.2).card /
    stepTwoJointDenominator n free

omit [DecidableEq I] in
@[simp]
theorem stepTwoJointDenominator_pos (n : Nat) (free : Finset I) :
    0 < stepTwoJointDenominator n free := by
  simp [stepTwoJointDenominator]

/-- For a fixed Fourier vector, the Step-2 residue fibres partition the
entire coordinate subcube. -/
theorem sum_card_boolStepTwoMeasuredFibre
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) :
    (∑ measured : ZMod (2 ^ (n - 1)),
        (boolStepTwoMeasuredFibre n free fixed sample measured).card) =
      2 ^ free.card := by
  classical
  have hMaps :
      (↑(coordinateSubcube free fixed) : Set (I -> Bool)).MapsTo
        (stepTwoLowOutcome n sample)
        (↑(Finset.univ : Finset (ZMod (2 ^ (n - 1)))) :
          Set (ZMod (2 ^ (n - 1)))) := by
    simp
  calc
    (∑ measured : ZMod (2 ^ (n - 1)),
        (boolStepTwoMeasuredFibre n free fixed sample measured).card) =
        ∑ measured ∈ (Finset.univ : Finset (ZMod (2 ^ (n - 1)))),
          ((coordinateSubcube free fixed).filter fun selection =>
            stepTwoLowOutcome n sample selection = measured).card := by
      simp [boolStepTwoMeasuredFibre]
    _ = (coordinateSubcube free fixed).card :=
      (Finset.card_eq_sum_card_fiberwise hMaps).symm
    _ = 2 ^ free.card := card_coordinateSubcube free fixed

/-- The finite Step-2 joint weight is nonnegative. -/
theorem stepTwoJointWeight_nonneg
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (outcome : StepTwoJointOutcome I n) :
    0 <= stepTwoJointWeight n free fixed outcome := by
  unfold stepTwoJointWeight
  positivity

/-- Summing out the measured residue recovers the uniform law on the full
Fourier vector. -/
theorem sum_stepTwoJointWeight_eq_uniformFullFourierWeight
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) :
    (∑ measured : ZMod (2 ^ (n - 1)),
        stepTwoJointWeight n free fixed (sample, measured)) =
      uniformFullFourierWeight n sample := by
  rw [uniformFullFourierWeight_eq]
  unfold stepTwoJointWeight stepTwoJointDenominator
  rw [← Finset.sum_div]
  have hFibreSum :
      (∑ measured : ZMod (2 ^ (n - 1)),
          ((boolStepTwoMeasuredFibre n free fixed sample measured).card :
            Rat)) =
        ((2 ^ free.card : Nat) : Rat) := by
    exact_mod_cast sum_card_boolStepTwoMeasuredFibre n free fixed sample
  rw [hFibreSum]
  push_cast
  field_simp

/-- The finite Step-2 joint kernel has total mass one. -/
theorem sum_stepTwoJointWeight_eq_one
    (n : Nat) (free : Finset I) (fixed : I -> Bool) :
    (∑ outcome : StepTwoJointOutcome I n,
        stepTwoJointWeight n free fixed outcome) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_stepTwoJointWeight_eq_uniformFullFourierWeight]
  simp [uniformFullFourierWeight]

/-- A joint outcome has nonzero weight exactly when its Step-2 selection
fibre is nonempty. -/
theorem stepTwoJointWeight_ne_zero_iff
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (outcome : StepTwoJointOutcome I n) :
    stepTwoJointWeight n free fixed outcome ≠ 0 ↔
      (boolStepTwoMeasuredFibre n free fixed
        outcome.1 outcome.2).Nonempty := by
  constructor
  · intro hweight
    apply Finset.card_ne_zero.mp
    intro hcard
    apply hweight
    simp [stepTwoJointWeight, hcard]
  · intro hsupport
    unfold stepTwoJointWeight
    apply div_ne_zero
    · exact_mod_cast Finset.card_ne_zero.mpr hsupport
    · exact_mod_cast ne_of_gt (stepTwoJointDenominator_pos n free)

/-- Equivalently, positivity of a joint outcome is exactly reachability of
the measured residue. -/
theorem stepTwoJointWeight_pos_iff
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (outcome : StepTwoJointOutcome I n) :
    0 < stepTwoJointWeight n free fixed outcome ↔
      (boolStepTwoMeasuredFibre n free fixed
        outcome.1 outcome.2).Nonempty := by
  constructor
  · intro hpositive
    exact (stepTwoJointWeight_ne_zero_iff n free fixed outcome).mp
      (ne_of_gt hpositive)
  · intro hsupport
    exact lt_of_le_of_ne
      (stepTwoJointWeight_nonneg n free fixed outcome)
      (Ne.symm
        ((stepTwoJointWeight_ne_zero_iff n free fixed outcome).mpr hsupport))

/-- Under the joint Step-2 law, every requested local restriction of the
reduced Fourier vector remains exactly uniform. -/
theorem hasUniformLocalMarginals_stepTwoJointWeight_lowBits
    (n : Nat) (hn : 0 < n) (free : Finset I) (fixed : I -> Bool)
    (family : Finset (Finset I)) :
    HasUniformLocalMarginals family
      (stepTwoJointWeight n free fixed)
      (fun outcome i => lowBitsHom n (outcome.1 i)) := by
  exact hasUniformLocalMarginals_prod_of_first_marginal
    family (uniformFullFourierWeight n)
      (fun sample i => lowBitsHom n (sample i))
      (stepTwoJointWeight n free fixed)
      (sum_stepTwoJointWeight_eq_uniformFullFourierWeight n free fixed)
      (hasUniformLocalMarginals_lowBits n hn family)

/-- Pointwise projective-measurement bridge: after casting to `Real`, the
joint counting weight is exactly the mixed-state Born mass summed over the
Boolean selections in the measured Step-2 fibre.  This identifies the full
Fourier-vector/low-residue joint law for the analytic fixed-environment
amplitude model. -/
theorem cast_stepTwoJointWeight_eq_sum_fibre_mixedBorn
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (positions : I -> ZMod (2 ^ n)) (secret : ZMod (2 ^ n))
    (frequencies : I -> ZMod (2 ^ n))
    (measured : ZMod (2 ^ (n - 1))) :
    (stepTwoJointWeight n free fixed (frequencies, measured) : Real) =
      ∑ selection ∈
          boolStepTwoMeasuredFibre n free fixed frequencies measured,
        ‖mixedPostPositionDftProductAmplitude
          free fixed positions secret (selection, frequencies)‖ ^ 2 := by
  classical
  let fibre :=
    boolStepTwoMeasuredFibre n free fixed frequencies measured
  have hSum :
      (∑ selection ∈ fibre,
          ‖mixedPostPositionDftProductAmplitude
            free fixed positions secret (selection, frequencies)‖ ^ 2) =
        (fibre.card : Real) *
          ((1 / 2 : Real) ^ free.card *
            ((((2 ^ n : Nat) : Real)⁻¹) ^ Fintype.card I)) := by
    calc
      (∑ selection ∈ fibre,
          ‖mixedPostPositionDftProductAmplitude
            free fixed positions secret (selection, frequencies)‖ ^ 2) =
          ∑ _selection ∈ fibre,
            ((1 / 2 : Real) ^ free.card *
              ((((2 ^ n : Nat) : Real)⁻¹) ^ Fintype.card I)) := by
        apply Finset.sum_congr rfl
        intro selection hselection
        rw [normSq_mixedPostPositionDftProductAmplitude]
        rw [if_pos]
        exact (mem_boolStepTwoMeasuredFibre_iff.mp hselection).1
      _ = (fibre.card : Real) *
          ((1 / 2 : Real) ^ free.card *
            ((((2 ^ n : Nat) : Real)⁻¹) ^ Fintype.card I)) := by
        simp
  change (stepTwoJointWeight n free fixed (frequencies, measured) : Real) =
    ∑ selection ∈ fibre,
      ‖mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies)‖ ^ 2
  rw [hSum]
  unfold stepTwoJointWeight stepTwoJointDenominator
  push_cast
  simp [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- The rational first marginal, cast to `Real`, is exactly the Born marginal
obtained by summing the analytic mixed correct/fault amplitude over every
Boolean selection.  The sign convention of the base position DFT is
irrelevant here because only squared norms occur. -/
theorem cast_sum_stepTwoJointWeight_eq_mixedBornFourierMarginal
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (positions : I -> ZMod (2 ^ n)) (secret : ZMod (2 ^ n))
    (frequencies : I -> ZMod (2 ^ n)) :
    ((∑ measured : ZMod (2 ^ (n - 1)),
        stepTwoJointWeight n free fixed (frequencies, measured)) : Rat) =
      ∑ selection : I -> Bool,
        ‖mixedPostPositionDftProductAmplitude
          free fixed positions secret (selection, frequencies)‖ ^ 2 := by
  rw [sum_stepTwoJointWeight_eq_uniformFullFourierWeight,
    uniformFullFourierWeight_eq,
    sum_selection_normSq_mixedPostPositionDftProductAmplitude]
  push_cast
  simp [one_div, inv_pow]

end SimonDCP.Probability.StepTwoJointKernel
