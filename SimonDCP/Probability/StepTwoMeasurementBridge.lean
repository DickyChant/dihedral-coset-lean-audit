import Mathlib.Data.ZMod.Basic
import SimonDCP.Probability.BooleanMaskBridge
import SimonDCP.Probability.CoordinateSubcubeBorn

/-!
# Step-2 low-residue measurement bridge

The paper computes

`z = sum_i b_i * y_i` in `ZMod (2 ^ n)`

and measures all but its highest bit.  The measured value is therefore the
image of `z` under the canonical quotient map from `ZMod (2 ^ n)` to
`ZMod (2 ^ (n - 1))`.  This file models that quotient map explicitly and
proves that conditioning a fault-pattern coordinate subcube on the measured
outcome gives exactly the coordinate-subcube residue fibre used by
`CoordinateSubcubeBorn`.

This is a support-level semantic bridge.  It does not identify the amplitudes
of the paper's mixed correct/faulty tensor state with the unweighted labelled
amplitudes used by `CoordinateSubcubeBorn`; that separate identification must
also show that every additional phase is constant on each complete Step-4
label fibre.

In particular, a faulty basis sample has no secret-dependent `b_i * y_i * d`
phase, although the displayed Step-2 state in the paper writes the secret
phase using the full computed sum `z`.  For a fixed fault environment the
actual secret exponent is the free-coordinate sum, while `z` also contains a
fixed faulty-coordinate offset.  Connecting this support theorem to
`Quantum.Step2Phase` therefore requires an affine high-bit carry calculation
for subtraction of that offset; the support identity below does not assume
the paper's unsupported full-sum phase rewrite.
-/

namespace SimonDCP.Probability.StepTwoMeasurementBridge

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.CoordinateSubcubeBorn
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.FaultySamplePhase
open SimonDCP.Probability.LabelledBornProbability

open scoped BigOperators

/-- The canonical map that forgets the highest bit of an `n`-bit residue. -/
def lowBitsHom (n : Nat) :
    ZMod (2 ^ n) →+ ZMod (2 ^ (n - 1)) :=
  (ZMod.castHom
    (pow_dvd_pow 2 (Nat.sub_le n 1))
    (ZMod (2 ^ (n - 1)))).toAddMonoidHom

@[simp]
theorem lowBitsHom_apply (n : Nat) (z : ZMod (2 ^ n)) :
    lowBitsHom n z = ZMod.cast z :=
  rfl

/-- On canonical representatives, `lowBitsHom` is literal reduction modulo
`2 ^ (n - 1)`, hence it records exactly the lower `n - 1` bits. -/
@[simp]
theorem lowBitsHom_val (n : Nat) (z : ZMod (2 ^ n)) :
    (lowBitsHom n z).val = z.val % (2 ^ (n - 1)) := by
  rw [lowBitsHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

/-- The quotient map commutes with the subset sum encoded by a binary mask. -/
theorem lowBitsHom_booleanSubsetSum
    {I : Type*} [Fintype I]
    (n : Nat) (sample : I -> ZMod (2 ^ n)) (selection : Mask I) :
    lowBitsHom n (booleanSubsetSum sample selection) =
      booleanSubsetSum (fun i => lowBitsHom n (sample i)) selection := by
  classical
  unfold booleanSubsetSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hselection : selection i = 0 <;> simp [hselection]

/-- The same commuting identity for the Boolean selection representation. -/
theorem lowBitsHom_fullSubsetSum
    {I : Type*} [Fintype I]
    (n : Nat) (sample : I -> ZMod (2 ^ n)) (selection : I -> Bool) :
    lowBitsHom n (fullSubsetSum selection sample) =
      fullSubsetSum selection (fun i => lowBitsHom n (sample i)) := by
  classical
  unfold fullSubsetSum boolSelectedTerm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hselection : selection i = true <;> simp [hselection]

/-- The actual Step-2 classical value obtained by measuring the low `n - 1`
bits of the computed modular subset sum. -/
def stepTwoLowOutcome
    {I : Type*} [Fintype I]
    (n : Nat) (sample : I -> ZMod (2 ^ n)) (selection : I -> Bool) :
    ZMod (2 ^ (n - 1)) :=
  lowBitsHom n (fullSubsetSum selection sample)

/-- Boolean selections compatible with a fixed fault pattern and one measured
Step-2 low-residue outcome. -/
noncomputable def boolStepTwoMeasuredFibre
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) (measured : ZMod (2 ^ (n - 1))) :
    Finset (I -> Bool) :=
  (coordinateSubcube free fixed).filter fun selection =>
    stepTwoLowOutcome n sample selection = measured

@[simp]
theorem mem_boolStepTwoMeasuredFibre_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} {free : Finset I} {fixed selection : I -> Bool}
    {sample : I -> ZMod (2 ^ n)} {measured : ZMod (2 ^ (n - 1))} :
    selection ∈ boolStepTwoMeasuredFibre n free fixed sample measured ↔
      selection ∈ coordinateSubcube free fixed ∧
        stepTwoLowOutcome n sample selection = measured := by
  classical
  simp [boolStepTwoMeasuredFibre]

/-- Conditioning on the measured low residue is exactly ordinary residue
conditioning after reducing every Fourier sample modulo `2 ^ (n - 1)`. -/
theorem boolStepTwoMeasuredFibre_eq_boolCoordinateSubcubeResidueFibre
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) (measured : ZMod (2 ^ (n - 1))) :
    boolStepTwoMeasuredFibre n free fixed sample measured =
      boolCoordinateSubcubeResidueFibre free fixed
        (fun i => lowBitsHom n (sample i)) measured := by
  classical
  ext selection
  simp only [mem_boolStepTwoMeasuredFibre_iff,
    mem_boolCoordinateSubcubeResidueFibre_iff, stepTwoLowOutcome]
  rw [lowBitsHom_fullSubsetSum]

/-- After the canonical Boolean-to-`ZMod 2` encoding, the actual Step-2
measurement fibre is precisely the mask residue fibre consumed by
`CoordinateSubcubeBorn`. -/
theorem image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) (measured : ZMod (2 ^ (n - 1))) :
    Finset.image (boolMaskEquiv I)
        (boolStepTwoMeasuredFibre n free fixed sample measured) =
      maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun i => lowBitsHom n (sample i)) measured := by
  rw [boolStepTwoMeasuredFibre_eq_boolCoordinateSubcubeResidueFibre]
  exact image_boolCoordinateSubcubeResidueFibre_eq_mask
    free fixed (fun i => lowBitsHom n (sample i)) measured

/-- Support-level Step-2 specialization of the exact labelled Born identity.

The conclusion is deliberately stated using `labelledZeroEventMass`.  Turning
it into the probability of the paper's circuit still requires the separate
amplitude and complete-label identification described in the module header.
-/
theorem labelledZeroEventMass_stepTwoMeasuredFibre_eq
    {I Label : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq Label]
    (n : Nat) (free A : Finset I) (fixed : I -> Bool)
    (sample : I -> ZMod (2 ^ n)) (measured : ZMod (2 ^ (n - 1)))
    (label : Mask I -> Label)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ A)
        (fun i => lowBitsHom n (sample i))) :
    labelledZeroEventMass A
        (Finset.image (boolMaskEquiv I)
          (boolStepTwoMeasuredFibre n free fixed sample measured)) label =
      (1 / 2 : Rat) ^ A.card := by
  have hmaskSupport :
      (maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun i => lowBitsHom n (sample i)) measured).Nonempty := by
    rw [← image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
    exact hsupport.image (boolMaskEquiv I)
  rw [image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
  exact labelledZeroEventMass_maskCoordinateSubcubeResidueFibre_eq
    free A (boolMaskEquiv I fixed)
      (fun i => lowBitsHom n (sample i)) measured label hmaskSupport hinjective

end SimonDCP.Probability.StepTwoMeasurementBridge
