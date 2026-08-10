import SimonDCP.Probability.FaultyHighBitCarry

/-!
# Actual fixed-environment Step-4 Born masses

This file closes the amplitude-level composition for a fixed fault
environment.  The input data are the actual mixed correct/faulty product
amplitudes, the low-residue outcome measured in Step 2, and the complete
paper-style Step-4 label `(h, s_1, ..., s_g)`.

There are two deliberately separate normalizations.

* `mixedStepFourProjectedHadamardFibreAmplitude` is the exact unnormalized
  amplitude obtained by projecting onto one Step-2 outcome and one complete
  Step-4 label and then applying the normalized Boolean Hadamards.  Its common
  base-position/position-DFT scalar is displayed explicitly.
* `mixedStepFourZeroEventMass` is the conditional Born mass after that common
  scalar, including the Step-2 postselection normalization, has cancelled.
  Its denominator `2 ^ |I| * |support|` is therefore exact whenever the
  measured support is nonempty.

The key theorem transports the Boolean selection fibre through
`boolMaskEquiv` and uses
`mixedProductSecretPhase_eq_paperLabelPhase` term by term.  Thus the concrete
mixed-state Walsh amplitude is exactly the paper-label phased amplitude, not
merely equal to it in norm.  The common phase then cancels, and local
subset-sum injectivity gives the exact one-group and two-group all-zero Born
masses.

These results remain statements about the explicit finite analytic amplitude
model assembled in the imported modules.  They do not assert a new gate-level
circuit denotation theorem.
-/

namespace SimonDCP.Probability.ActualStepFourBorn

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.FaultySamplePhase
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepFourLabelPhaseBridge
open SimonDCP.Probability.FaultyHighBitCarry
open SimonDCP.Probability.LabelledBornProbability
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.CoordinateSubcubeBorn
open SimonDCP.Quantum.FaultPatternProductAmplitude
open SimonDCP.Quantum.FaultPatternFourierProduct
open SimonDCP.Quantum.MixedFaultPatternFourierProduct

noncomputable section

section CommonScalar

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {n : Nat}

/-- The selection-independent factor in every supported mixed product
amplitude at fixed base positions and fixed Fourier samples. -/
def mixedStepFourBasePositionDftScalar
    (free : Finset I) (positions sample : I -> Word n) : Complex :=
  QuantumAlg.PureState.invSqrt2 ^ free.card *
    productPositionDftAmplitude positions sample

/-- On the coordinate-subcube support, the actual post-position-DFT product
amplitude is the common base scalar times the concrete secret phase. -/
theorem mixedPostPositionDftProductAmplitude_eq_base_mul_secretPhase_of_mem
    (free : Finset I) (fixed : I -> Bool) (positions : I -> Word n)
    (secret : Word n) (selection : I -> Bool) (sample : I -> Word n)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, sample) =
      mixedStepFourBasePositionDftScalar free positions sample *
        mixedProductSecretPhase free secret selection sample := by
  rw [mixedPostPositionDftProductAmplitude_eq_surrogate_mul_phase,
    postPositionDftProductAmplitude,
    productSelectionAmplitude_eq_pow_of_mem_coordinateSubcube hselection]
  rfl

end CommonScalar

section ConcreteFibre

variable {I J S : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq S]
variable {n : Nat}

/-- The selections in the real Step-2 measured Boolean fibre which also have
one fixed complete paper-style Step-4 label. -/
def mixedStepFourSelectionFibre
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S) :
    Finset (I -> Bool) :=
  (boolStepTwoMeasuredFibre n free fixed sample measured).filter
    fun selection =>
      paperStepFourLabel (fullSumHighBit n sample) groupSummary
        (boolMaskEquiv I selection) = labelValue

@[simp]
theorem mem_mixedStepFourSelectionFibre_iff
    {free : Finset I} {fixed : I -> Bool}
    {sample : I -> Word n} {measured : ZMod (2 ^ (n - 1))}
    {groupSummary : Mask I -> J -> S} {labelValue : StepFourLabel J S}
    {selection : I -> Bool} :
    selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
        groupSummary labelValue ↔
      selection ∈ boolStepTwoMeasuredFibre n free fixed sample measured ∧
        paperStepFourLabel (fullSumHighBit n sample) groupSummary
          (boolMaskEquiv I selection) = labelValue := by
  simp [mixedStepFourSelectionFibre]

/-- The mask support obtained from the actual Boolean Step-2 measurement
fibre. -/
def mixedStepTwoMaskSupport
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1))) :
    Finset (Mask I) :=
  Finset.image (boolMaskEquiv I)
    (boolStepTwoMeasuredFibre n free fixed sample measured)

/-- The actual measured support is exactly the coordinate-subcube residue
fibre over the low-bit Fourier samples. -/
theorem mixedStepTwoMaskSupport_eq_maskCoordinateSubcubeResidueFibre
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1))) :
    mixedStepTwoMaskSupport n free fixed sample measured =
      maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun i => lowBitsHom n (sample i)) measured := by
  exact image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre
    n free fixed sample measured

/-- Boolean-to-mask transport takes a concrete selection/label fibre to the
corresponding `labelFibre` in the labelled Walsh model. -/
theorem image_mixedStepFourSelectionFibre_eq_labelFibre
    (n : Nat) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S) :
    Finset.image (boolMaskEquiv I)
        (mixedStepFourSelectionFibre n free fixed sample measured
          groupSummary labelValue) =
      labelFibre (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        labelValue := by
  classical
  ext mask
  constructor
  · intro hmask
    rcases Finset.mem_image.mp hmask with
      ⟨selection, hselectionFibre, hselectionMask⟩
    rcases mem_mixedStepFourSelectionFibre_iff.mp hselectionFibre with
      ⟨hstepTwo, hlabel⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr
        ⟨selection, hstepTwo, hselectionMask⟩
    · rwa [hselectionMask] at hlabel
  · intro hmask
    rcases Finset.mem_filter.mp hmask with ⟨hstepTwoMask, hlabel⟩
    rcases Finset.mem_image.mp hstepTwoMask with
      ⟨selection, hstepTwo, hselectionMask⟩
    apply Finset.mem_image.mpr
    refine ⟨selection, ?_, hselectionMask⟩
    apply mem_mixedStepFourSelectionFibre_iff.mpr
    refine ⟨hstepTwo, ?_⟩
    rwa [hselectionMask]

/-- The concrete reduced Step-4 Walsh amplitude on one measured Boolean
selection fibre and one complete paper label.  Only the selection-dependent
actual mixed-state phase remains; all common circuit scalars are kept
separate below. -/
def mixedStepFourFibreWalshAmplitude
    (n : Nat) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S)
    (output : Mask I) : Complex :=
  ∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
      groupSummary labelValue,
    mixedProductSecretPhase free secret selection sample *
      (walsh (boolMaskEquiv I selection) output : Complex)

/-- The concrete common phase determined by the measured residue and fixed
fault environment. -/
def actualAdjustedResiduePhase
    (n : Nat) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1))) : Complex :=
  adjustedResiduePhase n (positionSecretCharacter secret) measured
    (fixedFaultyContribution free fixed sample)

/-- Exact amplitude bridge: after Boolean-to-mask transport, the concrete
mixed-state phase sum is the paper-label phased Walsh amplitude. -/
theorem mixedStepFourFibreWalshAmplitude_eq_paperPhased
    (hn : 0 < n) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S)
    (output : Mask I) :
    mixedStepFourFibreWalshAmplitude n secret free fixed sample measured
        groupSummary labelValue output =
      fibrePhaseAmplitude
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        (paperLabelPhase
          (actualAdjustedResiduePhase n secret free fixed sample measured)
          (lastBitBool secret.val))
        labelValue output := by
  classical
  let selectionFibre :=
    mixedStepFourSelectionFibre n free fixed sample measured
      groupSummary labelValue
  let maskFibre := Finset.image (boolMaskEquiv I) selectionFibre
  calc
    mixedStepFourFibreWalshAmplitude n secret free fixed sample measured
        groupSummary labelValue output =
        ∑ mask ∈ maskFibre,
          mixedProductSecretPhase free secret
              ((boolMaskEquiv I).symm mask) sample *
            (walsh mask output : Complex) := by
      unfold mixedStepFourFibreWalshAmplitude maskFibre selectionFibre
      rw [Finset.sum_image (boolMaskEquiv I).injective.injOn]
      simp
    _ = ∑ mask ∈ maskFibre,
          paperLabelPhase
              (actualAdjustedResiduePhase n secret free fixed sample measured)
              (lastBitBool secret.val)
              (paperStepFourLabel (fullSumHighBit n sample) groupSummary mask) *
            (walsh mask output : Complex) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      rcases Finset.mem_image.mp hmask with ⟨selection, hselectionFibre, rfl⟩
      rw [Equiv.symm_apply_apply]
      have hstepTwo :=
        (mem_mixedStepFourSelectionFibre_iff.mp hselectionFibre).1
      have hstepTwoData := mem_boolStepTwoMeasuredFibre_iff.mp hstepTwo
      have hmeasured :
          lowResidue n (fullSubsetSum selection sample) = measured := by
        rw [lowResidue_eq_lowBitsHom]
        simpa [stepTwoLowOutcome] using hstepTwoData.2
      rw [mixedProductSecretPhase_eq_paperLabelPhase hn secret free fixed
        sample measured groupSummary selection hstepTwoData.1 hmeasured]
      rfl
    _ = fibrePhaseAmplitude
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        (paperLabelPhase
          (actualAdjustedResiduePhase n secret free fixed sample measured)
          (lastBitBool secret.val))
        labelValue output := by
      unfold fibrePhaseAmplitude maskFibre selectionFibre
      rw [image_mixedStepFourSelectionFibre_eq_labelFibre]

/-- The exact unnormalized amplitude after projection onto the measured
Step-2 outcome and complete Step-4 label, followed by normalized Hadamards.
No postselection renormalization is included in this definition. -/
def mixedStepFourProjectedHadamardFibreAmplitude
    (n : Nat) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S)
    (output : Mask I) : Complex :=
  QuantumAlg.PureState.invSqrt2 ^ Fintype.card I *
    ∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
        groupSummary labelValue,
      mixedPostPositionDftProductAmplitude
          free fixed positions secret (selection, sample) *
        (walsh (boolMaskEquiv I selection) output : Complex)

/-- The complete selection-independent scalar before Step-2 postselection
renormalization: free-branch normalization, position DFT, and Step-4
Hadamard normalization. -/
def mixedStepFourUnnormalizedCommonScalar
    (free : Finset I) (positions sample : I -> Word n) : Complex :=
  QuantumAlg.PureState.invSqrt2 ^ Fintype.card I *
    mixedStepFourBasePositionDftScalar free positions sample

omit [DecidableEq I] in
/-- The common projected-amplitude scalar never vanishes. -/
theorem mixedStepFourUnnormalizedCommonScalar_ne_zero
    (free : Finset I) (positions sample : I -> Word n) :
    mixedStepFourUnnormalizedCommonScalar free positions sample ≠ 0 := by
  unfold mixedStepFourUnnormalizedCommonScalar
    mixedStepFourBasePositionDftScalar
  exact mul_ne_zero
    (pow_ne_zero _ QuantumAlg.PureState.invSqrt2_ne_zero)
    (mul_ne_zero
      (pow_ne_zero _ QuantumAlg.PureState.invSqrt2_ne_zero)
      (productPositionDftAmplitude_ne_zero positions sample))

/-- The exact projected circuit amplitude is the displayed common scalar
times the reduced concrete Walsh amplitude. -/
theorem mixedStepFourProjectedHadamardFibreAmplitude_eq_common_mul
    (n : Nat) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (labelValue : StepFourLabel J S)
    (output : Mask I) :
    mixedStepFourProjectedHadamardFibreAmplitude n positions secret free fixed
        sample measured groupSummary labelValue output =
      mixedStepFourUnnormalizedCommonScalar free positions sample *
        mixedStepFourFibreWalshAmplitude n secret free fixed sample measured
          groupSummary labelValue output := by
  classical
  have hsum :
      (∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
          groupSummary labelValue,
        mixedPostPositionDftProductAmplitude
            free fixed positions secret (selection, sample) *
          (walsh (boolMaskEquiv I selection) output : Complex)) =
        mixedStepFourBasePositionDftScalar free positions sample *
          ∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
              groupSummary labelValue,
            mixedProductSecretPhase free secret selection sample *
              (walsh (boolMaskEquiv I selection) output : Complex) := by
    calc
      (∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
          groupSummary labelValue,
        mixedPostPositionDftProductAmplitude
            free fixed positions secret (selection, sample) *
          (walsh (boolMaskEquiv I selection) output : Complex)) =
        ∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
            groupSummary labelValue,
          (mixedStepFourBasePositionDftScalar free positions sample *
              mixedProductSecretPhase free secret selection sample) *
            (walsh (boolMaskEquiv I selection) output : Complex) := by
        apply Finset.sum_congr rfl
        intro selection hselectionFibre
        have hstepTwo :=
          (mem_mixedStepFourSelectionFibre_iff.mp hselectionFibre).1
        have hselection := (mem_boolStepTwoMeasuredFibre_iff.mp hstepTwo).1
        rw [mixedPostPositionDftProductAmplitude_eq_base_mul_secretPhase_of_mem
          free fixed positions secret selection sample hselection]
      _ = mixedStepFourBasePositionDftScalar free positions sample *
          ∑ selection ∈ mixedStepFourSelectionFibre n free fixed sample measured
              groupSummary labelValue,
            mixedProductSecretPhase free secret selection sample *
              (walsh (boolMaskEquiv I selection) output : Complex) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro selection _
        ring
  unfold mixedStepFourProjectedHadamardFibreAmplitude
    mixedStepFourUnnormalizedCommonScalar mixedStepFourFibreWalshAmplitude
  rw [hsum]
  ring

end ConcreteFibre

section ConditionalBornMass

variable {I J S : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq S]
variable {n : Nat}

/-- Sum of concrete squared fibre amplitudes over all occupied complete
Step-4 labels at one Boolean-Hadamard output. -/
def mixedStepFourSquaredAmplitude
    (n : Nat) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) : Real :=
  ∑ labelValue ∈ occupiedLabels
      (mixedStepTwoMaskSupport n free fixed sample measured)
      (paperStepFourLabel (fullSumHighBit n sample) groupSummary),
    Complex.normSq
      (mixedStepFourFibreWalshAmplitude n secret free fixed sample measured
        groupSummary labelValue output)

/-- Raw squared mass of one Step-4 output, summed over its orthogonal occupied
complete-label fibres.  This retains the exact unnormalized projected
amplitudes and therefore still contains the common position/DFT/Hadamard
scalar. -/
def mixedStepFourRawOutputMass
    (n : Nat) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) : Real :=
  ∑ labelValue ∈ occupiedLabels
      (mixedStepTwoMaskSupport n free fixed sample measured)
      (paperStepFourLabel (fullSumHighBit n sample) groupSummary),
    Complex.normSq
      (mixedStepFourProjectedHadamardFibreAmplitude n positions secret free
        fixed sample measured groupSummary labelValue output)

/-- Total raw projected Step-4 mass over every Boolean-Hadamard output. -/
def mixedStepFourRawTotalMass
    (n : Nat) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) : Real :=
  ∑ output : Mask I,
    mixedStepFourRawOutputMass n positions secret free fixed sample measured
      groupSummary output

/-- The raw output mass factors into the squared norm of the common projected
scalar and the reduced mixed-state squared amplitude. -/
theorem mixedStepFourRawOutputMass_eq_common_normSq_mul
    (n : Nat) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) :
    mixedStepFourRawOutputMass n positions secret free fixed sample measured
        groupSummary output =
      Complex.normSq
          (mixedStepFourUnnormalizedCommonScalar free positions sample) *
        mixedStepFourSquaredAmplitude n secret free fixed sample measured
          groupSummary output := by
  unfold mixedStepFourRawOutputMass mixedStepFourSquaredAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro labelValue _
  rw [mixedStepFourProjectedHadamardFibreAmplitude_eq_common_mul,
    Complex.normSq_mul]

/-- The normalized pointwise output weight after the common projected
amplitude scalar and Step-2 postselection normalization have cancelled. -/
def mixedStepFourBornWeight
    (n : Nat) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) : Real :=
  mixedStepFourSquaredAmplitude n secret free fixed sample measured
      groupSummary output /
    (labelledBornDenominator
      (mixedStepTwoMaskSupport n free fixed sample measured) : Real)

/-- The concrete conditional all-zero Born mass.  The denominator is exact
after cancellation of the common projected amplitude scalar.  Nonempty
support is required only when interpreting this ratio as a conditional
probability. -/
def mixedStepFourZeroEventMass
    (A : Finset I) (n : Nat) (secret : Word n) (free : Finset I)
    (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) : Real :=
  (∑ output : MasksVanishingOn A,
      mixedStepFourSquaredAmplitude n secret free fixed sample measured
        groupSummary output) /
    (labelledBornDenominator
      (mixedStepTwoMaskSupport n free fixed sample measured) : Real)

/-- Pointwise, the concrete squared-amplitude numerator is the phased
paper-label numerator. -/
theorem mixedStepFourSquaredAmplitude_eq_paperPhased
    (hn : 0 < n) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) :
    mixedStepFourSquaredAmplitude n secret free fixed sample measured
        groupSummary output =
      phasedLabelledSquaredAmplitude
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        (paperLabelPhase
          (actualAdjustedResiduePhase n secret free fixed sample measured)
          (lastBitBool secret.val)) output := by
  unfold mixedStepFourSquaredAmplitude phasedLabelledSquaredAmplitude
  apply Finset.sum_congr rfl
  intro labelValue _
  rw [mixedStepFourFibreWalshAmplitude_eq_paperPhased hn]

/-- The concrete pointwise output weight is exactly the phased paper-label
Born weight. -/
theorem mixedStepFourBornWeight_eq_paperPhased
    (hn : 0 < n) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) :
    mixedStepFourBornWeight n secret free fixed sample measured groupSummary
        output =
      phasedLabelledBornWeight
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        (paperLabelPhase
          (actualAdjustedResiduePhase n secret free fixed sample measured)
          (lastBitBool secret.val)) output := by
  unfold mixedStepFourBornWeight phasedLabelledBornWeight
  rw [mixedStepFourSquaredAmplitude_eq_paperPhased hn]

/-- Distribution-level bridge: the actual fixed-environment pointwise Born
weight is the real cast of the existing rational labelled Walsh weight. -/
theorem mixedStepFourBornWeight_eq_labelled
    (hn : 0 < n) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) (output : Mask I) :
    mixedStepFourBornWeight n secret free fixed sample measured groupSummary
        output =
      (labelledBornWeight
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        output : Real) := by
  rw [mixedStepFourBornWeight_eq_paperPhased hn]
  exact phasedLabelledBornWeight_paperStepFour_eq
    (mixedStepTwoMaskSupport n free fixed sample measured)
    (fullSumHighBit n sample) groupSummary
    (actualAdjustedResiduePhase n secret free fixed sample measured)
    (lastBitBool secret.val) output
    (normSq_actualAdjustedResiduePhase secret measured
      (fixedFaultyContribution free fixed sample))

/-- For a nonempty measured support, the reduced squared amplitudes sum to
the exact labelled Born denominator. -/
theorem sum_mixedStepFourSquaredAmplitude_eq_denominator
    (hn : 0 < n) (secret : Word n) (free : Finset I) (fixed : I -> Bool)
    (sample : I -> Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty) :
    (∑ output : Mask I,
      mixedStepFourSquaredAmplitude n secret free fixed sample measured
        groupSummary output) =
      (labelledBornDenominator
        (mixedStepTwoMaskSupport n free fixed sample measured) : Real) := by
  let support := mixedStepTwoMaskSupport n free fixed sample measured
  let label := paperStepFourLabel (fullSumHighBit n sample) groupSummary
  have hmaskSupport : support.Nonempty := by
    unfold support mixedStepTwoMaskSupport
    exact hsupport.image (boolMaskEquiv I)
  have hdenominatorRat : labelledBornDenominator support ≠ 0 := by
    unfold labelledBornDenominator
    apply mul_ne_zero
    · positivity
    · exact_mod_cast Finset.card_ne_zero.mpr hmaskSupport
  have hdenominatorReal :
      (labelledBornDenominator support : Real) ≠ 0 := by
    exact_mod_cast hdenominatorRat
  have hlabelledSum :
      (∑ output : Mask I, labelledBornWeight support label output) = 1 :=
    sum_labelledBornWeight_eq_one support label hmaskSupport
  have hmixedWeightSum :
      (∑ output : Mask I,
        mixedStepFourBornWeight n secret free fixed sample measured
          groupSummary output) = 1 := by
    calc
      (∑ output : Mask I,
        mixedStepFourBornWeight n secret free fixed sample measured
          groupSummary output) =
          ∑ output : Mask I,
            (labelledBornWeight support label output : Real) := by
        apply Finset.sum_congr rfl
        intro output _
        simpa [support, label] using
          mixedStepFourBornWeight_eq_labelled hn secret free fixed sample
            measured groupSummary output
      _ = 1 := by exact_mod_cast hlabelledSum
  unfold mixedStepFourBornWeight at hmixedWeightSum
  rw [← Finset.sum_div] at hmixedWeightSum
  have hsum := (div_eq_one_iff_eq hdenominatorReal).mp hmixedWeightSum
  simpa [support] using hsum

/-- For a nonempty measured support, the total raw projected mass is the
squared common scalar times the exact labelled Born denominator. -/
theorem mixedStepFourRawTotalMass_eq_common_normSq_mul_denominator
    (hn : 0 < n) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty) :
    mixedStepFourRawTotalMass n positions secret free fixed sample measured
        groupSummary =
      Complex.normSq
          (mixedStepFourUnnormalizedCommonScalar free positions sample) *
        (labelledBornDenominator
          (mixedStepTwoMaskSupport n free fixed sample measured) : Real) := by
  unfold mixedStepFourRawTotalMass
  simp_rw [mixedStepFourRawOutputMass_eq_common_normSq_mul]
  rw [← Finset.mul_sum,
    sum_mixedStepFourSquaredAmplitude_eq_denominator hn secret free fixed
      sample measured groupSummary hsupport]

/-- Exact normalization theorem: dividing one raw projected output mass by
the total raw projected mass gives the reduced conditional Step-4 Born
weight. -/
theorem mixedStepFourRawOutputMass_div_total_eq_bornWeight
    (hn : 0 < n) (positions : I -> Word n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty)
    (output : Mask I) :
    mixedStepFourRawOutputMass n positions secret free fixed sample measured
          groupSummary output /
        mixedStepFourRawTotalMass n positions secret free fixed sample measured
          groupSummary =
      mixedStepFourBornWeight n secret free fixed sample measured groupSummary
        output := by
  rw [mixedStepFourRawOutputMass_eq_common_normSq_mul,
    mixedStepFourRawTotalMass_eq_common_normSq_mul_denominator hn positions
      secret free fixed sample measured groupSummary hsupport]
  unfold mixedStepFourBornWeight
  have hcommon :
      Complex.normSq
          (mixedStepFourUnnormalizedCommonScalar free positions sample) ≠ 0 :=
    (Complex.normSq_pos.mpr
      (mixedStepFourUnnormalizedCommonScalar_ne_zero
        free positions sample)).ne'
  have hmaskSupport :
      (mixedStepTwoMaskSupport n free fixed sample measured).Nonempty := by
    unfold mixedStepTwoMaskSupport
    exact hsupport.image (boolMaskEquiv I)
  have hdenominatorRat :
      labelledBornDenominator
          (mixedStepTwoMaskSupport n free fixed sample measured) ≠ 0 := by
    unfold labelledBornDenominator
    apply mul_ne_zero
    · positivity
    · exact_mod_cast Finset.card_ne_zero.mpr hmaskSupport
  have hdenominatorReal :
      (labelledBornDenominator
        (mixedStepTwoMaskSupport n free fixed sample measured) : Real) ≠ 0 := by
    exact_mod_cast hdenominatorRat
  field_simp [hcommon, hdenominatorReal]

/-- The concrete conditional event mass is exactly the phased paper-label
event mass. -/
theorem mixedStepFourZeroEventMass_eq_paperPhased
    (A : Finset I) (hn : 0 < n) (secret : Word n) (free : Finset I)
    (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) :
    mixedStepFourZeroEventMass A n secret free fixed sample measured
        groupSummary =
      phasedLabelledZeroEventMass A
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
        (paperLabelPhase
          (actualAdjustedResiduePhase n secret free fixed sample measured)
          (lastBitBool secret.val)) := by
  unfold mixedStepFourZeroEventMass phasedLabelledZeroEventMass
  simp_rw [mixedStepFourSquaredAmplitude_eq_paperPhased hn]

/-- After the concrete unit phase cancels, the actual conditional mass is
the existing unit-coefficient labelled Walsh mass. -/
theorem mixedStepFourZeroEventMass_eq_labelled
    (A : Finset I) (hn : 0 < n) (secret : Word n) (free : Finset I)
    (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S) :
    mixedStepFourZeroEventMass A n secret free fixed sample measured
        groupSummary =
      (labelledZeroEventMass A
        (mixedStepTwoMaskSupport n free fixed sample measured)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary) : Real) := by
  rw [mixedStepFourZeroEventMass_eq_paperPhased A hn]
  apply phasedLabelledZeroEventMass_eq
  intro labelValue _
  exact normSq_paperLabelPhase
    (actualAdjustedResiduePhase n secret free fixed sample measured)
    (lastBitBool secret.val) labelValue
    (normSq_actualAdjustedResiduePhase secret measured
      (fixedFaultyContribution free fixed sample))

/-- Under local injectivity, one coordinate group is all zero with its exact
uniform conditional Born mass. -/
theorem mixedStepFourZeroEventMass_coordinateGroup_eq
    (A : Finset I) (hn : 0 < n) (secret : Word n) (free : Finset I)
    (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ A)
        (fun i => lowBitsHom n (sample i))) :
    mixedStepFourZeroEventMass A n secret free fixed sample measured
        groupSummary =
      (1 / 2 : Real) ^ A.card := by
  rw [mixedStepFourZeroEventMass_eq_labelled A hn]
  unfold mixedStepTwoMaskSupport
  rw [labelledZeroEventMass_stepTwoMeasuredFibre_eq n free A fixed sample
    measured (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
    hsupport hinjective]
  push_cast
  rfl

/-- Under injectivity on a disjoint union, the joint all-zero mass of two
coordinate groups is the product of their exact uniform masses. -/
theorem mixedStepFourZeroEventMass_disjoint_union_eq_mul
    (left right : Finset I) (hn : 0 < n) (secret : Word n)
    (free : Finset I) (fixed : I -> Bool) (sample : I -> Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I -> J -> S)
    (hsupport :
      (boolStepTwoMeasuredFibre n free fixed sample measured).Nonempty)
    (hdisjoint : Disjoint left right)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ (left ∪ right))
        (fun i => lowBitsHom n (sample i))) :
    mixedStepFourZeroEventMass (left ∪ right) n secret free fixed sample
        measured groupSummary =
      (1 / 2 : Real) ^ left.card * (1 / 2 : Real) ^ right.card := by
  rw [mixedStepFourZeroEventMass_eq_labelled (left ∪ right) hn]
  rw [mixedStepTwoMaskSupport_eq_maskCoordinateSubcubeResidueFibre]
  have hmaskSupport :
      (maskCoordinateSubcubeResidueFibre free (boolMaskEquiv I fixed)
        (fun i => lowBitsHom n (sample i)) measured).Nonempty := by
    rw [← image_boolStepTwoMeasuredFibre_eq_maskCoordinateSubcubeResidueFibre]
    exact hsupport.image (boolMaskEquiv I)
  rw [labelledZeroEventMass_disjoint_union_eq_mul free left right
    (boolMaskEquiv I fixed) (fun i => lowBitsHom n (sample i)) measured
    (paperStepFourLabel (fullSumHighBit n sample) groupSummary)
    hmaskSupport hdisjoint hinjective]
  push_cast
  rfl

end ConditionalBornMass

end

end SimonDCP.Probability.ActualStepFourBorn
