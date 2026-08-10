import SimonDCP.Probability.BooleanMaskBridge
import SimonDCP.Probability.LabelledBornPairwiseTail

/-!
# Step-4 labels and common phases

After the Step-2 residue and the Fourier samples have been measured, the
paper's Step-4 basis label has the form

`(h, s₁, ..., s_g)`.

This file represents it exactly as `Bool × (J → S)`: `J` indexes the groups
and `S` is the type of one retained group summary.  The functions computing
`h` and the summaries are parameters.  Thus this module does not identify
them with the paper's high-bit arithmetic; it isolates the algebra that is
valid once that identification has been supplied.

The phase left before the Step-4 Hadamards is a measured global phase times
the sign depending on `h` and the last secret bit.  It is therefore constant
on every complete-label fibre.  The theorems below prove directly over
complex amplitudes that this common unit phase factors out and disappears
from `Complex.normSq`.  Consequently the phased Born weights, including the
one- and two-group all-zero masses, agree with the existing labelled Walsh
model.
-/

namespace SimonDCP.Probability.StepFourLabelPhaseBridge

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.FaultySamplePhase
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.LabelledBornProbability
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.CoordinateSubcubeBorn
open SimonDCP.Probability.LabelledBornPairwiseTail

/-- The complete classical label retained in Step 4. -/
abbrev StepFourLabel (J S : Type*) := Bool × (J → S)

/-- Assemble the paper-style label `(h, s₁, ..., s_g)` from its observables. -/
def paperStepFourLabel {I J S : Type*}
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (selection : Mask I) : StepFourLabel J S :=
  (highBit selection, groupSummary selection)

@[simp]
theorem paperStepFourLabel_highBit {I J S : Type*}
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (selection : Mask I) :
    (paperStepFourLabel highBit groupSummary selection).1 =
      highBit selection :=
  rfl

@[simp]
theorem paperStepFourLabel_groupSummary {I J S : Type*}
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (selection : Mask I) :
    (paperStepFourLabel highBit groupSummary selection).2 =
      groupSummary selection :=
  rfl

/-- The complex sign `(-1)^(h * d_n)`. -/
def highBitSecretPhase (secretBit highBit : Bool) : ℂ :=
  if highBit && secretBit then -1 else 1

@[simp]
theorem normSq_highBitSecretPhase (secretBit highBit : Bool) :
    Complex.normSq (highBitSecretPhase secretBit highBit) = 1 := by
  cases secretBit <;> cases highBit <;> simp [highBitSecretPhase]

/-- The complete phase which remains after fixing the measured environment. -/
def paperLabelPhase {J S : Type*}
    (globalPhase : ℂ) (secretBit : Bool) (label : StepFourLabel J S) : ℂ :=
  globalPhase * highBitSecretPhase secretBit label.1

/-- A unit global phase makes every complete-label phase unit-modulus. -/
theorem normSq_paperLabelPhase {J S : Type*}
    (globalPhase : ℂ) (secretBit : Bool) (label : StepFourLabel J S)
    (hglobal : Complex.normSq globalPhase = 1) :
    Complex.normSq (paperLabelPhase globalPhase secretBit label) = 1 := by
  rw [paperLabelPhase, Complex.normSq_mul, hglobal,
    normSq_highBitSecretPhase, one_mul]

/-- The paper phase is equal for terms with the same complete Step-4 label. -/
theorem paperLabelPhase_eq_of_stepFourLabel_eq {I J S : Type*}
    (globalPhase : ℂ) (secretBit : Bool)
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    {left right : Mask I}
    (hlabel : paperStepFourLabel highBit groupSummary left =
      paperStepFourLabel highBit groupSummary right) :
    paperLabelPhase globalPhase secretBit
        (paperStepFourLabel highBit groupSummary left) =
      paperLabelPhase globalPhase secretBit
        (paperStepFourLabel highBit groupSummary right) := by
  exact congrArg (paperLabelPhase globalPhase secretBit) hlabel

section FaultyGlobalPhase

variable {I G : Type*}
  [Fintype I] [DecidableEq I] [AddCommGroup G]

/-- The fixed faulty-coordinate contribution, viewed as a complex phase. -/
def faultyGlobalPhase (character : AddChar G ℂ)
    (free : Finset I) (fixed : I → Bool) (sample : I → G) : ℂ :=
  character (fixedFaultyContribution free fixed sample)

/-- A unitary additive character makes the faulty-coordinate phase unit. -/
theorem normSq_faultyGlobalPhase
    (character : AddChar G ℂ)
    (free : Finset I) (fixed : I → Bool) (sample : I → G)
    (hunit : ∀ exponent, Complex.normSq (character exponent) = 1) :
    Complex.normSq (faultyGlobalPhase character free fixed sample) = 1 := by
  exact hunit (fixedFaultyContribution free fixed sample)

/-- After Boolean-to-mask encoding, the faulty coordinates still contribute
one common right factor to every supported selection amplitude. -/
theorem character_booleanSubsetSum_eq_free_mul_faultyGlobal
    (character : AddChar G ℂ)
    {free : Finset I} {fixed selection : I → Bool} (sample : I → G)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    character (booleanSubsetSum sample (boolMaskEquiv I selection)) =
      character (freeSelectedSum free selection sample) *
        faultyGlobalPhase character free fixed sample := by
  rw [← fullSubsetSum_eq_booleanSubsetSum sample selection]
  exact character_fullSubsetSum_eq_free_mul_fixed
    character sample hselection

end FaultyGlobalPhase

section FibreAmplitude

variable {I Label : Type*} [Fintype I] [DecidableEq I] [DecidableEq Label]

/-- A complex Walsh amplitude with a phase attached term-by-term through its
complete classical label. -/
noncomputable def fibrePhaseAmplitude
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (labelValue : Label) (output : Mask I) : ℂ :=
  ∑ selection ∈ labelFibre support label labelValue,
    phase (label selection) * (walsh selection output : ℂ)

omit [DecidableEq I] in
/-- Inside one label fibre, a label-dependent phase is a common factor. -/
theorem fibrePhaseAmplitude_eq_common_mul
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (labelValue : Label) (output : Mask I) :
    fibrePhaseAmplitude support label phase labelValue output =
      phase labelValue *
        (signedAmplitude (labelFibre support label labelValue)
          (fun _ ↦ 1) output : ℂ) := by
  classical
  unfold fibrePhaseAmplitude
  calc
    (∑ selection ∈ labelFibre support label labelValue,
        phase (label selection) * (walsh selection output : ℂ)) =
        ∑ selection ∈ labelFibre support label labelValue,
          phase labelValue * (walsh selection output : ℂ) := by
      apply Finset.sum_congr rfl
      intro selection hselection
      have hlabel : label selection = labelValue :=
        (Finset.mem_filter.mp hselection).2
      rw [hlabel]
    _ = phase labelValue *
        ∑ selection ∈ labelFibre support label labelValue,
          (walsh selection output : ℂ) := by
      rw [Finset.mul_sum]
    _ = phase labelValue *
        (signedAmplitude (labelFibre support label labelValue)
          (fun _ ↦ 1) output : ℂ) := by
      congr 1
      simp [signedAmplitude]

omit [DecidableEq I] in
/-- A common unit phase does not change the squared norm of one fibre
amplitude. -/
theorem normSq_fibrePhaseAmplitude_eq_sq
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (labelValue : Label) (output : Mask I)
    (hphase : Complex.normSq (phase labelValue) = 1) :
    Complex.normSq
        (fibrePhaseAmplitude support label phase labelValue output) =
      ((signedAmplitude (labelFibre support label labelValue)
        (fun _ ↦ 1) output : ℤ) : ℝ) ^ 2 := by
  rw [fibrePhaseAmplitude_eq_common_mul, Complex.normSq_mul, hphase,
    one_mul, Complex.normSq_intCast]
  ring

/-- Sum the complex squared norms over all orthogonal complete labels. -/
noncomputable def phasedLabelledSquaredAmplitude
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (output : Mask I) : ℝ :=
  ∑ labelValue ∈ occupiedLabels support label,
    Complex.normSq
      (fibrePhaseAmplitude support label phase labelValue output)

omit [DecidableEq I] in
/-- Unit phases that are constant on complete-label fibres leave the complete
labelled Born numerator unchanged. -/
theorem phasedLabelledSquaredAmplitude_eq
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (output : Mask I)
    (hphase : ∀ labelValue ∈ occupiedLabels support label,
      Complex.normSq (phase labelValue) = 1) :
    phasedLabelledSquaredAmplitude support label phase output =
      (labelledSquaredAmplitude support label output : ℝ) := by
  unfold phasedLabelledSquaredAmplitude labelledSquaredAmplitude
  push_cast
  apply Finset.sum_congr rfl
  intro labelValue hlabelValue
  exact normSq_fibrePhaseAmplitude_eq_sq support label phase labelValue output
    (hphase labelValue hlabelValue)

/-- The phased version of the normalized complete-output Born weight. -/
noncomputable def phasedLabelledBornWeight
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (output : Mask I) : ℝ :=
  phasedLabelledSquaredAmplitude support label phase output /
    (labelledBornDenominator support : ℝ)

omit [DecidableEq I] in
/-- Pointwise Born weights are unchanged by common unit phases on label
fibres. -/
theorem phasedLabelledBornWeight_eq
    (support : Finset (Mask I)) (label : Mask I → Label)
    (phase : Label → ℂ) (output : Mask I)
    (hphase : ∀ labelValue ∈ occupiedLabels support label,
      Complex.normSq (phase labelValue) = 1) :
    phasedLabelledBornWeight support label phase output =
      (labelledBornWeight support label output : ℝ) := by
  rw [phasedLabelledBornWeight,
    phasedLabelledSquaredAmplitude_eq support label phase output hphase]
  unfold labelledBornWeight
  push_cast
  rfl

/-- The phased normalized mass of the event that every output coordinate in
`fixed` is zero. -/
noncomputable def phasedLabelledZeroEventMass
    (fixed : Finset I) (support : Finset (Mask I))
    (label : Mask I → Label) (phase : Label → ℂ) : ℝ :=
  (∑ output : MasksVanishingOn fixed,
      phasedLabelledSquaredAmplitude support label phase output) /
    (labelledBornDenominator support : ℝ)

omit [DecidableEq I] in
/-- Common unit phases do not change any labelled all-zero event mass. -/
theorem phasedLabelledZeroEventMass_eq
    (fixed : Finset I) (support : Finset (Mask I))
    (label : Mask I → Label) (phase : Label → ℂ)
    (hphase : ∀ labelValue ∈ occupiedLabels support label,
      Complex.normSq (phase labelValue) = 1) :
    phasedLabelledZeroEventMass fixed support label phase =
      (labelledZeroEventMass fixed support label : ℝ) := by
  unfold phasedLabelledZeroEventMass labelledZeroEventMass
  simp_rw [phasedLabelledSquaredAmplitude_eq support label phase _ hphase]
  push_cast
  rfl

end FibreAmplitude

section PaperSpecialization

variable {I J S G : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq S]
  [AddCommGroup G] [DecidableEq G]

omit [DecidableEq I] in
/-- The full Step-4 phase specialization has exactly the same pointwise Born
weight as the unit-coefficient labelled Walsh model. -/
theorem phasedLabelledBornWeight_paperStepFour_eq
    (support : Finset (Mask I))
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (globalPhase : ℂ) (secretBit : Bool) (output : Mask I)
    (hglobal : Complex.normSq globalPhase = 1) :
    phasedLabelledBornWeight support
        (paperStepFourLabel highBit groupSummary)
        (paperLabelPhase globalPhase secretBit) output =
      (labelledBornWeight support
        (paperStepFourLabel highBit groupSummary) output : ℝ) := by
  apply phasedLabelledBornWeight_eq
  intro labelValue hlabelValue
  exact normSq_paperLabelPhase globalPhase secretBit labelValue hglobal

/-- Under local subset-sum injectivity, the phased paper-style label model
has the exact uniform all-zero mass for one coordinate group. -/
theorem phasedLabelledZeroEventMass_paperStepFour_coordinateSubcube_eq
    (free fixedGroup : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (globalPhase : ℂ) (secretBit : Bool)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hinjective : SubsetSumInjectiveWithin (free ∩ fixedGroup) sample)
    (hglobal : Complex.normSq globalPhase = 1) :
    phasedLabelledZeroEventMass fixedGroup
        (maskCoordinateSubcubeResidueFibre free fixed sample residue)
        (paperStepFourLabel highBit groupSummary)
        (paperLabelPhase globalPhase secretBit) =
      (1 / 2 : ℝ) ^ fixedGroup.card := by
  rw [phasedLabelledZeroEventMass_eq]
  · rw [labelledZeroEventMass_maskCoordinateSubcubeResidueFibre_eq
      free fixedGroup fixed sample residue
        (paperStepFourLabel highBit groupSummary) hsupport hinjective]
    push_cast
    rfl
  · intro labelValue hlabelValue
    exact normSq_paperLabelPhase globalPhase secretBit labelValue hglobal

/-- The same phase cancellation preserves the exact two-group Born moment. -/
theorem phasedLabelledZeroEventMass_paperStepFour_disjoint_union_eq_mul
    (free left right : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (highBit : Mask I → Bool) (groupSummary : Mask I → J → S)
    (globalPhase : ℂ) (secretBit : Bool)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hdisjoint : Disjoint left right)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ (left ∪ right)) sample)
    (hglobal : Complex.normSq globalPhase = 1) :
    phasedLabelledZeroEventMass (left ∪ right)
        (maskCoordinateSubcubeResidueFibre free fixed sample residue)
        (paperStepFourLabel highBit groupSummary)
        (paperLabelPhase globalPhase secretBit) =
      (1 / 2 : ℝ) ^ left.card * (1 / 2 : ℝ) ^ right.card := by
  rw [phasedLabelledZeroEventMass_eq]
  · rw [labelledZeroEventMass_disjoint_union_eq_mul
      free left right fixed sample residue
        (paperStepFourLabel highBit groupSummary) hsupport hdisjoint hinjective]
    push_cast
    rfl
  · intro labelValue hlabelValue
    exact normSq_paperLabelPhase globalPhase secretBit labelValue hglobal

end PaperSpecialization

end SimonDCP.Probability.StepFourLabelPhaseBridge
