import Mathlib.Tactic
import SimonDCP.Arithmetic.TranslationFiber
import SimonDCP.Probability.StepTwoMeasurementBridge
import SimonDCP.Probability.StepFourLabelPhaseBridge
import SimonDCP.Quantum.Step2Phase
import SimonDCP.Quantum.MixedFaultPatternFourierProduct

/-!
# Fixed faulty offsets and the Step-2 high-bit carry

For a fixed fault environment, the secret-dependent exponent in the actual
mixed state is the subset sum over the coherent (correct) coordinates.  The
classical value used by Step 2 is the full subset sum, including the fixed
faulty coordinates.  Thus the two exponents differ by one fixed offset.

This file makes the remaining binary arithmetic exact for modulus `2 ^ n`.
After the low `n - 1` bits of the full sum have been measured, subtraction of
the faulty offset has a canonical base word.  Its high bit is the borrow/carry
bit.  Crucially, that bit depends only on the measured residue and the fixed
fault environment.  The only selection-dependent high bit is still the high
bit `h` of the full sum retained by the paper's Step-4 label.

Consequently, the actual secret character is a unit phase depending on the
measured residue and fault environment, multiplied by the paper-style phase
`(-1)^(h * d_n)`.  No extra carry bit is required in the Step-4 label after
conditioning on the Step-2 residue.  If the residue is not part of the
conditioning data, the carry (or an equivalent residue identifier) must be
retained as additional orthogonal label data.
-/

namespace SimonDCP.Probability.FaultyHighBitCarry

open scoped BigOperators

open SimonDCP.Arithmetic.TranslationFiber
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.FaultySamplePhase
open SimonDCP.Probability.BooleanMaskBridge
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.StepFourLabelPhaseBridge
open SimonDCP.Quantum.FaultyBasisSample
open SimonDCP.Quantum.MixedFaultPatternFourierProduct
open SimonDCP.Quantum.Step2Phase

abbrev Word (n : Nat) := ZMod (2 ^ n)

/-- The measured low `(n - 1)`-bit residue.  This is definitionally the same
cast used by `StepTwoMeasurementBridge.lowBitsHom`. -/
def lowResidue (n : Nat) (z : Word n) : ZMod (2 ^ (n - 1)) :=
  ZMod.cast z

/-- `lowResidue` is the pointwise form of the Step-2 quotient homomorphism. -/
@[simp]
theorem lowResidue_eq_lowBitsHom (n : Nat) (z : Word n) :
    lowResidue n z = lowBitsHom n z :=
  rfl

/-- Canonically lift an `(n - 1)`-bit residue to the lower half of an
`n`-bit word. -/
def liftLow (n : Nat) (residue : ZMod (2 ^ (n - 1))) : Word n :=
  (residue.val : Word n)

/-- The natural high-bit coefficient of an `n`-bit word. -/
def highBitNat (n : Nat) (z : Word n) : Nat :=
  z.val / 2 ^ (n - 1)

/-- The high-bit coefficient encoded as the Boolean used in Step 4. -/
def highBit (n : Nat) (z : Word n) : Bool :=
  decide (highBitNat n z = 1)

@[simp]
theorem lowResidue_val (n : Nat) (z : Word n) :
    (lowResidue n z).val = z.val % 2 ^ (n - 1) := by
  rw [lowResidue, ZMod.cast_eq_val, ZMod.val_natCast]

/-- An `n`-bit word has a high-bit coefficient strictly below two. -/
theorem highBitNat_lt_two {n : Nat} (hn : 0 < n) (z : Word n) :
    highBitNat n z < 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [highBitNat, Nat.succ_sub_one]
  rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)]
  simpa [pow_succ, Nat.mul_comm] using z.val_lt

/-- Hence the natural high-bit coefficient is exactly zero or one. -/
theorem highBitNat_eq_zero_or_one {n : Nat} (hn : 0 < n) (z : Word n) :
    highBitNat n z = 0 ∨ highBitNat n z = 1 := by
  have := highBitNat_lt_two hn z
  omega

/-- Boolean encoding does not change the high-bit coefficient. -/
@[simp]
theorem highBit_toNat {n : Nat} (hn : 0 < n) (z : Word n) :
    (highBit n z).toNat = highBitNat n z := by
  rcases highBitNat_eq_zero_or_one hn z with hzero | hone
  · simp [highBit, hzero]
  · simp [highBit, hone]

/-- The canonical natural representative splits into its low residue and its
Boolean high bit. -/
theorem val_eq_low_add_high {n : Nat} (hn : 0 < n) (z : Word n) :
    z.val = (lowResidue n z).val +
      (highBit n z).toNat * 2 ^ (n - 1) := by
  rw [lowResidue_val, highBit_toNat hn]
  simpa [highBitNat, Nat.mul_comm] using
    (Nat.mod_add_div z.val (2 ^ (n - 1))).symm

/-- Lifting a measured low residue and then reducing it recovers that
residue. -/
@[simp]
theorem lowResidue_liftLow (n : Nat) (residue : ZMod (2 ^ (n - 1))) :
    lowResidue n (liftLow n residue) = residue := by
  cases n with
  | zero => simp [lowResidue, liftLow]
  | succ k =>
    have hltLow : residue.val < 2 ^ k := by
      simpa using residue.val_lt
    have hlt : residue.val < 2 ^ (k + 1) := by
      calc
        residue.val < 2 ^ k := hltLow
        _ ≤ 2 ^ (k + 1) := by
          simp only [pow_succ]
          omega
    apply ZMod.val_injective
    rw [lowResidue_val]
    change (residue.val : ZMod (2 ^ (k + 1))).val % 2 ^ k = residue.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hltLow]

/-- Every nonempty binary word is its canonical low lift plus either zero or
the high-bit element. -/
theorem word_eq_liftLow_add_bitValue {n : Nat} (hn : 0 < n) (z : Word n) :
    z = liftLow n (lowResidue n z) + bitValue n (highBit n z) := by
  have hval := val_eq_low_add_high hn z
  calc
    z = (z.val : Word n) := (ZMod.natCast_zmod_val z).symm
    _ = ((lowResidue n z).val +
          (highBit n z).toNat * 2 ^ (n - 1) : Nat) := by
      exact congrArg (fun value : Nat => (value : Word n)) hval
    _ = liftLow n (lowResidue n z) + bitValue n (highBit n z) := by
      cases highBit n z <;> simp [liftLow, bitValue, halfTurn]

/-- Adding two high-bit values combines their bits by XOR. -/
theorem bitValue_add_bitValue {n : Nat} (hn : 0 < n) (left right : Bool) :
    bitValue n left + bitValue n right = bitValue n (left.xor right) := by
  cases left <;> cases right <;> simp [bitValue, halfTurn_add_self hn]

/-- The high-bit encoding is injective for positive word width. -/
theorem bitValue_injective {n : Nat} (hn : 0 < n) :
    Function.Injective (bitValue n) := by
  intro left right heq
  cases left <;> cases right
  · rfl
  · exact False.elim ((halfTurn_ne_zero hn) heq.symm)
  · exact False.elim ((halfTurn_ne_zero hn) heq)
  · rfl

/-- A high-bit value vanishes under the Step-2 low-bits quotient. -/
@[simp]
theorem lowResidue_bitValue {n : Nat} (hn : 0 < n) (bit : Bool) :
    lowResidue n (bitValue n bit) = 0 := by
  cases bit
  · simp [lowResidue, bitValue]
  · obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    change ZMod.cast ((2 ^ k : Nat) : ZMod (2 ^ (k + 1))) = 0
    rw [ZMod.cast_natCast (pow_dvd_pow 2 (Nat.le_succ k))]
    exact ZMod.natCast_self (2 ^ k)

/-- Adding a Boolean high bit does not change the low residue. -/
@[simp]
theorem lowResidue_liftLow_add_bitValue {n : Nat} (hn : 0 < n)
    (residue : ZMod (2 ^ (n - 1))) (bit : Bool) :
    lowResidue n (liftLow n residue + bitValue n bit) = residue := by
  rw [lowResidue_eq_lowBitsHom, map_add]
  rw [← lowResidue_eq_lowBitsHom, lowResidue_liftLow]
  rw [← lowResidue_eq_lowBitsHom, lowResidue_bitValue hn, add_zero]

/-- The explicit low/high decomposition has the stated Boolean high bit. -/
@[simp]
theorem highBit_liftLow_add_bitValue {n : Nat} (hn : 0 < n)
    (residue : ZMod (2 ^ (n - 1))) (bit : Bool) :
    highBit n (liftLow n residue + bitValue n bit) = bit := by
  have hdecomposition := word_eq_liftLow_add_bitValue hn
    (liftLow n residue + bitValue n bit)
  rw [lowResidue_liftLow_add_bitValue hn] at hdecomposition
  have hbits : bitValue n bit =
      bitValue n (highBit n (liftLow n residue + bitValue n bit)) := by
    exact add_left_cancel hdecomposition
  exact (bitValue_injective hn hbits).symm

/-- The canonical word obtained after subtracting the fixed faulty offset
from the canonical lift of a measured residue. -/
def adjustedResidueBase (n : Nat) (residue : ZMod (2 ^ (n - 1)))
    (faultyOffset : Word n) : Word n :=
  liftLow n residue - faultyOffset

/-- The borrow/carry bit introduced by subtracting a fixed faulty offset from
the canonical lift of the measured residue. -/
def residueCarryBit (n : Nat) (residue : ZMod (2 ^ (n - 1)))
    (faultyOffset : Word n) : Bool :=
  highBit n (adjustedResidueBase n residue faultyOffset)

/-- The low part of the adjusted base is affine translation by the low part
of the fixed faulty offset. -/
theorem lowResidue_adjustedResidueBase (n : Nat)
    (residue : ZMod (2 ^ (n - 1))) (faultyOffset : Word n) :
    lowResidue n (adjustedResidueBase n residue faultyOffset) =
      residue - lowResidue n faultyOffset := by
  change ZMod.cast (liftLow n residue - faultyOffset) =
    residue - ZMod.cast faultyOffset
  rw [ZMod.cast_sub (pow_dvd_pow 2 (Nat.sub_le n 1))]
  change lowResidue n (liftLow n residue) - lowResidue n faultyOffset =
    residue - lowResidue n faultyOffset
  rw [lowResidue_liftLow]

/-- On a fixed Step-2 residue fibre, subtracting the faulty offset is an
affine base translation followed by the unchanged full-sum high bit. -/
theorem sub_eq_adjustedResidueBase_add_highBit {n : Nat} (hn : 0 < n)
    (z faultyOffset : Word n) :
    z - faultyOffset =
      adjustedResidueBase n (lowResidue n z) faultyOffset +
        bitValue n (highBit n z) := by
  calc
    z - faultyOffset =
        (liftLow n (lowResidue n z) + bitValue n (highBit n z)) -
          faultyOffset := by
      exact congrArg (fun word : Word n => word - faultyOffset)
        (word_eq_liftLow_add_bitValue hn z)
    _ = adjustedResidueBase n (lowResidue n z) faultyOffset +
          bitValue n (highBit n z) := by
      simp only [adjustedResidueBase]
      abel

/-- Expanded carry decomposition.  The high bit of the free exponent is the
XOR of the full-sum high bit and a carry fixed by the measured residue and
fault environment. -/
theorem sub_eq_liftLow_add_carry_xor_highBit {n : Nat} (hn : 0 < n)
    (z faultyOffset : Word n) :
    z - faultyOffset =
      liftLow n (lowResidue n z - lowResidue n faultyOffset) +
        bitValue n
          ((residueCarryBit n (lowResidue n z) faultyOffset).xor
            (highBit n z)) := by
  rw [sub_eq_adjustedResidueBase_add_highBit hn]
  rw [word_eq_liftLow_add_bitValue hn
    (adjustedResidueBase n (lowResidue n z) faultyOffset)]
  rw [lowResidue_adjustedResidueBase]
  simp only [residueCarryBit]
  rw [add_assoc, bitValue_add_bitValue hn]

/-- The high bit of the free exponent is exactly the fixed residue carry XOR
the high bit of the full Step-2 sum. -/
theorem highBit_sub_eq_residueCarryBit_xor_highBit {n : Nat} (hn : 0 < n)
    (z faultyOffset : Word n) :
    highBit n (z - faultyOffset) =
      (residueCarryBit n (lowResidue n z) faultyOffset).xor
        (highBit n z) := by
  calc
    highBit n (z - faultyOffset) =
        highBit n
          (liftLow n (lowResidue n z - lowResidue n faultyOffset) +
            bitValue n
              ((residueCarryBit n (lowResidue n z) faultyOffset).xor
                (highBit n z))) :=
      congrArg (highBit n)
        (sub_eq_liftLow_add_carry_xor_highBit hn z faultyOffset)
    _ = (residueCarryBit n (lowResidue n z) faultyOffset).xor
          (highBit n z) := highBit_liftLow_add_bitValue hn _ _

/-! ## Character factorization on a measured residue fibre -/

/-- The phase common to a fixed Step-2 residue after removing the fixed
faulty-coordinate contribution. -/
def adjustedResiduePhase (n : Nat) (character : AddChar (Word n) ℂ)
    (residue : ZMod (2 ^ (n - 1)))
    (faultyOffset : Word n) : ℂ :=
  character (adjustedResidueBase n residue faultyOffset)

/-- A unitary character gives a unit adjusted-residue phase. -/
theorem normSq_adjustedResiduePhase
    (n : Nat) (character : AddChar (Word n) ℂ)
    (residue : ZMod (2 ^ (n - 1))) (faultyOffset : Word n)
    (hunit : ∀ exponent, Complex.normSq (character exponent) = 1) :
    Complex.normSq
        (adjustedResiduePhase n character residue faultyOffset) = 1 := by
  exact hunit (adjustedResidueBase n residue faultyOffset)

/-- It suffices to identify the character at the high-bit element in order
to identify its value at either Boolean high-bit choice. -/
theorem character_bitValue_eq_highBitSecretPhase
    (n : Nat) (character : AddChar (Word n) ℂ) (secretBit bit : Bool)
    (hhalf : character (halfTurn n) =
      highBitSecretPhase secretBit true) :
    character (bitValue n bit) = highBitSecretPhase secretBit bit := by
  cases bit
  · simp [bitValue, highBitSecretPhase]
  · simpa [bitValue] using hhalf

/-- Exact phase factorization after subtraction of the fixed faulty offset.
The first factor is constant on the measured low-residue fibre; the second is
exactly the paper-style high-bit/secret-bit sign. -/
theorem character_sub_eq_adjustedResiduePhase_mul_highBitSecretPhase
    {n : Nat} (hn : 0 < n) (character : AddChar (Word n) ℂ)
    (secretBit : Bool) (z faultyOffset : Word n)
    (hhalf : character (halfTurn n) =
      highBitSecretPhase secretBit true) :
    character (z - faultyOffset) =
      adjustedResiduePhase n character (lowResidue n z) faultyOffset *
        highBitSecretPhase secretBit (highBit n z) := by
  rw [sub_eq_adjustedResidueBase_add_highBit hn]
  rw [character.map_add_eq_mul]
  exact congrArg
    (fun phase : ℂ =>
      adjustedResiduePhase n character (lowResidue n z) faultyOffset * phase)
    (character_bitValue_eq_highBitSecretPhase
      n character secretBit (highBit n z) hhalf)

/-- The high bit of the complete subset sum, expressed on the mask encoding
used by Step 4. -/
def fullSumHighBit {I : Type*} [Fintype I]
    (n : Nat) (sample : I → Word n) (selection : Mask I) : Bool :=
  highBit n (booleanSubsetSum sample selection)

/-- Complete orthogonal label when Step-2 residues are not handled by outer
conditioning.  The residue, not a separate carry bit, is the extra datum
needed to make the common phase a function of the label. -/
abbrev ResidueStepFourLabel (n : Nat) (J S : Type*) :=
  ZMod (2 ^ (n - 1)) × StepFourLabel J S

/-- Package the measured Step-2 residue with the paper's Step-4 label. -/
def residueStepFourLabel {I J S : Type*} [Fintype I]
    (n : Nat) (sample : I → Word n) (groupSummary : Mask I → J → S)
    (selection : Mask I) : ResidueStepFourLabel n J S :=
  (lowResidue n (booleanSubsetSum sample selection),
    paperStepFourLabel (fullSumHighBit n sample) groupSummary selection)

/-- For a supported Boolean selection, the actual coherent secret exponent
is the full Step-2 subset sum minus the fixed faulty contribution. -/
theorem freeSelectedSum_eq_fullSubsetSum_sub_faultyOffset
    {I : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} {free : Finset I} {fixed selection : I → Bool}
    (sample : I → Word n)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    freeSelectedSum free selection sample =
      fullSubsetSum selection sample -
        fixedFaultyContribution free fixed sample :=
  freeSelectedSum_eq_full_sub_fixed sample hselection

/-- Exact selection-level bridge from the actual coherent exponent to the
paper's complete Step-4 label.  The measured residue fixes the global phase,
while the label retains the full-sum high bit. -/
theorem character_freeSelectedSum_eq_paperLabelPhase
    {I J S : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 0 < n) (character : AddChar (Word n) ℂ)
    (secretBit : Bool) (free : Finset I) (fixed : I → Bool)
    (sample : I → Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I → J → S) (selection : I → Bool)
    (hselection : selection ∈ coordinateSubcube free fixed)
    (hmeasured : lowResidue n (fullSubsetSum selection sample) = measured)
    (hhalf : character (halfTurn n) =
      highBitSecretPhase secretBit true) :
    character (freeSelectedSum free selection sample) =
      paperLabelPhase
        (adjustedResiduePhase n character measured
          (fixedFaultyContribution free fixed sample))
        secretBit
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary
          (boolMaskEquiv I selection)) := by
  rw [freeSelectedSum_eq_full_sub_fixed sample hselection]
  rw [character_sub_eq_adjustedResiduePhase_mul_highBitSecretPhase
    hn character secretBit]
  · rw [hmeasured]
    unfold paperLabelPhase paperStepFourLabel fullSumHighBit
    rw [← fullSubsetSum_eq_booleanSubsetSum sample selection]
  · exact hhalf

/-- Therefore two supported selections in the same measured-residue and
complete Step-4-label fibre have exactly the same actual secret phase. -/
theorem character_freeSelectedSum_eq_of_same_residue_and_stepFourLabel
    {I J S : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 0 < n) (character : AddChar (Word n) ℂ)
    (secretBit : Bool) (free : Finset I) (fixed : I → Bool)
    (sample : I → Word n) (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I → J → S) (left right : I → Bool)
    (hleft : left ∈ coordinateSubcube free fixed)
    (hright : right ∈ coordinateSubcube free fixed)
    (hleftMeasured : lowResidue n (fullSubsetSum left sample) = measured)
    (hrightMeasured : lowResidue n (fullSubsetSum right sample) = measured)
    (hlabel :
      paperStepFourLabel (fullSumHighBit n sample) groupSummary
          (boolMaskEquiv I left) =
        paperStepFourLabel (fullSumHighBit n sample) groupSummary
          (boolMaskEquiv I right))
    (hhalf : character (halfTurn n) =
      highBitSecretPhase secretBit true) :
    character (freeSelectedSum free left sample) =
      character (freeSelectedSum free right sample) := by
  rw [character_freeSelectedSum_eq_paperLabelPhase hn character secretBit
    free fixed sample measured groupSummary left hleft hleftMeasured hhalf]
  rw [character_freeSelectedSum_eq_paperLabelPhase hn character secretBit
    free fixed sample measured groupSummary right hright hrightMeasured hhalf]
  exact congrArg
    (paperLabelPhase
      (adjustedResiduePhase n character measured
        (fixedFaultyContribution free fixed sample)) secretBit)
    hlabel

/-- Equivalent unconditioned formulation: if branches with different Step-2
residues are compared together, equality of the residue-extended complete
label is sufficient for equality of the actual secret phase. -/
theorem character_freeSelectedSum_eq_of_same_residueStepFourLabel
    {I J S : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 0 < n) (character : AddChar (Word n) ℂ)
    (secretBit : Bool) (free : Finset I) (fixed : I → Bool)
    (sample : I → Word n) (groupSummary : Mask I → J → S)
    (left right : I → Bool)
    (hleft : left ∈ coordinateSubcube free fixed)
    (hright : right ∈ coordinateSubcube free fixed)
    (hlabel :
      residueStepFourLabel n sample groupSummary (boolMaskEquiv I left) =
        residueStepFourLabel n sample groupSummary (boolMaskEquiv I right))
    (hhalf : character (halfTurn n) =
      highBitSecretPhase secretBit true) :
    character (freeSelectedSum free left sample) =
      character (freeSelectedSum free right sample) := by
  have hresidue := congrArg Prod.fst hlabel
  have hstepFour := congrArg Prod.snd hlabel
  change lowResidue n (booleanSubsetSum sample (boolMaskEquiv I left)) =
    lowResidue n (booleanSubsetSum sample (boolMaskEquiv I right)) at hresidue
  rw [← fullSubsetSum_eq_booleanSubsetSum sample left,
    ← fullSubsetSum_eq_booleanSubsetSum sample right] at hresidue
  change paperStepFourLabel (fullSumHighBit n sample) groupSummary
      (boolMaskEquiv I left) =
    paperStepFourLabel (fullSumHighBit n sample) groupSummary
      (boolMaskEquiv I right) at hstepFour
  exact character_freeSelectedSum_eq_of_same_residue_and_stepFourLabel
    hn character secretBit free fixed sample
    (lowResidue n (fullSubsetSum left sample)) groupSummary left right
    hleft hright rfl hresidue.symm hstepFour hhalf

/-! ## Specialization to the actual post-position-DFT secret character -/

/-- Additive exponent map underlying `positionPhase secret`. -/
def positionSecretExponentHom {n : Nat} (secret : Word n) : Word n →+ Word n where
  toFun exponent := -(secret * exponent)
  map_zero' := by simp
  map_add' left right := by
    simp only [mul_add, neg_add_rev]
    abel

/-- The actual secret character contributed by the position DFT. -/
noncomputable def positionSecretCharacter {n : Nat} (secret : Word n) :
    AddChar (Word n) ℂ :=
  (ZMod.stdAddChar (N := 2 ^ n)).compAddMonoidHom
    (positionSecretExponentHom secret)

@[simp]
theorem positionSecretCharacter_apply {n : Nat} (secret exponent : Word n) :
    positionSecretCharacter secret exponent = positionPhase secret exponent :=
  rfl

/-- The actual position-DFT secret character is unitary. -/
theorem normSq_positionSecretCharacter {n : Nat} (secret exponent : Word n) :
    Complex.normSq (positionSecretCharacter secret exponent) = 1 := by
  rw [positionSecretCharacter_apply, Complex.normSq_eq_norm_sq,
    norm_positionPhase, one_pow]

/-- The standard character takes the high-bit element to `-1`.  This proof
uses only primitivity and the fact that the high-bit element has order two. -/
theorem stdAddChar_halfTurn {n : Nat} (hn : 0 < n) :
    (ZMod.stdAddChar (N := 2 ^ n)) (halfTurn n) = (-1 : ℂ) := by
  let character : AddChar (Word n) ℂ := ZMod.stdAddChar
  have hne : character (halfTurn n) ≠ 1 := by
    intro heq
    have hzero : character (halfTurn n) = character 0 := by
      simpa using heq
    exact halfTurn_ne_zero hn (ZMod.injective_stdAddChar hzero)
  have hsquare : character (halfTurn n) ^ 2 = 1 := by
    calc
      character (halfTurn n) ^ 2 = character (2 • halfTurn n) :=
        (character.map_nsmul_eq_pow 2 (halfTurn n)).symm
      _ = character (halfTurn n + halfTurn n) := by rw [two_nsmul]
      _ = character 0 := by rw [halfTurn_add_self hn]
      _ = 1 := character.map_zero_eq_one
  exact (sq_eq_one_iff.mp hsquare).resolve_left hne

/-- Multiplication by a word is repeated addition by its canonical
representative. -/
theorem mul_halfTurn_eq_val_nsmul {n : Nat} (secret : Word n) :
    secret * halfTurn n = secret.val • halfTurn n := by
  rw [← ZMod.natCast_zmod_val secret]
  simp [nsmul_eq_mul]

/-- Boolean form of `Step2Phase.lastBit`. -/
def lastBitBool (d : Nat) : Bool :=
  decide (lastBit d = 1)

@[simp]
theorem lastBitBool_toNat (d : Nat) :
    (lastBitBool d).toNat = lastBit d := by
  rcases lastBit_eq_zero_or_one d with hzero | hone
  · simp [lastBitBool, hzero]
  · simp [lastBitBool, hone]

/-- The paper's Boolean sign agrees with the natural-number sign used by
`Step2Phase`. -/
theorem highBitSecretPhase_lastBitBool_true (d : Nat) :
    highBitSecretPhase (lastBitBool d) true =
      (-1 : ℂ) ^ lastBit d := by
  rcases lastBit_eq_zero_or_one d with hzero | hone
  · simp [lastBitBool, highBitSecretPhase, hzero]
  · simp [lastBitBool, highBitSecretPhase, hone]

/-- Exact high-bit value of the actual position-DFT secret character. -/
theorem positionSecretCharacter_halfTurn {n : Nat} (hn : 0 < n)
    (secret : Word n) :
    positionSecretCharacter secret (halfTurn n) =
      highBitSecretPhase (lastBitBool secret.val) true := by
  rw [positionSecretCharacter_apply, positionPhase]
  rw [AddChar.map_neg_eq_inv]
  rw [mul_halfTurn_eq_val_nsmul]
  rw [AddChar.map_nsmul_eq_pow, stdAddChar_halfTurn hn]
  rw [← inv_pow, inv_neg, inv_one]
  rw [negOnePow_eq_lastBit]
  exact (highBitSecretPhase_lastBitBool_true secret.val).symm

/-- A character maps a finite additive sum to the corresponding product. -/
theorem character_finsetSum_eq_prod
    {I G M : Type*} [AddCommMonoid G] [CommMonoid M]
    (character : AddChar G M) (terms : I → G) (indices : Finset I) :
    character (∑ i ∈ indices, terms i) =
      ∏ i ∈ indices, character (terms i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex induction =>
    simp [hindex, character.map_add_eq_mul, induction]

/-- One local mixed-state phase is the actual secret character evaluated on
the selected free-coordinate term. -/
theorem mixedCoordinateSecretPhase_eq_positionSecretCharacter
    {I : Type*} [Fintype I] [DecidableEq I] {n : Nat}
    (free : Finset I) (secret : Word n) (selection : I → Bool)
    (sample : I → Word n) (i : I) :
    mixedCoordinateSecretPhase free secret selection sample i =
      positionSecretCharacter secret
        (if i ∈ free then boolSelectedTerm (selection i) (sample i) else 0) := by
  by_cases hi : i ∈ free
  · cases hselection : selection i <;>
      simp [mixedCoordinateSecretPhase, hi, hselection, boolSelectedTerm]
  · simp [mixedCoordinateSecretPhase, hi]

/-- The complete actual mixed-state secret phase is precisely the secret
character evaluated on `freeSelectedSum`; faulty coordinates contribute no
secret exponent. -/
theorem mixedProductSecretPhase_eq_positionSecretCharacter_freeSelectedSum
    {I : Type*} [Fintype I] [DecidableEq I] {n : Nat}
    (free : Finset I) (secret : Word n) (selection : I → Bool)
    (sample : I → Word n) :
    mixedProductSecretPhase free secret selection sample =
      positionSecretCharacter secret
        (freeSelectedSum free selection sample) := by
  classical
  rw [mixedProductSecretPhase, freeSelectedSum]
  rw [character_finsetSum_eq_prod
    (positionSecretCharacter secret)
    (fun i => if i ∈ free then
      boolSelectedTerm (selection i) (sample i) else 0) Finset.univ]
  apply Finset.prod_congr rfl
  intro i _
  exact mixedCoordinateSecretPhase_eq_positionSecretCharacter
    free secret selection sample i

/-- Fully concrete bridge for the actual mixed-state amplitude: on every
Step-2 residue and complete Step-4 label fibre, its secret phase is the
paper-style sign times a common unit phase. -/
theorem mixedProductSecretPhase_eq_paperLabelPhase
    {I J S : Type*} [Fintype I] [DecidableEq I]
    {n : Nat} (hn : 0 < n) (secret : Word n)
    (free : Finset I) (fixed : I → Bool) (sample : I → Word n)
    (measured : ZMod (2 ^ (n - 1)))
    (groupSummary : Mask I → J → S) (selection : I → Bool)
    (hselection : selection ∈ coordinateSubcube free fixed)
    (hmeasured : lowResidue n (fullSubsetSum selection sample) = measured) :
    mixedProductSecretPhase free secret selection sample =
      paperLabelPhase
        (adjustedResiduePhase n (positionSecretCharacter secret) measured
          (fixedFaultyContribution free fixed sample))
        (lastBitBool secret.val)
        (paperStepFourLabel (fullSumHighBit n sample) groupSummary
          (boolMaskEquiv I selection)) := by
  rw [mixedProductSecretPhase_eq_positionSecretCharacter_freeSelectedSum]
  exact character_freeSelectedSum_eq_paperLabelPhase hn
    (positionSecretCharacter secret) (lastBitBool secret.val)
    free fixed sample measured groupSummary selection hselection hmeasured
    (positionSecretCharacter_halfTurn hn secret)

/-- The concrete common phase in the previous theorem has unit squared
modulus, so it can be discharged directly by `StepFourLabelPhaseBridge`. -/
theorem normSq_actualAdjustedResiduePhase
    {n : Nat} (secret : Word n) (measured : ZMod (2 ^ (n - 1)))
    (faultyOffset : Word n) :
    Complex.normSq
      (adjustedResiduePhase n (positionSecretCharacter secret)
        measured faultyOffset) = 1 := by
  exact normSq_adjustedResiduePhase n (positionSecretCharacter secret)
    measured faultyOffset (normSq_positionSecretCharacter secret)

end SimonDCP.Probability.FaultyHighBitCarry
