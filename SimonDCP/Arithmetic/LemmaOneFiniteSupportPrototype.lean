import SimonDCP.Arithmetic.SwapFiberRepair
import Mathlib.Data.Fintype.Perm

/-!
# A finite-support prototype for the next Lemma 1 repair

This file tests four API boundaries needed by a future repair:

* a measured record is fixed while the hidden zero/one selection ranges over a
  finite fibre;
* the complete Step-4 basis label contains both the high subset-sum bit `h` and
  the stored group summaries, while the Hadamard parity remains an amplitude
  sign;
* all coordinate permutations of the six-coordinate witness are enumerable;
* the API distinguishes equality of complete label partitions from the weaker
  one-way factorization condition needed to map occupied source labels.

The concrete exhaustive search below uses the one-way factorization condition:
a source coherent class may not be split.  The separate partition predicate is
available for arguments that must also forbid merging distinct source classes.
-/

namespace SimonDCP.Arithmetic.LemmaOneFiniteSupportPrototype

open SimonDCP.Arithmetic.SwapFiber
open SimonDCP.Arithmetic.SwapFiberRepair

/-! ## Finite hidden selections over one measured record -/

/-- A hidden selection is finite and bit-valued by construction. -/
abbrev HiddenSelection (Index : Type*) := Index → Bool

/-- The measured data retained after erasing the hidden selection. -/
structure MeasuredRecord (Index : Type*) where
  sample : Index → ℤ
  hadamardOutput : Index → Bool

/-- Reinsert a hidden selection into a measured record. -/
def stateOfSelection {Index : Type*} (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) : CoordinateState Index where
  selection i := if selection i then 1 else 0
  sample := outcome.sample
  hadamardOutput i := if outcome.hadamardOutput i then 1 else 0

/-- Transport a hidden selection along a coordinate permutation. -/
def permuteSelection {Index : Type*} (permutation : Equiv.Perm Index)
    (selection : HiddenSelection Index) : HiddenSelection Index :=
  fun i ↦ selection (permutation.symm i)

/-- Transport the measured part of a record along the same permutation. -/
def permuteMeasuredRecord {Index : Type*} (permutation : Equiv.Perm Index)
    (outcome : MeasuredRecord Index) : MeasuredRecord Index where
  sample i := outcome.sample (permutation.symm i)
  hadamardOutput i := outcome.hadamardOutput (permutation.symm i)

@[simp]
theorem permuteSelection_refl {Index : Type*} (selection : HiddenSelection Index) :
    permuteSelection (Equiv.refl Index) selection = selection := by
  rfl

@[simp]
theorem permuteMeasuredRecord_refl {Index : Type*} (outcome : MeasuredRecord Index) :
    permuteMeasuredRecord (Equiv.refl Index) outcome = outcome := by
  rfl

/-- Reconstructing a state commutes with simultaneous coordinate transport. -/
theorem stateOfSelection_permute {Index : Type*} (permutation : Equiv.Perm Index)
    (outcome : MeasuredRecord Index) (selection : HiddenSelection Index) :
    stateOfSelection (permuteMeasuredRecord permutation outcome)
        (permuteSelection permutation selection) =
      permuteCoordinates permutation (stateOfSelection outcome selection) :=
  rfl

/-- All hidden selections satisfying a decidable physical predicate. -/
def finiteSupport {Index : Type*} [Fintype Index] [DecidableEq Index]
    (admissible : HiddenSelection Index → Bool) :
    Finset (HiddenSelection Index) :=
  Finset.univ.filter fun selection ↦ admissible selection = true

@[simp]
theorem mem_finiteSupport {Index : Type*} [Fintype Index] [DecidableEq Index]
    (admissible : HiddenSelection Index → Bool)
    (selection : HiddenSelection Index) :
    selection ∈ finiteSupport admissible ↔ admissible selection = true := by
  simp [finiteSupport]

/-- The finite hidden support inside one measured modular subset-sum fibre. -/
def physicalFibre {Index : Type*} [Fintype Index] [DecidableEq Index]
    (outcome : MeasuredRecord Index) (modulus residue : ℤ) :
    Finset (HiddenSelection Index) :=
  finiteSupport fun selection ↦ decide <|
    subsetContribution (stateOfSelection outcome selection) % modulus =
      residue % modulus

@[simp]
theorem mem_physicalFibre {Index : Type*} [Fintype Index] [DecidableEq Index]
    (outcome : MeasuredRecord Index) (modulus residue : ℤ)
    (selection : HiddenSelection Index) :
    selection ∈ physicalFibre outcome modulus residue ↔
      InMeasuredFiber modulus residue
        (subsetContribution (stateOfSelection outcome selection)) := by
  simp [physicalFibre, InMeasuredFiber]

/-- Simultaneous coordinate transport preserves membership in the physical fibre. -/
theorem mem_physicalFibre_permute_iff {Index : Type*}
    [Fintype Index] [DecidableEq Index]
    (permutation : Equiv.Perm Index) (outcome : MeasuredRecord Index)
    (modulus residue : ℤ) (selection : HiddenSelection Index) :
    permuteSelection permutation selection ∈
        physicalFibre (permuteMeasuredRecord permutation outcome) modulus residue ↔
      selection ∈ physicalFibre outcome modulus residue := by
  simp only [mem_physicalFibre, stateOfSelection_permute]
  exact permuteCoordinates_preserves_fiber modulus residue permutation
    (stateOfSelection outcome selection)

/-! ## Complete Step-4 labels -/

/-- The orthogonal Step-4 label tested by this prototype. -/
structure FullStepFourLabel (Group Summary : Type*) where
  subsetHighBit : ZMod 2
  truncatedLabel : Group → Summary

/--
The high bit `h` of the measured subset sum after fixing its residue modulo
`modulus / 2`.  This is a basis label, not the Hadamard sign exponent.
-/
def subsetHighBit {Index : Type*} [Fintype Index] (ambientModulus : ℤ)
    (outcome : MeasuredRecord Index) (selection : HiddenSelection Index) : ZMod 2 :=
  (((subsetContribution (stateOfSelection outcome selection) % ambientModulus) /
      (ambientModulus / 2) : ℤ) : ZMod 2)

/-- The parity controlling the signed amplitude of one hidden term. -/
def hadamardParity {Index : Type*} [Fintype Index] (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) : ZMod 2 :=
  (totalHadamardExponent (stateOfSelection outcome selection) : ZMod 2)

/-- The raw `(-1)^(selection · hadamardOutput)` coefficient. -/
def hadamardSign {Index : Type*} [Fintype Index] (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) : ℤ :=
  if hadamardParity outcome selection = 0 then 1 else -1

/-- Pair the subset-sum high bit with every stored group-contribution summary. -/
def fullStepFourLabel {Index Group Summary : Type*}
    [Fintype Index] [DecidableEq Group]
    (ambientModulus : ℤ) (summary : ℤ → Summary) (groupOf : Index → Group)
    (outcome : MeasuredRecord Index) (selection : HiddenSelection Index) :
    FullStepFourLabel Group Summary where
  subsetHighBit := subsetHighBit ambientModulus outcome selection
  truncatedLabel :=
    summarizedGroupContributionLabel summary groupOf
      (stateOfSelection outcome selection)

/-- The complete target label after transporting a term and its measured record. -/
def transportedFullStepFourLabel {Index Group Summary : Type*}
    [Fintype Index] [DecidableEq Group]
    (ambientModulus : ℤ) (summary : ℤ → Summary) (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) : FullStepFourLabel Group Summary :=
  fullStepFourLabel ambientModulus summary groupOf
    (permuteMeasuredRecord permutation outcome)
    (permuteSelection permutation selection)

/-- Complete-record transport preserves the Hadamard amplitude parity. -/
theorem hadamardParity_permute {Index : Type*} [Fintype Index]
    (permutation : Equiv.Perm Index) (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) :
    hadamardParity (permuteMeasuredRecord permutation outcome)
        (permuteSelection permutation selection) =
      hadamardParity outcome selection := by
  unfold hadamardParity
  rw [stateOfSelection_permute, totalHadamardExponent_permute]

/-- Complete-record transport also preserves the signed coefficient. -/
theorem hadamardSign_permute {Index : Type*} [Fintype Index]
    (permutation : Equiv.Perm Index) (outcome : MeasuredRecord Index)
    (selection : HiddenSelection Index) :
    hadamardSign (permuteMeasuredRecord permutation outcome)
        (permuteSelection permutation selection) =
      hadamardSign outcome selection := by
  simp [hadamardSign, hadamardParity_permute]

/-! ## Executable compatibility checks -/

/--
Two label maps induce the same coherent-class partition on a finite support.
This is necessary for either map to be obtained from the other through a label
equivalence.
-/
def LabelPartitionCompatibleOn {Term Label : Type*}
    (support : Finset Term) (sourceLabel targetLabel : Term → Label) : Prop :=
  ∀ left, left ∈ support → ∀ right, right ∈ support →
    (sourceLabel left = sourceLabel right ↔
      targetLabel left = targetLabel right)

/--
The target label factors through the occupied source labels.  This is the
one-way condition needed for a well-defined map on source coherent classes.
-/
def LabelFactorsThroughOn {Term SourceLabel TargetLabel : Type*}
    (support : Finset Term) (sourceLabel : Term → SourceLabel)
    (targetLabel : Term → TargetLabel) : Prop :=
  ∀ left, left ∈ support → ∀ right, right ∈ support →
    sourceLabel left = sourceLabel right → targetLabel left = targetLabel right

/-- A computable compatibility test for finite term and label types. -/
def labelPartitionCompatibilityCheck {Term Label : Type*}
    [Fintype Term] [DecidableEq Term] [DecidableEq Label]
    (support : Finset Term) (sourceLabel targetLabel : Term → Label) : Bool :=
  decide <| ((support.product support).filter fun pair ↦
    ¬ (sourceLabel pair.1 = sourceLabel pair.2 ↔
      targetLabel pair.1 = targetLabel pair.2)).card = 0

@[simp]
theorem labelPartitionCompatibilityCheck_eq_true_iff
    {Term Label : Type*} [Fintype Term] [DecidableEq Term] [DecidableEq Label]
    (support : Finset Term) (sourceLabel targetLabel : Term → Label) :
    labelPartitionCompatibilityCheck support sourceLabel targetLabel = true ↔
      LabelPartitionCompatibleOn support sourceLabel targetLabel := by
  simp only [labelPartitionCompatibilityCheck, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, not_not, LabelPartitionCompatibleOn]
  aesop

/-- Executable factor-through test on finite types. -/
def labelFactorsThroughCheck {Term SourceLabel TargetLabel : Type*}
    [Fintype Term] [DecidableEq Term]
    [DecidableEq SourceLabel] [DecidableEq TargetLabel]
    (support : Finset Term) (sourceLabel : Term → SourceLabel)
    (targetLabel : Term → TargetLabel) : Bool :=
  decide <| ((support.product support).filter fun pair ↦
    sourceLabel pair.1 = sourceLabel pair.2 ∧
      targetLabel pair.1 ≠ targetLabel pair.2).card = 0

@[simp]
theorem labelFactorsThroughCheck_eq_true_iff
    {Term SourceLabel TargetLabel : Type*}
    [Fintype Term] [DecidableEq Term]
    [DecidableEq SourceLabel] [DecidableEq TargetLabel]
    (support : Finset Term) (sourceLabel : Term → SourceLabel)
    (targetLabel : Term → TargetLabel) :
    labelFactorsThroughCheck support sourceLabel targetLabel = true ↔
      LabelFactorsThroughOn support sourceLabel targetLabel := by
  simp only [labelFactorsThroughCheck, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, not_and, not_not, LabelFactorsThroughOn]
  aesop

/-- Full partition compatibility implies factorization through occupied labels. -/
theorem LabelPartitionCompatibleOn.factorsThrough
    {Term Label : Type*} {support : Finset Term}
    {sourceLabel targetLabel : Term → Label}
    (compatible : LabelPartitionCompatibleOn support sourceLabel targetLabel) :
    LabelFactorsThroughOn support sourceLabel targetLabel := by
  intro left left_mem right right_mem equal
  exact (compatible left left_mem right right_mem).mp equal

/-- Any genuine label equivalence passes the partition-compatibility test. -/
theorem labelPartitionCompatibleOn_of_equiv {Term Label : Type*}
    (support : Finset Term) (sourceLabel targetLabel : Term → Label)
    (labelEquiv : Label ≃ Label)
    (mapsLabel : ∀ term, term ∈ support →
      targetLabel term = labelEquiv (sourceLabel term)) :
    LabelPartitionCompatibleOn support sourceLabel targetLabel := by
  intro left left_mem right right_mem
  constructor
  · intro equal
    simpa [mapsLabel left left_mem, mapsLabel right right_mem] using
      congrArg labelEquiv equal
  · intro equal
    apply labelEquiv.injective
    simpa [mapsLabel left left_mem, mapsLabel right right_mem] using equal

/-! ## Finite coherent signed weights -/

/-- Labels actually occupied by a finite hidden support. -/
def occupiedLabels {Term Label : Type*} [DecidableEq Label]
    (support : Finset Term) (label : Term → Label) : Finset Label :=
  support.image label

/-- Raw coherent sum inside one occupied orthogonal label. -/
def coherentSignedAmplitude {Term Label : Type*}
    [DecidableEq Term] [DecidableEq Label]
    (support : Finset Term) (label : Term → Label) (coefficient : Term → ℤ)
    (labelValue : Label) : ℤ :=
  ∑ term ∈ support.filter fun term ↦ label term = labelValue, coefficient term

/-- Sum of squared coherent amplitudes over the occupied orthogonal labels. -/
def rawCoherentWeight {Term Label : Type*}
    [DecidableEq Term] [DecidableEq Label]
    (support : Finset Term) (label : Term → Label)
    (coefficient : Term → ℤ) : ℤ :=
  ∑ labelValue ∈ occupiedLabels support label,
    (coherentSignedAmplitude support label coefficient labelValue) ^ 2

/-! ## Exhaustive compatibility search for the six-coordinate witness -/

/-- Every permutation of the six witness coordinates, as an executable finite enumeration. -/
def allCrossGroupPermutations : Finset (Equiv.Perm CrossGroupIndex) :=
  Finset.univ

@[simp]
theorem mem_allCrossGroupPermutations (permutation : Equiv.Perm CrossGroupIndex) :
    permutation ∈ allCrossGroupPermutations := by
  simp [allCrossGroupPermutations]

abbrev CrossGroupSelection := HiddenSelection CrossGroupIndex

/-- The measured portion shared by the two truncated witness terms. -/
def crossGroupMeasuredRecord : MeasuredRecord CrossGroupIndex where
  sample := crossGroupTruncatedSample
  hadamardOutput
    | .a0 | .b1 => true
    | .a1 | .a2 | .b0 | .b2 => false

def crossGroupLeftSelection : CrossGroupSelection
  | .a0 | .a1 | .b2 => true
  | .a2 | .b0 | .b1 => false

def crossGroupRightSelection : CrossGroupSelection
  | .a2 | .b0 | .b1 => true
  | .a0 | .a1 | .b2 => false

/-- The measured residue fibre `z ≡ 76 (mod 128)` for the local witness. -/
def crossGroupPhysicalSupport : Finset CrossGroupSelection :=
  physicalFibre crossGroupMeasuredRecord 128 76

abbrev CrossGroupFullLabel := ZMod 2 × ℤ × ℤ

/-- Materialize the two group coordinates so equality is executable. -/
def concreteCrossGroupFullLabel (label : FullStepFourLabel Bool ℤ) :
    CrossGroupFullLabel :=
  (label.subsetHighBit, label.truncatedLabel false, label.truncatedLabel true)

def crossGroupSourceFullLabel (selection : CrossGroupSelection) :
    CrossGroupFullLabel :=
  concreteCrossGroupFullLabel <|
    fullStepFourLabel 256 crossGroupHighSummary crossGroupOf
      crossGroupMeasuredRecord selection

def crossGroupTargetFullLabel (permutation : Equiv.Perm CrossGroupIndex)
    (selection : CrossGroupSelection) : CrossGroupFullLabel :=
  concreteCrossGroupFullLabel <|
    transportedFullStepFourLabel 256 crossGroupHighSummary crossGroupOf
      permutation crossGroupMeasuredRecord selection

/-- Semantic compatibility of one candidate permutation on the physical fibre. -/
def CrossGroupPermutationCompatible (permutation : Equiv.Perm CrossGroupIndex) : Prop :=
  LabelFactorsThroughOn crossGroupPhysicalSupport
    crossGroupSourceFullLabel (crossGroupTargetFullLabel permutation)

/-- Executable form of `CrossGroupPermutationCompatible`. -/
def crossGroupPermutationCompatibilityCheck
    (permutation : Equiv.Perm CrossGroupIndex) : Bool :=
  labelFactorsThroughCheck crossGroupPhysicalSupport
    crossGroupSourceFullLabel (crossGroupTargetFullLabel permutation)

@[simp]
theorem crossGroupPermutationCompatibilityCheck_eq_true_iff
    (permutation : Equiv.Perm CrossGroupIndex) :
    crossGroupPermutationCompatibilityCheck permutation = true ↔
      CrossGroupPermutationCompatible permutation := by
  simp [crossGroupPermutationCompatibilityCheck, CrossGroupPermutationCompatible]

/-- Exhaustive list whose target label factors through the occupied source label. -/
def compatibleCrossGroupPermutations : Finset (Equiv.Perm CrossGroupIndex) :=
  allCrossGroupPermutations.filter fun permutation ↦
    crossGroupPermutationCompatibilityCheck permutation = true

@[simp]
theorem mem_compatibleCrossGroupPermutations_iff
    (permutation : Equiv.Perm CrossGroupIndex) :
    permutation ∈ compatibleCrossGroupPermutations ↔
      CrossGroupPermutationCompatible permutation := by
  simp [compatibleCrossGroupPermutations]

theorem crossGroupLeftSelection_mem_support :
    crossGroupLeftSelection ∈ crossGroupPhysicalSupport := by
  native_decide

theorem crossGroupRightSelection_mem_support :
    crossGroupRightSelection ∈ crossGroupPhysicalSupport := by
  native_decide

/-- The current witness still collides after adding the phase-bit component. -/
theorem crossGroupSourceFullLabels_equal :
    crossGroupSourceFullLabel crossGroupLeftSelection =
      crossGroupSourceFullLabel crossGroupRightSelection := by
  native_decide

/-- The partial cross-group swap splits that complete Step-4 label. -/
theorem partialCrossGroupSwap_targetFullLabels_ne :
    crossGroupTargetFullLabel partialCrossGroupSwap crossGroupLeftSelection ≠
      crossGroupTargetFullLabel partialCrossGroupSwap crossGroupRightSelection := by
  native_decide

/-- Therefore the published partial swap fails the finite-support compatibility criterion. -/
theorem partialCrossGroupSwap_not_compatible :
    ¬ CrossGroupPermutationCompatible partialCrossGroupSwap := by
  intro compatible
  have mapped_equal :=
    compatible crossGroupLeftSelection crossGroupLeftSelection_mem_support
      crossGroupRightSelection crossGroupRightSelection_mem_support
      crossGroupSourceFullLabels_equal
  exact partialCrossGroupSwap_targetFullLabels_ne mapped_equal

theorem partialCrossGroupSwap_not_mem_compatiblePermutations :
    partialCrossGroupSwap ∉ compatibleCrossGroupPermutations := by
  simpa using partialCrossGroupSwap_not_compatible

/-- The identity permutation is a basic positive sanity check. -/
theorem identity_crossGroupPermutationCompatible :
    CrossGroupPermutationCompatible (Equiv.refl CrossGroupIndex) := by
  intro left left_mem right right_mem
  simp [crossGroupSourceFullLabel, crossGroupTargetFullLabel,
    transportedFullStepFourLabel, permuteMeasuredRecord]

/-- A coordinate permutation moves the two witness groups only as whole blocks. -/
def CrossGroupPermutationMovesWholeGroups
    (permutation : Equiv.Perm CrossGroupIndex) : Prop :=
  ∃ groupRelabel : Equiv.Perm Bool,
    RelabelsGroups crossGroupOf permutation groupRelabel

/-- Executable form of `CrossGroupPermutationMovesWholeGroups`. -/
def crossGroupPermutationMovesWholeGroupsCheck
    (permutation : Equiv.Perm CrossGroupIndex) : Bool :=
  letI : DecidablePred (fun groupRelabel : Equiv.Perm Bool ↦
      RelabelsGroups crossGroupOf permutation groupRelabel) :=
    fun _ ↦ Fintype.decidableForallFintype
  @decide (CrossGroupPermutationMovesWholeGroups permutation)
    Fintype.decidableExistsFintype

@[simp]
theorem crossGroupPermutationMovesWholeGroupsCheck_eq_true_iff
    (permutation : Equiv.Perm CrossGroupIndex) :
    crossGroupPermutationMovesWholeGroupsCheck permutation = true ↔
      CrossGroupPermutationMovesWholeGroups permutation := by
  simp [crossGroupPermutationMovesWholeGroupsCheck,
    CrossGroupPermutationMovesWholeGroups, RelabelsGroups]

/--
On this fibre, the executable label-compatibility test accepts exactly the
whole-group movers.  This is an instance-specific classification, not a
general equivalence between factorization and group preservation.
-/
theorem crossGroupPermutationChecks_eq :
    ∀ permutation : Equiv.Perm CrossGroupIndex,
      crossGroupPermutationCompatibilityCheck permutation =
        crossGroupPermutationMovesWholeGroupsCheck permutation := by
  native_decide

theorem crossGroupPermutationCompatible_iff_movesWholeGroups
    (permutation : Equiv.Perm CrossGroupIndex) :
    CrossGroupPermutationCompatible permutation ↔
      CrossGroupPermutationMovesWholeGroups permutation := by
  rw [← crossGroupPermutationCompatibilityCheck_eq_true_iff,
    ← crossGroupPermutationMovesWholeGroupsCheck_eq_true_iff,
    crossGroupPermutationChecks_eq]

/-! ## Decisive exhaustive facts for the local fibre -/

/-- An all-zero group predicate stated directly on measured data. -/
def MeasuredGroupAllZero {Index Group : Type*} (groupOf : Index → Group)
    (outcome : MeasuredRecord Index) (group : Group) : Prop :=
  ∀ index, groupOf index = group → outcome.hadamardOutput index = false

/-- Whether a candidate permutation creates at least one all-zero group. -/
def CrossGroupPermutationCreatesAllZero
    (permutation : Equiv.Perm CrossGroupIndex) : Prop :=
  ∃ group : Bool,
    MeasuredGroupAllZero crossGroupOf
      (permuteMeasuredRecord permutation crossGroupMeasuredRecord) group

def crossGroupPermutationCreatesAllZeroCheck
    (permutation : Equiv.Perm CrossGroupIndex) : Bool :=
  decide (∃ group : Bool, ∀ index : CrossGroupIndex,
    crossGroupOf index = group →
      (permuteMeasuredRecord permutation crossGroupMeasuredRecord).hadamardOutput index = false)

@[simp]
theorem crossGroupPermutationCreatesAllZeroCheck_eq_true_iff
    (permutation : Equiv.Perm CrossGroupIndex) :
    crossGroupPermutationCreatesAllZeroCheck permutation = true ↔
      CrossGroupPermutationCreatesAllZero permutation := by
  simp [crossGroupPermutationCreatesAllZeroCheck,
    CrossGroupPermutationCreatesAllZero, MeasuredGroupAllZero]

/-- Exhaustive list of permutations that create an all-zero group. -/
def allZeroCreatingCrossGroupPermutations : Finset (Equiv.Perm CrossGroupIndex) :=
  allCrossGroupPermutations.filter fun permutation ↦
    crossGroupPermutationCreatesAllZeroCheck permutation = true

@[simp]
theorem mem_allZeroCreatingCrossGroupPermutations_iff
    (permutation : Equiv.Perm CrossGroupIndex) :
    permutation ∈ allZeroCreatingCrossGroupPermutations ↔
      CrossGroupPermutationCreatesAllZero permutation := by
  simp [allZeroCreatingCrossGroupPermutations]

/-- The complement of the 72 label-compatible permutations. -/
def incompatibleCrossGroupPermutations : Finset (Equiv.Perm CrossGroupIndex) :=
  allCrossGroupPermutations \ compatibleCrossGroupPermutations

def crossGroupSourceCoefficient (selection : CrossGroupSelection) : ℤ :=
  hadamardSign crossGroupMeasuredRecord selection

def crossGroupTargetCoefficient (permutation : Equiv.Perm CrossGroupIndex)
    (selection : CrossGroupSelection) : ℤ :=
  hadamardSign (permuteMeasuredRecord permutation crossGroupMeasuredRecord)
    (permuteSelection permutation selection)

/-- Raw coherent weight on the source fibre, grouped by the full Step-4 basis label. -/
def crossGroupSourceRawWeight : ℤ :=
  rawCoherentWeight crossGroupPhysicalSupport
    crossGroupSourceFullLabel crossGroupSourceCoefficient

/-- Raw coherent weight after one candidate coordinate permutation. -/
def crossGroupTargetRawWeight
    (permutation : Equiv.Perm CrossGroupIndex) : ℤ :=
  rawCoherentWeight crossGroupPhysicalSupport
    (crossGroupTargetFullLabel permutation)
    (crossGroupTargetCoefficient permutation)

/-- The unique full Step-4 label occupied by the four source terms: `(h, s_a, s_b)`. -/
def crossGroupOccupiedFullLabel : CrossGroupFullLabel := (1, 3, 9)

theorem crossGroupSourceFullLabel_eq_occupied :
    ∀ selection : CrossGroupSelection,
      selection ∈ crossGroupPhysicalSupport →
        crossGroupSourceFullLabel selection = crossGroupOccupiedFullLabel := by
  native_decide

theorem card_crossGroupPhysicalSupport :
    crossGroupPhysicalSupport.card = 4 := by
  native_decide

theorem card_allCrossGroupPermutations :
    allCrossGroupPermutations.card = 720 := by
  native_decide

theorem card_compatibleCrossGroupPermutations :
    compatibleCrossGroupPermutations.card = 72 := by
  native_decide

theorem card_allZeroCreatingCrossGroupPermutations :
    allZeroCreatingCrossGroupPermutations.card = 288 := by
  native_decide

/-- No permutation both creates an all-zero group and respects the occupied full label. -/
theorem compatible_inter_allZeroCreating_card :
    (compatibleCrossGroupPermutations ∩
      allZeroCreatingCrossGroupPermutations).card = 0 := by
  native_decide

/-- The exhaustive cardinality result as the semantic no-go statement. -/
theorem no_compatible_allZeroCreating_permutation :
    ¬ ∃ permutation : Equiv.Perm CrossGroupIndex,
      CrossGroupPermutationCompatible permutation ∧
        CrossGroupPermutationCreatesAllZero permutation := by
  rintro ⟨permutation, compatible, creates⟩
  have member : permutation ∈
      compatibleCrossGroupPermutations ∩
        allZeroCreatingCrossGroupPermutations := by
    simp [compatible, creates]
  have empty : compatibleCrossGroupPermutations ∩
      allZeroCreatingCrossGroupPermutations = ∅ :=
    Finset.card_eq_zero.mp compatible_inter_allZeroCreating_card
  rw [empty] at member
  simp at member

theorem card_incompatibleCrossGroupPermutations :
    incompatibleCrossGroupPermutations.card = 648 := by
  native_decide

theorem crossGroupSourceRawWeight_eq_zero :
    crossGroupSourceRawWeight = 0 := by
  native_decide

/--
The exhaustive raw-weight dichotomy: the 72 compatible permutations retain
the source cancellation, while each of the other 648 has raw weight four.
-/
theorem crossGroupTargetRawWeight_classification :
    ∀ permutation : Equiv.Perm CrossGroupIndex,
      crossGroupTargetRawWeight permutation =
        if permutation ∈ compatibleCrossGroupPermutations then 0 else 4 := by
  native_decide

/-! ## Exhaustive classification of measured output masks -/

/-- Replace only the six measured Hadamard-output bits. -/
def crossGroupMeasuredRecordWithOutput
    (output : CrossGroupIndex → Bool) : MeasuredRecord CrossGroupIndex where
  sample := crossGroupTruncatedSample
  hadamardOutput := output

/-- Hamming weight of a measured six-bit output. -/
def crossGroupOutputWeight (output : CrossGroupIndex → Bool) : ℕ :=
  (Finset.univ.filter fun index ↦ output index = true).card

/-- Both three-coordinate groups contain at least one measured one. -/
def CrossGroupOutputHasNoAllZeroGroup
    (output : CrossGroupIndex → Bool) : Prop :=
  ∀ group : Bool, ∃ index : CrossGroupIndex,
    crossGroupOf index = group ∧ output index = true

/-- Executable form of `CrossGroupOutputHasNoAllZeroGroup`. -/
def crossGroupOutputHasNoAllZeroGroupCheck
    (output : CrossGroupIndex → Bool) : Bool :=
  letI : DecidablePred (fun group : Bool ↦
      ∃ index : CrossGroupIndex,
        crossGroupOf index = group ∧ output index = true) :=
    fun _ ↦ Fintype.decidableExistsFintype
  @decide (CrossGroupOutputHasNoAllZeroGroup output)
    Fintype.decidableForallFintype

@[simp]
theorem crossGroupOutputHasNoAllZeroGroupCheck_eq_true_iff
    (output : CrossGroupIndex → Bool) :
    crossGroupOutputHasNoAllZeroGroupCheck output = true ↔
      CrossGroupOutputHasNoAllZeroGroup output := by
  simp [crossGroupOutputHasNoAllZeroGroupCheck,
    CrossGroupOutputHasNoAllZeroGroup]

/-- Raw source weight after varying only the measured output mask. -/
def crossGroupSourceRawWeightForOutput
    (output : CrossGroupIndex → Bool) : ℤ :=
  rawCoherentWeight crossGroupPhysicalSupport crossGroupSourceFullLabel
    (fun selection ↦
      hadamardSign (crossGroupMeasuredRecordWithOutput output) selection)

/-- Parity of the measured ones in one of the two groups. -/
def crossGroupOutputParity (output : CrossGroupIndex → Bool)
    (group : Bool) : ZMod 2 :=
  ∑ index, if crossGroupOf index = group ∧ output index = true then 1 else 0

/--
The fibre is a product of two two-term collisions.  Its raw weight is sixteen
exactly when both group-output parities are even, and zero otherwise.
-/
theorem crossGroupSourceRawWeightForOutput_classification :
    ∀ output : CrossGroupIndex → Bool,
      crossGroupSourceRawWeightForOutput output =
        if crossGroupOutputParity output false = 0 ∧
            crossGroupOutputParity output true = 0
        then 16 else 0 := by
  native_decide

/-- The local analogue of the paper's zero-majority bad event. -/
def CrossGroupSparseBadOutput (output : CrossGroupIndex → Bool) : Prop :=
  crossGroupOutputWeight output ≤ 3 ∧
    CrossGroupOutputHasNoAllZeroGroup output

/-- Executable form of `CrossGroupSparseBadOutput`. -/
def crossGroupSparseBadOutputCheck
    (output : CrossGroupIndex → Bool) : Bool :=
  decide (crossGroupOutputWeight output ≤ 3) &&
    crossGroupOutputHasNoAllZeroGroupCheck output

@[simp]
theorem crossGroupSparseBadOutputCheck_eq_true_iff
    (output : CrossGroupIndex → Bool) :
    crossGroupSparseBadOutputCheck output = true ↔
      CrossGroupSparseBadOutput output := by
  simp [crossGroupSparseBadOutputCheck, CrossGroupSparseBadOutput]

/-- All 27 local bad masks are null outcomes on the source fibre. -/
theorem crossGroupSparseBadOutputs_have_zero_raw_weight :
    ∀ output : CrossGroupIndex → Bool,
      CrossGroupSparseBadOutput output →
        crossGroupSourceRawWeightForOutput output = 0 := by
  intro output bad
  have checked : crossGroupSparseBadOutputCheck output = true :=
    (crossGroupSparseBadOutputCheck_eq_true_iff output).mpr bad
  have exhaustive : ∀ candidate : CrossGroupIndex → Bool,
      crossGroupSparseBadOutputCheck candidate = true →
        crossGroupSourceRawWeightForOutput candidate = 0 := by
    native_decide
  exact exhaustive output checked

/-- Executable enumeration of the local bad masks. -/
def crossGroupSparseBadOutputs : Finset (CrossGroupIndex → Bool) :=
  Finset.univ.filter fun output ↦ crossGroupSparseBadOutputCheck output = true

theorem card_crossGroupSparseBadOutputs :
    crossGroupSparseBadOutputs.card = 27 := by
  native_decide

/-- The conditional Born-probability denominator `|Z_Y| * 2^Q = 4 * 64`. -/
def crossGroupWeightDenominator : ℕ :=
  crossGroupPhysicalSupport.card * 2 ^ Fintype.card CrossGroupIndex

def crossGroupSourceNormalizedWeight : ℚ :=
  (crossGroupSourceRawWeight : ℚ) / crossGroupWeightDenominator

def crossGroupTargetNormalizedWeight
    (permutation : Equiv.Perm CrossGroupIndex) : ℚ :=
  (crossGroupTargetRawWeight permutation : ℚ) / crossGroupWeightDenominator

theorem crossGroupWeightDenominator_eq : crossGroupWeightDenominator = 256 := by
  native_decide

/-- The displayed bad outcome is a null outcome on its complete local fibre. -/
theorem crossGroupSourceNormalizedWeight_eq_zero :
    crossGroupSourceNormalizedWeight = 0 := by
  rw [crossGroupSourceNormalizedWeight, crossGroupSourceRawWeight_eq_zero]
  norm_num

/-- The partial swap splits the cancellation and gives normalized weight `1/64`. -/
theorem partialCrossGroupSwap_normalizedWeight :
    crossGroupTargetNormalizedWeight partialCrossGroupSwap = 1 / 64 := by
  rw [crossGroupTargetNormalizedWeight,
    crossGroupTargetRawWeight_classification,
    crossGroupWeightDenominator_eq]
  rw [if_neg partialCrossGroupSwap_not_mem_compatiblePermutations]
  norm_num

end SimonDCP.Arithmetic.LemmaOneFiniteSupportPrototype
