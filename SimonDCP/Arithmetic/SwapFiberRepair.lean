import SimonDCP.Arithmetic.SwapFiber
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.NNReal.Basic

/-!
# Fibre-preserving replacements for the swap used in Lemma 1

The sketch of Lemma 1 permutes selection bits and Hadamard-output bits, but
only the low parts of the associated Fourier samples.  The audit in
`SwapFiber` shows that this changes the measured subset sum by

`B * (phiJ - phiI) * (highI - highJ)`.

This file records two precise repairs.

1. The original low-part-only operation is valid exactly when the measured
   modulus divides that error.  This is the minimal local matching condition.
2. If the *entire* Fourier samples are permuted together with the selection
   and Hadamard-output bits, both the subset sum and Hadamard phase are
   preserved exactly.  The resulting coordinate permutation is a bijection.

This second result is an algebraic kernel, not by itself a proof of Lemma 1.
After Step 4 the selection string is no longer a register: terms with equal
`(h, s₁, ..., s_g)` labels interfere.  A permutation chosen from a measured
outcome must therefore be independent of the hidden selection string and
must carry these interference classes through a fixed relabeling.  In
addition, a state-dependent choice must be reversible.  The definitions at
the end of this file expose all three obligations instead of assuming them
implicitly.
-/

namespace SimonDCP.Arithmetic.SwapFiberRepair

open scoped BigOperators
open scoped NNReal
open SimonDCP.Arithmetic.SwapFiber

/-! ## The exact condition for retaining the paper's low-part-only swap -/

/--
The minimal arithmetic matching condition for the low-part-only swap.  It
says precisely that the error identified by `lowPartBitSwap_delta` vanishes
in the measured residue class.
-/
def LowPartMatchingCondition (modulus B : ℤ) (x : SwapInput) : Prop :=
  modulus ∣ B * (x.phiJ - x.phiI) * (x.highI - x.highJ)

/-- The low-part-only swap preserves the measured fibre exactly under the matching condition. -/
theorem lowPart_swap_fiber_iff_matching (modulus B : ℤ) (x : SwapInput) :
    InMeasuredFiber modulus (beforeContribution B x) (afterContribution B x) ↔
      LowPartMatchingCondition modulus B x := by
  unfold InMeasuredFiber LowPartMatchingCondition
  change Int.ModEq modulus (afterContribution B x) (beforeContribution B x) ↔ _
  rw [Int.modEq_iff_dvd]
  rw [show beforeContribution B x - afterContribution B x =
      -(afterContribution B x - beforeContribution B x) by ring]
  rw [lowPartBitSwap_delta]
  simp only [Int.dvd_neg]

/--
When the swapped selection bits are respectively zero and one, the exact
condition reduces to divisibility of `B * (highI - highJ)`.
-/
theorem zero_one_lowPart_swap_fiber_iff
    (modulus B : ℤ) (x : SwapInput)
    (hphiI : x.phiI = 0) (hphiJ : x.phiJ = 1) :
    InMeasuredFiber modulus (beforeContribution B x) (afterContribution B x) ↔
      modulus ∣ B * (x.highI - x.highJ) := by
  rw [lowPart_swap_fiber_iff_matching]
  simp [LowPartMatchingCondition, hphiI, hphiJ]

/--
If the measured modulus is `B * stride` and `B` is nonzero, a zero/one swap
is valid exactly when the two high parts agree modulo `stride`.  In the
paper's power-of-two split, `stride` is the quotient of the measured modulus
by the number of possible low parts.
-/
theorem zero_one_scaled_modulus_swap_fiber_iff
    (B stride : ℤ) (x : SwapInput) (hB : B ≠ 0)
    (hphiI : x.phiI = 0) (hphiJ : x.phiJ = 1) :
    InMeasuredFiber (B * stride) (beforeContribution B x) (afterContribution B x) ↔
      stride ∣ x.highI - x.highJ := by
  rw [zero_one_lowPart_swap_fiber_iff (B * stride) B x hphiI hphiJ]
  exact mul_dvd_mul_iff_left hB

/-- Equal high parts are a simple sufficient matching rule. -/
theorem lowPart_swap_preserves_fiber_of_equal_high
    (modulus B : ℤ) (x : SwapInput) (hhigh : x.highI = x.highJ) :
    InMeasuredFiber modulus (beforeContribution B x) (afterContribution B x) := by
  rw [lowPart_swap_fiber_iff_matching]
  simp [LowPartMatchingCondition, hhigh]

/-! ## A local unconditional repair: swap each entire sample -/

/-- Swap the selection bits and both the low and high parts of their samples. -/
def fullSwap (x : SwapInput) : SwapInput where
  phiI := x.phiJ
  phiJ := x.phiI
  lowI := x.lowJ
  lowJ := x.lowI
  highI := x.highJ
  highJ := x.highI

/-- Swapping the two complete coordinate records twice is the identity. -/
theorem fullSwap_involutive : Function.Involutive fullSwap := by
  intro x
  cases x
  rfl

/-- The repaired local map is a bijection, and hence an injection. -/
theorem fullSwap_bijective : Function.Bijective fullSwap :=
  fullSwap_involutive.bijective

/-- The repaired swap packaged as an equivalence. -/
def fullSwapEquiv : SwapInput ≃ SwapInput where
  toFun := fullSwap
  invFun := fullSwap
  left_inv := fullSwap_involutive
  right_inv := fullSwap_involutive

/-- Swapping complete samples preserves the two-coordinate subset sum exactly. -/
theorem fullSwap_preserves_contribution (B : ℤ) (x : SwapInput) :
    beforeContribution B (fullSwap x) = beforeContribution B x := by
  simp only [beforeContribution, fullSwap]
  ring

/-- Consequently, the repaired local map preserves every measured fibre. -/
theorem fullSwap_preserves_fiber (modulus residue B : ℤ) (x : SwapInput) :
    InMeasuredFiber modulus residue (beforeContribution B (fullSwap x)) ↔
      InMeasuredFiber modulus residue (beforeContribution B x) := by
  rw [fullSwap_preserves_contribution]

/--
Swapping the Hadamard-output coordinates with the complete samples preserves
the phase exponent as well.
-/
theorem fullSwap_preserves_phase
    (x : SwapInput) (outputI outputJ : ℤ) :
    phaseExponent (fullSwap x).phiI (fullSwap x).phiJ outputJ outputI =
      phaseExponent x.phiI x.phiJ outputI outputJ := by
  exact simultaneousSwap_preserves_phase x.phiI x.phiJ outputI outputJ

/-! ## Arbitrary finite coordinate permutations -/

/--
The three coordinate-indexed records relevant to the algebraic part of
Lemma 1.  `sample` is the entire Fourier sample `y`, not merely its low part.
-/
structure CoordinateState (Index : Type*) where
  selection : Index → ℤ
  sample : Index → ℤ
  hadamardOutput : Index → ℤ

/-- Relocate complete coordinate records according to a permutation. -/
def permuteCoordinates {Index : Type*} (permutation : Equiv.Perm Index)
    (state : CoordinateState Index) : CoordinateState Index where
  selection i := state.selection (permutation.symm i)
  sample i := state.sample (permutation.symm i)
  hadamardOutput i := state.hadamardOutput (permutation.symm i)

/-- Applying a permutation and then its inverse restores the state. -/
theorem permuteCoordinates_symm_apply {Index : Type*}
    (permutation : Equiv.Perm Index) (state : CoordinateState Index) :
    permuteCoordinates permutation.symm (permuteCoordinates permutation state) = state := by
  cases state
  simp [permuteCoordinates]

/-- Applying the inverse and then the permutation also restores the state. -/
theorem permuteCoordinates_apply_symm {Index : Type*}
    (permutation : Equiv.Perm Index) (state : CoordinateState Index) :
    permuteCoordinates permutation (permuteCoordinates permutation.symm state) = state := by
  cases state
  simp [permuteCoordinates]

/-- Every complete-coordinate permutation is a bijection on states. -/
def permuteCoordinatesEquiv {Index : Type*} (permutation : Equiv.Perm Index) :
    CoordinateState Index ≃ CoordinateState Index where
  toFun := permuteCoordinates permutation
  invFun := permuteCoordinates permutation.symm
  left_inv := permuteCoordinates_symm_apply permutation
  right_inv := permuteCoordinates_apply_symm permutation

/-- The full subset sum represented by a coordinate state. -/
def subsetContribution {Index : Type*} [Fintype Index]
    (state : CoordinateState Index) : ℤ :=
  ∑ i, state.selection i * state.sample i

/-- The full Hadamard dot-product exponent represented by a coordinate state. -/
def totalHadamardExponent {Index : Type*} [Fintype Index]
    (state : CoordinateState Index) : ℤ :=
  ∑ i, state.selection i * state.hadamardOutput i

/-- Simultaneously permuting selection bits and complete samples preserves the subset sum. -/
theorem subsetContribution_permute {Index : Type*} [Fintype Index]
    (permutation : Equiv.Perm Index) (state : CoordinateState Index) :
    subsetContribution (permuteCoordinates permutation state) =
      subsetContribution state := by
  simpa only [subsetContribution, permuteCoordinates] using
    (Equiv.sum_comp permutation.symm
      (fun i : Index ↦ state.selection i * state.sample i))

/-- Simultaneously permuting selection and output bits preserves the Hadamard exponent. -/
theorem totalHadamardExponent_permute {Index : Type*} [Fintype Index]
    (permutation : Equiv.Perm Index) (state : CoordinateState Index) :
    totalHadamardExponent (permuteCoordinates permutation state) =
      totalHadamardExponent state := by
  simpa only [totalHadamardExponent, permuteCoordinates] using
    (Equiv.sum_comp permutation.symm
      (fun i : Index ↦ state.selection i * state.hadamardOutput i))

/-- Every complete-coordinate permutation preserves every measured subset-sum fibre. -/
theorem permuteCoordinates_preserves_fiber {Index : Type*} [Fintype Index]
    (modulus residue : ℤ) (permutation : Equiv.Perm Index)
    (state : CoordinateState Index) :
    InMeasuredFiber modulus residue
        (subsetContribution (permuteCoordinates permutation state)) ↔
      InMeasuredFiber modulus residue (subsetContribution state) := by
  rw [subsetContribution_permute]

/-- Distinct Fourier samples remain distinct after a coordinate permutation. -/
theorem sample_injective_permute_iff {Index : Type*}
    (permutation : Equiv.Perm Index) (state : CoordinateState Index) :
    Function.Injective (permuteCoordinates permutation state).sample ↔
      Function.Injective state.sample := by
  constructor
  · intro hPermuted i j hij
    apply permutation.injective
    apply hPermuted
    simpa only [permuteCoordinates, Equiv.symm_apply_apply] using hij
  · intro hSample i j hij
    apply permutation.symm.injective
    apply hSample
    exact hij

/-! ## State-dependent permutations and the missing injection obligations -/

/--
A state-dependent coordinate-permutation rule whose choice can be recovered
after applying it.  Pairwise swaps chosen by a canonical rule should satisfy
this law; an arbitrary state-dependent choice need not.
-/
structure ReversiblePlan (Index : Type*) where
  plan : CoordinateState Index → Equiv.Perm Index
  reverse_plan : ∀ state,
    plan (permuteCoordinates (plan state) state) = (plan state).symm

/-- Apply the permutation selected by a reversible plan. -/
def plannedPermute {Index : Type*} (repair : ReversiblePlan Index)
    (state : CoordinateState Index) : CoordinateState Index :=
  permuteCoordinates (repair.plan state) state

/-- A reversible state-dependent plan defines an involution. -/
theorem plannedPermute_involutive {Index : Type*} (repair : ReversiblePlan Index) :
    Function.Involutive (plannedPermute repair) := by
  intro state
  change permuteCoordinates
      (repair.plan (permuteCoordinates (repair.plan state) state))
      (permuteCoordinates (repair.plan state) state) = state
  rw [repair.reverse_plan state]
  exact permuteCoordinates_symm_apply (repair.plan state) state

/-- Hence a reversible state-dependent plan is a bijection. -/
theorem plannedPermute_bijective {Index : Type*} (repair : ReversiblePlan Index) :
    Function.Bijective (plannedPermute repair) :=
  (plannedPermute_involutive repair).bijective

/-- A reversible planned permutation preserves the measured fibre. -/
theorem plannedPermute_preserves_fiber {Index : Type*} [Fintype Index]
    (modulus residue : ℤ) (repair : ReversiblePlan Index)
    (state : CoordinateState Index) :
    InMeasuredFiber modulus residue (subsetContribution (plannedPermute repair state)) ↔
      InMeasuredFiber modulus residue (subsetContribution state) := by
  exact permuteCoordinates_preserves_fiber modulus residue (repair.plan state) state

/-- A reversible planned permutation preserves the Hadamard phase exponent. -/
theorem plannedPermute_preserves_phase {Index : Type*} [Fintype Index]
    (repair : ReversiblePlan Index) (state : CoordinateState Index) :
    totalHadamardExponent (plannedPermute repair state) =
      totalHadamardExponent state := by
  exact totalHadamardExponent_permute (repair.plan state) state

/--
Restrict a reversible plan to a proposed bad-to-good map.  The only remaining
combinatorial hypothesis is that the chosen permutation really maps every
bad state to a good state.
-/
def restrictedRepair {Index : Type*} (repair : ReversiblePlan Index)
    (Bad Good : CoordinateState Index → Prop)
    (maps_to_good : ∀ state, Bad state → Good (plannedPermute repair state)) :
    {state // Bad state} → {state // Good state} :=
  fun state ↦ ⟨plannedPermute repair state.1, maps_to_good state.1 state.2⟩

/-- The repaired bad-to-good map is injective. -/
theorem restrictedRepair_injective {Index : Type*} (repair : ReversiblePlan Index)
    (Bad Good : CoordinateState Index → Prop)
    (maps_to_good : ∀ state, Bad state → Good (plannedPermute repair state)) :
    Function.Injective (restrictedRepair repair Bad Good maps_to_good) := by
  intro left right h
  apply Subtype.ext
  apply (plannedPermute_involutive repair).injective
  exact congrArg Subtype.val h

/-! ## Conditions needed to lift the algebraic map to the Step-4 amplitudes -/

/--
Two terms have the same measured `(Y, D)` outcome when their complete sample
and Hadamard-output records agree.  Their hidden selection strings may differ.
-/
def SameMeasuredOutcome {Index : Type*}
    (left right : CoordinateState Index) : Prop :=
  left.sample = right.sample ∧
    left.hadamardOutput = right.hadamardOutput

/-- A predicate describes measured outcomes rather than hidden selection strings. -/
def DependsOnlyOnMeasuredOutcome {Index : Type*}
    (predicate : CoordinateState Index → Prop) : Prop :=
  ∀ left right,
    SameMeasuredOutcome left right → (predicate left ↔ predicate right)

/--
The permutation choice is coherent across every hidden selection string in a
single measured outcome.  This is necessary because Step 4 has no selection
register on which a selection-dependent map could act.
-/
def OutcomeCoherent {Index : Type*} (repair : ReversiblePlan Index) : Prop :=
  ∀ left right,
    SameMeasuredOutcome left right → repair.plan left = repair.plan right

/--
Compatibility with the orthogonal labels that determine interference after
Step 4.  For the paper, `Label` represents `(h, s₁, ..., s_g)`.  A fixed label
equivalence is allowed because it only relabels orthogonal basis states; a
selection-dependent relabeling would not preserve the amplitude classes.
-/
def PreservesInterferenceClasses {Index Label : Type*}
    (repair : ReversiblePlan Index)
    (interferenceLabel : CoordinateState Index → Label)
    (labelRelabel : Label ≃ Label) : Prop :=
  ∀ state,
    interferenceLabel (plannedPermute repair state) =
      labelRelabel (interferenceLabel state)

/-- The hidden states contributing coherently to one orthogonal Step-4 label. -/
def InterferenceFiber {Index Label : Type*}
    (interferenceLabel : CoordinateState Index → Label) (label : Label) :=
  {state // interferenceLabel state = label}

/--
An interference-compatible reversible plan bijects each coherent class with
the corresponding relabeled class.
-/
def interferenceFiberEquiv {Index Label : Type*}
    (repair : ReversiblePlan Index)
    (interferenceLabel : CoordinateState Index → Label)
    (labelRelabel : Label ≃ Label)
    (preserves : PreservesInterferenceClasses repair interferenceLabel labelRelabel)
    (label : Label) :
    InterferenceFiber interferenceLabel label ≃
      InterferenceFiber interferenceLabel (labelRelabel label) where
  toFun state := ⟨plannedPermute repair state.1, by
    rw [preserves state.1, state.2]⟩
  invFun state := ⟨plannedPermute repair state.1, by
    apply labelRelabel.injective
    calc
      labelRelabel (interferenceLabel (plannedPermute repair state.1)) =
          interferenceLabel (plannedPermute repair (plannedPermute repair state.1)) :=
        (preserves (plannedPermute repair state.1)).symm
      _ = interferenceLabel state.1 :=
        congrArg interferenceLabel (plannedPermute_involutive repair state.1)
      _ = labelRelabel label := state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact plannedPermute_involutive repair state.1
  right_inv state := by
    apply Subtype.ext
    exact plannedPermute_involutive repair state.1

/--
A *partial structural* certificate for a map on complete hidden states.

Even an inhabitant of this structure would not by itself prove Lemma 1: the
paper compares probabilities of measured outcomes, whose weights are squared
magnitudes of coherent sums over hidden states.  Injectivity on hidden states
does not imply the required inequality between those weights.  In addition,
an arbitrary cross-group permutation can change the group high-sum labels
`s_j`, so `preserves_interference` is already a substantive prerequisite.

No certificate is constructed here.  The separate measured-outcome
certificate below states the further weighted injection that Lemma 1 needs.
-/
structure LemmaOneRepairCertificate (Index Label : Type*)
    (interferenceLabel : CoordinateState Index → Label)
    (Bad Good : CoordinateState Index → Prop) where
  repair : ReversiblePlan Index
  outcome_coherent : OutcomeCoherent repair
  bad_is_outcome_predicate : DependsOnlyOnMeasuredOutcome Bad
  good_is_outcome_predicate : DependsOnlyOnMeasuredOutcome Good
  labelRelabel : Label ≃ Label
  preserves_interference :
    PreservesInterferenceClasses repair interferenceLabel labelRelabel
  maps_to_good : ∀ state, Bad state → Good (plannedPermute repair state)

/-- A partial structural certificate induces a bad-to-good map on complete hidden states. -/
def certifiedRepair {Index Label : Type*}
    {interferenceLabel : CoordinateState Index → Label}
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index Label interferenceLabel Bad Good) :
    {state // Bad state} → {state // Good state} :=
  restrictedRepair certificate.repair Bad Good certificate.maps_to_good

/-- The hidden-state map is injective; this theorem makes no claim about measured weights. -/
theorem certifiedRepair_injective {Index Label : Type*}
    {interferenceLabel : CoordinateState Index → Label}
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index Label interferenceLabel Bad Good) :
    Function.Injective (certifiedRepair certificate) :=
  restrictedRepair_injective certificate.repair Bad Good certificate.maps_to_good

/-! ## The separate weighted measured-outcome obligation -/

/-- Total nonnegative weight of a finite measured-outcome type. -/
def totalOutcomeWeight {Outcome : Type*} [Fintype Outcome]
    (weight : Outcome → ℝ≥0) : ℝ≥0 :=
  ∑ outcome, weight outcome

/--
The weighted injection actually needed to compare bad and good measured
outcomes.  `BadOutcome` and `GoodOutcome` may be subtypes of a common finite
outcome space.  Weights live in `ℝ≥0`, so outcomes outside the image of
`map` contribute a nonnegative amount to the good total.

For Lemma 1, the weights must be the genuine measured-outcome probabilities
(or a common positive multiple of them), after all coherent sums over hidden
selection strings have been taken.  The pointwise `weight_le` field is not a
consequence of `LemmaOneRepairCertificate` and must be proved separately.
-/
structure MeasuredOutcomeWeightInjectionCertificate
    (BadOutcome GoodOutcome : Type*)
    [Fintype BadOutcome] [Fintype GoodOutcome]
    (badWeight : BadOutcome → ℝ≥0) (goodWeight : GoodOutcome → ℝ≥0) where
  map : BadOutcome → GoodOutcome
  map_injective : Function.Injective map
  weight_le : ∀ outcome, badWeight outcome ≤ goodWeight (map outcome)

/--
An injective pointwise weight-dominating map bounds the total bad measured
weight by the total good measured weight.
-/
theorem bad_totalOutcomeWeight_le_good_totalOutcomeWeight
    {BadOutcome GoodOutcome : Type*}
    [Fintype BadOutcome] [Fintype GoodOutcome]
    {badWeight : BadOutcome → ℝ≥0} {goodWeight : GoodOutcome → ℝ≥0}
    (certificate : MeasuredOutcomeWeightInjectionCertificate
      BadOutcome GoodOutcome badWeight goodWeight) :
    totalOutcomeWeight badWeight ≤ totalOutcomeWeight goodWeight := by
  classical
  unfold totalOutcomeWeight
  calc
    Finset.univ.sum badWeight ≤
        Finset.univ.sum (fun outcome ↦ goodWeight (certificate.map outcome)) :=
      Finset.sum_le_sum fun outcome _ ↦ certificate.weight_le outcome
    _ = (Finset.univ.image certificate.map).sum goodWeight :=
      (Finset.sum_image certificate.map_injective.injOn).symm
    _ ≤ Finset.univ.sum goodWeight :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end SimonDCP.Arithmetic.SwapFiberRepair
