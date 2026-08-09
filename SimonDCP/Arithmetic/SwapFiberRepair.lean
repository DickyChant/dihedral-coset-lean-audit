import SimonDCP.Arithmetic.SwapFiber
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.NNReal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype

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

/-! ## Group labels and the obstruction to a within-group repair -/

/-- The subset-sum contribution made by the coordinates in one Step-3 group. -/
def groupContribution {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (state : CoordinateState Index) (group : Group) : ℤ :=
  ∑ i, if groupOf i = group then state.selection i * state.sample i else 0

/-- The complete vector of group contributions, before truncation to the paper's `s_j`. -/
def groupContributionLabel {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (state : CoordinateState Index) : Group → ℤ :=
  fun group ↦ groupContribution groupOf state group

/-- Apply an arbitrary stored summary (for example, high-bit truncation) to each group sum. -/
def summarizedGroupContributionLabel {Index Group Summary : Type*}
    [Fintype Index] [DecidableEq Group] (summary : ℤ → Summary)
    (groupOf : Index → Group) (state : CoordinateState Index) : Group → Summary :=
  fun group ↦ summary (groupContribution groupOf state group)

/-- A coordinate permutation stays inside each Step-3 group. -/
def PreservesGroups {Index Group : Type*}
    (groupOf : Index → Group) (permutation : Equiv.Perm Index) : Prop :=
  ∀ i, groupOf (permutation i) = groupOf i

/-- A coordinate permutation moves each whole group according to one fixed relabeling. -/
def RelabelsGroups {Index Group : Type*} (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group) : Prop :=
  ∀ i, groupOf (permutation i) = groupRelabel (groupOf i)

/-- Relabel a group-indexed vector by precomposition with the inverse permutation. -/
def relabelGroupFunction {Group Value : Type*} (groupRelabel : Group ≃ Group) :
    (Group → Value) ≃ (Group → Value) where
  toFun label group := label (groupRelabel.symm group)
  invFun label group := label (groupRelabel group)
  left_inv label := by
    funext group
    simp
  right_inv label := by
    funext group
    simp

@[simp]
theorem relabelGroupFunction_apply {Group Value : Type*} (groupRelabel : Group ≃ Group)
    (label : Group → Value) (group : Group) :
    relabelGroupFunction groupRelabel label group = label (groupRelabel.symm group) :=
  rfl

/-- A within-group complete-record permutation preserves every group contribution. -/
theorem groupContribution_permute_of_preservesGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (preserves : PreservesGroups groupOf permutation) (state : CoordinateState Index)
    (group : Group) :
    groupContribution groupOf (permuteCoordinates permutation state) group =
      groupContribution groupOf state group := by
  unfold groupContribution
  simp only [permuteCoordinates]
  calc
    (∑ i, if groupOf i = group then
          state.selection (permutation.symm i) * state.sample (permutation.symm i) else 0) =
        (∑ i, if groupOf (permutation.symm i) = group then
          state.selection (permutation.symm i) * state.sample (permutation.symm i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← preserves (permutation.symm i), permutation.apply_symm_apply]
    _ = (∑ i, if groupOf i = group then state.selection i * state.sample i else 0) := by
      simpa using (Equiv.sum_comp permutation.symm
        (fun i : Index ↦ if groupOf i = group then
          state.selection i * state.sample i else 0))

/-- Hence a within-group permutation preserves the whole group-label vector. -/
theorem groupContributionLabel_permute_of_preservesGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (preserves : PreservesGroups groupOf permutation) (state : CoordinateState Index) :
    groupContributionLabel groupOf (permuteCoordinates permutation state) =
      groupContributionLabel groupOf state := by
  funext group
  exact groupContribution_permute_of_preservesGroups groupOf permutation preserves state group

/-- Moving whole groups relabels, rather than changes, their contribution vector. -/
theorem groupContribution_permute_of_relabelsGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (groupRelabel : Group ≃ Group) (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) (group : Group) :
    groupContribution groupOf (permuteCoordinates permutation state) (groupRelabel group) =
      groupContribution groupOf state group := by
  unfold groupContribution
  simp only [permuteCoordinates]
  calc
    (∑ i, if groupOf i = groupRelabel group then
          state.selection (permutation.symm i) * state.sample (permutation.symm i) else 0) =
        (∑ i, if groupOf (permutation.symm i) = group then
          state.selection (permutation.symm i) * state.sample (permutation.symm i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      have hgroup : groupOf i = groupRelabel (groupOf (permutation.symm i)) := by
        simpa using relabels (permutation.symm i)
      rw [hgroup]
      simp only [groupRelabel.injective.eq_iff]
    _ = (∑ i, if groupOf i = group then state.selection i * state.sample i else 0) := by
      simpa using (Equiv.sum_comp permutation.symm
        (fun i : Index ↦ if groupOf i = group then
          state.selection i * state.sample i else 0))

/-- The complete group-label vector transforms by the same fixed group relabeling. -/
theorem groupContributionLabel_permute_of_relabelsGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (groupRelabel : Group ≃ Group) (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) :
    groupContributionLabel groupOf (permuteCoordinates permutation state) =
      relabelGroupFunction groupRelabel (groupContributionLabel groupOf state) := by
  funext group
  change groupContribution groupOf (permuteCoordinates permutation state) group =
    groupContribution groupOf state (groupRelabel.symm group)
  simpa using groupContribution_permute_of_relabelsGroups groupOf permutation groupRelabel relabels
    state (groupRelabel.symm group)

/-- Moving whole groups relabels every pointwise summary of their contributions. -/
theorem summarizedGroupContributionLabel_permute_of_relabelsGroups
    {Index Group Summary : Type*} [Fintype Index] [DecidableEq Group]
    (summary : ℤ → Summary) (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group)
    (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) :
    summarizedGroupContributionLabel summary groupOf
        (permuteCoordinates permutation state) =
      relabelGroupFunction groupRelabel
        (summarizedGroupContributionLabel summary groupOf state) := by
  funext group
  change summary (groupContribution groupOf (permuteCoordinates permutation state) group) =
    summary (groupContribution groupOf state (groupRelabel.symm group))
  congr 1
  simpa using groupContribution_permute_of_relabelsGroups groupOf permutation groupRelabel relabels
    state (groupRelabel.symm group)

/-- A hidden state selecting exactly one coordinate, used to probe group labels. -/
def singleSelectionState {Index : Type*} [DecidableEq Index]
    (sample hadamardOutput : Index → ℤ) (selected : Index) : CoordinateState Index where
  selection i := if i = selected then 1 else 0
  sample := sample
  hadamardOutput := hadamardOutput

/-- A one-coordinate probe contributes its sample exactly to that coordinate's group. -/
theorem groupContribution_singleSelectionState
    {Index Group : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Group]
    (groupOf : Index → Group) (sample hadamardOutput : Index → ℤ)
    (selected : Index) (group : Group) :
    groupContribution groupOf (singleSelectionState sample hadamardOutput selected) group =
      if groupOf selected = group then sample selected else 0 := by
  classical
  unfold groupContribution
  calc
    (∑ i, if groupOf i = group then
        (singleSelectionState sample hadamardOutput selected).selection i *
          (singleSelectionState sample hadamardOutput selected).sample i else 0) =
      ∑ i, if i = selected then
        (if groupOf selected = group then sample selected else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = selected
      · subst i
        simp [singleSelectionState]
      · simp [singleSelectionState, hi]
    _ = if groupOf selected = group then sample selected else 0 := by simp

/-- Permuting a one-coordinate probe moves its contribution to the image coordinate's group. -/
theorem groupContribution_permute_singleSelectionState
    {Index Group : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (sample hadamardOutput : Index → ℤ) (selected : Index) (group : Group) :
    groupContribution groupOf
        (permuteCoordinates permutation (singleSelectionState sample hadamardOutput selected)) group =
      if groupOf (permutation selected) = group then sample selected else 0 := by
  classical
  unfold groupContribution
  simp only [permuteCoordinates, singleSelectionState]
  calc
    (∑ i, if groupOf i = group then
        (if permutation.symm i = selected then 1 else 0) * sample (permutation.symm i) else 0) =
      ∑ i, if i = permutation selected then
        (if groupOf (permutation selected) = group then sample selected else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = permutation selected
      · subst i
        simp
      · have hsymm : permutation.symm i ≠ selected := by
          intro equal
          apply hi
          simpa using congrArg permutation equal
        simp [hi, hsymm]
    _ = if groupOf (permutation selected) = group then sample selected else 0 := by simp

/--
Rigidity of fixed group-label relabeling: if every hidden one-coordinate
selection probe transforms by the same group relabeling and no sample is zero,
then the underlying coordinate permutation must move whole groups according to
that relabeling.
-/
theorem relabelsGroups_of_groupContributionLabel_singleSelection
    {Index Group : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Group]
    (groupOf : Index → Group) (permutation : Equiv.Perm Index)
    (groupRelabel : Group ≃ Group) (sample hadamardOutput : Index → ℤ)
    (sample_ne_zero : ∀ i, sample i ≠ 0)
    (transforms : ∀ selected,
      groupContributionLabel groupOf
          (permuteCoordinates permutation
            (singleSelectionState sample hadamardOutput selected)) =
        relabelGroupFunction groupRelabel
          (groupContributionLabel groupOf
            (singleSelectionState sample hadamardOutput selected))) :
    RelabelsGroups groupOf permutation groupRelabel := by
  intro selected
  have equality := congrFun (transforms selected) (groupRelabel (groupOf selected))
  rw [groupContributionLabel, groupContribution_permute_singleSelectionState] at equality
  rw [relabelGroupFunction_apply] at equality
  change (if groupOf (permutation selected) = groupRelabel (groupOf selected) then
      sample selected else 0) =
    groupContribution groupOf (singleSelectionState sample hadamardOutput selected)
      (groupRelabel.symm (groupRelabel (groupOf selected))) at equality
  rw [Equiv.symm_apply_apply, groupContribution_singleSelectionState] at equality
  simp only [↓reduceIte] at equality
  by_contra not_group
  simp [not_group] at equality
  exact sample_ne_zero selected equality.symm

/--
Rigidity for truncated or otherwise summarized labels.  It is enough that every
one-coordinate sample has a stored summary different from the zero
contribution's summary.
-/
theorem relabelsGroups_of_summarizedLabel_singleSelection
    {Index Group Summary : Type*} [Fintype Index] [DecidableEq Index]
    [DecidableEq Group] (summary : ℤ → Summary) (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group)
    (sample hadamardOutput : Index → ℤ)
    (sample_summary_ne_zero : ∀ i, summary (sample i) ≠ summary 0)
    (transforms : ∀ selected,
      summarizedGroupContributionLabel summary groupOf
          (permuteCoordinates permutation
            (singleSelectionState sample hadamardOutput selected)) =
        relabelGroupFunction groupRelabel
          (summarizedGroupContributionLabel summary groupOf
            (singleSelectionState sample hadamardOutput selected))) :
    RelabelsGroups groupOf permutation groupRelabel := by
  intro selected
  have equality := congrFun (transforms selected) (groupRelabel (groupOf selected))
  rw [summarizedGroupContributionLabel,
    groupContribution_permute_singleSelectionState] at equality
  rw [relabelGroupFunction_apply] at equality
  change summary
      (if groupOf (permutation selected) = groupRelabel (groupOf selected) then
        sample selected else 0) =
    summary (groupContribution groupOf (singleSelectionState sample hadamardOutput selected)
      (groupRelabel.symm (groupRelabel (groupOf selected)))) at equality
  rw [Equiv.symm_apply_apply, groupContribution_singleSelectionState] at equality
  simp only [↓reduceIte] at equality
  by_contra not_group
  simp [not_group] at equality
  exact sample_summary_ne_zero selected equality.symm

/-- A group is selected for `A` in Step 4 exactly when all its measured outputs are zero. -/
def GroupAllZero {Index Group : Type*} (groupOf : Index → Group)
    (state : CoordinateState Index) (group : Group) : Prop :=
  ∀ i, groupOf i = group → state.hadamardOutput i = 0

/-- Number of measured coordinates having a specified output value. -/
def outputValueCount {Index : Type*} [Fintype Index] [DecidableEq ℤ]
    (state : CoordinateState Index) (value : ℤ) : ℕ :=
  (Finset.univ.filter fun i ↦ state.hadamardOutput i = value).card

/-- A within-group complete-record permutation cannot change whether a group is all-zero. -/
theorem groupAllZero_permute_iff_of_preservesGroups
    {Index Group : Type*} (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (preserves : PreservesGroups groupOf permutation)
    (state : CoordinateState Index) (group : Group) :
    GroupAllZero groupOf (permuteCoordinates permutation state) group ↔
      GroupAllZero groupOf state group := by
  constructor
  · intro allZero i hi
    have group_symm : groupOf (permutation.symm i) = group := by
      rw [← preserves (permutation.symm i), permutation.apply_symm_apply]
      exact hi
    simpa only [permuteCoordinates, permutation.symm_apply_apply] using
      allZero (permutation i) (by simpa [preserves i] using hi)
  · intro allZero i hi
    exact allZero (permutation.symm i) (by
      rw [← preserves (permutation.symm i), permutation.apply_symm_apply]
      exact hi)

/-- Moving whole groups bijectively only relabels which groups are all-zero. -/
theorem groupAllZero_permute_iff_of_relabelsGroups
    {Index Group : Type*} (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group)
    (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) (group : Group) :
    GroupAllZero groupOf (permuteCoordinates permutation state) (groupRelabel group) ↔
      GroupAllZero groupOf state group := by
  constructor
  · intro allZero i hi
    simpa only [permuteCoordinates, permutation.symm_apply_apply] using
      allZero (permutation i) (by simpa [relabels i] using congrArg groupRelabel hi)
  · intro allZero i hi
    exact allZero (permutation.symm i) (by
      have hgroup : groupOf i = groupRelabel (groupOf (permutation.symm i)) := by
        simpa using relabels (permutation.symm i)
      rw [hgroup] at hi
      exact groupRelabel.injective hi)

/-- A whole-group move bijects the all-zero groups before and after the move. -/
def allZeroGroupEquivOfRelabelsGroups
    {Index Group : Type*} (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group)
    (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) :
    {group // GroupAllZero groupOf state group} ≃
      {group // GroupAllZero groupOf (permuteCoordinates permutation state) group} where
  toFun group := ⟨groupRelabel group.1,
    (groupAllZero_permute_iff_of_relabelsGroups groupOf permutation groupRelabel relabels
      state group.1).2 group.2⟩
  invFun group := ⟨groupRelabel.symm group.1, by
    apply (groupAllZero_permute_iff_of_relabelsGroups groupOf permutation groupRelabel relabels
      state (groupRelabel.symm group.1)).1
    simpa using group.2⟩
  left_inv group := by
    apply Subtype.ext
    simp
  right_inv group := by
    apply Subtype.ext
    simp

/-- In particular, moving whole groups cannot change the number of all-zero groups. -/
theorem card_allZeroGroups_eq_of_relabelsGroups
    {Index Group : Type*} (groupOf : Index → Group)
    (permutation : Equiv.Perm Index) (groupRelabel : Group ≃ Group)
    (relabels : RelabelsGroups groupOf permutation groupRelabel)
    (state : CoordinateState Index) :
    Nat.card {group // GroupAllZero groupOf state group} =
      Nat.card {group // GroupAllZero groupOf (permuteCoordinates permutation state) group} :=
  Nat.card_congr
    (allZeroGroupEquivOfRelabelsGroups groupOf permutation groupRelabel relabels state)

/-! ## A partial cross-group swap can split one interference class -/

/-- Six coordinates arranged as two groups of three for a concrete interference witness. -/
inductive CrossGroupIndex where
  | a0 | a1 | a2 | b0 | b1 | b2
deriving DecidableEq, Fintype

/-- The `a` coordinates form one group and the `b` coordinates the other. -/
def crossGroupOf : CrossGroupIndex → Bool
  | .a0 | .a1 | .a2 => false
  | .b0 | .b1 | .b2 => true

/-- Distinct samples with collisions `1 + 2 = 3` and `4 + 5 = 9`. -/
def crossGroupSample : CrossGroupIndex → ℤ
  | .a0 => 1
  | .a1 => 2
  | .a2 => 3
  | .b0 => 4
  | .b1 => 5
  | .b2 => 9

/-- Swap just the first coordinate of each group, leaving the other four fixed. -/
def partialCrossGroupSwap : Equiv.Perm CrossGroupIndex where
  toFun
    | .a0 => .b0
    | .b0 => .a0
    | i => i
  invFun
    | .a0 => .b0
    | .b0 => .a0
    | i => i
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- Two measured one-bits, arranged so the partial swap creates one all-zero group. -/
def crossGroupOutput : CrossGroupIndex → ℤ
  | .a0 | .b1 => 1
  | .a1 | .a2 | .b0 | .b2 => 0

/-- First hidden selection: `1 + 2` in group `a`, and `9` in group `b`. -/
def crossGroupLeft : CoordinateState CrossGroupIndex where
  selection
    | .a0 | .a1 | .b2 => 1
    | .a2 | .b0 | .b1 => 0
  sample := crossGroupSample
  hadamardOutput := crossGroupOutput

/-- Second hidden selection: `3` in group `a`, and `4 + 5` in group `b`. -/
def crossGroupRight : CoordinateState CrossGroupIndex where
  selection
    | .a2 | .b0 | .b1 => 1
    | .a0 | .a1 | .b2 => 0
  sample := crossGroupSample
  hadamardOutput := crossGroupOutput

/-- Before the swap both hidden states have the same group-sum interference label `(3, 9)`. -/
theorem crossGroup_labels_equal_before :
    groupContributionLabel crossGroupOf crossGroupLeft =
      groupContributionLabel crossGroupOf crossGroupRight := by
  decide

theorem crossGroup_left_label_after_false :
    groupContributionLabel crossGroupOf
      (permuteCoordinates partialCrossGroupSwap crossGroupLeft) false = 2 := by
  decide

theorem crossGroup_right_label_after_false :
    groupContributionLabel crossGroupOf
      (permuteCoordinates partialCrossGroupSwap crossGroupRight) false = 7 := by
  decide

/-- The partial cross-group swap sends the common input label to two different output labels. -/
theorem crossGroup_labels_ne_after :
    groupContributionLabel crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupLeft) ≠
      groupContributionLabel crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupRight) := by
  intro equal
  have at_false := congrFun equal false
  rw [crossGroup_left_label_after_false, crossGroup_right_label_after_false] at at_false
  norm_num at at_false

/--
Consequently no fixed equivalence of group-sum labels can make this partial
cross-group swap preserve the two hidden states' interference classes.
-/
theorem no_fixed_labelRelabel_for_partialCrossGroupSwap :
    ¬ ∃ labelRelabel : (Bool → ℤ) ≃ (Bool → ℤ),
      groupContributionLabel crossGroupOf
          (permuteCoordinates partialCrossGroupSwap crossGroupLeft) =
        labelRelabel (groupContributionLabel crossGroupOf crossGroupLeft) ∧
      groupContributionLabel crossGroupOf
          (permuteCoordinates partialCrossGroupSwap crossGroupRight) =
        labelRelabel (groupContributionLabel crossGroupOf crossGroupRight) := by
  rintro ⟨labelRelabel, left, right⟩
  apply crossGroup_labels_ne_after
  calc
    groupContributionLabel crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupLeft) =
        labelRelabel (groupContributionLabel crossGroupOf crossGroupLeft) := left
    _ = labelRelabel (groupContributionLabel crossGroupOf crossGroupRight) :=
      congrArg labelRelabel crossGroup_labels_equal_before
    _ = groupContributionLabel crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupRight) := right.symm

/-! ### The same collision survives a high-bit truncation with distinct low parts -/

/-- Base separating the stored high part from the distinct low residues. -/
def crossGroupBase : ℤ := 16

/-- Samples `17, 34, 51, 68, 85, 153`, with distinct residues modulo `16`. -/
def crossGroupTruncatedSample : CrossGroupIndex → ℤ
  | .a0 => 17
  | .a1 => 34
  | .a2 => 51
  | .b0 => 68
  | .b1 => 85
  | .b2 => 153

/-- Quotient by the low-part base, modeling the stored high part. -/
def crossGroupHighSummary (value : ℤ) : ℤ :=
  value / crossGroupBase

def crossGroupTruncatedLeft : CoordinateState CrossGroupIndex where
  selection := crossGroupLeft.selection
  sample := crossGroupTruncatedSample
  hadamardOutput := crossGroupOutput

def crossGroupTruncatedRight : CoordinateState CrossGroupIndex where
  selection := crossGroupRight.selection
  sample := crossGroupTruncatedSample
  hadamardOutput := crossGroupOutput

/-- The six low sample parts are pairwise distinct, as required locally by `D_Y`. -/
theorem crossGroupTruncated_lowParts_injective :
    Function.Injective (fun i ↦ crossGroupTruncatedSample i % crossGroupBase) := by
  decide

/-- The measured mask lies in the paper's `D₀`: it has four zeroes and two ones. -/
theorem crossGroupTruncated_output_counts :
    outputValueCount crossGroupTruncatedLeft 0 = 4 ∧
      outputValueCount crossGroupTruncatedLeft 1 = 2 := by
  decide

/-- Both hidden states have the same truncated group label `(3, 9)` before the swap. -/
theorem crossGroupTruncated_labels_equal_before :
    summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        crossGroupTruncatedLeft =
      summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        crossGroupTruncatedRight := by
  decide

theorem crossGroupTruncated_left_label_after_false :
    summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
      (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedLeft) false = 2 := by
  decide

theorem crossGroupTruncated_right_label_after_false :
    summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
      (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedRight) false = 7 := by
  decide

theorem crossGroupTruncated_labels_ne_after :
    summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedLeft) ≠
      summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedRight) := by
  intro equal
  have at_false := congrFun equal false
  rw [crossGroupTruncated_left_label_after_false,
    crossGroupTruncated_right_label_after_false] at at_false
  norm_num at at_false

/-- No fixed relabeling can repair the truncated interference labels of this swap. -/
theorem no_fixed_truncatedLabelRelabel_for_partialCrossGroupSwap :
    ¬ ∃ labelRelabel : (Bool → ℤ) ≃ (Bool → ℤ),
      summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
          (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedLeft) =
        labelRelabel
          (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
            crossGroupTruncatedLeft) ∧
      summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
          (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedRight) =
        labelRelabel
          (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
            crossGroupTruncatedRight) := by
  rintro ⟨labelRelabel, left, right⟩
  apply crossGroupTruncated_labels_ne_after
  calc
    summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedLeft) =
        labelRelabel
          (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
            crossGroupTruncatedLeft) := left
    _ = labelRelabel
        (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
          crossGroupTruncatedRight) :=
      congrArg labelRelabel crossGroupTruncated_labels_equal_before
    _ = summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf
        (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedRight) := right.symm

/-- Before the swap neither of the two groups is all-zero. -/
theorem crossGroupTruncated_no_allZeroGroup_before :
    ¬ ∃ group, GroupAllZero crossGroupOf crossGroupTruncatedLeft group := by
  rintro ⟨group, allZero⟩
  cases group
  · have := allZero CrossGroupIndex.a0 rfl
    norm_num [crossGroupTruncatedLeft, crossGroupOutput] at this
  · have := allZero CrossGroupIndex.b1 rfl
    norm_num [crossGroupTruncatedLeft, crossGroupOutput] at this

/-- After swapping `a0` with `b0`, group `a` is all-zero. -/
theorem crossGroupTruncated_has_allZeroGroup_after :
    ∃ group, GroupAllZero crossGroupOf
      (permuteCoordinates partialCrossGroupSwap crossGroupTruncatedLeft) group := by
  refine ⟨false, ?_⟩
  intro i hi
  cases i <;>
    simp_all [crossGroupOf, permuteCoordinates, partialCrossGroupSwap,
      crossGroupTruncatedLeft, crossGroupOutput]

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

/-- The concrete partial cross-group involution, viewed as a constant repair plan. -/
def partialCrossGroupRepair : ReversiblePlan CrossGroupIndex where
  plan := fun _ ↦ partialCrossGroupSwap
  reverse_plan := by
    intro state
    ext i
    cases i <;> rfl

/-- Apply the permutation selected by a reversible plan. -/
def plannedPermute {Index : Type*} (repair : ReversiblePlan Index)
    (state : CoordinateState Index) : CoordinateState Index :=
  permuteCoordinates (repair.plan state) state

/-- Every state-dependent permutation selected by a plan stays within groups. -/
def PlanPreservesGroups {Index Group : Type*} (repair : ReversiblePlan Index)
    (groupOf : Index → Group) : Prop :=
  ∀ state, PreservesGroups groupOf (repair.plan state)

/-- Every permutation selected by a plan moves whole groups by one fixed relabeling. -/
def PlanRelabelsGroups {Index Group : Type*} (repair : ReversiblePlan Index)
    (groupOf : Index → Group) (groupRelabel : Group ≃ Group) : Prop :=
  ∀ state, RelabelsGroups groupOf (repair.plan state) groupRelabel

/-- A within-group plan preserves the full vector of Step-3 group contributions. -/
theorem groupContributionLabel_plannedPermute_of_preservesGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (preserves : PlanPreservesGroups repair groupOf) (state : CoordinateState Index) :
    groupContributionLabel groupOf (plannedPermute repair state) =
      groupContributionLabel groupOf state :=
  groupContributionLabel_permute_of_preservesGroups groupOf (repair.plan state)
    (preserves state) state

/-- A within-group plan also preserves the all-zero status of every group. -/
theorem groupAllZero_plannedPermute_iff_of_preservesGroups
    {Index Group : Type*} (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (preserves : PlanPreservesGroups repair groupOf)
    (state : CoordinateState Index) (group : Group) :
    GroupAllZero groupOf (plannedPermute repair state) group ↔
      GroupAllZero groupOf state group :=
  groupAllZero_permute_iff_of_preservesGroups groupOf (repair.plan state)
    (preserves state) state group

/-- A plan that moves whole groups only bijects the all-zero groups. -/
def allZeroGroupEquivOfPlanRelabelsGroups
    {Index Group : Type*} (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (groupRelabel : Group ≃ Group)
    (relabels : PlanRelabelsGroups repair groupOf groupRelabel)
    (state : CoordinateState Index) :
    {group // GroupAllZero groupOf state group} ≃
      {group // GroupAllZero groupOf (plannedPermute repair state) group} :=
  allZeroGroupEquivOfRelabelsGroups groupOf (repair.plan state) groupRelabel
    (relabels state) state

/-- Number of Step-4 all-zero groups in a measured outcome. -/
noncomputable def allZeroGroupCount {Index Group : Type*}
    [Fintype Group] (groupOf : Index → Group) (state : CoordinateState Index) : ℕ := by
  classical
  exact (Finset.univ.filter (GroupAllZero groupOf state)).card

/--
A within-group plan cannot increase the number of all-zero groups, so it cannot
implement the paper's `D_Y^bad`-to-`D_Y^good` step.
-/
theorem allZeroGroupCount_plannedPermute_of_preservesGroups
    {Index Group : Type*} [Fintype Group]
    (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (preserves : PlanPreservesGroups repair groupOf) (state : CoordinateState Index) :
    allZeroGroupCount groupOf (plannedPermute repair state) =
      allZeroGroupCount groupOf state := by
  classical
  unfold allZeroGroupCount
  congr 1
  ext group
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact groupAllZero_plannedPermute_iff_of_preservesGroups repair groupOf preserves state group

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

/-- The cross-group witness states differ only in their erased selection strings. -/
theorem crossGroup_sameMeasuredOutcome :
    SameMeasuredOutcome crossGroupLeft crossGroupRight :=
  ⟨rfl, rfl⟩

theorem crossGroupTruncated_sameMeasuredOutcome :
    SameMeasuredOutcome crossGroupTruncatedLeft crossGroupTruncatedRight :=
  ⟨rfl, rfl⟩

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
An outcome-coherent plan sends hidden representatives of the same measured
outcome to representatives of the same measured outcome.  This is the
well-definedness fact needed before the hidden-state permutation can descend
to a map on measured outcomes.
-/
theorem plannedPermute_sameMeasuredOutcome {Index : Type*}
    (repair : ReversiblePlan Index) (coherent : OutcomeCoherent repair)
    {left right : CoordinateState Index}
    (same : SameMeasuredOutcome left right) :
    SameMeasuredOutcome (plannedPermute repair left) (plannedPermute repair right) := by
  rcases same with ⟨sample_eq, output_eq⟩
  unfold plannedPermute permuteCoordinates
  rw [coherent left right ⟨sample_eq, output_eq⟩]
  constructor
  · funext i
    exact congrFun sample_eq ((repair.plan right).symm i)
  · funext i
    exact congrFun output_eq ((repair.plan right).symm i)

/-- Equality of measured records is an equivalence relation on hidden states. -/
def sameMeasuredOutcomeSetoid (Index : Type*) : Setoid (CoordinateState Index) where
  r := SameMeasuredOutcome
  iseqv := {
    refl := fun _ ↦ ⟨rfl, rfl⟩
    symm := fun ⟨sample_eq, output_eq⟩ ↦ ⟨sample_eq.symm, output_eq.symm⟩
    trans := fun ⟨sample_left, output_left⟩ ⟨sample_right, output_right⟩ ↦
      ⟨sample_left.trans sample_right, output_left.trans output_right⟩ }

/-- A measured outcome is a hidden coordinate state modulo its selection string. -/
abbrev MeasuredOutcome (Index : Type*) :=
  Quotient (sameMeasuredOutcomeSetoid Index)

/-- Project a complete hidden state to its measured outcome. -/
def measuredOutcome {Index : Type*} (state : CoordinateState Index) :
    MeasuredOutcome Index :=
  Quotient.mk (sameMeasuredOutcomeSetoid Index) state

/-- Lift a hidden-state predicate that depends only on measured data to outcomes. -/
def measuredOutcomePredicate {Index : Type*}
    (predicate : CoordinateState Index → Prop)
    (depends : DependsOnlyOnMeasuredOutcome predicate) : MeasuredOutcome Index → Prop :=
  Quotient.lift predicate (fun left right same ↦ propext (depends left right same))

/-- The lifted predicate has its expected value on a hidden representative. -/
theorem measuredOutcomePredicate_mk {Index : Type*}
    (predicate : CoordinateState Index → Prop)
    (depends : DependsOnlyOnMeasuredOutcome predicate) (state : CoordinateState Index) :
    measuredOutcomePredicate predicate depends (measuredOutcome state) = predicate state :=
  rfl

/--
An outcome-coherent hidden-state repair induces an actual map on measured
outcomes, independently of the chosen hidden selection-string representative.
-/
def plannedMeasuredOutcome {Index : Type*} (repair : ReversiblePlan Index)
    (coherent : OutcomeCoherent repair) : MeasuredOutcome Index → MeasuredOutcome Index :=
  Quotient.map (plannedPermute repair)
    (fun _ _ same ↦ plannedPermute_sameMeasuredOutcome repair coherent same)

/-- The induced map agrees with the hidden-state repair on every representative. -/
theorem plannedMeasuredOutcome_mk {Index : Type*} (repair : ReversiblePlan Index)
    (coherent : OutcomeCoherent repair) (state : CoordinateState Index) :
    plannedMeasuredOutcome repair coherent (measuredOutcome state) =
      measuredOutcome (plannedPermute repair state) :=
  rfl

/-- The map induced on measured outcomes is an involution. -/
theorem plannedMeasuredOutcome_involutive {Index : Type*}
    (repair : ReversiblePlan Index) (coherent : OutcomeCoherent repair) :
    Function.Involutive (plannedMeasuredOutcome repair coherent) := by
  intro outcome
  refine Quotient.inductionOn outcome ?_
  intro state
  change plannedMeasuredOutcome repair coherent
      (plannedMeasuredOutcome repair coherent (measuredOutcome state)) = measuredOutcome state
  rw [plannedMeasuredOutcome_mk, plannedMeasuredOutcome_mk,
    plannedPermute_involutive repair]

/-- Hence an outcome-coherent reversible plan bijects measured outcomes. -/
theorem plannedMeasuredOutcome_bijective {Index : Type*}
    (repair : ReversiblePlan Index) (coherent : OutcomeCoherent repair) :
    Function.Bijective (plannedMeasuredOutcome repair coherent) :=
  (plannedMeasuredOutcome_involutive repair coherent).bijective

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

/--
If two hidden states share an interference label but their repaired images do
not, no fixed label equivalence can make the repair preserve interference
classes.
-/
theorem no_preservesInterferenceClasses_of_collision
    {Index Label : Type*} (repair : ReversiblePlan Index)
    (interferenceLabel : CoordinateState Index → Label)
    (left right : CoordinateState Index)
    (labels_equal : interferenceLabel left = interferenceLabel right)
    (image_labels_ne : interferenceLabel (plannedPermute repair left) ≠
      interferenceLabel (plannedPermute repair right)) :
    ¬ ∃ labelRelabel : Label ≃ Label,
      PreservesInterferenceClasses repair interferenceLabel labelRelabel := by
  rintro ⟨labelRelabel, preserves⟩
  apply image_labels_ne
  calc
    interferenceLabel (plannedPermute repair left) =
        labelRelabel (interferenceLabel left) := preserves left
    _ = labelRelabel (interferenceLabel right) := congrArg labelRelabel labels_equal
    _ = interferenceLabel (plannedPermute repair right) := (preserves right).symm

/-- The constant partial cross-group repair is independent of the hidden selection string. -/
theorem partialCrossGroupRepair_outcomeCoherent :
    OutcomeCoherent partialCrossGroupRepair := by
  intro left right same
  rfl

/--
Despite reversibility and outcome coherence, the partial cross-group repair
cannot preserve the concrete truncated interference classes through any fixed
label equivalence.
-/
theorem partialCrossGroupRepair_not_preserves_truncatedInterference :
    ¬ ∃ labelRelabel : (Bool → ℤ) ≃ (Bool → ℤ),
      PreservesInterferenceClasses partialCrossGroupRepair
        (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf)
        labelRelabel := by
  apply no_preservesInterferenceClasses_of_collision partialCrossGroupRepair
    (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf)
    crossGroupTruncatedLeft crossGroupTruncatedRight
    crossGroupTruncated_labels_equal_before
  simpa only [plannedPermute, partialCrossGroupRepair] using
    crossGroupTruncated_labels_ne_after

/-- A within-group plan preserves the group-contribution interference labels exactly. -/
theorem preservesInterferenceClasses_groupContributionLabel
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (preserves : PlanPreservesGroups repair groupOf) :
    PreservesInterferenceClasses repair (groupContributionLabel groupOf) (Equiv.refl _) := by
  intro state
  exact groupContributionLabel_plannedPermute_of_preservesGroups repair groupOf preserves state

/--
A plan that moves whole groups by a fixed permutation preserves the group-sum
interference classes by that same fixed relabeling.
-/
theorem preservesInterferenceClasses_groupContributionLabel_of_relabelsGroups
    {Index Group : Type*} [Fintype Index] [DecidableEq Group]
    (repair : ReversiblePlan Index) (groupOf : Index → Group)
    (groupRelabel : Group ≃ Group)
    (relabels : PlanRelabelsGroups repair groupOf groupRelabel) :
    PreservesInterferenceClasses repair (groupContributionLabel groupOf)
      (relabelGroupFunction groupRelabel) := by
  intro state
  exact groupContributionLabel_permute_of_relabelsGroups groupOf (repair.plan state)
    groupRelabel (relabels state) state

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

/-- No choice of bad/good predicates can complete the concrete mixed-group plan to a certificate. -/
theorem no_certificate_with_partialCrossGroupRepair
    (Bad Good : CoordinateState CrossGroupIndex → Prop) :
    ¬ ∃ certificate : LemmaOneRepairCertificate CrossGroupIndex (Bool → ℤ)
        (summarizedGroupContributionLabel crossGroupHighSummary crossGroupOf) Bad Good,
      certificate.repair = partialCrossGroupRepair := by
  rintro ⟨certificate, repair_eq⟩
  apply partialCrossGroupRepair_not_preserves_truncatedInterference
  refine ⟨certificate.labelRelabel, ?_⟩
  rw [← repair_eq]
  exact certificate.preserves_interference

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

/-! ## Rigidity of a certificate with the paper's group-sum labels -/

/--
Outcome coherence lets us vary the erased selection string while keeping the
certificate's chosen permutation fixed.  The one-coordinate probes above then
show that, for nonzero samples, a certificate whose fixed label equivalence is
a group relabeling must move whole groups by that same relabeling.
-/
theorem certificate_plan_relabelsGroups_of_nonzero_samples
    {Index Group : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Group]
    (groupOf : Index → Group) {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index (Group → ℤ)
      (groupContributionLabel groupOf) Bad Good)
    (groupRelabel : Group ≃ Group)
    (labelRelabel_eq : certificate.labelRelabel = relabelGroupFunction groupRelabel)
    (state : CoordinateState Index) (sample_ne_zero : ∀ i, state.sample i ≠ 0) :
    RelabelsGroups groupOf (certificate.repair.plan state) groupRelabel := by
  apply relabelsGroups_of_groupContributionLabel_singleSelection groupOf
    (certificate.repair.plan state) groupRelabel state.sample state.hadamardOutput
    sample_ne_zero
  intro selected
  let probe := singleSelectionState state.sample state.hadamardOutput selected
  have same : SameMeasuredOutcome probe state := ⟨rfl, rfl⟩
  have plan_eq := certificate.outcome_coherent probe state same
  have preserves := certificate.preserves_interference probe
  unfold plannedPermute at preserves
  rw [plan_eq, labelRelabel_eq] at preserves
  exact preserves

/--
Consequently, such a certificate cannot change the number of all-zero groups
on any measured outcome whose Fourier samples are all nonzero.
-/
theorem certificate_card_allZeroGroups_eq_of_nonzero_samples
    {Index Group : Type*} [Fintype Index] [DecidableEq Index] [DecidableEq Group]
    (groupOf : Index → Group) {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index (Group → ℤ)
      (groupContributionLabel groupOf) Bad Good)
    (groupRelabel : Group ≃ Group)
    (labelRelabel_eq : certificate.labelRelabel = relabelGroupFunction groupRelabel)
    (state : CoordinateState Index) (sample_ne_zero : ∀ i, state.sample i ≠ 0) :
    Nat.card {group // GroupAllZero groupOf state group} =
      Nat.card {group // GroupAllZero groupOf (plannedPermute certificate.repair state) group} :=
  card_allZeroGroups_eq_of_relabelsGroups groupOf (certificate.repair.plan state)
    groupRelabel
    (certificate_plan_relabelsGroups_of_nonzero_samples groupOf certificate groupRelabel
      labelRelabel_eq state sample_ne_zero)
    state

/--
The certificate rigidity theorem for an arbitrary stored summary of each group
sum.  This applies to high-bit labels exactly on outcomes where every
one-coordinate sample is distinguishable from zero by that truncation.
-/
theorem certificate_plan_relabelsGroups_of_distinguishing_summary
    {Index Group Summary : Type*} [Fintype Index] [DecidableEq Index]
    [DecidableEq Group] (summary : ℤ → Summary) (groupOf : Index → Group)
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index (Group → Summary)
      (summarizedGroupContributionLabel summary groupOf) Bad Good)
    (groupRelabel : Group ≃ Group)
    (labelRelabel_eq : certificate.labelRelabel = relabelGroupFunction groupRelabel)
    (state : CoordinateState Index)
    (sample_summary_ne_zero : ∀ i, summary (state.sample i) ≠ summary 0) :
    RelabelsGroups groupOf (certificate.repair.plan state) groupRelabel := by
  apply relabelsGroups_of_summarizedLabel_singleSelection summary groupOf
    (certificate.repair.plan state) groupRelabel state.sample state.hadamardOutput
    sample_summary_ne_zero
  intro selected
  let probe := singleSelectionState state.sample state.hadamardOutput selected
  have same : SameMeasuredOutcome probe state := ⟨rfl, rfl⟩
  have plan_eq := certificate.outcome_coherent probe state same
  have preserves := certificate.preserves_interference probe
  unfold plannedPermute at preserves
  rw [plan_eq, labelRelabel_eq] at preserves
  exact preserves

/-- Such a summarized-label certificate cannot change the all-zero-group cardinality. -/
theorem certificate_card_allZeroGroups_eq_of_distinguishing_summary
    {Index Group Summary : Type*} [Fintype Index] [DecidableEq Index]
    [DecidableEq Group] (summary : ℤ → Summary) (groupOf : Index → Group)
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index (Group → Summary)
      (summarizedGroupContributionLabel summary groupOf) Bad Good)
    (groupRelabel : Group ≃ Group)
    (labelRelabel_eq : certificate.labelRelabel = relabelGroupFunction groupRelabel)
    (state : CoordinateState Index)
    (sample_summary_ne_zero : ∀ i, summary (state.sample i) ≠ summary 0) :
    Nat.card {group // GroupAllZero groupOf state group} =
      Nat.card {group // GroupAllZero groupOf (plannedPermute certificate.repair state) group} :=
  card_allZeroGroups_eq_of_relabelsGroups groupOf (certificate.repair.plan state)
    groupRelabel
    (certificate_plan_relabelsGroups_of_distinguishing_summary summary groupOf certificate
      groupRelabel labelRelabel_eq state sample_summary_ne_zero)
    state

/-- The induced measured-outcome map sends every bad outcome to a good outcome. -/
theorem certifiedPlannedMeasuredOutcome_maps_to_good {Index Label : Type*}
    {interferenceLabel : CoordinateState Index → Label}
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index Label interferenceLabel Bad Good)
    (outcome : MeasuredOutcome Index) :
    measuredOutcomePredicate Bad certificate.bad_is_outcome_predicate outcome →
      measuredOutcomePredicate Good certificate.good_is_outcome_predicate
        (plannedMeasuredOutcome certificate.repair certificate.outcome_coherent outcome) := by
  refine Quotient.inductionOn outcome ?_
  intro state bad
  exact certificate.maps_to_good state bad

/--
A structural repair certificate therefore descends to an injective bad-to-good
map on measured outcomes.  Establishing its pointwise probability-weight bound
is the separate obligation represented below.
-/
def certifiedMeasuredRepair {Index Label : Type*}
    {interferenceLabel : CoordinateState Index → Label}
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index Label interferenceLabel Bad Good) :
    {outcome // measuredOutcomePredicate Bad certificate.bad_is_outcome_predicate outcome} →
      {outcome // measuredOutcomePredicate Good certificate.good_is_outcome_predicate outcome} :=
  fun outcome ↦
    ⟨plannedMeasuredOutcome certificate.repair certificate.outcome_coherent outcome.1,
      certifiedPlannedMeasuredOutcome_maps_to_good certificate outcome.1 outcome.2⟩

/-- The descended bad-to-good map on measured outcomes is injective. -/
theorem certifiedMeasuredRepair_injective {Index Label : Type*}
    {interferenceLabel : CoordinateState Index → Label}
    {Bad Good : CoordinateState Index → Prop}
    (certificate : LemmaOneRepairCertificate Index Label interferenceLabel Bad Good) :
    Function.Injective (certifiedMeasuredRepair certificate) := by
  intro left right equal
  apply Subtype.ext
  exact (plannedMeasuredOutcome_bijective certificate.repair certificate.outcome_coherent).1
    (congrArg Subtype.val equal)

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
