import Mathlib.Tactic.FinCases
import SimonDCP.Probability.FaultySamplePhase
import SimonDCP.Probability.CoordinateSubcubeProjection

/-!
# Bridge between Boolean selections and binary Walsh masks

The finite conditioning model represents a selection by `I → Bool`, whereas
the restricted-Parseval development represents it by
`Mask I = I → ZMod 2`.  This file gives the coordinatewise equivalence and
proves that it preserves subset sums and coordinate-subcube supports.
-/

namespace SimonDCP.Probability.BooleanMaskBridge

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.FaultySamplePhase

/-- The canonical encoding of one Boolean bit as an element of `ZMod 2`. -/
def boolZModEquiv : Bool ≃ ZMod 2 :=
  finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv

@[simp]
theorem boolZModEquiv_false : boolZModEquiv false = 0 := by
  rfl

@[simp]
theorem boolZModEquiv_true : boolZModEquiv true = 1 := by
  rfl

@[simp]
theorem boolZModEquiv_eq_zero_iff (bit : Bool) :
    boolZModEquiv bit = 0 ↔ bit = false := by
  cases bit <;> simp

@[simp]
theorem boolZModEquiv_ne_zero_iff (bit : Bool) :
    boolZModEquiv bit ≠ 0 ↔ bit = true := by
  cases bit <;> simp

/-- Apply `boolZModEquiv` independently at every selection coordinate. -/
def boolMaskEquiv (I : Type*) : (I → Bool) ≃ Mask I :=
  Equiv.piCongrRight fun _ => boolZModEquiv

@[simp]
theorem boolMaskEquiv_apply (I : Type*) (selection : I → Bool) (i : I) :
    boolMaskEquiv I selection i = boolZModEquiv (selection i) := by
  rfl

@[simp]
theorem boolMaskEquiv_symm_apply (I : Type*) (mask : Mask I) (i : I) :
    (boolMaskEquiv I).symm mask i = boolZModEquiv.symm (mask i) := by
  rfl

section FiniteIndex

variable {I : Type*} [Fintype I]

/-- Boolean and `ZMod 2` encodings select exactly the same sample terms. -/
theorem fullSubsetSum_eq_booleanSubsetSum
    {G : Type*} [AddCommGroup G]
    (sample : I → G) (selection : I → Bool) :
    fullSubsetSum selection sample =
      booleanSubsetSum sample (boolMaskEquiv I selection) := by
  classical
  unfold fullSubsetSum booleanSubsetSum
  apply Finset.sum_congr rfl
  intro i _
  cases hbit : selection i <;>
    simp [boolSelectedTerm, boolMaskEquiv_apply, hbit]

/-- The subset-sum identity stated after pulling a mask back to Booleans. -/
@[simp]
theorem fullSubsetSum_boolMaskEquiv_symm
    {G : Type*} [AddCommGroup G]
    (sample : I → G) (mask : Mask I) :
    fullSubsetSum ((boolMaskEquiv I).symm mask) sample =
      booleanSubsetSum sample mask := by
  rw [fullSubsetSum_eq_booleanSubsetSum]
  simp

/-- Membership in the image of the function equivalence can be pulled back
by its inverse. -/
theorem mem_image_boolMaskEquiv_iff
    (support : Finset (I → Bool)) (mask : Mask I) :
    mask ∈ Finset.image (boolMaskEquiv I) support ↔
      (boolMaskEquiv I).symm mask ∈ support := by
  classical
  constructor
  · intro hmask
    rcases Finset.mem_image.mp hmask with ⟨selection, hselection, rfl⟩
    simpa using hselection
  · intro hmask
    exact Finset.mem_image.mpr
      ⟨(boolMaskEquiv I).symm mask, hmask, (boolMaskEquiv I).apply_symm_apply mask⟩

variable [DecidableEq I]

/-- The coordinate-subcube membership predicates agree under the encoding. -/
@[simp]
theorem mem_maskCoordinateSubcube_boolMaskEquiv_iff
    {free : Finset I} {fixed selection : I → Bool} :
    boolMaskEquiv I selection ∈
        maskCoordinateSubcube free (boolMaskEquiv I fixed) ↔
      selection ∈ coordinateSubcube free fixed := by
  rw [mem_maskCoordinateSubcube_iff, mem_coordinateSubcube_iff]
  constructor
  · intro h i hi
    apply boolZModEquiv.injective
    exact h i hi
  · intro h i hi
    exact congrArg boolZModEquiv (h i hi)

/-- Encoding a Boolean coordinate subcube gives exactly the corresponding
`ZMod 2` mask coordinate subcube. -/
theorem image_coordinateSubcube_eq_maskCoordinateSubcube
    (free : Finset I) (fixed : I → Bool) :
    Finset.image (boolMaskEquiv I) (coordinateSubcube free fixed) =
      maskCoordinateSubcube free (boolMaskEquiv I fixed) := by
  classical
  ext mask
  rw [mem_image_boolMaskEquiv_iff, mem_maskCoordinateSubcube_iff,
    mem_coordinateSubcube_iff]
  constructor
  · intro h i hi
    have hfixed := h i hi
    have hencoded := congrArg boolZModEquiv hfixed
    simpa using hencoded
  · intro h i hi
    apply boolZModEquiv.injective
    have hmask := h i hi
    simpa using hmask

section ResidueFibre

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The Boolean conditioning-side version of a coordinate-subcube residue
fibre. -/
noncomputable def boolCoordinateSubcubeResidueFibre
    (free : Finset I) (fixed : I → Bool)
    (sample : I → G) (residue : G) : Finset (I → Bool) :=
  (coordinateSubcube free fixed).filter fun selection =>
    fullSubsetSum selection sample = residue

@[simp]
theorem mem_boolCoordinateSubcubeResidueFibre_iff
    {free : Finset I} {fixed : I → Bool}
    {sample : I → G} {residue : G} {selection : I → Bool} :
    selection ∈
        boolCoordinateSubcubeResidueFibre free fixed sample residue ↔
      selection ∈ coordinateSubcube free fixed ∧
        fullSubsetSum selection sample = residue := by
  classical
  simp [boolCoordinateSubcubeResidueFibre]

/--
The complete residue-conditioned support is preserved by the Boolean-to-mask
encoding.  This is the support-level interface from finite conditioning to
the restricted-Parseval model.
-/
theorem image_boolCoordinateSubcubeResidueFibre_eq_mask
    (free : Finset I) (fixed : I → Bool)
    (sample : I → G) (residue : G) :
    Finset.image (boolMaskEquiv I)
        (boolCoordinateSubcubeResidueFibre free fixed sample residue) =
      maskCoordinateSubcubeResidueFibre
        free (boolMaskEquiv I fixed) sample residue := by
  classical
  ext mask
  rw [mem_image_boolMaskEquiv_iff,
    mem_boolCoordinateSubcubeResidueFibre_iff,
    mem_maskCoordinateSubcubeResidueFibre_iff]
  constructor
  · rintro ⟨hsubcube, hresidue⟩
    constructor
    · have hencoded :=
        (mem_maskCoordinateSubcube_boolMaskEquiv_iff
          (free := free) (fixed := fixed)
          (selection := (boolMaskEquiv I).symm mask)).2 hsubcube
      simpa using hencoded
    · simpa using hresidue
  · rintro ⟨hsubcube, hresidue⟩
    constructor
    · apply
        (mem_maskCoordinateSubcube_boolMaskEquiv_iff
          (free := free) (fixed := fixed)
          (selection := (boolMaskEquiv I).symm mask)).1
      simpa using hsubcube
    · simpa using hresidue

end ResidueFibre

end FiniteIndex

end SimonDCP.Probability.BooleanMaskBridge
