import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Abel

/-!
# Finite one-time-pad counting

This file proves the finite counting fact behind the residue-conditioning
estimate for Lemma 1.  Fix the samples on a coordinate set `A`.  If a Boolean
selection uses at least one coordinate outside `A`, translating that sample
coordinate gives an explicit equivalence between the fibres over any two
residues of a finite additive commutative group.

The result is deterministic.  Randomness enters only when equal fibre sizes
are interpreted as probabilities for a uniform outside sample.
-/

namespace SimonDCP.Probability.OneTimePadCounting

open scoped BigOperators

section FiniteAdditiveGroup

variable {I G : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Coordinates whose samples have already been fixed. -/
abbrev InsideIndex (A : Finset I) := {i : I // i ∈ A}

/-- Coordinates whose samples remain free after fixing `Y_A`. -/
abbrev OutsideIndex (A : Finset I) := {i : I // i ∉ A}

/-- A fixed assignment to the coordinates in `A`. -/
abbrev InsideSample (A : Finset I) (H : Type*) := InsideIndex A → H

/-- A free assignment to the coordinates outside `A`. -/
abbrev OutsideSample (A : Finset I) (H : Type*) := OutsideIndex A → H

/-- Contribution of the fixed coordinates selected by `selection`. -/
def selectedInsideSum
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G) : G :=
  ∑ i : InsideIndex A, if selection i.1 = true then inside i else 0

/-- Contribution of the free coordinates selected by `selection`. -/
def selectedOutsideSum
    (selection : I → Bool) (A : Finset I) (outside : OutsideSample A G) : G :=
  ∑ i : OutsideIndex A, if selection i.1 = true then outside i else 0

/-- The selected sum after combining fixed inside and free outside samples. -/
def completedSelectedSum
    (selection : I → Bool) (A : Finset I)
    (inside : InsideSample A G) (outside : OutsideSample A G) : G :=
  selectedInsideSum selection A inside + selectedOutsideSum selection A outside

/-- A sample supported only at the one-time-pad coordinate `pivot`. -/
def pivotImpulse
    (A : Finset I) (pivot : OutsideIndex A) (shift : G) : OutsideSample A G :=
  fun i => if i = pivot then shift else 0

/-- Translate only the selected outside coordinate `pivot`. -/
def translateOutside
    (A : Finset I) (pivot : OutsideIndex A) (shift : G) :
    OutsideSample A G → OutsideSample A G :=
  fun outside => outside + pivotImpulse A pivot shift

/-- Translation of one outside coordinate is a permutation of outside samples. -/
def translateOutsideEquiv
    (A : Finset I) (pivot : OutsideIndex A) (shift : G) :
    OutsideSample A G ≃ OutsideSample A G where
  toFun := translateOutside A pivot shift
  invFun := translateOutside A pivot (-shift)
  left_inv outside := by
    funext i
    by_cases hi : i = pivot <;>
      simp [translateOutside, pivotImpulse, hi, add_assoc]
  right_inv outside := by
    funext i
    by_cases hi : i = pivot <;>
      simp [translateOutside, pivotImpulse, hi, add_assoc]

omit [Fintype I] [Fintype G] [DecidableEq G] in
@[simp]
theorem translateOutsideEquiv_apply
    (A : Finset I) (pivot : OutsideIndex A) (shift : G)
    (outside : OutsideSample A G) :
    translateOutsideEquiv A pivot shift outside =
      translateOutside A pivot shift outside :=
  rfl

omit [Fintype I] [Fintype G] [DecidableEq G] in
@[simp]
theorem translateOutsideEquiv_symm_apply
    (A : Finset I) (pivot : OutsideIndex A) (shift : G)
    (outside : OutsideSample A G) :
    (translateOutsideEquiv A pivot shift).symm outside =
      translateOutside A pivot (-shift) outside :=
  rfl

omit [Fintype G] [DecidableEq G] in
/-- A selected pivot impulse contributes exactly its shift. -/
theorem selectedOutsideSum_pivotImpulse
    (selection : I → Bool) (A : Finset I) (pivot : OutsideIndex A)
    (hpivot : selection pivot.1 = true) (shift : G) :
    selectedOutsideSum selection A (pivotImpulse A pivot shift) = shift := by
  classical
  unfold selectedOutsideSum
  rw [Finset.sum_eq_single pivot]
  · simp [pivotImpulse, hpivot]
  · intro i _ hi
    simp [pivotImpulse, hi]
  · simp

omit [Fintype G] [DecidableEq G] in
/-- Translating a selected outside pivot adds the shift to the outside sum. -/
theorem selectedOutsideSum_translate
    (selection : I → Bool) (A : Finset I) (pivot : OutsideIndex A)
    (hpivot : selection pivot.1 = true) (shift : G)
    (outside : OutsideSample A G) :
    selectedOutsideSum selection A (translateOutside A pivot shift outside) =
      selectedOutsideSum selection A outside + shift := by
  classical
  unfold selectedOutsideSum translateOutside
  simp only [Pi.add_apply]
  calc
    (∑ i : OutsideIndex A,
        if selection i.1 = true then
          outside i + pivotImpulse A pivot shift i
        else 0) =
        ∑ i : OutsideIndex A,
          ((if selection i.1 = true then outside i else 0) +
            (if selection i.1 = true then pivotImpulse A pivot shift i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : selection i.1 = true <;> simp [hi]
    _ = (∑ i : OutsideIndex A,
          if selection i.1 = true then outside i else 0) +
        (∑ i : OutsideIndex A,
          if selection i.1 = true then pivotImpulse A pivot shift i else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : OutsideIndex A,
          if selection i.1 = true then outside i else 0) + shift := by
      congr 1
      simpa only [selectedOutsideSum] using
        selectedOutsideSum_pivotImpulse selection A pivot hpivot shift

omit [Fintype G] [DecidableEq G] in
/-- The fixed inside contribution is unchanged by the outside translation. -/
theorem completedSelectedSum_translate
    (selection : I → Bool) (A : Finset I)
    (inside : InsideSample A G) (pivot : OutsideIndex A)
    (hpivot : selection pivot.1 = true) (shift : G)
    (outside : OutsideSample A G) :
    completedSelectedSum selection A inside
        (translateOutside A pivot shift outside) =
      completedSelectedSum selection A inside outside + shift := by
  simp only [completedSelectedSum]
  rw [selectedOutsideSum_translate selection A pivot hpivot]
  abel

/-- Outside assignments whose completed selected sum is one fixed residue. -/
def OutsideResidueFibre
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (residue : G) :=
  {outside : OutsideSample A G //
    completedSelectedSum selection A inside outside = residue}

/--
Explicit one-time-pad equivalence between the fibres over two residues.
It translates the pivot sample by `target - source`.
-/
def outsideResidueFibreEquiv
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (pivot : OutsideIndex A) (hpivot : selection pivot.1 = true)
    (source target : G) :
    OutsideResidueFibre selection A inside source ≃
      OutsideResidueFibre selection A inside target where
  toFun outside := ⟨
    translateOutside A pivot (target - source) outside.1,
    by
      rw [completedSelectedSum_translate selection A inside pivot hpivot,
        outside.2]
      abel⟩
  invFun outside := ⟨
    translateOutside A pivot (-(target - source)) outside.1,
    by
      rw [completedSelectedSum_translate selection A inside pivot hpivot,
        outside.2]
      abel⟩
  left_inv outside := by
    apply Subtype.ext
    exact (translateOutsideEquiv A pivot (target - source)).left_inv outside.1
  right_inv outside := by
    apply Subtype.ext
    exact (translateOutsideEquiv A pivot (target - source)).right_inv outside.1

end FiniteAdditiveGroup

end SimonDCP.Probability.OneTimePadCounting
