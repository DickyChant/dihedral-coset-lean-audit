import SimonDCP.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Phase correlation for Walsh characters

This file records a deterministic obstruction to treating certain Walsh phases
as pairwise independent.  If a mask vanishes on a selected set of coordinates,
then changing a bit string only on those coordinates cannot change either its
Walsh dot parity or the associated phase.
-/

namespace SimonDCP.Quantum.PhaseCorrelation

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mod-two dot product used by a Walsh character. -/
def walshDot (mask state : ι → ZMod 2) : ZMod 2 :=
  ∑ i, mask i * state i

/-- The complex sign determined by a mod-two Walsh dot product. -/
def walshPhase (mask state : ι → ZMod 2) : ℂ :=
  (-1 : ℂ) ^ (walshDot mask state).val

/--
Changing a state only on coordinates where the mask is zero leaves its Walsh
dot parity unchanged.
-/
theorem walshDot_eq_of_eq_off_zero_set
    (A : Finset ι) (mask left right : ι → ZMod 2)
    (mask_zero : ∀ i ∈ A, mask i = 0)
    (states_equal : ∀ i ∉ A, left i = right i) :
    walshDot mask left = walshDot mask right := by
  unfold walshDot
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp [mask_zero i hi]
  · rw [states_equal i hi]

/--
Changing a state only on coordinates where the mask is zero also leaves the
associated `(-1)^parity` phase unchanged.
-/
theorem walshPhase_eq_of_eq_off_zero_set
    (A : Finset ι) (mask left right : ι → ZMod 2)
    (mask_zero : ∀ i ∈ A, mask i = 0)
    (states_equal : ∀ i ∉ A, left i = right i) :
    walshPhase mask left = walshPhase mask right := by
  rw [walshPhase, walshPhase,
    walshDot_eq_of_eq_off_zero_set A mask left right mask_zero states_equal]

/--
Concrete four-bit instance: arbitrary changes in coordinates `0` and `1`
cannot affect the phase when the mask vanishes there.
-/
example (mask left right : Fin 4 → ZMod 2)
    (mask_zero_at_zero : mask 0 = 0)
    (mask_zero_at_one : mask 1 = 0)
    (equal_at_two : left 2 = right 2)
    (equal_at_three : left 3 = right 3) :
    walshPhase mask left = walshPhase mask right := by
  apply walshPhase_eq_of_eq_off_zero_set {0, 1} mask left right
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact mask_zero_at_zero
    · exact mask_zero_at_one
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact equal_at_two
    · exact equal_at_three

end SimonDCP.Quantum.PhaseCorrelation
