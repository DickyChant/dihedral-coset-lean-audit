import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SimonDCP.Probability.CoordinateSubcubeSupport

/-!
# Fixed phase contributed by faulty samples

In the fault model, the selection bits attached to correct DCP samples are
free, while the bits attached to faulty samples are fixed.  Thus the support
of the selection register is a coordinate subcube.  This file separates the
selected subset sum into

* the coherent sum over the free, correct coordinates, and
* a fixed contribution from the faulty coordinates.

Consequently, faulty samples do not add coherent summation variables.  They
only translate every exponent by the same group element, or equivalently
multiply every additive-character phase by the same factor.
-/

namespace SimonDCP.Probability.FaultySamplePhase

open scoped BigOperators
open SimonDCP.Probability.CoordinateSubcubeSupport

section FixedFaultyContribution

variable {I G : Type*}
  [Fintype I] [DecidableEq I] [AddCommGroup G]

/-- The contribution of one Boolean-selected sample. -/
def boolSelectedTerm (bit : Bool) (value : G) : G :=
  if bit = true then value else 0

/-- The full Boolean subset sum appearing in the measured residue. -/
def fullSubsetSum (selection : I → Bool) (sample : I → G) : G :=
  ∑ i, boolSelectedTerm (selection i) (sample i)

/-- The part of the subset sum whose selection bits remain coherent. -/
def freeSelectedSum
    (free : Finset I) (selection : I → Bool) (sample : I → G) : G :=
  ∑ i, if i ∈ free then boolSelectedTerm (selection i) (sample i) else 0

/--
The contribution of the faulty samples.  It depends on their fixed selection
bits, but not on the free selection variables.
-/
def fixedFaultyContribution
    (free : Finset I) (fixed : I → Bool) (sample : I → G) : G :=
  ∑ i, if i ∈ free then 0 else boolSelectedTerm (fixed i) (sample i)

/--
On a coordinate-subcube support, the full selected sum is the coherent free
sum plus one fixed faulty-sample contribution.
-/
theorem fullSubsetSum_eq_free_add_fixed
    {free : Finset I} {fixed selection : I → Bool} (sample : I → G)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    fullSubsetSum selection sample =
      freeSelectedSum free selection sample +
        fixedFaultyContribution free fixed sample := by
  classical
  rw [freeSelectedSum, fixedFaultyContribution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ free
  · simp [hi, boolSelectedTerm]
  · have hfixed := (mem_coordinateSubcube_iff.mp hselection) i hi
    simp [hi, boolSelectedTerm, hfixed]

/-- The coherent exponent is obtained by subtracting the fixed offset. -/
theorem freeSelectedSum_eq_full_sub_fixed
    {free : Finset I} {fixed selection : I → Bool} (sample : I → G)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    freeSelectedSum free selection sample =
      fullSubsetSum selection sample -
        fixedFaultyContribution free fixed sample := by
  rw [fullSubsetSum_eq_free_add_fixed sample hselection]
  simp

/--
For two supported selections, equality of full residues is exactly equality
of the free phase exponents.  The faulty offset cancels from both sides.
-/
theorem fullSubsetSum_eq_iff_freeSelectedSum_eq
    {free : Finset I} {fixed left right : I → Bool} (sample : I → G)
    (hleft : left ∈ coordinateSubcube free fixed)
    (hright : right ∈ coordinateSubcube free fixed) :
    fullSubsetSum left sample = fullSubsetSum right sample ↔
      freeSelectedSum free left sample = freeSelectedSum free right sample := by
  rw [fullSubsetSum_eq_free_add_fixed sample hleft,
    fullSubsetSum_eq_free_add_fixed sample hright]
  exact add_right_cancel_iff

section AdditiveCharacter

variable {M : Type*} [Monoid M]

/--
An additive character turns the fixed faulty exponent into a common right
factor.  No commutativity assumption on the phase target is needed.
-/
theorem character_fullSubsetSum_eq_free_mul_fixed
    (character : AddChar G M)
    {free : Finset I} {fixed selection : I → Bool} (sample : I → G)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    character (fullSubsetSum selection sample) =
      character (freeSelectedSum free selection sample) *
        character (fixedFaultyContribution free fixed sample) := by
  rw [fullSubsetSum_eq_free_add_fixed sample hselection]
  exact character.map_add_eq_mul _ _

end AdditiveCharacter

section GroupValuedCharacter

variable {M : Type*} [Group M]

/--
For a group-valued phase, equality of full phases is equivalent to equality
of the free phases, because both contain the same cancellable faulty factor.
-/
theorem character_fullSubsetSum_eq_iff_freeSelectedSum_eq
    (character : AddChar G M)
    {free : Finset I} {fixed left right : I → Bool} (sample : I → G)
    (hleft : left ∈ coordinateSubcube free fixed)
    (hright : right ∈ coordinateSubcube free fixed) :
    character (fullSubsetSum left sample) =
        character (fullSubsetSum right sample) ↔
      character (freeSelectedSum free left sample) =
        character (freeSelectedSum free right sample) := by
  rw [character_fullSubsetSum_eq_free_mul_fixed character sample hleft,
    character_fullSubsetSum_eq_free_mul_fixed character sample hright]
  exact mul_right_cancel_iff

end GroupValuedCharacter

end FixedFaultyContribution

end SimonDCP.Probability.FaultySamplePhase
