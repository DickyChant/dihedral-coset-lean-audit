import Mathlib

/-!
# A four-bit counterexample to adaptive sector-energy normalization

This file formalizes a finite Walsh toy model used in the audit of Lemma 3.
It mirrors the relevant equal-support and first-zero features but does not
instantiate the paper's parameter schedule or prove reachability of this
support in its full experiment.  There are four Boolean coordinates.  A hidden
mask `phi` is valid when exactly one of its first three bits is true; its fourth
bit is arbitrary.  All six valid masks have the same path amplitude.  The
Walsh outcome is a four-bit mask `d`.

For each outcome, the adaptive rule selects its first zero coordinate (using
coordinate three as the default for the all-true mask).  With
`y = (1, 1, 1, 0)`, the sector label is the selected hidden bit unless the
selected coordinate is three, in which case the label is zero.

The unrefined Walsh numerators have total squared magnitude `96`, exactly the
normalization denominator `16 * 6`.  Splitting every Walsh outcome according
to the outcome-dependent sector raises the total squared numerator to `128`.
Consequently the coarse Born mass is one while the adaptive sector energy is
`128 / 96 = 4 / 3`.  This disproves the generic claim that coarse
normalization automatically bounds an adaptive coherent regrouping by one;
it is not a counterexample to the paper-specific asymptotic tail statement.
-/

namespace SimonDCP.Probability.LemmaThreeAdaptiveSectorCounterexample

open scoped BigOperators

/-- The four Boolean coordinates of the finite example. -/
abbrev Coordinate := Fin 4

/-- A four-bit Boolean mask. -/
abbrev Mask := Coordinate -> Bool

/-- The number of true bits among coordinates zero, one, and two. -/
def firstThreeWeight (phi : Mask) : Nat :=
  (if phi 0 = true then 1 else 0) +
  (if phi 1 = true then 1 else 0) +
  (if phi 2 = true then 1 else 0)

/-- A hidden mask is valid exactly when one of its first three bits is true.
The fourth bit is unrestricted, so there are six valid masks. -/
def validHiddenMask (phi : Mask) : Bool :=
  decide (firstThreeWeight phi = 1)

/-- One factor in the Walsh character `(-1)^(phi dot d)`. -/
def walshFactor (phi d : Mask) (coordinate : Coordinate) : Int :=
  if phi coordinate && d coordinate then -1 else 1

/-- The four-bit Walsh sign of a path `phi` at outcome `d`. -/
def walshSign (phi d : Mask) : Int :=
  ∏ coordinate, walshFactor phi d coordinate

/-- The signed numerator of the coarse Walsh amplitude at `d`. -/
def coarseNumerator (d : Mask) : Int :=
  ∑ phi, if validHiddenMask phi = true then walshSign phi d else 0

/-- The first zero coordinate of `d`.  Coordinate three is also the default
when all four coordinates are true. -/
def firstZero (d : Mask) : Coordinate :=
  if d 0 = false then 0
  else if d 1 = false then 1
  else if d 2 = false then 2
  else 3

/-- The fixed public mask `y = (1, 1, 1, 0)`. -/
def publicMaskY (coordinate : Coordinate) : Bool :=
  coordinate != 3

/-- The outcome-dependent sector label.  Since the fourth public bit is zero,
selecting coordinate three always produces the zero sector. -/
def sectorLabel (d phi : Mask) : Bool :=
  phi (firstZero d) && publicMaskY (firstZero d)

/-- Expanded form of the sector rule: use the selected hidden bit in the
first three coordinates and zero in coordinate three. -/
theorem sectorLabel_eq_selected_bit_unless_fourth :
    ∀ d phi : Mask,
      sectorLabel d phi =
        if firstZero d = 3 then false else phi (firstZero d) := by
  native_decide

/-- The signed numerator retained in sector `z` of outcome `d`. -/
def sectorNumerator (d : Mask) (z : Bool) : Int :=
  ∑ phi,
    if validHiddenMask phi = true ∧ sectorLabel d phi = z then
      walshSign phi d
    else 0

/-- There are exactly six equal-amplitude valid hidden masks. -/
theorem validHiddenMask_card :
    (Finset.univ.filter fun phi : Mask => validHiddenMask phi = true).card = 6 := by
  native_decide

/-- The coarse Walsh numerators satisfy the exact Parseval numerator identity.
The value `96` is `16` Walsh outcomes times `6` equal input paths. -/
theorem coarseNumerator_sq_sum :
    (∑ d : Mask, coarseNumerator d ^ 2) = 96 := by
  native_decide

/-- Outcome-dependent sectoring increases the squared-numerator total from
`96` to `128`. -/
theorem adaptiveSectorNumerator_sq_sum :
    (∑ d : Mask, ∑ z : Bool, sectorNumerator d z ^ 2) = 128 := by
  native_decide

/-- The normalized coarse Born mass.  Uniform path amplitudes contribute a
factor `1 / 6`, and the four-bit Walsh transform contributes `1 / 16`, hence
the denominator `96`. -/
def normalizedCoarseMass (d : Mask) : Rat :=
  (coarseNumerator d : Rat) ^ 2 / 96

/-- The normalized energy retained by one adaptive sector. -/
def normalizedAdaptiveSectorEnergy (d : Mask) (z : Bool) : Rat :=
  (sectorNumerator d z : Rat) ^ 2 / 96

/-- The coarse Walsh outcome distribution is normalized. -/
theorem normalizedCoarseMass_sum :
    (∑ d : Mask, normalizedCoarseMass d) = 1 := by
  native_decide

/-- The adaptive sectors have total energy `4/3`, despite the normalized
coarse Born mass. -/
theorem normalizedAdaptiveSectorEnergy_sum :
    (∑ d : Mask, ∑ z : Bool, normalizedAdaptiveSectorEnergy d z) =
      (4 : Rat) / 3 := by
  native_decide

/-- Every Walsh outcome with nonzero coarse numerator contains a zero bit, so
the first-zero selection rule succeeds on every outcome in the coarse Born
support. -/
theorem nonzeroCoarseNumerator_has_zero :
    ∀ d : Mask, coarseNumerator d ≠ 0 → ∃ coordinate, d coordinate = false := by
  native_decide

/-- A direct formulation saying that the selected coordinate is zero on every
outcome in the coarse Born support. -/
theorem firstZero_is_zero_of_nonzeroCoarseNumerator :
    ∀ d : Mask, coarseNumerator d ≠ 0 → d (firstZero d) = false := by
  native_decide

/-- The exact counterexample inequality. -/
theorem adaptiveSectorEnergy_strictly_exceeds_one :
    (1 : Rat) <
      ∑ d : Mask, ∑ z : Bool, normalizedAdaptiveSectorEnergy d z := by
  rw [normalizedAdaptiveSectorEnergy_sum]
  norm_num

end SimonDCP.Probability.LemmaThreeAdaptiveSectorCounterexample
