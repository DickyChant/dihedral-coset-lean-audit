import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import SimonDCP.Probability.AffineResidueCounting
import SimonDCP.Probability.ResidueConditioningAssembly

/-!
# Coordinate-subcube selection supports

A coordinate subcube has a set `free` of Boolean coordinates and fixes every
coordinate outside `free` to a prescribed bit.  This file computes its size,
the number of globally zero selections, and the number of selections that are
exceptional for a local coordinate set `A`.

The exceptional count has a small but important case split.  If a coordinate
outside both `free` and `A` is fixed to `true`, there are no exceptional
selections.  Otherwise there are exactly `2 ^ |free ∩ A|` exceptional
selections, so their mass in the subcube is `2 ^ (-|free \ A|)`.
-/

namespace SimonDCP.Probability.CoordinateSubcubeSupport

open SimonDCP.Probability.AffineResidueCounting
open SimonDCP.Probability.ResidueConditioningAssembly

section CoordinateSubcube

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Boolean masks that agree with `fixed` away from the free coordinates. -/
noncomputable def coordinateSubcube
    (free : Finset I) (fixed : I → Bool) : Finset (I → Bool) := by
  classical
  exact Finset.univ.filter fun selection =>
    ∀ i, i ∉ free → selection i = fixed i

@[simp]
theorem mem_coordinateSubcube_iff
    {free : Finset I} {fixed selection : I → Bool} :
    selection ∈ coordinateSubcube free fixed ↔
      ∀ i, i ∉ free → selection i = fixed i := by
  classical
  simp [coordinateSubcube]

/-- Restriction to the free coordinates parametrizes a coordinate subcube. -/
noncomputable def coordinateSubcubeEquiv
    (free : Finset I) (fixed : I → Bool) :
    {selection // selection ∈ coordinateSubcube free fixed} ≃
      (↥free → Bool) := by
  classical
  refine
    { toFun := fun selection i => selection.1 i.1
      invFun := fun values =>
        ⟨fun i => if hi : i ∈ free then values ⟨i, hi⟩ else fixed i, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply mem_coordinateSubcube_iff.mpr
    intro i hi
    simp [hi]
  · intro selection
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ free
    · simp [hi]
    · simp [hi, (mem_coordinateSubcube_iff.mp selection.2) i hi]
  · intro values
    funext i
    simp [i.2]

/-- A coordinate subcube has one Boolean degree of freedom per free coordinate. -/
@[simp]
theorem card_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) :
    (coordinateSubcube free fixed).card = 2 ^ free.card := by
  classical
  calc
    (coordinateSubcube free fixed).card =
        Fintype.card {selection // selection ∈ coordinateSubcube free fixed} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (↥free → Bool) :=
      Fintype.card_congr (coordinateSubcubeEquiv free fixed)
    _ = 2 ^ free.card := by simp

/-- The zero mask belongs exactly when every fixed coordinate is fixed to zero. -/
@[simp]
theorem zeroSelection_mem_coordinateSubcube_iff
    (free : Finset I) (fixed : I → Bool) :
    zeroSelection ∈ coordinateSubcube free fixed ↔
      ∀ i, i ∉ free → fixed i = false := by
  rw [mem_coordinateSubcube_iff]
  constructor
  · intro hselection i hi
    simpa [zeroSelection] using (hselection i hi).symm
  · intro hfixed i hi
    simpa [zeroSelection] using (hfixed i hi).symm

/-- A coordinate subcube contains either zero or one globally zero mask. -/
theorem zeroSelectionCount_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) :
    zeroSelectionCount (coordinateSubcube free fixed) =
      if (∀ i, i ∉ free → fixed i = false) then 1 else 0 := by
  classical
  by_cases hzero : ∀ i, i ∉ free → fixed i = false
  · rw [if_pos hzero]
    have hmem : zeroSelection ∈ coordinateSubcube free fixed :=
      (zeroSelection_mem_coordinateSubcube_iff free fixed).2 hzero
    unfold zeroSelectionCount
    have hfilter :
        (coordinateSubcube free fixed).filter
            (fun selection => selection = zeroSelection) =
          {zeroSelection} := by
      ext selection
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · rintro rfl
        exact ⟨hmem, rfl⟩
    rw [hfilter]
    simp
  · rw [if_neg hzero]
    have hnotmem : zeroSelection ∉ coordinateSubcube free fixed := by
      intro hmem
      exact hzero ((zeroSelection_mem_coordinateSubcube_iff free fixed).mp hmem)
    unfold zeroSelectionCount
    have hfilter :
        (coordinateSubcube free fixed).filter
            (fun selection => selection = zeroSelection) = ∅ := by
      ext selection
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hselection, rfl⟩
        exact (hnotmem hselection).elim
      · simp
    rw [hfilter]
    simp

/-- In particular, the globally zero selection count is always at most one. -/
theorem zeroSelectionCount_coordinateSubcube_le_one
    (free : Finset I) (fixed : I → Bool) :
    zeroSelectionCount (coordinateSubcube free fixed) ≤ 1 := by
  rw [zeroSelectionCount_coordinateSubcube]
  split <;> simp

/-- A fixed `true` bit outside `A` prevents every exceptional selection. -/
abbrev HasFixedOneOutside
    (free : Finset I) (fixed : I → Bool) (A : Finset I) : Prop :=
  ∃ i, i ∉ free ∧ i ∉ A ∧ fixed i = true

/--
The base mask for exceptional selections: free coordinates outside `A` are
forced to zero, while coordinates outside `free` retain their fixed value.
-/
def exceptionalFixed
    (free : Finset I) (fixed : I → Bool) (A : Finset I) : I → Bool :=
  fun i => if i ∈ free ∧ i ∉ A then false else fixed i

/-- A fixed `true` coordinate outside `A` makes the exceptional set empty. -/
theorem exceptionalSelections_eq_empty_of_hasFixedOneOutside
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (hfixed : HasFixedOneOutside free fixed A) :
    exceptionalSelections (coordinateSubcube free fixed) A = ∅ := by
  classical
  rcases hfixed with ⟨i, hifree, hiA, hfixed⟩
  ext selection
  constructor
  · intro hselection
    have hdata := mem_exceptionalSelections_iff.mp hselection
    have hselected : selection i = true := by
      rw [(mem_coordinateSubcube_iff.mp hdata.1) i hifree, hfixed]
    exact (hdata.2 ⟨⟨i, hiA⟩, hselected⟩).elim
  · simp

/--
Without a conflicting fixed `true` bit, exceptional selections form the
coordinate subcube whose free coordinates are exactly `free ∩ A`.
-/
theorem exceptionalSelections_eq_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (hfixed : ¬ HasFixedOneOutside free fixed A) :
    exceptionalSelections (coordinateSubcube free fixed) A =
      coordinateSubcube (free ∩ A) (exceptionalFixed free fixed A) := by
  classical
  ext selection
  constructor
  · intro hselection
    have hdata := mem_exceptionalSelections_iff.mp hselection
    apply mem_coordinateSubcube_iff.mpr
    intro i hi
    by_cases hifree : i ∈ free
    · have hiA : i ∉ A := by
        intro hiA
        exact hi (Finset.mem_inter.mpr ⟨hifree, hiA⟩)
      have hfalse : selection i = false := by
        cases hvalue : selection i with
        | false => rfl
        | true => exact (hdata.2 ⟨⟨i, hiA⟩, hvalue⟩).elim
      simpa [exceptionalFixed, hifree, hiA] using hfalse
    · have hvalue := (mem_coordinateSubcube_iff.mp hdata.1) i hifree
      simpa [exceptionalFixed, hifree] using hvalue
  · intro hselection
    have hsubcube := mem_coordinateSubcube_iff.mp hselection
    apply mem_exceptionalSelections_iff.mpr
    constructor
    · apply mem_coordinateSubcube_iff.mpr
      intro i hifree
      have hinter : i ∉ free ∩ A := by simp [hifree]
      have hvalue := hsubcube i hinter
      simpa [exceptionalFixed, hifree] using hvalue
    · rintro ⟨pivot, hpivot⟩
      have hinter : pivot.1 ∉ free ∩ A := by simp [pivot.2]
      have hvalue := hsubcube pivot.1 hinter
      by_cases hifree : pivot.1 ∈ free
      · have : selection pivot.1 = false := by
          simpa [exceptionalFixed, hifree, pivot.2] using hvalue
        simp [this] at hpivot
      · have hfixedFalse : fixed pivot.1 = false := by
          cases hbit : fixed pivot.1 with
          | false => rfl
          | true =>
              exact (hfixed ⟨pivot.1, hifree, pivot.2, hbit⟩).elim
        have : selection pivot.1 = false := by
          simpa [exceptionalFixed, hifree, hfixedFalse] using hvalue
        simp [this] at hpivot

/-- Exact exceptional count, including the inconsistent-fixed-bit case. -/
theorem card_exceptionalSelections_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) (A : Finset I) :
    (exceptionalSelections (coordinateSubcube free fixed) A).card =
      if HasFixedOneOutside free fixed A then 0 else 2 ^ (free ∩ A).card := by
  classical
  by_cases hfixed : HasFixedOneOutside free fixed A
  · rw [if_pos hfixed,
      exceptionalSelections_eq_empty_of_hasFixedOneOutside free fixed A hfixed]
    simp
  · rw [if_neg hfixed,
      exceptionalSelections_eq_coordinateSubcube free fixed A hfixed,
      card_coordinateSubcube]

/-- The exceptional selection count never exceeds `2 ^ |free ∩ A|`. -/
theorem card_exceptionalSelections_coordinateSubcube_le
    (free : Finset I) (fixed : I → Bool) (A : Finset I) :
    (exceptionalSelections (coordinateSubcube free fixed) A).card ≤
      2 ^ (free ∩ A).card := by
  rw [card_exceptionalSelections_coordinateSubcube]
  split <;> simp

/--
In the nonempty exceptional case, multiplying its count by
`2 ^ |free \ A|` recovers the full support size.
-/
theorem pow_card_sdiff_mul_card_exceptionalSelections
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (hfixed : ¬ HasFixedOneOutside free fixed A) :
    2 ^ (free \ A).card *
        (exceptionalSelections (coordinateSubcube free fixed) A).card =
      (coordinateSubcube free fixed).card := by
  rw [card_exceptionalSelections_coordinateSubcube, if_neg hfixed,
    card_coordinateSubcube, ← pow_add,
    Finset.card_sdiff_add_card_inter]

/--
Rational form of the exact exceptional mass `2 ^ (-|free \ A|)`.
-/
theorem exceptionalSelections_mass_eq
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (hfixed : ¬ HasFixedOneOutside free fixed A) :
    ((exceptionalSelections (coordinateSubcube free fixed) A).card : ℚ) /
        (coordinateSubcube free fixed).card =
      1 / (2 ^ (free \ A).card : ℚ) := by
  have hsupport : (coordinateSubcube free fixed).card ≠ 0 := by
    rw [card_coordinateSubcube]
    exact pow_ne_zero _ (by decide)
  have hpower : (2 ^ (free \ A).card : ℕ) ≠ 0 :=
    pow_ne_zero _ (by decide)
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hsupport)).2
  field_simp
  exact_mod_cast (by
    simpa [Nat.mul_comm] using
      pow_card_sdiff_mul_card_exceptionalSelections free fixed A hfixed)

/-!
## Parameters for the residue-conditioning bound

The following statements expose the preceding counts through the rational
mass definitions used by `ResidueConditioningAssembly`.  They are the
paper-facing interface for a coordinate-subcube fault support.
-/

/--
For a coordinate subcube, the globally zero selection has mass
`2 ^ (-|free|)` exactly when all fixed coordinates are zero, and otherwise
has mass zero.
-/
theorem zeroSelectionMass_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) :
    zeroSelectionMass (coordinateSubcube free fixed) =
      if (∀ i, i ∉ free → fixed i = false) then
        1 / (2 ^ free.card : ℚ)
      else 0 := by
  classical
  rw [zeroSelectionMass, zeroSelectionCount_coordinateSubcube,
    card_coordinateSubcube]
  by_cases hzero : ∀ i, i ∉ free → fixed i = false
  · rw [if_pos hzero, if_pos hzero]
    norm_num
  · rw [if_neg hzero, if_neg hzero]
    norm_num

/-- The zero-selection mass in the all-fixed-zero branch. -/
theorem zeroSelectionMass_coordinateSubcube_eq_inv_pow
    (free : Finset I) (fixed : I → Bool)
    (hzero : ∀ i, i ∉ free → fixed i = false) :
    zeroSelectionMass (coordinateSubcube free fixed) =
      1 / (2 ^ free.card : ℚ) := by
  rw [zeroSelectionMass_coordinateSubcube, if_pos hzero]

/-- The zero-selection mass when some fixed coordinate is one. -/
theorem zeroSelectionMass_coordinateSubcube_eq_zero
    (free : Finset I) (fixed : I → Bool)
    (hzero : ¬ ∀ i, i ∉ free → fixed i = false) :
    zeroSelectionMass (coordinateSubcube free fixed) = 0 := by
  rw [zeroSelectionMass_coordinateSubcube, if_neg hzero]

/--
If there is no fixed one outside `A`, the exceptional-selection mass is
exactly `2 ^ (-|free \ A|)`.
-/
theorem exceptionalSelectionMass_coordinateSubcube_eq
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (hfixed : ¬ HasFixedOneOutside free fixed A) :
    exceptionalSelectionMass (coordinateSubcube free fixed) A =
      1 / (2 ^ (free \ A).card : ℚ) := by
  simpa [exceptionalSelectionMass] using
    exceptionalSelections_mass_eq free fixed A hfixed

/--
Exact case split for the exceptional-selection mass.  A conflicting fixed
one makes the mass zero; otherwise the dyadic upper bound is attained.
-/
theorem exceptionalSelectionMass_coordinateSubcube
    (free : Finset I) (fixed : I → Bool) (A : Finset I) :
    exceptionalSelectionMass (coordinateSubcube free fixed) A =
      if HasFixedOneOutside free fixed A then 0
      else 1 / (2 ^ (free \ A).card : ℚ) := by
  classical
  by_cases hfixed : HasFixedOneOutside free fixed A
  · rw [if_pos hfixed, exceptionalSelectionMass]
    simp [exceptionalSelections_eq_empty_of_hasFixedOneOutside
      free fixed A hfixed]
  · rw [if_neg hfixed]
    exact exceptionalSelectionMass_coordinateSubcube_eq free fixed A hfixed

/--
For every coordinate subcube, the exceptional-selection mass is at most
`2 ^ (-|free \ A|)`.  The inequality is strict exactly in the conflicting
fixed-one branch.
-/
theorem exceptionalSelectionMass_coordinateSubcube_le
    (free : Finset I) (fixed : I → Bool) (A : Finset I) :
    exceptionalSelectionMass (coordinateSubcube free fixed) A ≤
      1 / (2 ^ (free \ A).card : ℚ) := by
  rw [exceptionalSelectionMass_coordinateSubcube]
  split
  · positivity
  · exact le_rfl

end CoordinateSubcube

end SimonDCP.Probability.CoordinateSubcubeSupport
