import SimonDCP.Probability.GroupUnionFamily
import SimonDCP.Probability.LabelledBornPairwiseTail

/-!
# Rectangular coordinate-group partitions

This file isolates the exact-divisibility kernel used by the group-counting
part of the Lemma 1 repair.  The coordinate type is presented as
`Fin N × Fin m`, and group `i` is the complete fibre over first coordinate
`i`.  Consequently there are exactly `N` pairwise-disjoint groups, every
group has exactly `m` coordinates, and the groups cover the whole coordinate
space.

No floor or ceiling convention is hidden here.  A later arithmetic layer must
choose `N` and `m` and prove that the paper's sample count is exactly `N * m`
before transporting these groups to a flat coordinate type.
-/

namespace SimonDCP.Probability.RectangularGroupPartition

open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.TernarySubsetSumBound
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.PairwiseBernoulliTail

variable {N m : Nat}

/-- The exact product-coordinate presentation can be flattened without any
rounding. -/
def rectangularCoordinateEquiv (N m : Nat) :
    Fin N × Fin m ≃ Fin (N * m) :=
  finProdFinEquiv

/-- Group `i` is the complete fibre over first coordinate `i`. -/
def rectangularGroups (N m : Nat) (i : Fin N) :
    Finset (Fin N × Fin m) :=
  ({i} : Finset (Fin N)) ×ˢ Finset.univ

/-- Membership in a rectangular group is determined by the first coordinate. -/
@[simp]
theorem mem_rectangularGroups_iff (i : Fin N) (coordinate : Fin N × Fin m) :
    coordinate ∈ rectangularGroups N m i ↔ coordinate.1 = i := by
  rw [rectangularGroups, Finset.mem_product]
  simp

/-- Every coordinate belongs to the group named by its first coordinate. -/
theorem mem_rectangularGroups_first (coordinate : Fin N × Fin m) :
    coordinate ∈ rectangularGroups N m coordinate.1 := by
  simp

/-- Every rectangular group has exactly `m` coordinates. -/
@[simp]
theorem card_rectangularGroups (i : Fin N) :
    (rectangularGroups N m i).card = m := by
  simp [rectangularGroups]

/-- Positive group width makes every rectangular group nonempty. -/
theorem rectangularGroups_nonempty (hm : 0 < m) (i : Fin N) :
    (rectangularGroups N m i).Nonempty := by
  exact ⟨(i, ⟨0, hm⟩), by simp⟩

/-- Distinct first-coordinate fibres are disjoint. -/
theorem rectangularGroups_disjoint (i j : Fin N) (hij : i ≠ j) :
    Disjoint (rectangularGroups N m i) (rectangularGroups N m j) := by
  rw [Finset.disjoint_left]
  intro coordinate hi hj
  exact hij ((mem_rectangularGroups_iff i coordinate).mp hi |>.symm.trans
    ((mem_rectangularGroups_iff j coordinate).mp hj))

/-- The rectangular groups form a pairwise-disjoint indexed family.  This is
the disjointness interface expected by `LabelledBornPairwiseTail`. -/
theorem rectangularGroups_pairwiseDisjoint :
    ∀ i j : Fin N, i ≠ j →
      Disjoint (rectangularGroups N m i) (rectangularGroups N m j) := by
  exact fun i j hij ↦ rectangularGroups_disjoint i j hij

/-- The rectangular groups cover the entire product coordinate space. -/
theorem biUnion_rectangularGroups :
    (Finset.univ : Finset (Fin N)).biUnion (rectangularGroups N m) =
      Finset.univ := by
  ext coordinate
  simp

/-- Exact group-cardinality data in the function shape consumed by the Born
mean and pair-moment theorems. -/
theorem rectangularGroups_card_eq :
    ∀ i : Fin N, (rectangularGroups N m i).card = m := by
  exact fun i ↦ card_rectangularGroups i

/-- Upper group-cardinality data in the function shape consumed by
`GroupUnionFamily.mass_groupUnionFailure_le`. -/
theorem rectangularGroups_card_le :
    ∀ i : Fin N, (rectangularGroups N m i).card ≤ m := by
  exact fun i ↦ (card_rectangularGroups i).le

/-- Nonemptiness data in the function shape consumed by
`GroupUnionFamily.mass_groupUnionFailure_le`. -/
theorem rectangularGroups_all_nonempty (hm : 0 < m) :
    ∀ i : Fin N, (rectangularGroups N m i).Nonempty := by
  exact fun i ↦ rectangularGroups_nonempty hm i

/-- Any one- or two-group set in the associated union family is nonempty. -/
theorem groupUnionFamily_rectangular_nonempty
    (hm : 0 < m) (fixed : Finset (Fin N × Fin m))
    (hfixed : fixed ∈ groupUnionFamily (rectangularGroups N m)) :
    fixed.Nonempty := by
  exact nonempty_of_mem_groupUnionFamily
    (rectangularGroups N m) (rectangularGroups_all_nonempty hm) fixed hfixed

/-- Any one- or two-group set in the associated union family contains at most
`2 * m` coordinates. -/
theorem groupUnionFamily_rectangular_card_le
    (fixed : Finset (Fin N × Fin m))
    (hfixed : fixed ∈ groupUnionFamily (rectangularGroups N m)) :
    fixed.card ≤ 2 * m := by
  exact card_le_two_mul_of_mem_groupUnionFamily
    (rectangularGroups N m) rectangularGroups_card_le fixed hfixed

section GroupUnionFailure

variable {Omega G : Type*}
  [Fintype Omega] [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The simultaneous local-injectivity union bound specialized to the exact
rectangular partition. -/
theorem mass_rectangularGroupUnionFailure_le
    (weight : Omega → Rat)
    (sample : Omega → (Fin N × Fin m) → G)
    (hWeight : ∀ omega, 0 ≤ weight omega)
    (hUniform :
      HasUniformLocalMarginals
        (groupUnionFamily (rectangularGroups N m)) weight sample)
    (hm : 0 < m) :
    finiteMass weight
        (simultaneousLocalFailure
          (groupUnionFamily (rectangularGroups N m)) sample) ≤
      (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) /
          (Fintype.card G : Rat)) := by
  exact mass_groupUnionFailure_le
    (rectangularGroups N m) weight sample hWeight hUniform
      (rectangularGroups_all_nonempty hm) rectangularGroups_card_le

end GroupUnionFailure

section LabelledBornInterfaces

variable {G Label : Type*}
  [AddCommGroup G] [DecidableEq G]
  [DecidableEq Label]

/-- Rectangular groups directly supply the equal-size hypothesis of the
labelled Born mean theorem. -/
theorem rectangular_groupZeroIndicator_mean_eq
    (free : Finset (Fin N × Fin m))
    (fixed : Mask (Fin N × Fin m))
    (sample : (Fin N × Fin m) → G) (residue : G)
    (label : Mask (Fin N × Fin m) → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hinjective : ∀ index,
      SubsetSumInjectiveWithin
        (free ∩ rectangularGroups N m index) sample) :
    ∀ index,
      weightedMean
          (labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              free fixed sample residue) label)
          (groupZeroIndicator (rectangularGroups N m) index) =
        (1 / 2 : ℚ) ^ m := by
  exact groupZeroIndicator_mean_eq
    (rectangularGroups N m) free fixed sample residue label hsupport
      rectangularGroups_card_eq hinjective

/-- Rectangular groups directly supply the equal-size and pairwise-disjoint
hypotheses of the labelled Born pair-moment theorem. -/
theorem rectangular_groupZeroIndicator_pair_mean_eq
    (free : Finset (Fin N × Fin m))
    (fixed : Mask (Fin N × Fin m))
    (sample : (Fin N × Fin m) → G) (residue : G)
    (label : Mask (Fin N × Fin m) → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hinjective : ∀ left right, left ≠ right →
      SubsetSumInjectiveWithin
        (free ∩
          (rectangularGroups N m left ∪ rectangularGroups N m right))
        sample) :
    ∀ left right, left ≠ right →
      weightedMean
          (labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              free fixed sample residue) label)
          (fun output ↦
            groupZeroIndicator (rectangularGroups N m) left output *
              groupZeroIndicator (rectangularGroups N m) right output) =
        ((1 / 2 : ℚ) ^ m) ^ 2 := by
  exact groupZeroIndicator_pair_mean_eq
    (rectangularGroups N m) free fixed sample residue label hsupport
      rectangularGroups_card_eq rectangularGroups_pairwiseDisjoint hinjective

end LabelledBornInterfaces

end SimonDCP.Probability.RectangularGroupPartition
