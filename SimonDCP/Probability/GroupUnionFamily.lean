import SimonDCP.Probability.SimultaneousLocalInjectivity

/-!
# Families of one- and two-group coordinate sets

Lemma 1 needs local subset-sum injectivity on every single coordinate group
and on every union of two groups.  Taking all ordered pairs, including the
diagonal, packages both requirements into one finite family.  This file
records the elementary cardinality estimates needed to apply the simultaneous
local-injectivity bound.
-/

namespace SimonDCP.Probability.GroupUnionFamily

open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.TernarySubsetSumBound

variable {I G Omega : Type*} {N m : Nat}

/-- All unions of two members of an indexed family.  Diagonal pairs are
included, so every individual group is represented as well. -/
def groupUnionFamily [DecidableEq I]
    (groups : Fin N -> Finset I) : Finset (Finset I) :=
  (Finset.univ.product Finset.univ).image
    (fun pair => groups pair.1 ∪ groups pair.2)

/-- Every prescribed pair union occurs in `groupUnionFamily`. -/
theorem union_mem_groupUnionFamily [DecidableEq I]
    (groups : Fin N -> Finset I) (i j : Fin N) :
    groups i ∪ groups j ∈ groupUnionFamily groups := by
  refine Finset.mem_image.mpr ⟨(i, j), ?_, rfl⟩
  simp

/-- Diagonal pairs ensure that every individual group occurs in the family. -/
theorem group_mem_groupUnionFamily [DecidableEq I]
    (groups : Fin N -> Finset I) (i : Fin N) :
    groups i ∈ groupUnionFamily groups := by
  simpa using union_mem_groupUnionFamily groups i i

/-- There are at most `N^2` distinct unions of two groups. -/
theorem card_groupUnionFamily_le [DecidableEq I]
    (groups : Fin N -> Finset I) :
    (groupUnionFamily groups).card <= N ^ 2 := by
  calc
    (groupUnionFamily groups).card <=
        (Finset.univ.product (Finset.univ : Finset (Fin N))).card := by
      exact Finset.card_image_le
    _ = N ^ 2 := by simp [pow_two]

/-- Unions in the family are nonempty when every input group is nonempty. -/
theorem nonempty_of_mem_groupUnionFamily [DecidableEq I]
    (groups : Fin N -> Finset I)
    (hNonempty : ∀ i, (groups i).Nonempty)
    (fixed : Finset I) (hfixed : fixed ∈ groupUnionFamily groups) :
    fixed.Nonempty := by
  rcases Finset.mem_image.mp hfixed with ⟨⟨i, j⟩, _hij, rfl⟩
  exact (hNonempty i).mono Finset.subset_union_left

/-- If each group has at most `m` coordinates, every pair union has at most
`2 * m` coordinates.  No disjointness assumption is required. -/
theorem card_le_two_mul_of_mem_groupUnionFamily [DecidableEq I]
    (groups : Fin N -> Finset I)
    (hCard : ∀ i, (groups i).card <= m)
    (fixed : Finset I) (hfixed : fixed ∈ groupUnionFamily groups) :
    fixed.card <= 2 * m := by
  rcases Finset.mem_image.mp hfixed with ⟨⟨i, j⟩, _hij, rfl⟩
  calc
    (groups i ∪ groups j).card <= (groups i).card + (groups j).card :=
      Finset.card_union_le _ _
    _ <= m + m := Nat.add_le_add (hCard i) (hCard j)
    _ = 2 * m := by omega

section SimultaneousFailure

variable [Fintype Omega] [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The simultaneous local-injectivity estimate specialized to all one- and
two-group coordinate sets.  The ordered-pair presentation contributes at
most `N^2` local events, while each event uses at most `2 * m` coordinates.
-/
theorem mass_groupUnionFailure_le
    (groups : Fin N -> Finset I) (weight : Omega -> Rat)
    (sample : Omega -> I -> G)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hUniform :
      HasUniformLocalMarginals (groupUnionFamily groups) weight sample)
    (hGroupsNonempty : ∀ i, (groups i).Nonempty)
    (hGroupsCard : ∀ i, (groups i).card <= m) :
    finiteMass weight
        (simultaneousLocalFailure (groupUnionFamily groups) sample) <=
      (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) /
          (Fintype.card G : Rat)) := by
  let localBound : Rat :=
    ((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)
  calc
    finiteMass weight
        (simultaneousLocalFailure (groupUnionFamily groups) sample) <=
        ((groupUnionFamily groups).card : Rat) * localBound := by
      exact mass_simultaneousLocalFailure_le_card_mul
        (groupUnionFamily groups) weight sample (2 * m)
        hWeight hUniform
        (nonempty_of_mem_groupUnionFamily groups hGroupsNonempty)
        (card_le_two_mul_of_mem_groupUnionFamily groups hGroupsCard)
    _ <= (N ^ 2 : Rat) * localBound := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_groupUnionFamily_le groups
      · dsimp [localBound]
        positivity
    _ = (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) /
          (Fintype.card G : Rat)) := rfl

end SimultaneousFailure

end SimonDCP.Probability.GroupUnionFamily
