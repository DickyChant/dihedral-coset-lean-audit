import SimonDCP.Probability.TernarySubsetSumBound
import SimonDCP.Probability.ProjectionInjectivity

/-!
# From ternary collision freeness to subset-sum injectivity

Two distinct Boolean masks with the same subset sum determine a nonzero
ternary relation: use coefficient `+1` on the left-only coordinates, `-1`
on the right-only coordinates, and `0` elsewhere.  This file makes that
elementary bridge explicit and connects the ternary union bound to the
projection-injectivity hypotheses used by restricted Parseval.
-/

namespace SimonDCP.Probability.TernaryProjectionBridge

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernarySubsetSumBound

variable {ι G : Type*}

/-- The ternary coefficient vector obtained by subtracting the indicator of
`right` from the indicator of `left`. -/
def maskDifferenceCoefficient (left right : Mask ι) : TernaryVector ι :=
  fun i =>
    if left i = 0 then
      if right i = 0 then none else some true
    else
      if right i = 0 then some false else none

/-- A single difference coefficient acts as the difference of the two
Boolean indicator terms. -/
theorem ternaryTerm_maskDifferenceCoefficient [AddCommGroup G]
    (left right : Mask ι) (sample : ι → G) (i : ι) :
    ternaryTerm (maskDifferenceCoefficient left right i) (sample i) =
      (if left i = 0 then 0 else sample i) -
        (if right i = 0 then 0 else sample i) := by
  by_cases hleft : left i = 0 <;> by_cases hright : right i = 0 <;>
    simp [maskDifferenceCoefficient, ternaryTerm, hleft, hright]

/-- The ternary sum of the difference vector is exactly the difference of
the two Boolean subset sums. -/
theorem ternarySum_maskDifferenceCoefficient
    [Fintype ι] [AddCommGroup G]
    (left right : Mask ι) (sample : ι → G) :
    ternarySum (maskDifferenceCoefficient left right) sample =
      booleanSubsetSum sample left - booleanSubsetSum sample right := by
  classical
  unfold ternarySum booleanSubsetSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact ternaryTerm_maskDifferenceCoefficient left right sample i

/-- Distinct `ZMod 2` masks give a nonzero difference coefficient vector. -/
theorem maskDifferenceCoefficient_ne_zero
    {left right : Mask ι} (hne : left ≠ right) :
    maskDifferenceCoefficient left right ≠ zeroTernaryVector := by
  intro hzero
  apply hne
  funext i
  have hi := congrFun hzero i
  by_cases hleft : left i = 0
  · by_cases hright : right i = 0
    · exact hleft.trans hright.symm
    · simp [maskDifferenceCoefficient, zeroTernaryVector, hleft, hright] at hi
  · by_cases hright : right i = 0
    · simp [maskDifferenceCoefficient, zeroTernaryVector, hleft, hright] at hi
    · apply ZMod.val_injective 2
      have hleftVal : (left i).val ≠ 0 := (ZMod.val_ne_zero (left i)).2 hleft
      have hrightVal : (right i).val ≠ 0 := (ZMod.val_ne_zero (right i)).2 hright
      have hleftLt : (left i).val < 2 := ZMod.val_lt (left i)
      have hrightLt : (right i).val < 2 := ZMod.val_lt (right i)
      omega

section FiniteIndex

variable [Fintype ι] [DecidableEq ι] [AddCommGroup G]

/-- An equality between two distinct Boolean subset sums is a nontrivial
ternary collision. -/
theorem mem_ternaryCollisionSamples_of_subsetSum_eq
    [Fintype G] [DecidableEq G]
    (sample : ι → G) {left right : Mask ι}
    (hne : left ≠ right)
    (hsum : booleanSubsetSum sample left = booleanSubsetSum sample right) :
    sample ∈ ternaryCollisionSamples (I := ι) (G := G) := by
  rw [mem_ternaryCollisionSamples]
  refine ⟨maskDifferenceCoefficient left right,
    maskDifferenceCoefficient_ne_zero hne, ?_⟩
  rw [ternarySum_maskDifferenceCoefficient, hsum, sub_self]

/-- Ternary-collision freeness implies global injectivity of the Boolean
subset-sum map. -/
theorem booleanSubsetSum_injective_of_not_mem_ternaryCollisionSamples
    [Fintype G] [DecidableEq G]
    (sample : ι → G)
    (hfree : sample ∉ ternaryCollisionSamples (I := ι) (G := G)) :
    Function.Injective (booleanSubsetSum sample) := by
  intro left right hsum
  by_contra hne
  exact hfree (mem_ternaryCollisionSamples_of_subsetSum_eq sample hne hsum)

/-- In particular, ternary-collision freeness implies local subset-sum
injectivity on every prescribed coordinate set. -/
theorem subsetSumInjectiveWithin_of_not_mem_ternaryCollisionSamples
    [Fintype G] [DecidableEq G]
    (fixed : Finset ι) (sample : ι → G)
    (hfree : sample ∉ ternaryCollisionSamples (I := ι) (G := G)) :
    SubsetSumInjectiveWithin fixed sample := by
  intro left right hsum
  have hinjective :=
    booleanSubsetSum_injective_of_not_mem_ternaryCollisionSamples sample hfree
  have hvalues : left.1 = right.1 := hinjective hsum
  exact Subtype.ext hvalues

/-- Samples on which local subset-sum injectivity fails. -/
noncomputable def nonInjectiveWithinSamples
    [Fintype G] [DecidableEq G] (fixed : Finset ι) : Finset (ι → G) := by
  classical
  exact Finset.univ.filter fun sample => ¬ SubsetSumInjectiveWithin fixed sample

@[simp]
theorem mem_nonInjectiveWithinSamples
    [Fintype G] [DecidableEq G] (fixed : Finset ι) (sample : ι → G) :
    sample ∈ nonInjectiveWithinSamples (G := G) fixed ↔
      ¬ SubsetSumInjectiveWithin fixed sample := by
  classical
  simp [nonInjectiveWithinSamples]

/-- Every failure of local subset-sum injectivity is witnessed by a
nontrivial ternary relation. -/
theorem nonInjectiveWithinSamples_subset_ternaryCollisionSamples
    [Fintype G] [DecidableEq G] (fixed : Finset ι) :
    nonInjectiveWithinSamples (G := G) fixed ⊆
      ternaryCollisionSamples (I := ι) (G := G) := by
  intro sample hbad
  rw [mem_nonInjectiveWithinSamples] at hbad
  by_contra hfree
  exact hbad
    (subsetSumInjectiveWithin_of_not_mem_ternaryCollisionSamples fixed sample hfree)

/-- The global ternary bound therefore also bounds the number of samples
with failed local subset-sum injectivity. -/
theorem card_nonInjectiveWithinSamples_le
    [Fintype G] [DecidableEq G] (fixed : Finset ι) :
    (nonInjectiveWithinSamples (G := G) fixed).card ≤
      (3 ^ Fintype.card ι - 1) *
        Fintype.card G ^ (Fintype.card ι - 1) := by
  calc
    (nonInjectiveWithinSamples (G := G) fixed).card ≤
        (ternaryCollisionSamples (I := ι) (G := G)).card :=
      Finset.card_le_card
        (nonInjectiveWithinSamples_subset_ternaryCollisionSamples fixed)
    _ ≤ (3 ^ Fintype.card ι - 1) *
        Fintype.card G ^ (Fintype.card ι - 1) :=
      card_ternaryCollisionSamples_le

/-! ## Local collision bounds

The global bound above is deliberately retained, but it pays for ternary
coefficients on every ambient coordinate.  For the application, only the
coordinates in `fixed` participate in the two subset sums.  The following
equivalence moves the problem to that smaller index type before applying the
ternary union bound.
-/

/-- A mask supported on `fixed` is the same thing as an unrestricted mask
whose index type is the subtype `fixed`. -/
def masksSupportedOnEquivRestrictedMask (fixed : Finset ι) :
    MasksSupportedOn fixed ≃ Mask (↑fixed) where
  toFun selection := fun i => selection.1 i.1
  invFun selection :=
    ⟨fun i => if hi : i ∈ fixed then selection ⟨i, hi⟩ else 0, by
      intro i hi
      simp [hi]⟩
  left_inv selection := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ fixed
    · simp [hi]
    · simp [hi, selection.2 i hi]
  right_inv selection := by
    funext i
    simp [i.2]

/-- Restrict an ambient sample to the coordinates in `fixed`. -/
def restrictedSample (fixed : Finset ι) (sample : ι → G) : ↑fixed → G :=
  fun i => sample i.1

/-- Transporting a supported mask and restricting the sample do not change
its Boolean subset sum. -/
theorem booleanSubsetSum_eq_restricted
    (fixed : Finset ι) (sample : ι → G)
    (selection : MasksSupportedOn fixed) :
    booleanSubsetSum sample selection.1 =
      booleanSubsetSum (restrictedSample fixed sample)
        (masksSupportedOnEquivRestrictedMask fixed selection) := by
  classical
  unfold booleanSubsetSum
  calc
    (∑ i, if selection.1 i = 0 then 0 else sample i) =
        ∑ i ∈ fixed, if selection.1 i = 0 then 0 else sample i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ fixed)
      intro i _ hi
      simp [selection.2 i hi]
    _ = ∑ i : ↑fixed,
        if selection.1 i.1 = 0 then 0 else sample i.1 := by
      exact (Finset.sum_coe_sort fixed
        (fun i => if selection.1 i = 0 then 0 else sample i)).symm
    _ = ∑ i : ↑fixed,
        if (masksSupportedOnEquivRestrictedMask fixed selection) i = 0 then
          0
        else
          restrictedSample fixed sample i := by
      rfl

/-- Local subset-sum injectivity is exactly injectivity of the subset-sum map
on the restricted sample. -/
theorem subsetSumInjectiveWithin_iff_restricted
    (fixed : Finset ι) (sample : ι → G) :
    SubsetSumInjectiveWithin fixed sample ↔
      Function.Injective (booleanSubsetSum (restrictedSample fixed sample)) := by
  constructor
  · intro hinjective left right hsum
    let equivalence := masksSupportedOnEquivRestrictedMask fixed
    have hambient :
        booleanSubsetSum sample (equivalence.symm left).1 =
          booleanSubsetSum sample (equivalence.symm right).1 := by
      rw [booleanSubsetSum_eq_restricted fixed sample (equivalence.symm left),
        booleanSubsetSum_eq_restricted fixed sample (equivalence.symm right)]
      simpa [equivalence] using hsum
    exact equivalence.symm.injective (hinjective hambient)
  · intro hinjective left right hsum
    let equivalence := masksSupportedOnEquivRestrictedMask fixed
    apply equivalence.injective
    apply hinjective
    rw [← booleanSubsetSum_eq_restricted fixed sample left,
      ← booleanSubsetSum_eq_restricted fixed sample right]
    exact hsum

/-- It is enough to exclude ternary collisions on the restricted sample;
ambient coordinates outside `fixed` incur no union-bound cost. -/
theorem subsetSumInjectiveWithin_of_restricted_not_mem_ternaryCollisionSamples
    [Fintype G] [DecidableEq G]
    (fixed : Finset ι) (sample : ι → G)
    (hfree : restrictedSample fixed sample ∉
      ternaryCollisionSamples (I := ↑fixed) (G := G)) :
    SubsetSumInjectiveWithin fixed sample := by
  rw [subsetSumInjectiveWithin_iff_restricted]
  exact booleanSubsetSum_injective_of_not_mem_ternaryCollisionSamples
    (restrictedSample fixed sample) hfree

/-- Restricted samples on which the Boolean subset-sum map is not
injective. -/
noncomputable def localNonInjectiveSamples
    [Fintype G] [DecidableEq G] (fixed : Finset ι) :
    Finset (↑fixed → G) := by
  classical
  exact Finset.univ.filter fun sample =>
    ¬ Function.Injective (booleanSubsetSum sample)

omit [Fintype ι] in
@[simp]
theorem mem_localNonInjectiveSamples
    [Fintype G] [DecidableEq G]
    (fixed : Finset ι) (sample : ↑fixed → G) :
    sample ∈ localNonInjectiveSamples (G := G) fixed ↔
      ¬ Function.Injective (booleanSubsetSum sample) := by
  classical
  simp [localNonInjectiveSamples]

omit [Fintype ι] in
/-- Every locally noninjective restricted sample has a nonzero ternary
collision on the same restricted coordinate type. -/
theorem localNonInjectiveSamples_subset_ternaryCollisionSamples
    [Fintype G] [DecidableEq G] (fixed : Finset ι) :
    localNonInjectiveSamples (G := G) fixed ⊆
      ternaryCollisionSamples (I := ↑fixed) (G := G) := by
  intro sample hbad
  rw [mem_localNonInjectiveSamples] at hbad
  by_contra hfree
  exact hbad
    (booleanSubsetSum_injective_of_not_mem_ternaryCollisionSamples sample hfree)

omit [Fintype ι] in
/-- Paper-facing local count: only the `fixed.card` participating coordinates
appear in the exponent. -/
theorem card_localNonInjectiveSamples_le
    [Fintype G] [DecidableEq G] (fixed : Finset ι) :
    (localNonInjectiveSamples (G := G) fixed).card ≤
      (3 ^ fixed.card - 1) * Fintype.card G ^ (fixed.card - 1) := by
  calc
    (localNonInjectiveSamples (G := G) fixed).card ≤
        (ternaryCollisionSamples (I := ↑fixed) (G := G)).card :=
      Finset.card_le_card
        (localNonInjectiveSamples_subset_ternaryCollisionSamples fixed)
    _ ≤ (3 ^ fixed.card - 1) *
        Fintype.card G ^ (fixed.card - 1) := by
      simpa using
        (card_ternaryCollisionSamples_le (I := ↑fixed) (G := G))

omit [Fintype ι] in
/-- Uniform-probability form of the local bad-event bound. -/
theorem uniform_localNonInjectiveSamples_le
    [Fintype G] [DecidableEq G]
    (fixed : Finset ι) (hfixed : fixed.Nonempty) :
    ((localNonInjectiveSamples (G := G) fixed).card : Rat) /
        (Fintype.card (↑fixed → G) : Rat) ≤
      ((3 ^ fixed.card - 1 : Nat) : Rat) /
        (Fintype.card G : Rat) := by
  letI : Nonempty (↑fixed) := Finset.nonempty_coe_sort.mpr hfixed
  have hcard :
      ((localNonInjectiveSamples (G := G) fixed).card : Rat) ≤
        ((ternaryCollisionSamples (I := ↑fixed) (G := G)).card : Rat) := by
    exact_mod_cast Finset.card_le_card
      (localNonInjectiveSamples_subset_ternaryCollisionSamples fixed)
  have hden : 0 < (Fintype.card (↑fixed → G) : Rat) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card (↑fixed → G))
  calc
    ((localNonInjectiveSamples (G := G) fixed).card : Rat) /
        (Fintype.card (↑fixed → G) : Rat) ≤
      ((ternaryCollisionSamples (I := ↑fixed) (G := G)).card : Rat) /
        (Fintype.card (↑fixed → G) : Rat) := by
          exact (div_le_div_iff_of_pos_right hden).2 hcard
    _ ≤ ((3 ^ fixed.card - 1 : Nat) : Rat) /
        (Fintype.card G : Rat) := by
      simpa using
        (uniform_ternaryCollisionSamples_le (I := ↑fixed) (G := G))

end FiniteIndex

end SimonDCP.Probability.TernaryProjectionBridge
