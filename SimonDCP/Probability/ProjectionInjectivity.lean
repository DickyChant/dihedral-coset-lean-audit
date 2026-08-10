import SimonDCP.Probability.LabelledParseval

/-!
# Projection injectivity and exact restricted Parseval

This file isolates a sufficient condition under which the diagonal lower
bound in restricted Parseval is an equality.  A finite support is
projection-injective relative to `fixed` when two supported masks agreeing
outside `fixed` must be equal.  Consequently, every projection fibre has one
point and the projection-collision count is exactly the support cardinality.

The final section packages the condition for Boolean subset sums in a finite
additive group.  It deliberately separates the deterministic implication
from any probabilistic claim that random samples satisfy the injectivity
hypothesis.
-/

namespace SimonDCP.Probability.ProjectionInjectivity

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval

variable {ι Label : Type*} [Fintype ι] [DecidableEq ι]

local instance projectionAgreeOutsideDecidable (fixed : Finset ι) :
    DecidableRel (AgreeOutside fixed) := fun _ _ => by
  unfold AgreeOutside
  infer_instance

/-- No two distinct supported masks have the same projection to the
coordinates outside `fixed`. -/
def ProjectionInjective
    (fixed : Finset ι) (support : Finset (Mask ι)) : Prop :=
  ∀ ⦃phi⦄, phi ∈ support → ∀ ⦃psi⦄, psi ∈ support →
    AgreeOutside fixed phi psi → phi = psi

omit [Fintype ι] [DecidableEq ι] in
/-- With no hidden coordinates, agreement outside `fixed` is ordinary
function equality. -/
theorem projectionInjective_empty (support : Finset (Mask ι)) :
    ProjectionInjective ∅ support := by
  intro phi hphi psi hpsi hagree
  funext i
  exact hagree i (by simp)

omit [Fintype ι] [DecidableEq ι] in
/-- Projection injectivity is inherited by a smaller finite support. -/
theorem ProjectionInjective.mono
    {fixed : Finset ι} {large small : Finset (Mask ι)}
    (hinjective : ProjectionInjective fixed large) (hsub : small ⊆ large) :
    ProjectionInjective fixed small := by
  intro phi hphi psi hpsi hagree
  exact hinjective (hsub hphi) (hsub hpsi) hagree

/-- Under projection injectivity, the support points agreeing outside
`fixed` with a given supported point form its singleton. -/
theorem filter_agreeOutside_eq_single
    (fixed : Finset ι) (support : Finset (Mask ι))
    (hinjective : ProjectionInjective fixed support)
    {phi : Mask ι} (hphi : phi ∈ support) :
    support.filter (fun psi => AgreeOutside fixed phi psi) = {phi} := by
  classical
  ext psi
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hpsi, hagree⟩
    exact (hinjective hphi hpsi hagree).symm
  · rintro rfl
    exact ⟨hphi, fun _ _ => rfl⟩

/-- Projection injectivity removes every off-diagonal contribution from the
projection-collision count. -/
theorem projectionCollisionCount_eq_card
    (fixed : Finset ι) (support : Finset (Mask ι))
    (hinjective : ProjectionInjective fixed support) :
    projectionCollisionCount fixed support = support.card := by
  classical
  unfold projectionCollisionCount
  calc
    (∑ phi ∈ support,
        (support.filter fun psi => AgreeOutside fixed phi psi).card) =
        ∑ phi ∈ support, 1 := by
      apply Finset.sum_congr rfl
      intro phi hphi
      rw [filter_agreeOutside_eq_single fixed support hinjective hphi]
      simp
    _ = support.card := by simp

/-- Exact unit-coefficient restricted Parseval under projection injectivity. -/
theorem restricted_parseval_unit_eq_diagonal
    (fixed : Finset ι) (support : Finset (Mask ι))
    (hinjective : ProjectionInjective fixed support) :
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support (fun _ => 1) mask) ^ 2) =
      (2 : ℤ) ^ (Fintype.card ι - fixed.card) * support.card := by
  rw [restricted_parseval_unit,
    projectionCollisionCount_eq_card fixed support hinjective]
  congr 1
  exact_mod_cast card_masksVanishingOn fixed

section Labelled

variable [DecidableEq Label]

/-- Every occupied complete-label fibre is projection-injective. -/
def LabelwiseProjectionInjective
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) : Prop :=
  ∀ labelValue ∈ occupiedLabels support label,
    ProjectionInjective fixed (labelFibre support label labelValue)

omit [Fintype ι] [DecidableEq ι] in
/-- Empty-coordinate projection injectivity holds in every label fibre. -/
theorem labelwiseProjectionInjective_empty
    (support : Finset (Mask ι)) (label : Mask ι → Label) :
    LabelwiseProjectionInjective ∅ support label := by
  intro labelValue hlabelValue
  exact projectionInjective_empty (labelFibre support label labelValue)

/-- Under labelwise projection injectivity, the total labelled collision
count consists exactly of the diagonal pairs. -/
theorem sum_projectionCollisionCount_labelFibre_eq_card
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label)
    (hinjective : LabelwiseProjectionInjective fixed support label) :
    ∑ labelValue ∈ occupiedLabels support label,
        projectionCollisionCount fixed
          (labelFibre support label labelValue) = support.card := by
  calc
    (∑ labelValue ∈ occupiedLabels support label,
        projectionCollisionCount fixed
          (labelFibre support label labelValue)) =
        ∑ labelValue ∈ occupiedLabels support label,
          (labelFibre support label labelValue).card := by
      apply Finset.sum_congr rfl
      intro labelValue hlabelValue
      exact projectionCollisionCount_eq_card fixed
        (labelFibre support label labelValue)
        (hinjective labelValue hlabelValue)
    _ = support.card := sum_card_labelFibre support label

/-- Exact labelled restricted Parseval when complete-label fibres have no
off-diagonal projection collisions. -/
theorem labelled_restricted_parseval_eq_diagonal
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label)
    (hinjective : LabelwiseProjectionInjective fixed support label) :
    (∑ mask : MasksVanishingOn fixed,
        labelledSquaredAmplitude support label mask) =
      (2 : ℤ) ^ (Fintype.card ι - fixed.card) * support.card := by
  rw [labelled_restricted_parseval]
  have hcollisions :
      (∑ labelValue ∈ occupiedLabels support label,
        (projectionCollisionCount fixed
          (labelFibre support label labelValue) : ℤ)) = support.card := by
    exact_mod_cast sum_projectionCollisionCount_labelFibre_eq_card
      fixed support label hinjective
  rw [hcollisions]
  congr 1
  exact_mod_cast card_masksVanishingOn fixed

end Labelled

section SubsetSum

variable {G : Type*} [AddCommGroup G]

/-- The additive subset sum selected by a Boolean mask. -/
def booleanSubsetSum (sample : ι → G) (selection : Mask ι) : G :=
  ∑ i, if selection i = 0 then 0 else sample i

/-- Boolean masks supported entirely on `fixed`. -/
def MasksSupportedOn (fixed : Finset ι) :=
  {selection : Mask ι // ∀ i, i ∉ fixed → selection i = 0}

/-- Restrict a Boolean mask to `fixed`, setting every other coordinate to
zero. -/
def restrictToFixed (fixed : Finset ι) (selection : Mask ι) :
    MasksSupportedOn fixed :=
  ⟨fun i => if i ∈ fixed then selection i else 0, by
    intro i hi
    simp [hi]⟩

/-- Restrict a Boolean mask to the complement of `fixed`. -/
def restrictOutsideFixed (fixed : Finset ι) (selection : Mask ι) : Mask ι :=
  fun i => if i ∈ fixed then 0 else selection i

/-- A Boolean subset sum splits into its `fixed` and complementary parts. -/
theorem booleanSubsetSum_decompose
    (fixed : Finset ι) (sample : ι → G) (selection : Mask ι) :
    booleanSubsetSum sample selection =
      booleanSubsetSum sample (restrictToFixed fixed selection).1 +
        booleanSubsetSum sample (restrictOutsideFixed fixed selection) := by
  classical
  unfold booleanSubsetSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hiUniv
  by_cases hi : i ∈ fixed <;>
    simp [restrictToFixed, restrictOutsideFixed, hi]

/-- The usual local injectivity condition: the Boolean subset-sum map is
injective on selections supported in `fixed`. -/
def SubsetSumInjectiveWithin
    (fixed : Finset ι) (sample : ι → G) : Prop :=
  Function.Injective fun selection : MasksSupportedOn fixed =>
    booleanSubsetSum sample selection.1

/-- The Boolean selections whose subset sum is a prescribed residue. -/
def residueFibre [DecidableEq G]
    (sample : ι → G) (residue : G) : Finset (Mask ι) :=
  Finset.univ.filter fun selection => booleanSubsetSum sample selection = residue

/-- Conditional subset-sum injectivity on `fixed`: after the complementary
coordinates are fixed, the total subset sum distinguishes the choices on
`fixed`. -/
def SubsetSumInjectiveOn
    (fixed : Finset ι) (sample : ι → G) : Prop :=
  ∀ ⦃left right : Mask ι⦄,
    AgreeOutside fixed left right →
    booleanSubsetSum sample left = booleanSubsetSum sample right →
    left = right

/-- Injectivity of the subset-sum map on masks supported in `fixed` implies
conditional injectivity after an arbitrary common complementary selection is
added. -/
theorem subsetSumInjectiveOn_of_injectiveWithin
    (fixed : Finset ι) (sample : ι → G)
    (hinjective : SubsetSumInjectiveWithin fixed sample) :
    SubsetSumInjectiveOn fixed sample := by
  intro left right hagree hsum
  have houtside :
      restrictOutsideFixed fixed left = restrictOutsideFixed fixed right := by
    funext i
    by_cases hi : i ∈ fixed
    · simp [restrictOutsideFixed, hi]
    · simp [restrictOutsideFixed, hi, hagree i hi]
  have hinsideSum :
      booleanSubsetSum sample (restrictToFixed fixed left).1 =
        booleanSubsetSum sample (restrictToFixed fixed right).1 := by
    rw [booleanSubsetSum_decompose fixed sample left,
      booleanSubsetSum_decompose fixed sample right] at hsum
    rw [houtside] at hsum
    exact add_right_cancel hsum
  have hinside :
      restrictToFixed fixed left = restrictToFixed fixed right :=
    hinjective hinsideSum
  have hinsideValues :
      (restrictToFixed fixed left).1 =
        (restrictToFixed fixed right).1 :=
    congrArg Subtype.val hinside
  funext i
  by_cases hi : i ∈ fixed
  · simpa [restrictToFixed, hi] using congrFun hinsideValues i
  · exact hagree i hi

omit [DecidableEq ι] in
/-- Global Boolean subset-sum injectivity implies conditional injectivity on
every coordinate set. -/
theorem subsetSumInjectiveOn_of_injective
    (fixed : Finset ι) (sample : ι → G)
    (hinjective : Function.Injective (booleanSubsetSum sample)) :
    SubsetSumInjectiveOn fixed sample := by
  intro left right hagree hsum
  exact hinjective hsum

/-- Conditional subset-sum injectivity makes every residue fibre
projection-injective. -/
theorem projectionInjective_residueFibre
    [DecidableEq G]
    (fixed : Finset ι) (sample : ι → G) (residue : G)
    (hinjective : SubsetSumInjectiveOn fixed sample) :
    ProjectionInjective fixed (residueFibre sample residue) := by
  intro left hleft right hright hagree
  apply hinjective hagree
  have hleftResidue : booleanSubsetSum sample left = residue := by
    exact (Finset.mem_filter.mp hleft).2
  have hrightResidue : booleanSubsetSum sample right = residue := by
    exact (Finset.mem_filter.mp hright).2
  exact hleftResidue.trans hrightResidue.symm

/-- Exact restricted Parseval for a residue fibre whose subset sums are
injective after fixing the complementary coordinates. -/
theorem residueFibre_restricted_parseval_eq_diagonal
    [DecidableEq G]
    (fixed : Finset ι) (sample : ι → G) (residue : G)
    (hinjective : SubsetSumInjectiveOn fixed sample) :
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude (residueFibre sample residue)
          (fun _ => 1) mask) ^ 2) =
      (2 : ℤ) ^ (Fintype.card ι - fixed.card) *
        (residueFibre sample residue).card :=
  restricted_parseval_unit_eq_diagonal fixed
    (residueFibre sample residue)
    (projectionInjective_residueFibre fixed sample residue hinjective)

end SubsetSum

end SimonDCP.Probability.ProjectionInjectivity
