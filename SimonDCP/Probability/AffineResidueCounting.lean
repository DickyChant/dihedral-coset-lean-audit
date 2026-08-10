import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import SimonDCP.Probability.OneTimePadCounting

/-!
# Aggregating one-time-pad residue counts

This file lifts `outsideResidueFibreEquiv` from one Boolean selection to a
finite support of selections.  A selection is regular when it chooses at
least one coordinate outside the fixed set `A`; its residue fibres are then
equicardinal.  An exceptional selection chooses no such coordinate, so its
completed sum is determined entirely by the fixed inside sample.

The final identity and inequality are unnormalized counting versions of the
likelihood estimate

`Pr[Z = z | fixed inside data] <= (1 - delta) / |G| + delta`.

They isolate exactly the finite-counting premise needed by the rational Bayes
bound in `ResidueConditioningBound.lean`.
-/

namespace SimonDCP.Probability.AffineResidueCounting

open scoped BigOperators
open SimonDCP.Probability.OneTimePadCounting

section FiniteAdditiveGroup

variable {I G : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The residue equality predicate gives every outside fibre a finite model. -/
noncomputable instance instFintypeOutsideResidueFibre
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (residue : G) :
    Fintype (OutsideResidueFibre selection A inside residue) :=
  by
    classical
    unfold OutsideResidueFibre
    infer_instance

/-- A selection has a one-time-pad coordinate outside the fixed set `A`. -/
def HasOutsidePad (selection : I → Bool) (A : Finset I) : Prop :=
  ∃ pivot : OutsideIndex A, selection pivot.1 = true

/-- The selections for which an outside one-time pad is available. -/
noncomputable def regularSelections (support : Finset (I → Bool)) (A : Finset I) :
    Finset (I → Bool) :=
  by
    classical
    exact support.filter fun selection => HasOutsidePad selection A

/-- The selections whose chosen coordinates are all contained in `A`. -/
noncomputable def exceptionalSelections (support : Finset (I → Bool)) (A : Finset I) :
    Finset (I → Bool) :=
  by
    classical
    exact support.filter fun selection => ¬ HasOutsidePad selection A

/-- Exceptional selections whose fixed inside contribution equals `residue`. -/
noncomputable def matchingExceptionalSelections
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) : Finset (I → Bool) :=
  by
    classical
    exact (exceptionalSelections support A).filter fun selection =>
      selectedInsideSum selection A inside = residue

/-- The number of outside assignments in one residue fibre. -/
noncomputable def residueCount
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (residue : G) : ℕ :=
  by
    classical
    exact Fintype.card (OutsideResidueFibre selection A inside residue)

/-- The joint count after summing one residue fibre over a selection support. -/
noncomputable def aggregateResidueCount
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) : ℕ :=
  ∑ selection ∈ support, residueCount selection A inside residue

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem mem_regularSelections_iff
    {support : Finset (I → Bool)} {A : Finset I} {selection : I → Bool} :
    selection ∈ regularSelections support A ↔
      selection ∈ support ∧ HasOutsidePad selection A := by
  simp [regularSelections]

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem mem_exceptionalSelections_iff
    {support : Finset (I → Bool)} {A : Finset I} {selection : I → Bool} :
    selection ∈ exceptionalSelections support A ↔
      selection ∈ support ∧ ¬ HasOutsidePad selection A := by
  simp [exceptionalSelections]

/-- A regular selection has equally large fibres over any two residues. -/
theorem residueCount_eq_of_hasOutsidePad
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (hpad : HasOutsidePad selection A) (source target : G) :
    residueCount selection A inside source =
      residueCount selection A inside target := by
  classical
  rcases hpad with ⟨pivot, hpivot⟩
  exact Fintype.card_congr
    (outsideResidueFibreEquiv selection A inside pivot hpivot source target)

/-- The disjoint union of all residue fibres is the full outside sample type. -/
def residueFibresEquiv
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G) :
    (Σ residue : G, OutsideResidueFibre selection A inside residue) ≃
      OutsideSample A G where
  toFun sample := sample.2.1
  invFun outside :=
    ⟨completedSelectedSum selection A inside outside, ⟨outside, rfl⟩⟩
  left_inv sample := by
    rcases sample with ⟨residue, outside, houtside⟩
    subst residue
    rfl
  right_inv _ := rfl

/-- Summing fibre cardinalities over all residues counts every outside sample. -/
theorem sum_residueCount
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G) :
    (∑ residue : G, residueCount selection A inside residue) =
      Fintype.card (OutsideSample A G) := by
  classical
  calc
    (∑ residue : G, residueCount selection A inside residue) =
        Fintype.card
          (Σ residue : G, OutsideResidueFibre selection A inside residue) := by
      symm
      exact Fintype.card_sigma
    _ = Fintype.card (OutsideSample A G) :=
      Fintype.card_congr (residueFibresEquiv selection A inside)

/-- A regular fibre has exactly `1 / |G|` of all outside assignments. -/
theorem card_mul_residueCount_eq
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (hpad : HasOutsidePad selection A) (residue : G) :
    Fintype.card G * residueCount selection A inside residue =
      Fintype.card (OutsideSample A G) := by
  classical
  calc
    Fintype.card G * residueCount selection A inside residue =
        ∑ target : G, residueCount selection A inside residue := by
      simp
    _ = ∑ target : G, residueCount selection A inside target := by
      apply Finset.sum_congr rfl
      intro target _
      exact residueCount_eq_of_hasOutsidePad
        selection A inside hpad residue target
    _ = Fintype.card (OutsideSample A G) :=
      sum_residueCount selection A inside

omit [Fintype G] [DecidableEq G] in
/-- A selection without an outside pad has zero free contribution. -/
theorem selectedOutsideSum_eq_zero_of_not_hasOutsidePad
    (selection : I → Bool) (A : Finset I)
    (hpad : ¬ HasOutsidePad selection A) (outside : OutsideSample A G) :
    selectedOutsideSum selection A outside = 0 := by
  classical
  unfold selectedOutsideSum
  apply Finset.sum_eq_zero
  intro pivot _
  have hpivot : selection pivot.1 ≠ true := by
    intro hpivot
    exact hpad ⟨pivot, hpivot⟩
  simp [hpivot]

omit [Fintype G] [DecidableEq G] in
/-- For an exceptional selection, the completed sum is already fixed inside. -/
theorem completedSelectedSum_eq_inside_of_not_hasOutsidePad
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (hpad : ¬ HasOutsidePad selection A) (outside : OutsideSample A G) :
    completedSelectedSum selection A inside outside =
      selectedInsideSum selection A inside := by
  simp [completedSelectedSum,
    selectedOutsideSum_eq_zero_of_not_hasOutsidePad selection A hpad outside]

/-- An exceptional fibre is either the full outside sample type or empty. -/
theorem residueCount_of_not_hasOutsidePad
    (selection : I → Bool) (A : Finset I) (inside : InsideSample A G)
    (hpad : ¬ HasOutsidePad selection A) (residue : G) :
    residueCount selection A inside residue =
      if selectedInsideSum selection A inside = residue then
        Fintype.card (OutsideSample A G)
      else 0 := by
  by_cases hresidue : selectedInsideSum selection A inside = residue
  · rw [if_pos hresidue]
    let equivalence : OutsideSample A G ≃
        OutsideResidueFibre selection A inside residue := {
      toFun outside := ⟨outside, by
        rw [completedSelectedSum_eq_inside_of_not_hasOutsidePad
          selection A inside hpad outside]
        exact hresidue⟩
      invFun outside := outside.1
      left_inv _ := rfl
      right_inv _ := rfl
    }
    exact (Fintype.card_congr equivalence).symm
  · rw [if_neg hresidue]
    unfold residueCount
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨?_⟩
    intro outside
    apply hresidue
    rw [← outside.2]
    exact (completedSelectedSum_eq_inside_of_not_hasOutsidePad
      selection A inside hpad outside.1).symm

/-- The regular and exceptional supports partition the original support. -/
theorem aggregateResidueCount_eq_regular_add_exceptional
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    aggregateResidueCount support A inside residue =
      aggregateResidueCount (regularSelections support A) A inside residue +
        aggregateResidueCount (exceptionalSelections support A) A inside residue := by
  classical
  unfold aggregateResidueCount regularSelections exceptionalSelections
  symm
  exact Finset.sum_filter_add_sum_filter_not
    support (fun selection => HasOutsidePad selection A)
      (fun selection => residueCount selection A inside residue)

/-- Regular selections contribute exactly uniform residue counts in aggregate. -/
theorem card_mul_regularAggregate_eq
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    Fintype.card G *
        aggregateResidueCount (regularSelections support A) A inside residue =
      (regularSelections support A).card *
        Fintype.card (OutsideSample A G) := by
  classical
  unfold aggregateResidueCount
  calc
    Fintype.card G *
        (∑ selection ∈ regularSelections support A,
          residueCount selection A inside residue) =
        ∑ selection ∈ regularSelections support A,
          Fintype.card G * residueCount selection A inside residue := by
      rw [Finset.mul_sum]
    _ = ∑ _selection ∈ regularSelections support A,
          Fintype.card (OutsideSample A G) := by
      apply Finset.sum_congr rfl
      intro selection hselection
      exact card_mul_residueCount_eq selection A inside
        (mem_regularSelections_iff.mp hselection).2 residue
    _ = (regularSelections support A).card *
        Fintype.card (OutsideSample A G) := by
      simp

/-- Exceptional selections contribute exactly when their fixed sum matches. -/
theorem exceptionalAggregate_eq
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    aggregateResidueCount (exceptionalSelections support A) A inside residue =
      (matchingExceptionalSelections support A inside residue).card *
        Fintype.card (OutsideSample A G) := by
  classical
  unfold aggregateResidueCount
  calc
    (∑ selection ∈ exceptionalSelections support A,
        residueCount selection A inside residue) =
        ∑ selection ∈ exceptionalSelections support A,
          if selectedInsideSum selection A inside = residue then
            Fintype.card (OutsideSample A G)
          else 0 := by
      apply Finset.sum_congr rfl
      intro selection hselection
      rw [residueCount_of_not_hasOutsidePad selection A inside
        (mem_exceptionalSelections_iff.mp hselection).2 residue]
    _ = (matchingExceptionalSelections support A inside residue).card *
        Fintype.card (OutsideSample A G) := by
      let predicate : (I → Bool) → Prop := fun selection =>
        selectedInsideSum selection A inside = residue
      have hsum (selections : Finset (I → Bool)) (constant : ℕ) :
          (∑ selection ∈ selections,
              if predicate selection then constant else 0) =
            (selections.filter predicate).card * constant := by
        induction selections using Finset.induction_on with
        | empty => simp
        | @insert selection selections hnotmem inductionHypothesis =>
            by_cases hpredicate : predicate selection
            · have hfilterNotMem :
                  selection ∉ selections.filter predicate := by
                intro hmem
                exact hnotmem (Finset.filter_subset _ _ hmem)
              rw [Finset.sum_insert hnotmem, if_pos hpredicate,
                inductionHypothesis, Finset.filter_insert]
              rw [if_pos hpredicate,
                Finset.card_insert_of_notMem hfilterNotMem]
              simp [Nat.add_mul, Nat.add_comm]
            · rw [Finset.sum_insert hnotmem, if_neg hpredicate,
                inductionHypothesis, Finset.filter_insert,
                if_neg hpredicate]
              simp
      simpa [matchingExceptionalSelections, predicate] using
        hsum (exceptionalSelections support A)
          (Fintype.card (OutsideSample A G))

/--
Exact aggregate count, separating uniform and exceptional contributions.

Multiplication by `|G|` avoids natural-number division and exposes the two
terms that become `(1 - delta) / |G|` and `delta` after normalization.
-/
theorem card_mul_aggregateResidueCount_eq
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    Fintype.card G * aggregateResidueCount support A inside residue =
      (regularSelections support A).card *
          Fintype.card (OutsideSample A G) +
        Fintype.card G *
          ((matchingExceptionalSelections support A inside residue).card *
            Fintype.card (OutsideSample A G)) := by
  rw [aggregateResidueCount_eq_regular_add_exceptional, Nat.mul_add,
    card_mul_regularAggregate_eq, exceptionalAggregate_eq]

/--
Count-level likelihood bound for a finite support of selections.

Every exceptional selection is bounded by a full outside sample space; all
other selections contribute exactly a `1 / |G|` fraction.  This is the
deterministic counting premise used in the repaired Bayes argument.
-/
theorem card_mul_aggregateResidueCount_le
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    Fintype.card G * aggregateResidueCount support A inside residue ≤
      (regularSelections support A).card *
          Fintype.card (OutsideSample A G) +
        Fintype.card G *
          ((exceptionalSelections support A).card *
            Fintype.card (OutsideSample A G)) := by
  rw [card_mul_aggregateResidueCount_eq]
  have hcard :
      (matchingExceptionalSelections support A inside residue).card ≤
        (exceptionalSelections support A).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard)) _

omit [Fintype I] [DecidableEq I] in
/-- The regular and exceptional selection counts add to the support size. -/
theorem regular_card_add_exceptional_card
    (support : Finset (I → Bool)) (A : Finset I) :
    (regularSelections support A).card +
        (exceptionalSelections support A).card = support.card := by
  classical
  simpa [regularSelections, exceptionalSelections] using
    (Finset.card_filter_add_card_filter_not
      (s := support) (p := fun selection => HasOutsidePad selection A))

/-- The aggregate bound rewritten using only support and exceptional counts. -/
theorem card_mul_aggregateResidueCount_le_support
    (support : Finset (I → Bool)) (A : Finset I)
    (inside : InsideSample A G) (residue : G) :
    Fintype.card G * aggregateResidueCount support A inside residue ≤
      Fintype.card (OutsideSample A G) *
        (support.card +
          (Fintype.card G - 1) * (exceptionalSelections support A).card) := by
  have hcardG : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hsplit :
      Fintype.card G = 1 + (Fintype.card G - 1) := by
    omega
  calc
    Fintype.card G * aggregateResidueCount support A inside residue ≤
        (regularSelections support A).card *
            Fintype.card (OutsideSample A G) +
          Fintype.card G *
            ((exceptionalSelections support A).card *
              Fintype.card (OutsideSample A G)) :=
      card_mul_aggregateResidueCount_le support A inside residue
    _ = (regularSelections support A).card *
          Fintype.card (OutsideSample A G) +
        (1 + (Fintype.card G - 1)) *
          ((exceptionalSelections support A).card *
            Fintype.card (OutsideSample A G)) := by
      rw [← hsplit]
    _ = Fintype.card (OutsideSample A G) *
        ((regularSelections support A).card +
          (exceptionalSelections support A).card +
          (Fintype.card G - 1) *
            (exceptionalSelections support A).card) := by
      ring
    _ = Fintype.card (OutsideSample A G) *
        (support.card +
          (Fintype.card G - 1) * (exceptionalSelections support A).card) := by
      rw [regular_card_add_exceptional_card support A]

/-- Joint count after also summing over a finite set of bad inside samples. -/
noncomputable def badResidueCount
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) : ℕ :=
  ∑ inside ∈ badInside, aggregateResidueCount support A inside residue

/-!
This is the exact count-level form recommended for the joint Bayes premise.
The exceptional count is `delta`'s numerator; it consists of selections that
vanish on `Aᶜ`, not merely the globally zero selection.
-/
theorem card_mul_badResidueCount_le
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :
    Fintype.card G * badResidueCount support A badInside residue ≤
      badInside.card * Fintype.card (OutsideSample A G) *
        (support.card +
          (Fintype.card G - 1) * (exceptionalSelections support A).card) := by
  classical
  unfold badResidueCount
  rw [Finset.mul_sum]
  calc
    (∑ inside ∈ badInside,
        Fintype.card G * aggregateResidueCount support A inside residue) ≤
        ∑ _inside ∈ badInside,
          Fintype.card (OutsideSample A G) *
            (support.card +
              (Fintype.card G - 1) *
                (exceptionalSelections support A).card) := by
      apply Finset.sum_le_sum
      intro inside _
      exact card_mul_aggregateResidueCount_le_support
        support A inside residue
    _ = badInside.card * Fintype.card (OutsideSample A G) *
        (support.card +
          (Fintype.card G - 1) * (exceptionalSelections support A).card) := by
      simp
      ring

/-!
Composition-friendly version of the same bound.  Its final factor is exactly
the regular/exceptional likelihood numerator used by `FiniteConditioningMass`.
-/
theorem card_mul_badResidueCount_le_regular_exceptional
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :
    Fintype.card G * badResidueCount support A badInside residue ≤
      badInside.card * Fintype.card (OutsideSample A G) *
        ((regularSelections support A).card +
          Fintype.card G * (exceptionalSelections support A).card) := by
  classical
  unfold badResidueCount
  rw [Finset.mul_sum]
  calc
    (∑ inside ∈ badInside,
        Fintype.card G * aggregateResidueCount support A inside residue) ≤
        ∑ _inside ∈ badInside,
          Fintype.card (OutsideSample A G) *
            ((regularSelections support A).card +
              Fintype.card G * (exceptionalSelections support A).card) := by
      apply Finset.sum_le_sum
      intro inside _
      calc
        Fintype.card G * aggregateResidueCount support A inside residue ≤
            (regularSelections support A).card *
                Fintype.card (OutsideSample A G) +
              Fintype.card G *
                ((exceptionalSelections support A).card *
                  Fintype.card (OutsideSample A G)) :=
          card_mul_aggregateResidueCount_le support A inside residue
        _ = Fintype.card (OutsideSample A G) *
            ((regularSelections support A).card +
              Fintype.card G * (exceptionalSelections support A).card) := by
          ring
    _ = badInside.card * Fintype.card (OutsideSample A G) *
        ((regularSelections support A).card +
          Fintype.card G * (exceptionalSelections support A).card) := by
      simp
      ring

/-- The Boolean selection that chooses no sample coordinate. -/
def zeroSelection : I → Bool := fun _ => false

/-- The number (zero or one) of globally zero masks in a finite support. -/
noncomputable def zeroSelectionCount (support : Finset (I → Bool)) : ℕ :=
  (support.filter fun selection => selection = zeroSelection).card

omit [Fintype I] [DecidableEq I] in
/-- With no fixed coordinates, exceptional means globally zero. -/
theorem not_hasOutsidePad_empty_iff (selection : I → Bool) :
    ¬ HasOutsidePad selection (∅ : Finset I) ↔ selection = zeroSelection := by
  constructor
  · intro hpad
    funext i
    cases hvalue : selection i with
    | false => simp [zeroSelection]
    | true =>
        exfalso
        apply hpad
        exact ⟨⟨i, by simp⟩, hvalue⟩
  · rintro rfl ⟨pivot, hpivot⟩
    simp [zeroSelection] at hpivot

omit [DecidableEq I] in
/-- At `A = ∅`, the exceptional support is the zero-mask sub-support. -/
theorem exceptionalSelections_empty_eq
    (support : Finset (I → Bool)) :
    exceptionalSelections support (∅ : Finset I) =
      support.filter fun selection => selection = zeroSelection := by
  classical
  ext selection
  simp [exceptionalSelections, not_hasOutsidePad_empty_iff]

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] in
/-- A sum over the empty inside-coordinate set is zero. -/
@[simp]
theorem selectedInsideSum_empty
    (selection : I → Bool) (inside : InsideSample (∅ : Finset I) G) :
    selectedInsideSum selection (∅ : Finset I) inside = 0 := by
  classical
  unfold selectedInsideSum
  simp

omit [DecidableEq I] [Fintype G] in
/--
For the full-sample marginal, an exceptional mask contributes only at residue
zero.  Thus its exceptional numerator is `epsilon = Pr[selection = 0]`, which
is distinct from the fixed-`A` numerator `delta` above.
-/
theorem matchingExceptionalSelections_empty_eq
    (support : Finset (I → Bool))
    (inside : InsideSample (∅ : Finset I) G) (residue : G) :
    matchingExceptionalSelections support (∅ : Finset I) inside residue =
      if residue = 0 then
        support.filter fun selection => selection = zeroSelection
      else ∅ := by
  classical
  ext selection
  by_cases hresidue : residue = 0
  · subst residue
    simp [matchingExceptionalSelections, exceptionalSelections,
      not_hasOutsidePad_empty_iff]
  · have hzero : ¬ (0 : G) = residue := by
      exact fun h => hresidue h.symm
    simp [matchingExceptionalSelections, hresidue, hzero]

/-- Exact scaled marginal count; only the globally zero mask creates bias. -/
theorem card_mul_fullSampleResidueCount_eq
    (support : Finset (I → Bool))
    (inside : InsideSample (∅ : Finset I) G) (residue : G) :
    Fintype.card G *
        aggregateResidueCount support (∅ : Finset I) inside residue =
      (support.card - zeroSelectionCount support) *
          Fintype.card (OutsideSample (∅ : Finset I) G) +
        Fintype.card G *
          ((if residue = 0 then zeroSelectionCount support else 0) *
            Fintype.card (OutsideSample (∅ : Finset I) G)) := by
  have hpartition := regular_card_add_exceptional_card
    support (∅ : Finset I)
  rw [exceptionalSelections_empty_eq] at hpartition
  have hregular :
      (regularSelections support (∅ : Finset I)).card =
        support.card - zeroSelectionCount support := by
    unfold zeroSelectionCount
    omega
  rw [card_mul_aggregateResidueCount_eq, hregular,
    matchingExceptionalSelections_empty_eq]
  by_cases hresidue : residue = 0 <;>
    simp [hresidue, zeroSelectionCount]

end FiniteAdditiveGroup

end SimonDCP.Probability.AffineResidueCounting
