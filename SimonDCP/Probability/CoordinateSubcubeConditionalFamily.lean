import SimonDCP.Probability.CoordinateSubcubeConditionalInjectivity
import SimonDCP.Probability.FaultySamplePhase

/-!
# Simultaneous conditional local injectivity

This file places all local injectivity failures in one common finite
experiment.  An outcome consists of a Boolean selection and a full group
sample.  The weight is supported on selections in a coordinate subcube whose
full subset sum is the prescribed residue.  Thus the finite union bound is
applied after residue conditioning, rather than separately changing the
probability space for every local coordinate set.
-/

namespace SimonDCP.Probability.CoordinateSubcubeConditionalFamily

open scoped BigOperators

open SimonDCP.Probability.TernarySubsetSumBound
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernaryProjectionBridge
open SimonDCP.Probability.OneTimePadCounting
open SimonDCP.Probability.AffineResidueCounting
open SimonDCP.Probability.ResidueConditioningAssembly
open SimonDCP.Probability.ResidueConditioningBound
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.CoordinateSubcubeConditionalInjectivity
open SimonDCP.Probability.CoordinateSubcubeParameters
open SimonDCP.Probability.FaultySamplePhase

variable {I G : Type*}

section CommonExperiment

variable [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- The common sample space used for every member of the local family. -/
abbrev ConditionalOutcome (I G : Type*) := (I → Bool) × (I → G)

/-- The unnormalized uniform weight of the prescribed residue fibre. -/
noncomputable def jointResidueWeight
    (support : Finset (I → Bool)) (residue : G)
    (outcome : ConditionalOutcome I G) : ℚ :=
  if outcome.1 ∈ support ∧ fullSubsetSum outcome.1 outcome.2 = residue then
    1 / ((support.card : ℚ) * (Fintype.card (I → G) : ℚ))
  else 0

/-- The full sample restricted to the coordinates in `A`. -/
def insideOfFullSample (A : Finset I) (sample : I → G) : InsideSample A G :=
  fun i => sample i.1

omit [Fintype G] [DecidableEq G] in
/-- Combining an inside and an outside assignment does not change the
Boolean subset sum. -/
theorem fullSubsetSum_insideOutsideSampleEquiv
    (selection : I → Bool) (A : Finset I)
    (inside : InsideSample A G) (outside : OutsideSample A G) :
    fullSubsetSum selection
        (insideOutsideSampleEquiv (G := G) A (inside, outside)) =
      completedSelectedSum selection A inside outside := by
  classical
  unfold fullSubsetSum completedSelectedSum selectedInsideSum
    selectedOutsideSum boolSelectedTerm
  let term : I → G := fun i => if selection i = true then
    insideOutsideSampleEquiv (G := G) A (inside, outside) i else 0
  change (∑ i, term i) =
    (∑ i : InsideIndex A, if selection i.1 = true then inside i else 0) +
      ∑ i : OutsideIndex A, if selection i.1 = true then outside i else 0
  have hinside :
      (∑ i : InsideIndex A, if selection i.1 = true then inside i else 0) =
        ∑ i ∈ A, term i := by
    rw [Finset.sum_subtype A (fun _ => Iff.rfl)]
    apply Fintype.sum_congr
    intro i
    simp [term, insideOutsideSampleEquiv, i.2]
  have houtside :
      (∑ i : OutsideIndex A, if selection i.1 = true then outside i else 0) =
        ∑ i ∈ Finset.univ with i ∉ A, term i := by
    rw [Finset.sum_subtype (p := fun i => i ∉ A)
      (Finset.univ.filter fun i => i ∉ A)
      (by intro i; simp)]
    apply Fintype.sum_congr
    intro i
    simp [term, insideOutsideSampleEquiv, i.2]
  rw [hinside, houtside]
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => i ∈ A) term).symm

/-- Failure of the repaired local injectivity condition for one set `A`. -/
def localConditionalFailure
    (free A : Finset I) (outcome : ConditionalOutcome I G) : Prop :=
  ¬ SubsetSumInjectiveWithin (free ∩ A) outcome.2

/-- Failure for at least one member of a finite family. -/
def simultaneousConditionalFailure
    (free : Finset I) (family : Finset (Finset I))
    (outcome : ConditionalOutcome I G) : Prop :=
  ∃ A, A ∈ family ∧ localConditionalFailure free A outcome

/-- The inside-sample event used by the one-set counting theorem has exactly
the intended local-injectivity semantics on a full sample. -/
theorem insideOfFullSample_mem_badInsideSamples_iff
    (free A : Finset I) (sample : I → G) :
    insideOfFullSample A sample ∈ badInsideSamples (G := G) free A ↔
      ¬ SubsetSumInjectiveWithin (free ∩ A) sample := by
  rw [mem_badInsideSamples, subsetSumInjectiveWithin_iff_restricted]
  rfl

/-- The common residue weight is nonnegative. -/
theorem jointResidueWeight_nonneg
    (support : Finset (I → Bool)) (residue : G)
    (outcome : ConditionalOutcome I G) :
    0 ≤ jointResidueWeight support residue outcome := by
  classical
  unfold jointResidueWeight
  split_ifs
  · positivity
  · exact le_rfl

/-- A sigma-type presentation of the outcomes counted by one
`badResidueCount`: first the bad inside sample, then the supported selection,
then an outside assignment in the requested residue fibre. -/
abbrev BadResidueWitness
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :=
  Σ inside : {inside : InsideSample A G // inside ∈ badInside},
    Σ selection : {selection : I → Bool // selection ∈ support},
      OutsideResidueFibre selection.1 A inside.1 residue

/-- The sigma-type count above is exactly the existing aggregate bad-residue
count. -/
theorem card_badResidueWitness
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :
    Fintype.card (BadResidueWitness support A badInside residue) =
      badResidueCount support A badInside residue := by
  classical
  simp only [BadResidueWitness, Fintype.card_sigma,
    badResidueCount, aggregateResidueCount, residueCount]
  rw [← Finset.sum_attach badInside]
  simp only [Finset.attach_eq_univ]
  apply Fintype.sum_congr
  intro inside
  rw [← Finset.sum_attach support]
  simp only [Finset.attach_eq_univ]

/-- A common outcome in one bad residue event determines a witness counted by
`badResidueCount`, by splitting its full sample into inside and outside
restrictions. -/
noncomputable def badResidueWitnessOfOutcome
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :
      {outcome : ConditionalOutcome I G //
        outcome.1 ∈ support ∧
        fullSubsetSum outcome.1 outcome.2 = residue ∧
        insideOfFullSample A outcome.2 ∈ badInside} →
      BadResidueWitness support A badInside residue := fun outcome => by
  let split := (insideOutsideSampleEquiv (G := G) A).symm outcome.1.2
  refine ⟨⟨split.1, ?_⟩, ⟨⟨outcome.1.1, outcome.2.1⟩, ⟨split.2, ?_⟩⟩⟩
  · dsimp [split, insideOutsideSampleEquiv]
    exact outcome.2.2.2
  · rw [← fullSubsetSum_insideOutsideSampleEquiv]
    simpa [split] using outcome.2.2.1

omit [Fintype G] [DecidableEq G] in
/-- Distinct common outcomes determine distinct bad-residue witnesses. -/
theorem badResidueWitnessOfOutcome_injective
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) :
    Function.Injective
      (badResidueWitnessOfOutcome support A badInside residue) := by
  intro left right heq
  apply Subtype.ext
  apply Prod.ext
  · simpa [badResidueWitnessOfOutcome] using congrArg
      (fun witness : BadResidueWitness support A badInside residue =>
        witness.2.1.1) heq
  · apply (insideOutsideSampleEquiv (G := G) A).symm.injective
    apply Prod.ext
    · simpa [badResidueWitnessOfOutcome] using congrArg
        (fun witness : BadResidueWitness support A badInside residue =>
          witness.1.1) heq
    · simpa [badResidueWitnessOfOutcome] using congrArg
        (fun witness : BadResidueWitness support A badInside residue =>
          witness.2.2.1) heq

/-- The finite set of common outcomes belonging to one bad local event and
the prescribed residue fibre. -/
noncomputable def singleBadResidueOutcomes
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    Finset (ConditionalOutcome I G) := by
  classical
  exact Finset.univ.filter fun outcome =>
    outcome.1 ∈ support ∧
      fullSubsetSum outcome.1 outcome.2 = residue ∧
      localConditionalFailure free A outcome

@[simp]
theorem mem_singleBadResidueOutcomes
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G)
    (outcome : ConditionalOutcome I G) :
    outcome ∈ singleBadResidueOutcomes support free A residue ↔
      outcome.1 ∈ support ∧
      fullSubsetSum outcome.1 outcome.2 = residue ∧
      localConditionalFailure free A outcome := by
  classical
  simp [singleBadResidueOutcomes]

/-- Repackage membership in the semantic local event as membership in the
inside-sample event used by `badResidueCount`. -/
noncomputable def singleBadOutcomeAsCountingOutcome
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    {outcome : ConditionalOutcome I G //
      outcome ∈ singleBadResidueOutcomes support free A residue} →
    {outcome : ConditionalOutcome I G //
      outcome.1 ∈ support ∧
      fullSubsetSum outcome.1 outcome.2 = residue ∧
      insideOfFullSample A outcome.2 ∈
        badInsideSamples (G := G) free A} := fun outcome => by
  have houtcome := (mem_singleBadResidueOutcomes
    support free A residue outcome.1).mp outcome.2
  exact ⟨outcome.1, houtcome.1, houtcome.2.1,
    (insideOfFullSample_mem_badInsideSamples_iff free A outcome.1.2).mpr
      houtcome.2.2⟩

theorem singleBadOutcomeAsCountingOutcome_injective
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    Function.Injective
      (singleBadOutcomeAsCountingOutcome (G := G) support free A residue) := by
  intro left right heq
  apply Subtype.ext
  simpa [singleBadOutcomeAsCountingOutcome] using
    congrArg Subtype.val heq

/-- The common single-event count is bounded by the existing
inside/outside aggregate count.  The map is in fact bijective, but the
injective direction is all that the conditional union bound needs. -/
theorem card_singleBadResidueOutcomes_le
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    (singleBadResidueOutcomes support free A residue).card ≤
      badResidueCount support A (badInsideSamples (G := G) free A) residue := by
  classical
  rw [← card_badResidueWitness]
  calc
    (singleBadResidueOutcomes support free A residue).card =
        Fintype.card
          {outcome // outcome ∈
            singleBadResidueOutcomes support free A residue} := by
      simp only [Fintype.card_coe]
    _ ≤ Fintype.card
        (BadResidueWitness support A
          (badInsideSamples (G := G) free A) residue) :=
      Fintype.card_le_of_injective
        (badResidueWitnessOfOutcome support A
          (badInsideSamples (G := G) free A) residue ∘
          singleBadOutcomeAsCountingOutcome (G := G)
            support free A residue)
        ((badResidueWitnessOfOutcome_injective support A
          (badInsideSamples (G := G) free A) residue).comp
          (singleBadOutcomeAsCountingOutcome_injective
            (G := G) support free A residue))

/-- The mass of one local failure is its common-outcome count divided by the
size of the uniform selection-by-full-sample experiment. -/
theorem mass_localConditionalFailure_eq
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    finiteMass (jointResidueWeight support residue)
        (localConditionalFailure free A) =
      ((singleBadResidueOutcomes support free A residue).card : ℚ) /
        ((support.card : ℚ) * (Fintype.card (I → G) : ℚ)) := by
  classical
  unfold finiteMass jointResidueWeight
  let scale : ℚ :=
    1 / ((support.card : ℚ) * (Fintype.card (I → G) : ℚ))
  calc
    (∑ outcome,
      if localConditionalFailure free A outcome then
        if outcome.1 ∈ support ∧
            fullSubsetSum outcome.1 outcome.2 = residue then scale else 0
      else 0) =
        ∑ outcome,
          if outcome ∈ singleBadResidueOutcomes support free A residue then
            scale else 0 := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases hlocal : localConditionalFailure free A outcome <;>
        by_cases hresidue : outcome.1 ∈ support ∧
          fullSubsetSum outcome.1 outcome.2 = residue <;>
        simp [hlocal, hresidue, mem_singleBadResidueOutcomes]
    _ = ((singleBadResidueOutcomes support free A residue).card : ℚ) *
        scale := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun outcome : ConditionalOutcome I G =>
            outcome ∈ singleBadResidueOutcomes support free A residue) =
            singleBadResidueOutcomes support free A residue := by
        ext outcome
        simp
      rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    _ = ((singleBadResidueOutcomes support free A residue).card : ℚ) /
        ((support.card : ℚ) * (Fintype.card (I → G) : ℚ)) := by
      simp [scale, div_eq_mul_inv]

/-- Each single event in the common experiment is bounded by the one-set
joint mass already controlled by the residue-conditioning theorem. -/
theorem mass_localConditionalFailure_le_normalizedBadResidueMass
    (support : Finset (I → Bool)) (free A : Finset I) (residue : G) :
    finiteMass (jointResidueWeight support residue)
        (localConditionalFailure free A) ≤
      normalizedBadResidueMass support A
        (badInsideSamples (G := G) free A) residue := by
  rw [mass_localConditionalFailure_eq, normalizedBadResidueMass]
  have hcard := card_singleBadResidueOutcomes_le
    (G := G) support free A residue
  have hsplit := card_inside_mul_card_outside_eq (G := G) A
  have hdenominator :
      (support.card : ℚ) * (Fintype.card (I → G) : ℚ) =
        (support.card : ℚ) *
          (Fintype.card (InsideSample A G) : ℚ) *
          (Fintype.card (OutsideSample A G) : ℚ) := by
    norm_cast
    rw [Nat.mul_assoc, hsplit]
  rw [hdenominator]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hcard
  · positivity

/-- The actual conditional weight obtained by dividing the joint residue
weight by the residue marginal. -/
noncomputable def conditionedResidueWeight
    (support : Finset (I → Bool)) (residue : G)
    (outcome : ConditionalOutcome I G) : ℚ :=
  jointResidueWeight support residue outcome /
    normalizedFullSampleResidueMass support residue

/-- Conditioning scales every event mass by the same residue marginal. -/
theorem finiteMass_conditionedResidueWeight_eq
    (support : Finset (I → Bool)) (residue : G)
    (event : ConditionalOutcome I G → Prop) :
    finiteMass (conditionedResidueWeight support residue) event =
      finiteMass (jointResidueWeight support residue) event /
        normalizedFullSampleResidueMass support residue := by
  classical
  unfold finiteMass conditionedResidueWeight
  calc
    (∑ outcome,
      if event outcome then
        jointResidueWeight support residue outcome /
          normalizedFullSampleResidueMass support residue
      else 0) =
        ∑ outcome,
          (if event outcome then jointResidueWeight support residue outcome
            else 0) /
            normalizedFullSampleResidueMass support residue := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases hevent : event outcome <;> simp [hevent]
    _ = (∑ outcome,
          if event outcome then jointResidueWeight support residue outcome
          else 0) /
        normalizedFullSampleResidueMass support residue := by
      rw [Finset.sum_div]

/-- A common conditional union bound whose summands are the existing one-set
conditional bad-residue ratios. -/
theorem mass_simultaneousConditionalFailure_le_sum_normalized
    (support : Finset (I → Bool)) (residue : G)
    (free : Finset I) (family : Finset (Finset I))
    (hmarginal : 0 < normalizedFullSampleResidueMass support residue) :
    finiteMass (conditionedResidueWeight support residue)
        (simultaneousConditionalFailure free family) ≤
      ∑ A ∈ family,
        normalizedBadResidueMass support A
            (badInsideSamples (G := G) free A) residue /
          normalizedFullSampleResidueMass support residue := by
  classical
  calc
    finiteMass (conditionedResidueWeight support residue)
        (simultaneousConditionalFailure free family) =
      finiteMass (jointResidueWeight support residue)
          (simultaneousConditionalFailure free family) /
        normalizedFullSampleResidueMass support residue :=
      finiteMass_conditionedResidueWeight_eq support residue _
    _ ≤ (∑ A ∈ family,
        finiteMass (jointResidueWeight support residue)
          (localConditionalFailure free A)) /
        normalizedFullSampleResidueMass support residue := by
      apply div_le_div_of_nonneg_right
      · exact finiteMass_iUnion_le family
          (jointResidueWeight support residue)
          (fun A => localConditionalFailure free A)
          (jointResidueWeight_nonneg support residue)
      · exact hmarginal.le
    _ = ∑ A ∈ family,
        finiteMass (jointResidueWeight support residue)
            (localConditionalFailure free A) /
          normalizedFullSampleResidueMass support residue := by
      rw [Finset.sum_div]
    _ ≤ ∑ A ∈ family,
        normalizedBadResidueMass support A
            (badInsideSamples (G := G) free A) residue /
          normalizedFullSampleResidueMass support residue := by
      apply Finset.sum_le_sum
      intro A hA
      apply div_le_div_of_nonneg_right
      · exact mass_localConditionalFailure_le_normalizedBadResidueMass
          support free A residue
      · exact hmarginal.le

/-- Every residue has positive marginal mass on a coordinate subcube with at
least one certified free coordinate. -/
theorem normalizedFullSampleResidueMass_coordinateSubcube_pos
    (free : Finset I) (fixed : I → Bool) (residue : G) (R : ℕ)
    (hR_pos : 0 < R) (hRfree : R ≤ free.card) :
    0 < normalizedFullSampleResidueMass
      (coordinateSubcube free fixed) residue := by
  classical
  let support := coordinateSubcube free fixed
  have hsupport : support.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [support]
    rw [card_coordinateSubcube]
    positivity
  rw [normalizedFullSampleResidueMass_eq support residue hsupport]
  have hepsilon : zeroSelectionMass support ≤ dyadicDecay R := by
    dsimp [support]
    exact zeroSelectionMass_coordinateSubcube_le_dyadicDecay
      free fixed R hRfree
  have hepsilon_lt : zeroSelectionMass support < 1 :=
    lt_of_le_of_lt hepsilon (dyadicDecay_lt_one hR_pos)
  have hM : (0 : ℚ) < (Fintype.card G : ℚ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩ : 0 < Fintype.card G)
  have hindicator : 0 ≤ residueZeroIndicator residue := by
    by_cases hresidue : residue = 0 <;>
      simp [residueZeroIndicator, hresidue]
  have hepsilon_nonneg : 0 ≤ zeroSelectionMass support := by
    unfold zeroSelectionMass
    positivity
  exact add_pos_of_pos_of_nonneg
    (div_pos (sub_pos.mpr hepsilon_lt) hM)
    (mul_nonneg hepsilon_nonneg hindicator)

/-- The simultaneous conditional failure mass is bounded by the sum of the
one-set dyadic estimates, all on the same conditioned experiment. -/
theorem mass_simultaneousConditionalFailure_le_sum_dyadic
    (free : Finset I) (fixed : I → Bool)
    (family : Finset (Finset I)) (residue : G) (R r : ℕ)
    (hR_pos : 0 < R) (hrR : r ≤ R)
    (hRfree : R ≤ free.card)
    (hAr : ∀ A ∈ family, A.card ≤ r) :
    finiteMass
        (conditionedResidueWeight (coordinateSubcube free fixed) residue)
        (simultaneousConditionalFailure free family) ≤
      ∑ A ∈ family,
        (((3 ^ (free ∩ A).card - 1 : ℕ) : ℚ) /
            (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R) := by
  have hmarginal := normalizedFullSampleResidueMass_coordinateSubcube_pos
    (G := G) free fixed residue R hR_pos hRfree
  calc
    finiteMass
        (conditionedResidueWeight (coordinateSubcube free fixed) residue)
        (simultaneousConditionalFailure free family) ≤
      ∑ A ∈ family,
        normalizedBadResidueMass (coordinateSubcube free fixed) A
            (badInsideSamples (G := G) free A) residue /
          normalizedFullSampleResidueMass
            (coordinateSubcube free fixed) residue :=
      mass_simultaneousConditionalFailure_le_sum_normalized
        (coordinateSubcube free fixed) residue free family hmarginal
    _ ≤ ∑ A ∈ family,
        (((3 ^ (free ∩ A).card - 1 : ℕ) : ℚ) /
            (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R) := by
      apply Finset.sum_le_sum
      intro A hA
      exact normalizedConditionalBadResidueMass_badInsideSamples_le_dyadic
        free fixed A residue R r hR_pos hrR hRfree (hAr A hA)

/-- Uniform-cardinality form of the simultaneous conditional estimate. -/
theorem mass_simultaneousConditionalFailure_le_card_mul_dyadic
    (free : Finset I) (fixed : I → Bool)
    (family : Finset (Finset I)) (residue : G) (R r : ℕ)
    (hR_pos : 0 < R) (hrR : r ≤ R)
    (hRfree : R ≤ free.card)
    (hAr : ∀ A ∈ family, A.card ≤ r) :
    finiteMass
        (conditionedResidueWeight (coordinateSubcube free fixed) residue)
        (simultaneousConditionalFailure free family) ≤
      (family.card : ℚ) *
        ((((3 ^ r - 1 : ℕ) : ℚ) / (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R)) := by
  have hMnat : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hM : (1 : ℚ) ≤ Fintype.card G := by
    exact_mod_cast hMnat
  have hnumerator :
      0 ≤ 1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r) :=
    add_nonneg (by norm_num)
      (mul_nonneg (sub_nonneg.mpr hM) (dyadicDecay_pos (R - r)).le)
  have hdenominator : 0 < 1 - dyadicDecay R :=
    sub_pos.mpr (dyadicDecay_lt_one hR_pos)
  calc
    finiteMass
        (conditionedResidueWeight (coordinateSubcube free fixed) residue)
        (simultaneousConditionalFailure free family) ≤
      ∑ A ∈ family,
        (((3 ^ (free ∩ A).card - 1 : ℕ) : ℚ) /
            (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R) :=
      mass_simultaneousConditionalFailure_le_sum_dyadic
        free fixed family residue R r hR_pos hrR hRfree hAr
    _ ≤ ∑ _A ∈ family,
        (((3 ^ r - 1 : ℕ) : ℚ) / (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R) := by
      apply Finset.sum_le_sum
      intro A hA
      have hlocalCard : (free ∩ A).card ≤ r :=
        (Finset.card_le_card Finset.inter_subset_right).trans (hAr A hA)
      have hpow : 3 ^ (free ∩ A).card ≤ 3 ^ r :=
        Nat.pow_le_pow_right (by omega) hlocalCard
      have hsub : 3 ^ (free ∩ A).card - 1 ≤ 3 ^ r - 1 :=
        Nat.sub_le_sub_right hpow 1
      apply div_le_div_of_nonneg_right _ hdenominator.le
      apply mul_le_mul_of_nonneg_right _ hnumerator
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hsub
      · positivity
    _ = (family.card : ℚ) *
        ((((3 ^ r - 1 : ℕ) : ℚ) / (Fintype.card G : ℚ)) *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A direct conditional union bound on the common selection-by-sample
experiment.  No independence between local failures is assumed. -/
theorem mass_simultaneousConditionalFailure_le_sum
    (support : Finset (I → Bool)) (residue : G)
    (free : Finset I) (family : Finset (Finset I)) :
    finiteMass (jointResidueWeight support residue)
        (simultaneousConditionalFailure free family) ≤
      ∑ A ∈ family,
        finiteMass (jointResidueWeight support residue)
          (localConditionalFailure free A) := by
  classical
  exact finiteMass_iUnion_le family (jointResidueWeight support residue)
    (fun A => localConditionalFailure free A)
    (jointResidueWeight_nonneg support residue)

end CommonExperiment

end SimonDCP.Probability.CoordinateSubcubeConditionalFamily
