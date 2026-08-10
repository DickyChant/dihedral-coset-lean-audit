import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

/-!
# Mixing random fixed bits with random free bits

Fix a set of free Boolean coordinates.  The remaining coordinates are the
faulty coordinates.  An assignment on the free coordinates together with an
assignment on the faulty coordinates determines a unique full Boolean mask,
and every full mask arises in this way.

Consequently, if both assignments are sampled uniformly and independently,
their composite is exactly uniform on all Boolean masks.  This statement is
deterministic in the fault pattern: after conditioning on any outer
environment, the resulting full-mask law is the same uniform law.  In
particular, the all-zero mask has probability `2 ^ (-|I|)`, independently of
which coordinates are faulty.
-/

namespace SimonDCP.Probability.RandomFixedBitsMixture

section AssignmentSplit

variable {I : Type*} [DecidableEq I]

/-- The coordinates outside `free`, viewed as a finite type. -/
abbrev FaultCoordinates (free : Finset I) :=
  {i : I // i ∉ free}

/-- Separate Boolean assignments on the free and faulty coordinates. -/
abbrev SplitBooleanAssignment (free : Finset I) :=
  (↑free → Bool) × (FaultCoordinates free → Bool)

/-- Combine assignments on the two complementary coordinate sets. -/
def combineSplitBooleanAssignment
    (free : Finset I) (parts : SplitBooleanAssignment free) : I → Bool :=
  fun i =>
    if hi : i ∈ free then
      parts.1 ⟨i, hi⟩
    else
      parts.2 ⟨i, by simp [hi]⟩

/-- Splitting and recombining Boolean assignments is an equivalence. -/
def splitBooleanAssignmentEquiv (free : Finset I) :
    SplitBooleanAssignment free ≃ (I → Bool) where
  toFun := combineSplitBooleanAssignment free
  invFun selection :=
    (fun i => selection i.1, fun i => selection i.1)
  left_inv parts := by
    apply Prod.ext
    · funext i
      simp [combineSplitBooleanAssignment, i.2]
    · funext i
      simp [combineSplitBooleanAssignment, i.2]
  right_inv selection := by
    funext i
    by_cases hi : i ∈ free
    · simp [combineSplitBooleanAssignment, hi]
    · simp [combineSplitBooleanAssignment, hi]

@[simp]
theorem splitBooleanAssignmentEquiv_apply
    (free : Finset I) (parts : SplitBooleanAssignment free) :
    splitBooleanAssignmentEquiv free parts =
      combineSplitBooleanAssignment free parts :=
  rfl

@[simp]
theorem combineSplitBooleanAssignment_apply_free
    (free : Finset I) (parts : SplitBooleanAssignment free)
    (i : ↑free) :
    combineSplitBooleanAssignment free parts i.1 = parts.1 i := by
  simp [combineSplitBooleanAssignment, i.2]

@[simp]
theorem combineSplitBooleanAssignment_apply_fault
    (free : Finset I) (parts : SplitBooleanAssignment free)
    (i : FaultCoordinates free) :
    combineSplitBooleanAssignment free parts i.1 = parts.2 i := by
  simp [combineSplitBooleanAssignment, i.2]

/-- Every full mask has a unique pair of free and faulty assignments. -/
theorem existsUnique_splitBooleanAssignment
    (free : Finset I) (selection : I → Bool) :
    ∃! parts : SplitBooleanAssignment free,
      combineSplitBooleanAssignment free parts = selection := by
  let equivalence := splitBooleanAssignmentEquiv free
  refine ⟨equivalence.symm selection, equivalence.apply_symm_apply selection, ?_⟩
  intro parts hparts
  apply equivalence.injective
  simpa [equivalence] using hparts

variable [Fintype I]

/-- The finite structure on split assignments transported from full masks. -/
noncomputable local instance splitBooleanAssignmentFintype
    (free : Finset I) : Fintype (SplitBooleanAssignment free) :=
  Fintype.ofEquiv (I → Bool) (splitBooleanAssignmentEquiv free).symm

/-- The two split coordinate types together have exactly `|I|` Boolean
degrees of freedom. -/
@[simp]
theorem card_splitBooleanAssignment (free : Finset I) :
    Fintype.card (SplitBooleanAssignment free) =
      2 ^ Fintype.card I := by
  calc
    Fintype.card (SplitBooleanAssignment free) =
        Fintype.card (I → Bool) :=
      Fintype.card_congr (splitBooleanAssignmentEquiv free)
    _ = 2 ^ Fintype.card I := by simp

/-- Split assignments that compose to a prescribed full mask. -/
noncomputable def splitAssignmentFibre
    (free : Finset I) (selection : I → Bool) :
    Finset (SplitBooleanAssignment free) := by
  classical
  exact Finset.univ.filter fun parts =>
    combineSplitBooleanAssignment free parts = selection

@[simp]
theorem mem_splitAssignmentFibre_iff
    {free : Finset I} {selection : I → Bool}
    {parts : SplitBooleanAssignment free} :
    parts ∈ splitAssignmentFibre free selection ↔
      combineSplitBooleanAssignment free parts = selection := by
  classical
  simp [splitAssignmentFibre]

/-- Every full mask has exactly one witness in the split assignment space. -/
@[simp]
theorem card_splitAssignmentFibre
    (free : Finset I) (selection : I → Bool) :
    (splitAssignmentFibre free selection).card = 1 := by
  classical
  let equivalence := splitBooleanAssignmentEquiv free
  have hfibre :
      splitAssignmentFibre free selection = {equivalence.symm selection} := by
    ext parts
    rw [mem_splitAssignmentFibre_iff, Finset.mem_singleton]
    constructor
    · intro hparts
      apply equivalence.injective
      simpa [equivalence] using hparts
    · rintro rfl
      exact equivalence.apply_symm_apply selection
  rw [hfibre]
  simp

/-- Point mass obtained by sampling the free and faulty assignments uniformly
and independently, then combining them. -/
noncomputable def splitAssignmentPointMass
    (free : Finset I) (selection : I → Bool) : ℚ :=
  ((splitAssignmentFibre free selection).card : ℚ) /
    (Fintype.card (SplitBooleanAssignment free) : ℚ)

/-- The composite of uniform free and faulty assignments is pointwise uniform
on full Boolean masks. -/
theorem splitAssignmentPointMass_eq_uniform
    (free : Finset I) (selection : I → Bool) :
    splitAssignmentPointMass free selection =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card I := by
  rw [splitAssignmentPointMass, card_splitAssignmentFibre,
    card_splitBooleanAssignment]
  norm_num

/-- The point law does not depend on which coordinates are declared free. -/
theorem splitAssignmentPointMass_independent_of_partition
    (free₁ free₂ : Finset I) (selection : I → Bool) :
    splitAssignmentPointMass free₁ selection =
      splitAssignmentPointMass free₂ selection := by
  rw [splitAssignmentPointMass_eq_uniform,
    splitAssignmentPointMass_eq_uniform]

/-- The all-zero Boolean mask. -/
def zeroBooleanAssignment : I → Bool :=
  fun _ => false

/-- The all-zero mask has probability `2 ^ (-|I|)`, independently of the
fault set. -/
theorem zeroBooleanAssignmentMass_eq
    (free : Finset I) :
    splitAssignmentPointMass free (zeroBooleanAssignment (I := I)) =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card I :=
  splitAssignmentPointMass_eq_uniform free _

/-- Restricting the split/full equivalence to any event gives an equivalence
of event witnesses. -/
def splitAssignmentEventEquiv
    (free : Finset I) (event : (I → Bool) → Prop) :
    {parts : SplitBooleanAssignment free //
      event (combineSplitBooleanAssignment free parts)} ≃
      {selection : I → Bool // event selection} where
  toFun parts :=
    ⟨splitBooleanAssignmentEquiv free parts.1, parts.2⟩
  invFun selection :=
    ⟨(splitBooleanAssignmentEquiv free).symm selection.1, by
      have hcombine :
          combineSplitBooleanAssignment free
              ((splitBooleanAssignmentEquiv free).symm selection.1) =
            selection.1 :=
        (splitBooleanAssignmentEquiv free).apply_symm_apply selection.1
      rw [hcombine]
      exact selection.2⟩
  left_inv parts := by
    apply Subtype.ext
    exact (splitBooleanAssignmentEquiv free).symm_apply_apply parts.1
  right_inv selection := by
    apply Subtype.ext
    exact (splitBooleanAssignmentEquiv free).apply_symm_apply selection.1

/-- Exact counting form of the pushforward statement for every event. -/
theorem card_splitAssignmentEvent_eq
    (free : Finset I) (event : (I → Bool) → Prop)
    [DecidablePred event] :
    Fintype.card
        {parts : SplitBooleanAssignment free //
          event (combineSplitBooleanAssignment free parts)} =
      Fintype.card {selection : I → Bool // event selection} :=
  Fintype.card_congr (splitAssignmentEventEquiv free event)

/-- Probability of an event under uniform split assignments. -/
noncomputable def splitAssignmentEventMass
    (free : Finset I) (event : (I → Bool) → Prop)
    [DecidablePred event] : ℚ :=
  (Fintype.card
      {parts : SplitBooleanAssignment free //
        event (combineSplitBooleanAssignment free parts)} : ℚ) /
    (Fintype.card (SplitBooleanAssignment free) : ℚ)

/-- Probability of an event under the uniform law on full Boolean masks. -/
noncomputable def uniformBooleanEventMass
    (event : (I → Bool) → Prop) [DecidablePred event] : ℚ :=
  (Fintype.card {selection : I → Bool // event selection} : ℚ) /
    (Fintype.card (I → Bool) : ℚ)

/-- Uniformly and independently sampling the two pieces pushes forward to the
uniform full-mask law, for every event. -/
theorem splitAssignmentEventMass_eq_uniform
    (free : Finset I) (event : (I → Bool) → Prop)
    [DecidablePred event] :
    splitAssignmentEventMass free event =
      uniformBooleanEventMass event := by
  unfold splitAssignmentEventMass uniformBooleanEventMass
  rw [card_splitAssignmentEvent_eq]
  rw [Fintype.card_congr (splitBooleanAssignmentEquiv free)]

/-- Event-level independence from the fault/free partition. -/
theorem splitAssignmentEventMass_independent_of_partition
    (free₁ free₂ : Finset I) (event : (I → Bool) → Prop)
    [DecidablePred event] :
    splitAssignmentEventMass free₁ event =
      splitAssignmentEventMass free₂ event := by
  rw [splitAssignmentEventMass_eq_uniform,
    splitAssignmentEventMass_eq_uniform]

end AssignmentSplit

section OuterEnvironment

variable {I Ω : Type*} [Fintype I] [DecidableEq I]

/-- Conditional on any outer environment `omega`, the full selection mask is
uniform whenever both coordinate pieces are conditionally uniform. -/
theorem conditionalPointMass_eq_uniform
    (free : Ω → Finset I) (omega : Ω) (selection : I → Bool) :
    splitAssignmentPointMass (free omega) selection =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card I :=
  splitAssignmentPointMass_eq_uniform (free omega) selection

/-- The conditional point law is identical in any two outer environments,
even when their fault patterns differ. -/
theorem conditionalPointMass_independent_of_environment
    (free : Ω → Finset I) (omega₁ omega₂ : Ω)
    (selection : I → Bool) :
    splitAssignmentPointMass (free omega₁) selection =
      splitAssignmentPointMass (free omega₂) selection := by
  rw [conditionalPointMass_eq_uniform,
    conditionalPointMass_eq_uniform]

/-- In every outer environment, the conditional probability of the all-zero
mask is exactly `2 ^ (-|I|)`. -/
theorem conditionalZeroBooleanAssignmentMass_eq
    (free : Ω → Finset I) (omega : Ω) :
    splitAssignmentPointMass (free omega)
        (zeroBooleanAssignment (I := I)) =
      (1 : ℚ) / (2 : ℚ) ^ Fintype.card I :=
  conditionalPointMass_eq_uniform free omega _

/-- The complete conditional event law is independent of the outer fault
pattern. -/
theorem conditionalEventMass_independent_of_environment
    (free : Ω → Finset I) (omega₁ omega₂ : Ω)
    (event : (I → Bool) → Prop) [DecidablePred event] :
    splitAssignmentEventMass (free omega₁) event =
      splitAssignmentEventMass (free omega₂) event :=
  splitAssignmentEventMass_independent_of_partition
    (free omega₁) (free omega₂) event

end OuterEnvironment

end SimonDCP.Probability.RandomFixedBitsMixture
