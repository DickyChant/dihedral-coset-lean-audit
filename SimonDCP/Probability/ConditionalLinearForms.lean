import SimonDCP.Probability.LinearPhaseIndependence

/-!
# Linear observations on a conditioned affine fibre

Unconditional surjectivity of a linear observation is not enough after
conditioning.  Let `condition : G →+ K` define the affine conditioning event
`condition x = conditionValue`, and let `observe : G →+ H` be a possibly
joint observation.  Translation inside the conditioned fibre is available
exactly along `ker condition`.

This file proves the following counting statement:

* if `observe` restricted to `ker condition` is surjective, then every
  `observe`-fibre inside `condition x = conditionValue` has the same size;
* on a reachable conditioning fibre, equality of all observation-fibre sizes
  also forces that restricted surjectivity;
* for two binary dot products, two dual masks in the condition kernel give a
  concrete rank-two certificate.

Thus the algebraic obligation created by conditioning is explicit.  No claim
is made that the adaptive measurements in the paper satisfy it.
-/

namespace SimonDCP.Probability.ConditionalLinearForms

open SimonDCP.Probability.LinearPhaseIndependence

/-! ## General finite additive groups -/

/-- The finite joint fibre of a condition and an observation. -/
def affineJointFiber
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (conditionValue : K) (observedValue : H) : Finset G :=
  Finset.univ.filter fun x ↦
    condition x = conditionValue ∧ observe x = observedValue

/--
The observation is surjective along directions that leave the conditioning
value unchanged.  This is the elementary, subgroup-free form of saying that
`observe` restricted to `ker condition` is surjective.
-/
def SurjectiveOnConditionKernel
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    (condition : G →+ K) (observe : G →+ H) : Prop :=
  ∀ target : H, ∃ shift : G, condition shift = 0 ∧ observe shift = target

/-- The observation map restricted to the additive kernel of the condition. -/
def observationOnConditionKernel
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    (condition : G →+ K) (observe : G →+ H) : condition.ker →+ H :=
  observe.comp condition.ker.subtype

@[simp]
theorem observationOnConditionKernel_apply
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    (condition : G →+ K) (observe : G →+ H) (shift : condition.ker) :
    observationOnConditionKernel condition observe shift = observe shift :=
  rfl

/-- `SurjectiveOnConditionKernel` is exactly surjectivity of the restricted
observation homomorphism.  For linear maps over a field, this is the full-rank
condition on the restriction to `ker condition`. -/
theorem surjectiveOnConditionKernel_iff_restricted_surjective
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    (condition : G →+ K) (observe : G →+ H) :
    SurjectiveOnConditionKernel condition observe ↔
      Function.Surjective (observationOnConditionKernel condition observe) := by
  constructor
  · intro h target
    obtain ⟨shift, hCondition, hObserve⟩ := h target
    exact ⟨⟨shift, hCondition⟩, by simpa using hObserve⟩
  · intro h target
    obtain ⟨shift, hObserve⟩ := h target
    exact ⟨shift, shift.property, by simpa using hObserve⟩

/--
Translation by a kernel element bijects two observation fibres inside the
same affine conditioning fibre.
-/
def affineJointFiberShiftEquiv
    {G K H : Type*} [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    (condition : G →+ K) (observe : G →+ H)
    (conditionValue : K) (left right : H)
    (shift : G) (hCondition : condition shift = 0)
    (hObserve : observe shift = right - left) :
    {x : G // condition x = conditionValue ∧ observe x = left} ≃
      {x : G // condition x = conditionValue ∧ observe x = right} where
  toFun x := ⟨x.1 + shift, by
    simp [x.2.1, x.2.2, hCondition, hObserve]⟩
  invFun x := ⟨x.1 - shift, by
    simp [x.2.1, x.2.2, hCondition, hObserve]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/--
Minimal shift form of conditional joint uniformity: two requested outputs
have equal fibre sizes whenever their difference is observed on a direction
in the kernel of the conditioning map.
-/
theorem affineJointFiber_card_eq_of_kernel_shift
    {G K H : Type*}
    [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (conditionValue : K) (left right : H)
    (shift : G) (hCondition : condition shift = 0)
    (hObserve : observe shift = right - left) :
    (affineJointFiber condition observe conditionValue left).card =
      (affineJointFiber condition observe conditionValue right).card := by
  let equivalence := affineJointFiberShiftEquiv condition observe
    conditionValue left right shift hCondition hObserve
  calc
    (affineJointFiber condition observe conditionValue left).card =
        Fintype.card
          {x : G // condition x = conditionValue ∧ observe x = left} :=
      (Fintype.card_subtype
        fun x : G ↦ condition x = conditionValue ∧ observe x = left).symm
    _ = Fintype.card
          {x : G // condition x = conditionValue ∧ observe x = right} :=
      Fintype.card_congr equivalence
    _ = (affineJointFiber condition observe conditionValue right).card :=
      Fintype.card_subtype
        fun x : G ↦ condition x = conditionValue ∧ observe x = right

/--
Surjectivity on the conditioning kernel makes every conditional observation
fibre equinumerous.
-/
theorem affineJointFiber_card_eq_of_kernel_surjective
    {G K H : Type*}
    [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (hSurjective : SurjectiveOnConditionKernel condition observe)
    (conditionValue : K) (left right : H) :
    (affineJointFiber condition observe conditionValue left).card =
      (affineJointFiber condition observe conditionValue right).card := by
  obtain ⟨shift, hCondition, hObserve⟩ := hSurjective (right - left)
  exact affineJointFiber_card_eq_of_kernel_shift condition observe
    conditionValue left right shift hCondition hObserve

/--
If the affine conditioning fibre is inhabited, kernel-surjectivity also makes
every requested observation fibre inhabited.  This separates genuine
conditional uniformity from the vacuous equality of empty fibres.
-/
theorem affineJointFiber_nonempty_of_reachable_of_kernel_surjective
    {G K H : Type*}
    [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (hSurjective : SurjectiveOnConditionKernel condition observe)
    (conditionValue : K) (hReachable : ∃ base : G, condition base = conditionValue)
    (observedValue : H) :
    (affineJointFiber condition observe conditionValue observedValue).Nonempty := by
  obtain ⟨base, hBase⟩ := hReachable
  obtain ⟨shift, hCondition, hObserve⟩ :=
    hSurjective (observedValue - observe base)
  refine ⟨base + shift, ?_⟩
  simp [affineJointFiber, hBase, hCondition, hObserve]

/--
Converse to conditional equinumerosity on an inhabited affine fibre.  A base
point supplies one nonempty observation fibre.  Equal cardinalities make the
fibre at `observe base + target` nonempty; subtracting the base point then
realizes `target` along the conditioning kernel.
-/
theorem surjectiveOnConditionKernel_of_affineJointFiber_card_eq
    {G K H : Type*}
    [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (conditionValue : K) (hReachable : ∃ base : G, condition base = conditionValue)
    (hEqual : ∀ left right : H,
      (affineJointFiber condition observe conditionValue left).card =
        (affineJointFiber condition observe conditionValue right).card) :
    SurjectiveOnConditionKernel condition observe := by
  obtain ⟨base, hBase⟩ := hReachable
  intro target
  have hBaseMem :
      base ∈ affineJointFiber condition observe conditionValue (observe base) := by
    simp [affineJointFiber, hBase]
  have hBaseCardPositive :
      0 < (affineJointFiber condition observe conditionValue (observe base)).card :=
    Finset.card_pos.mpr ⟨base, hBaseMem⟩
  have hTargetCardPositive :
      0 < (affineJointFiber condition observe conditionValue
        (observe base + target)).card := by
    rw [hEqual (observe base + target) (observe base)]
    exact hBaseCardPositive
  obtain ⟨point, hPoint⟩ := Finset.card_pos.mp hTargetCardPositive
  simp only [affineJointFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hPoint
  refine ⟨point - base, ?_, ?_⟩
  · simp [hPoint.1, hBase]
  · simp [hPoint.2]

/--
On an inhabited conditioning fibre, exact equality of all conditional
observation-fibre cardinalities is equivalent to surjectivity on the
conditioning kernel.
-/
theorem surjectiveOnConditionKernel_iff_affineJointFiber_card_eq
    {G K H : Type*}
    [AddCommGroup G] [AddCommGroup K] [AddCommGroup H]
    [Fintype G] [DecidableEq K] [DecidableEq H]
    (condition : G →+ K) (observe : G →+ H)
    (conditionValue : K) (hReachable : ∃ base : G, condition base = conditionValue) :
    SurjectiveOnConditionKernel condition observe ↔
      ∀ left right : H,
        (affineJointFiber condition observe conditionValue left).card =
          (affineJointFiber condition observe conditionValue right).card := by
  constructor
  · intro hSurjective left right
    exact affineJointFiber_card_eq_of_kernel_surjective condition observe
      hSurjective conditionValue left right
  · exact surjectiveOnConditionKernel_of_affineJointFiber_card_eq
      condition observe conditionValue hReachable

/-! ## Conditional joint uniformity for binary dot products -/

/--
The pair of binary dot products is surjective along the conditioning kernel
when it has two dual directions in that kernel.
-/
theorem pairDotHom_surjectiveOnConditionKernel_of_witnesses
    {ι K : Type*} [Fintype ι] [AddCommGroup K]
    (condition : Mask ι →+ K)
    (phi psi u v : Mask ι)
    (huCondition : condition u = 0) (hvCondition : condition v = 0)
    (huPhi : dot phi u = 1) (huPsi : dot psi u = 0)
    (hvPhi : dot phi v = 0) (hvPsi : dot psi v = 1) :
    SurjectiveOnConditionKernel condition (pairDotHom phi psi) := by
  rintro ⟨left, right⟩
  rcases zmodTwo_eq_zero_or_one left with hLeft | hLeft
  · rcases zmodTwo_eq_zero_or_one right with hRight | hRight
    · refine ⟨0, by simp, ?_⟩
      simp [pairDotHom_apply, hLeft, hRight]
    · refine ⟨v, hvCondition, ?_⟩
      simp [pairDotHom_apply, hLeft, hRight, hvPhi, hvPsi]
  · rcases zmodTwo_eq_zero_or_one right with hRight | hRight
    · refine ⟨u, huCondition, ?_⟩
      simp [pairDotHom_apply, hLeft, hRight, huPhi, huPsi]
    · refine ⟨u + v, by simp [huCondition, hvCondition], ?_⟩
      simp [pairDotHom_apply, dot_add, hLeft, hRight,
        huPhi, huPsi, hvPhi, hvPsi]

/-- A rank-two witness for two binary forms after conditioning: both witness
directions preserve the condition and their observations form the standard
basis of `F₂²`. -/
def ConditionalDualMasks
    {ι K : Type*} [Fintype ι] [AddCommGroup K]
    (condition : Mask ι →+ K) (phi psi : Mask ι) : Prop :=
  ∃ u v : Mask ι,
    condition u = 0 ∧ condition v = 0 ∧
      dot phi u = 1 ∧ dot psi u = 0 ∧
      dot phi v = 0 ∧ dot psi v = 1

/-- A packaged dual-mask certificate implies surjectivity on the condition
kernel. -/
theorem pairDotHom_surjectiveOnConditionKernel_of_conditionalDualMasks
    {ι K : Type*} [Fintype ι] [AddCommGroup K]
    (condition : Mask ι →+ K) (phi psi : Mask ι)
    (hDual : ConditionalDualMasks condition phi psi) :
    SurjectiveOnConditionKernel condition (pairDotHom phi psi) := by
  rcases hDual with ⟨u, v, huCondition, hvCondition,
    huPhi, huPsi, hvPhi, hvPsi⟩
  exact pairDotHom_surjectiveOnConditionKernel_of_witnesses condition
    phi psi u v huCondition hvCondition huPhi huPsi hvPhi hvPsi

/-- For two binary forms, surjectivity on the condition kernel is equivalent
to the existence of dual kernel masks. -/
theorem pairDotHom_surjectiveOnConditionKernel_iff_conditionalDualMasks
    {ι K : Type*} [Fintype ι] [AddCommGroup K]
    (condition : Mask ι →+ K) (phi psi : Mask ι) :
    SurjectiveOnConditionKernel condition (pairDotHom phi psi) ↔
      ConditionalDualMasks condition phi psi := by
  constructor
  · intro hSurjective
    obtain ⟨u, huCondition, hu⟩ := hSurjective (1, 0)
    obtain ⟨v, hvCondition, hv⟩ := hSurjective (0, 1)
    simp only [pairDotHom_apply, Prod.mk.injEq] at hu hv
    exact ⟨u, v, huCondition, hvCondition,
      hu.1, hu.2, hv.1, hv.2⟩
  · exact pairDotHom_surjectiveOnConditionKernel_of_conditionalDualMasks
      condition phi psi

/-- The conditioned binary joint fibre, written with separate output bits. -/
def conditionedBinaryJointFiber
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K) (conditionValue : K)
    (phi psi : Mask ι) (left right : ZMod 2) : Finset (Mask ι) :=
  affineJointFiber condition (pairDotHom phi psi)
    conditionValue (left, right)

/-- All four conditioned binary output fibres have equal cardinality.  This
predicate is vacuously true when the conditioning fibre is empty.  For a
uniform ambient mask and a reachable condition, it is equivalent to uniform
conditional output. -/
def BinaryJointFiberCountsEqual
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K) (conditionValue : K)
    (phi psi : Mask ι) : Prop :=
  ∀ left right left' right' : ZMod 2,
    (conditionedBinaryJointFiber condition conditionValue
      phi psi left right).card =
    (conditionedBinaryJointFiber condition conditionValue
      phi psi left' right').card

/--
Equal conditional joint-fibre cardinalities for two binary forms.  Under a
reachable condition and a uniform ambient mask, this is exact conditional
joint uniformity.  Unlike the unconditional theorem, the hypothesis here is
explicit surjectivity on the kernel of the conditioning map.
-/
theorem conditionedBinaryJointFiber_card_eq_of_kernel_surjective
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K)
    (phi psi : Mask ι)
    (hSurjective :
      SurjectiveOnConditionKernel condition (pairDotHom phi psi))
    (conditionValue : K)
    (left right left' right' : ZMod 2) :
    (conditionedBinaryJointFiber condition conditionValue phi psi left right).card =
      (conditionedBinaryJointFiber condition conditionValue phi psi left' right').card := by
  exact affineJointFiber_card_eq_of_kernel_surjective
    condition (pairDotHom phi psi) hSurjective conditionValue
      (left, right) (left', right')

/--
Dual masks in the conditioning kernel are a directly checkable sufficient
condition for equal conditional joint-fibre cardinalities.  The probabilistic
interpretation additionally requires a reachable condition and a uniform
ambient mask.
-/
theorem conditionedBinaryJointFiber_card_eq_of_witnesses
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K)
    (phi psi u v : Mask ι)
    (huCondition : condition u = 0) (hvCondition : condition v = 0)
    (huPhi : dot phi u = 1) (huPsi : dot psi u = 0)
    (hvPhi : dot phi v = 0) (hvPsi : dot psi v = 1)
    (conditionValue : K)
    (left right left' right' : ZMod 2) :
    (conditionedBinaryJointFiber condition conditionValue phi psi left right).card =
      (conditionedBinaryJointFiber condition conditionValue phi psi left' right').card := by
  apply conditionedBinaryJointFiber_card_eq_of_kernel_surjective
  exact pairDotHom_surjectiveOnConditionKernel_of_witnesses condition
    phi psi u v huCondition hvCondition huPhi huPsi hvPhi hvPsi

/-- A packaged dual-mask certificate gives equal conditional binary
joint-fibre cardinalities. -/
theorem conditionedBinaryJointFiber_card_eq_of_conditionalDualMasks
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K) (phi psi : Mask ι)
    (hDual : ConditionalDualMasks condition phi psi)
    (conditionValue : K)
    (left right left' right' : ZMod 2) :
    (conditionedBinaryJointFiber condition conditionValue phi psi left right).card =
      (conditionedBinaryJointFiber condition conditionValue phi psi left' right').card := by
  apply conditionedBinaryJointFiber_card_eq_of_kernel_surjective
  exact pairDotHom_surjectiveOnConditionKernel_of_conditionalDualMasks
    condition phi psi hDual

/-- On a reachable affine condition, equality of all four binary joint-fibre
counts is equivalent to surjectivity of the pair of forms on the condition
kernel.  Reachability excludes the vacuous equality of four empty fibres. -/
theorem binaryJointFiberCountsEqual_iff_surjectiveOnConditionKernel
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K) (conditionValue : K)
    (hReachable : ∃ base : Mask ι, condition base = conditionValue)
    (phi psi : Mask ι) :
    BinaryJointFiberCountsEqual condition conditionValue phi psi ↔
      SurjectiveOnConditionKernel condition (pairDotHom phi psi) := by
  constructor
  · intro hEqual
    apply surjectiveOnConditionKernel_of_affineJointFiber_card_eq
      condition (pairDotHom phi psi) conditionValue hReachable
    rintro ⟨left, right⟩ ⟨left', right'⟩
    exact hEqual left right left' right'
  · intro hSurjective left right left' right'
    exact conditionedBinaryJointFiber_card_eq_of_kernel_surjective
      condition phi psi hSurjective conditionValue left right left' right'

/-- Paper-facing rank-two counting criterion.  Under a fixed reachable affine
condition, counting-level joint uniformity holds if and only if there are two
condition-preserving directions with outputs `(1, 0)` and `(0, 1)`.  A uniform
ambient mask turns this counting statement into conditional joint uniformity. -/
theorem binaryJointFiberCountsEqual_iff_conditionalDualMasks
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [DecidableEq K]
    (condition : Mask ι →+ K) (conditionValue : K)
    (hReachable : ∃ base : Mask ι, condition base = conditionValue)
    (phi psi : Mask ι) :
    BinaryJointFiberCountsEqual condition conditionValue phi psi ↔
      ConditionalDualMasks condition phi psi :=
  (binaryJointFiberCountsEqual_iff_surjectiveOnConditionKernel
      condition conditionValue hReachable phi psi).trans
    (pairDotHom_surjectiveOnConditionKernel_iff_conditionalDualMasks
      condition phi psi)

end SimonDCP.Probability.ConditionalLinearForms
