import SimonDCP.Probability.SimultaneousLocalInjectivity

/-!
# Outer averaging for the repaired Lemma 1 argument

This file records two elementary steps needed to pass from a good sampled
environment to the final conditional probability estimate.

First, Boolean subset-sum injectivity is monotone in the participating
coordinate set: injectivity on a larger set implies injectivity on every
smaller set.  Thus simultaneous injectivity on the prescribed full groups
and pairwise unions automatically supplies injectivity on `free ∩ A` for an
arbitrary set of free coordinates.

Second, a finite outer distribution and a normalized finite inner kernel
obey the usual total-probability bound.  If bad outer environments have mass
at most `p`, and every good outer environment has conditional inner failure
mass at most `q`, then the joint failure mass is at most `p + q`.  No
independence between the two layers is assumed.
-/

namespace SimonDCP.Probability.LemmaOneOuterAveraging

open scoped BigOperators

open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.TernarySubsetSumBound

variable {I G Outer Inner : Type*}

section InjectivityMonotonicity

variable [Fintype I] [DecidableEq I] [AddCommGroup G]

omit [DecidableEq I] in
/-- Subset-sum injectivity on a coordinate set is inherited by every smaller
coordinate set. -/
theorem subsetSumInjectiveWithin_mono
    {small large : Finset I} {sample : I -> G}
    (hsub : small ⊆ large)
    (hinjective : SubsetSumInjectiveWithin large sample) :
    SubsetSumInjectiveWithin small sample := by
  intro left right hsum
  let promote : MasksSupportedOn small -> MasksSupportedOn large :=
    fun selection =>
      ⟨selection.1, by
        intro i hiLarge
        exact selection.2 i (fun hiSmall => hiLarge (hsub hiSmall))⟩
  have hpromoted : promote left = promote right := by
    apply hinjective
    simpa [promote] using hsum
  apply Subtype.ext
  simpa [promote] using
    congrArg (fun selection : MasksSupportedOn large => selection.1) hpromoted

/-- In particular, injectivity on `fixed` implies injectivity on the free
coordinates belonging to `fixed`. -/
theorem subsetSumInjectiveWithin_free_inter
    (free fixed : Finset I) (sample : I -> G)
    (hinjective : SubsetSumInjectiveWithin fixed sample) :
    SubsetSumInjectiveWithin (free ∩ fixed) sample :=
  subsetSumInjectiveWithin_mono Finset.inter_subset_right hinjective

end InjectivityMonotonicity

section NestedFiniteMass

variable [Fintype Outer] [Fintype Inner]

/-- The failure mass in a finite outer space equipped with a finite inner
kernel.  The kernel is allowed to depend on the outer outcome. -/
noncomputable def nestedFiniteMass
    (outerWeight : Outer -> Rat) (innerWeight : Outer -> Inner -> Rat)
    (event : Outer -> Inner -> Prop) : Rat :=
  ∑ outer, outerWeight outer * finiteMass (innerWeight outer) (event outer)

/-- A finite event has at most the total mass of its ambient nonnegatively
weighted space. -/
theorem finiteMass_le_total
    (weight : Inner -> Rat) (event : Inner -> Prop)
    (hWeight : ∀ inner, 0 <= weight inner) :
    finiteMass weight event <= ∑ inner, weight inner := by
  classical
  unfold finiteMass
  apply Finset.sum_le_sum
  intro inner _
  by_cases hEvent : event inner
  · simp [hEvent]
  · simp [hEvent, hWeight inner]

/-- Finite total probability with an exceptional outer event.

Bad outer outcomes are charged their full conditional mass, while every
good outer outcome is charged at most `q`.  The explicit hypothesis
`0 <= q` is necessary when the bad event has full outer mass. -/
theorem nestedFiniteMass_le_bad_add
    (outerWeight : Outer -> Rat) (innerWeight : Outer -> Inner -> Rat)
    (badOuter : Outer -> Prop) (failure : Outer -> Inner -> Prop)
    (p q : Rat)
    (hOuterWeight : ∀ outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hInnerWeight : ∀ outer, outerWeight outer ≠ 0 ->
      ∀ inner, 0 <= innerWeight outer inner)
    (hInnerNormalized : ∀ outer, outerWeight outer ≠ 0 ->
      (∑ inner, innerWeight outer inner) = 1)
    (hQ : 0 <= q)
    (hBad : finiteMass outerWeight badOuter <= p)
    (hGood : ∀ outer, outerWeight outer ≠ 0 -> ¬ badOuter outer ->
      finiteMass (innerWeight outer) (failure outer) <= q) :
    nestedFiniteMass outerWeight innerWeight failure <= p + q := by
  classical
  calc
    nestedFiniteMass outerWeight innerWeight failure <=
        finiteMass outerWeight badOuter +
          q * ∑ outer, outerWeight outer := by
      unfold nestedFiniteMass finiteMass
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro outer _
      by_cases hOuterZero : outerWeight outer = 0
      · simp [hOuterZero]
      · by_cases hOuterBad : badOuter outer
        · simp only [hOuterBad, if_true]
          have hInnerMass :
              (∑ inner,
                  if failure outer inner then innerWeight outer inner else 0) <=
                1 := by
            calc
              (∑ inner,
                  if failure outer inner then innerWeight outer inner else 0) <=
                  ∑ inner, innerWeight outer inner :=
                finiteMass_le_total (innerWeight outer) (failure outer)
                  (hInnerWeight outer hOuterZero)
              _ = 1 := hInnerNormalized outer hOuterZero
          calc
            outerWeight outer *
                  (∑ inner,
                    if failure outer inner then innerWeight outer inner else 0) <=
                outerWeight outer :=
              by
                simpa using
                  mul_le_mul_of_nonneg_left hInnerMass (hOuterWeight outer)
            _ <= outerWeight outer + q * outerWeight outer :=
              le_add_of_nonneg_right
                (mul_nonneg hQ (hOuterWeight outer))
        · simp only [hOuterBad, if_false, zero_add]
          have hConditional :
              (∑ inner,
                  if failure outer inner then innerWeight outer inner else 0) <=
                q := hGood outer hOuterZero hOuterBad
          calc
            outerWeight outer *
                  (∑ inner,
                    if failure outer inner then innerWeight outer inner else 0) <=
                outerWeight outer * q :=
              mul_le_mul_of_nonneg_left hConditional (hOuterWeight outer)
            _ = q * outerWeight outer := mul_comm _ _
    _ = finiteMass outerWeight badOuter + q := by
      rw [hOuterNormalized, mul_one]
    _ <= p + q := add_le_add hBad le_rfl

end NestedFiniteMass

section SimultaneousLocalSpecialization

variable [Fintype Outer] [Fintype Inner]
  [Fintype I] [DecidableEq I] [AddCommGroup G]

omit [Fintype Outer] in
/-- Outside the simultaneous local-failure event, every member of the full
family has an injective Boolean subset-sum map. -/
theorem subsetSumInjectiveWithin_of_goodOuter
    (family : Finset (Finset I)) (sample : Outer -> I -> G)
    (outer : Outer) (fixed : Finset I)
    (hGood : ¬ simultaneousLocalFailure family sample outer)
    (hFixed : fixed ∈ family) :
    SubsetSumInjectiveWithin fixed (sample outer) := by
  by_contra hNotInjective
  exact hGood ⟨fixed, hFixed, hNotInjective⟩

omit [Fintype Outer] in
/-- Consequently, a good outer environment supplies injectivity on
`free ∩ fixed` for every arbitrary set of free coordinates and every member
of the prescribed full family. -/
theorem subsetSumInjectiveWithin_free_inter_of_goodOuter
    (family : Finset (Finset I)) (sample : Outer -> I -> G)
    (outer : Outer) (free fixed : Finset I)
    (hGood : ¬ simultaneousLocalFailure family sample outer)
    (hFixed : fixed ∈ family) :
    SubsetSumInjectiveWithin (free ∩ fixed) (sample outer) :=
  subsetSumInjectiveWithin_free_inter free fixed (sample outer)
    (subsetSumInjectiveWithin_of_goodOuter family sample outer fixed
      hGood hFixed)

/-- The outer-averaging theorem specialized to the simultaneous failure of
the prescribed full group family. -/
theorem nestedFiniteMass_le_simultaneousLocalFailure_add
    (family : Finset (Finset I)) (sample : Outer -> I -> G)
    (outerWeight : Outer -> Rat) (innerWeight : Outer -> Inner -> Rat)
    (failure : Outer -> Inner -> Prop) (p q : Rat)
    (hOuterWeight : ∀ outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hInnerWeight : ∀ outer, outerWeight outer ≠ 0 ->
      ∀ inner, 0 <= innerWeight outer inner)
    (hInnerNormalized : ∀ outer, outerWeight outer ≠ 0 ->
      (∑ inner, innerWeight outer inner) = 1)
    (hQ : 0 <= q)
    (hBad :
      finiteMass outerWeight (simultaneousLocalFailure family sample) <= p)
    (hGood : ∀ outer, outerWeight outer ≠ 0 ->
      ¬ simultaneousLocalFailure family sample outer ->
        finiteMass (innerWeight outer) (failure outer) <= q) :
    nestedFiniteMass outerWeight innerWeight failure <= p + q :=
  nestedFiniteMass_le_bad_add outerWeight innerWeight
    (simultaneousLocalFailure family sample) failure p q
    hOuterWeight hOuterNormalized hInnerWeight hInnerNormalized hQ hBad hGood

/-- A downstream inner theorem may ask directly for all restricted
injectivity hypotheses.  This wrapper obtains them from the complement of
the simultaneous outer failure event before applying total probability. -/
theorem nestedFiniteMass_le_of_goodLocalInjectivity
    (family : Finset (Finset I)) (sample : Outer -> I -> G)
    (outerWeight : Outer -> Rat) (innerWeight : Outer -> Inner -> Rat)
    (failure : Outer -> Inner -> Prop) (p q : Rat)
    (hOuterWeight : ∀ outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hInnerWeight : ∀ outer, outerWeight outer ≠ 0 ->
      ∀ inner, 0 <= innerWeight outer inner)
    (hInnerNormalized : ∀ outer, outerWeight outer ≠ 0 ->
      (∑ inner, innerWeight outer inner) = 1)
    (hQ : 0 <= q)
    (hBad :
      finiteMass outerWeight (simultaneousLocalFailure family sample) <= p)
    (hInner : ∀ outer, outerWeight outer ≠ 0 ->
      (∀ free fixed, fixed ∈ family ->
        SubsetSumInjectiveWithin (free ∩ fixed) (sample outer)) ->
      finiteMass (innerWeight outer) (failure outer) <= q) :
    nestedFiniteMass outerWeight innerWeight failure <= p + q := by
  apply nestedFiniteMass_le_simultaneousLocalFailure_add family sample
    outerWeight innerWeight failure p q hOuterWeight hOuterNormalized
      hInnerWeight hInnerNormalized hQ hBad
  intro outer hOuter hGood
  apply hInner outer hOuter
  intro free fixed hFixed
  exact subsetSumInjectiveWithin_free_inter_of_goodOuter
    family sample outer free fixed hGood hFixed

end SimultaneousLocalSpecialization

end SimonDCP.Probability.LemmaOneOuterAveraging
