import SimonDCP.Probability.FaultCountMarkov
import SimonDCP.Probability.SimultaneousLocalInjectivity

/-!
# The combined good environment for Lemma 1

This file combines the two exceptional events that are already controlled in
the repaired Lemma 1 argument:

* at least half of the sampled coordinates are faulty; or
* one of the prescribed local Boolean subset-sum maps is noninjective.

Both events live on the same finite weighted space.  Their union is bounded
by the sum of their masses, so no independence assumption between the fault
pattern and the sampled group elements is needed.
-/

namespace SimonDCP.Probability.LemmaOneGoodEnvironment

open scoped BigOperators

open SimonDCP.Probability.FaultCountMarkov
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.TernarySubsetSumBound

variable {I G Omega : Type*}

/-- The exceptional environment used by the repaired Lemma 1 proof.  The
fault-count event deliberately uses the exact rational threshold from
`rational_faultTailMass_le_of_coordinate_marginals`; this avoids an implicit
rounding convention when `Q` is odd. -/
def lemmaOneBadEnvironment
    [Fintype I] [DecidableEq I] [AddCommGroup G]
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool)
    (family : Finset (Finset I)) (sample : Omega -> I -> G)
    (omega : Omega) : Prop :=
  (Q : Rat) / 2 <= (coordinateFaultCount Q faulted omega : Rat) ∨
    simultaneousLocalFailure family sample omega

section FiniteWeightedSpace

variable [Fintype Omega] [Fintype I] [DecidableEq I] [AddCommGroup G]

/-- The two finite-mass definitions used by the imported modules agree.
This is only a notational bridge; both sides are the same finite sum. -/
lemma finiteMass_eq_eventMass
    (weight : Omega -> Rat) (event : Omega -> Prop)
    [DecidablePred event] :
    finiteMass weight event = eventMass weight event := by
  classical
  unfold finiteMass eventMass
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hEvent : event omega <;> simp [hEvent]

/-- Union bound for two events on a finite nonnegatively weighted space.
Normalization and independence are not needed. -/
theorem finiteMass_or_le
    (weight : Omega -> Rat) (left right : Omega -> Prop)
    (hWeight : forall omega, 0 <= weight omega) :
    finiteMass weight (fun omega => left omega ∨ right omega) <=
      finiteMass weight left + finiteMass weight right := by
  classical
  unfold finiteMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro omega _
  by_cases hLeft : left omega <;>
    by_cases hRight : right omega <;>
    simp [hLeft, hRight, hWeight omega]

/-- Abstract combination step: component bounds on the fault event and the
simultaneous local-injectivity event add on the common weighted space. -/
theorem mass_lemmaOneBadEnvironment_le_of_component_bounds
    (Q : Nat) (weight : Omega -> Rat)
    (faulted : Fin Q -> Omega -> Bool)
    (family : Finset (Finset I)) (sample : Omega -> I -> G)
    (faultBound localBound : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hFault :
      finiteMass weight (fun omega =>
          (Q : Rat) / 2 <=
            (coordinateFaultCount Q faulted omega : Rat)) <= faultBound)
    (hLocal :
      finiteMass weight (simultaneousLocalFailure family sample) <=
        localBound) :
    finiteMass weight
        (lemmaOneBadEnvironment Q faulted family sample) <=
      faultBound + localBound := by
  calc
    finiteMass weight
        (lemmaOneBadEnvironment Q faulted family sample) <=
        finiteMass weight (fun omega =>
            (Q : Rat) / 2 <=
              (coordinateFaultCount Q faulted omega : Rat)) +
          finiteMass weight (simultaneousLocalFailure family sample) := by
      exact finiteMass_or_le weight _ _ hWeight
    _ <= faultBound + localBound := add_le_add hFault hLocal

end FiniteWeightedSpace

section PaperFacingBound

variable [Fintype Omega] [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Paper-facing bound for the combined bad environment.

Each coordinate has fault marginal at most `1 / (cPrime * L)`, every local
restriction in `family` is uniform, every participating local set is
nonempty, and every such set has cardinality at most `a`.  Then the mass of
the combined bad environment is at most

`2 / (cPrime * L) + family.card * ((3 ^ a - 1) / |G|)`.

The fault pattern and the group-element sample may be arbitrarily dependent;
only their stated marginals on the common weighted space are used. -/
theorem mass_lemmaOneBadEnvironment_le
    (Q : Nat) (weight : Omega -> Rat)
    (faulted : Fin Q -> Omega -> Bool)
    (family : Finset (Finset I)) (sample : Omega -> I -> G)
    (a : Nat) (cPrime L : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hNormalized : (∑ omega, weight omega) = 1)
    (hQ : 0 < Q) (hCPrime : 0 < cPrime) (hL : 0 < L)
    (hFaultMarginal : forall i,
      eventMass weight (fun omega => faulted i omega = true) <=
        1 / (cPrime * L))
    (hUniform : HasUniformLocalMarginals family weight sample)
    (hLocalNonempty : forall fixed, fixed ∈ family -> fixed.Nonempty)
    (hLocalCard : forall fixed, fixed ∈ family -> fixed.card <= a) :
    finiteMass weight
        (lemmaOneBadEnvironment Q faulted family sample) <=
      2 / (cPrime * L) +
        (family.card : Rat) *
          (((3 ^ a - 1 : Nat) : Rat) / (Fintype.card G : Rat)) := by
  classical
  apply mass_lemmaOneBadEnvironment_le_of_component_bounds
      Q weight faulted family sample
      (2 / (cPrime * L))
      ((family.card : Rat) *
        (((3 ^ a - 1 : Nat) : Rat) / (Fintype.card G : Rat)))
      hWeight
  · rw [finiteMass_eq_eventMass]
    exact rational_faultTailMass_le_of_coordinate_marginals
      Q weight faulted cPrime L hWeight hNormalized hQ hCPrime hL
        hFaultMarginal
  · exact mass_simultaneousLocalFailure_le_card_mul
      family weight sample a hWeight hUniform hLocalNonempty hLocalCard

end PaperFacingBound

end SimonDCP.Probability.LemmaOneGoodEnvironment
