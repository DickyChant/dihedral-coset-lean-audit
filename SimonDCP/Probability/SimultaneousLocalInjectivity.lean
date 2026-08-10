import SimonDCP.Probability.TernaryProjectionBridge

/-!
# Simultaneous local subset-sum injectivity

The ternary collision estimate applies to one prescribed coordinate set.
Lemma 1 needs the estimate simultaneously for a finite family of one-group
and two-group coordinate sets.  This file supplies the finite union step.

The common sample space is deliberately explicit.  A sample may contain
additional randomness, but every local restriction used by the family must
have the uniform marginal distribution.  Consequently, coordinates outside
a local set are integrated out by the marginal hypothesis; no spurious
factor such as `|G| ^ (|I| - |A|)` occurs in the probability bound.
-/

namespace SimonDCP.Probability.SimultaneousLocalInjectivity

open scoped BigOperators

open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernaryProjectionBridge
open SimonDCP.Probability.TernarySubsetSumBound

variable {I G Omega : Type*}

/-- Failure of local subset-sum injectivity for at least one member of a
finite family. -/
def simultaneousLocalFailure
    [Fintype I] [DecidableEq I] [AddCommGroup G]
    (family : Finset (Finset I)) (sample : Omega -> I -> G) (omega : Omega) :
    Prop :=
  exists fixed, fixed ∈ family ∧
    ¬ SubsetSumInjectiveWithin fixed (sample omega)

/-- Every local restriction in `family` has its uniform marginal law under
`weight`.  Requiring this for every finite event makes the probabilistic
interface reusable and records exactly the distributional assumption needed
by the paper-facing theorem below. -/
def HasUniformLocalMarginals
    [Fintype Omega] [Fintype I] [DecidableEq I] [Fintype G]
    (family : Finset (Finset I)) (weight : Omega -> Rat)
    (sample : Omega -> I -> G) : Prop :=
  ∀ fixed, fixed ∈ family -> ∀ event : Finset (↥fixed -> G),
    finiteMass weight
        (fun omega => restrictedSample fixed (sample omega) ∈ event) =
      (event.card : Rat) / (Fintype.card (↥fixed -> G) : Rat)

section FiniteUnion

variable [Fintype Omega] [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

omit [Fintype G] [DecidableEq G] in
/-- The union mass is at most the sum of the individual local failure
masses.  This theorem does not assume independence between different local
events. -/
theorem mass_simultaneousLocalFailure_le_sum
    (family : Finset (Finset I)) (weight : Omega -> Rat)
    (sample : Omega -> I -> G)
    (hWeight : ∀ omega, 0 <= weight omega) :
    finiteMass weight (simultaneousLocalFailure family sample) <=
      ∑ fixed ∈ family,
        finiteMass weight
          (fun omega => ¬ SubsetSumInjectiveWithin fixed (sample omega)) := by
  classical
  change finiteMass weight
      (fun omega => ∃ fixed, fixed ∈ family ∧
        ¬ SubsetSumInjectiveWithin fixed (sample omega)) <= _
  exact finiteMass_iUnion_le family weight
    (fun fixed omega => ¬ SubsetSumInjectiveWithin fixed (sample omega))
    hWeight

/-- Under uniform local marginals, the failure mass for one nonempty local
set has the ternary bound `(3 ^ |A| - 1) / |G|`. -/
theorem mass_localFailure_le
    (family : Finset (Finset I)) (weight : Omega -> Rat)
    (sample : Omega -> I -> G)
    (hUniform : HasUniformLocalMarginals family weight sample)
    (fixed : Finset I) (hfixed : fixed ∈ family)
    (hNonempty : fixed.Nonempty) :
    finiteMass weight
        (fun omega => ¬ SubsetSumInjectiveWithin fixed (sample omega)) <=
      ((3 ^ fixed.card - 1 : Nat) : Rat) / (Fintype.card G : Rat) := by
  classical
  have hEvent :
      finiteMass weight
          (fun omega => ¬ SubsetSumInjectiveWithin fixed (sample omega)) =
        finiteMass weight
          (fun omega =>
            restrictedSample fixed (sample omega) ∈
              localNonInjectiveSamples (G := G) fixed) := by
    apply congrArg (finiteMass weight)
    funext omega
    apply propext
    rw [mem_localNonInjectiveSamples,
      subsetSumInjectiveWithin_iff_restricted]
  rw [hEvent,
    hUniform fixed hfixed (localNonInjectiveSamples (G := G) fixed)]
  exact uniform_localNonInjectiveSamples_le fixed hNonempty

/-- Sharper simultaneous bound: sum the local ternary estimates rather than
replacing all local cardinalities by a common maximum. -/
theorem mass_simultaneousLocalFailure_le_sum_ternary
    (family : Finset (Finset I)) (weight : Omega -> Rat)
    (sample : Omega -> I -> G)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hUniform : HasUniformLocalMarginals family weight sample)
    (hNonempty : ∀ fixed ∈ family, fixed.Nonempty) :
    finiteMass weight (simultaneousLocalFailure family sample) <=
      ∑ fixed ∈ family,
        ((3 ^ fixed.card - 1 : Nat) : Rat) /
          (Fintype.card G : Rat) := by
  calc
    finiteMass weight (simultaneousLocalFailure family sample) <=
        ∑ fixed ∈ family,
          finiteMass weight
            (fun omega => ¬ SubsetSumInjectiveWithin fixed (sample omega)) :=
      mass_simultaneousLocalFailure_le_sum family weight sample hWeight
    _ <= ∑ fixed ∈ family,
        ((3 ^ fixed.card - 1 : Nat) : Rat) /
          (Fintype.card G : Rat) := by
      exact Finset.sum_le_sum fun fixed hfixed =>
        mass_localFailure_le family weight sample hUniform fixed hfixed
          (hNonempty fixed hfixed)

/-- Paper-facing simultaneous estimate.  If every participating local set
has at most `a` coordinates, then the probability that any of their Boolean
subset-sum maps is noninjective is at most
`family.card * (3 ^ a - 1) / |G|`.

Only uniform local marginals are assumed; the local events may be arbitrarily
dependent. -/
theorem mass_simultaneousLocalFailure_le_card_mul
    (family : Finset (Finset I)) (weight : Omega -> Rat)
    (sample : Omega -> I -> G) (a : Nat)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hUniform : HasUniformLocalMarginals family weight sample)
    (hNonempty : ∀ fixed ∈ family, fixed.Nonempty)
    (hCard : ∀ fixed ∈ family, fixed.card <= a) :
    finiteMass weight (simultaneousLocalFailure family sample) <=
      (family.card : Rat) *
        (((3 ^ a - 1 : Nat) : Rat) / (Fintype.card G : Rat)) := by
  calc
    finiteMass weight (simultaneousLocalFailure family sample) <=
        ∑ fixed ∈ family,
          ((3 ^ fixed.card - 1 : Nat) : Rat) /
            (Fintype.card G : Rat) :=
      mass_simultaneousLocalFailure_le_sum_ternary family weight sample
        hWeight hUniform hNonempty
    _ <= ∑ _fixed ∈ family,
        ((3 ^ a - 1 : Nat) : Rat) / (Fintype.card G : Rat) := by
      apply Finset.sum_le_sum
      intro fixed hfixed
      have hPow : 3 ^ fixed.card <= 3 ^ a :=
        Nat.pow_le_pow_right (by omega) (hCard fixed hfixed)
      have hSub : 3 ^ fixed.card - 1 <= 3 ^ a - 1 :=
        Nat.sub_le_sub_right hPow 1
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hSub
      · positivity
    _ = (family.card : Rat) *
        (((3 ^ a - 1 : Nat) : Rat) / (Fintype.card G : Rat)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

end FiniteUnion

end SimonDCP.Probability.SimultaneousLocalInjectivity
