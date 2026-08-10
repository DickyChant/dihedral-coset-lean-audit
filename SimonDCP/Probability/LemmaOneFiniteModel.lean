import SimonDCP.Probability.LemmaOneOuterAveraging
import SimonDCP.Probability.LemmaOneExactParameters
import SimonDCP.Probability.RectangularGroupPartition

/-!
# End-to-end finite-model bound for the Lemma 1 repair

This file combines the two probability layers that remain after the quantum
experiment has been identified with a coordinate-subcube residue fibre.

The outer layer samples the Fourier labels.  Failure of subset-sum
injectivity on one group or a union of two groups is bounded by the ternary
relation union bound.  For every good outer sample, injectivity descends to
the free coordinates of an arbitrary realized fault pattern.  The inner
labelled Born law then has the exact one-group means and two-group moments
needed by Chebyshev.  Total probability adds the two failure bounds without
an independence assumption between the layers.

This theorem is deliberately a finite-model theorem.  It does not claim that
the paper's circuit state, Step-2 measurement, or Step-4 labels have already
been identified with the parameters below.
-/

namespace SimonDCP.Probability.LemmaOneFiniteModel

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernarySubsetSumBound
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.GroupUnionFamily
open SimonDCP.Probability.RectangularGroupPartition
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.LabelledBornPairwiseTail
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.LemmaOneOuterAveraging
open SimonDCP.Probability.LemmaOneExactParameters

variable {Outer G Label : Type*} {N m : Nat}
  [Fintype Outer]
  [Fintype G] [DecidableEq G] [AddCommGroup G]
  [DecidableEq Label]

omit [DecidableEq G] in
/-- A concrete integer budget which makes the ternary-collision summand at
most `1/4`. -/
theorem rectangularCollisionBound_le_quarter
    (hBudget :
      4 * N ^ 2 * (3 ^ (2 * m) - 1) <= Fintype.card G) :
    (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)) <=
      1 / 4 := by
  have hCard : (0 : Rat) < (Fintype.card G : Rat) := by
    exact_mod_cast Fintype.card_pos
  have hBudgetRat :
      (4 : Rat) * (N : Rat) ^ 2 *
          ((3 ^ (2 * m) - 1 : Nat) : Rat) <=
        (Fintype.card G : Rat) := by
    exact_mod_cast hBudget
  rw [show
    (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)) =
      ((N : Rat) ^ 2 * ((3 ^ (2 * m) - 1 : Nat) : Rat)) /
        (Fintype.card G : Rat) by
      ring]
  rw [div_le_iff₀ hCard]
  linarith

/-- The collision budget with the residue group instantiated to the Step-2
cyclic group. -/
theorem rectangularCollisionBound_zmod_le_quarter
    (lowWidth : Nat)
    (hBudget :
      4 * N ^ 2 * (3 ^ (2 * m) - 1) <= 2 ^ lowWidth) :
    (N ^ 2 : Rat) *
        (((3 ^ (2 * m) - 1 : Nat) : Rat) /
          (Fintype.card (ZMod (2 ^ lowWidth)) : Rat)) <=
      1 / 4 := by
  apply rectangularCollisionBound_le_quarter
    (G := ZMod (2 ^ lowWidth))
  simpa using hBudget

/-- A concrete rational budget which makes the Chebyshev summand at most
`1/4`. -/
theorem paperTailBound_le_quarter
    (k c n L : Rat)
    (hn : 0 < n) (hkc : c < k)
    (hBudget : 4 * k * c * L <= (k - c) ^ 2 * n) :
    (k * c / (k - c) ^ 2) * (L / n) <= 1 / 4 := by
  have hDenominator : 0 < (k - c) ^ 2 * n := by
    exact mul_pos (pow_pos (sub_pos.mpr hkc) 2) hn
  rw [div_mul_div_comm]
  rw [div_le_iff₀ hDenominator]
  linarith

/--
The complete finite-model Lemma 1 estimate for an exactly rectangular group
partition.  The first summand is the prior probability that some one- or
two-group subset-sum map is noninjective.  The second summand is the uniform
conditional lower-tail bound for the number of all-zero Hadamard groups.

The free set, fixed faulty bits, measured residue, and complete orthogonal
label may all depend on the outer outcome.  Only nonemptiness of the realized
residue fibre is required.
-/
theorem nested_lowerTailMass_rectangular_le
    (outerWeight : Outer -> Rat)
    (sample : Outer -> (Fin N × Fin m) -> G)
    (free : Outer -> Finset (Fin N × Fin m))
    (fixed : Outer -> Mask (Fin N × Fin m))
    (residue : Outer -> G)
    (label : Outer -> Mask (Fin N × Fin m) -> Label)
    (target mean k c n L : Rat)
    (hOuterWeight : forall outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hUniform :
      HasUniformLocalMarginals
        (groupUnionFamily (rectangularGroups N m)) outerWeight sample)
    (hSupport : forall outer, outerWeight outer ≠ 0 ->
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer)).Nonempty)
    (hm : 0 < m)
    (hExactMean : (N : Rat) * (1 / 2 : Rat) ^ m = mean)
    (hMeanParameters : mean = (k / c) * (n / L))
    (hTargetParameters : target = n / L)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    nestedFiniteMass outerWeight
        (fun outer =>
          labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              (free outer) (fixed outer) (sample outer) (residue outer))
            (label outer))
        (fun _ output =>
          indicatorSum N
              (groupZeroIndicator (rectangularGroups N m)) output < target) <=
      (N ^ 2 : Rat) *
          (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)) +
        (k * c / (k - c) ^ 2) * (L / n) := by
  classical
  let collisionBound : Rat :=
    (N ^ 2 : Rat) *
      (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat))
  let tailBound : Rat := (k * c / (k - c) ^ 2) * (L / n)
  apply nestedFiniteMass_le_simultaneousLocalFailure_add
    (groupUnionFamily (rectangularGroups N m)) sample outerWeight
    (fun outer =>
      labelledBornWeight
        (maskCoordinateSubcubeResidueFibre
          (free outer) (fixed outer) (sample outer) (residue outer))
        (label outer))
    (fun _ output =>
      indicatorSum N
          (groupZeroIndicator (rectangularGroups N m)) output < target)
    collisionBound tailBound
  · exact hOuterWeight
  · exact hOuterNormalized
  · intro outer _ output
    exact labelledBornWeight_nonneg
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer))
      (label outer) output
  · intro outer hOuter
    exact sum_labelledBornWeight_eq_one
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer))
      (label outer) (hSupport outer hOuter)
  · dsimp [tailBound]
    have hk : 0 < k := lt_trans hc hkc
    have hdiff : 0 < k - c := sub_pos.mpr hkc
    exact (mul_pos
      (div_pos (mul_pos hk hc) (pow_pos hdiff 2))
      (div_pos hL hn)).le
  · dsimp [collisionBound]
    exact mass_rectangularGroupUnionFailure_le
      outerWeight sample hOuterWeight hUniform hm
  · intro outer hOuter hGood
    have hInjectiveOne : forall index,
        SubsetSumInjectiveWithin
          (free outer ∩ rectangularGroups N m index) (sample outer) := by
      intro index
      exact subsetSumInjectiveWithin_free_inter_of_goodOuter
        (groupUnionFamily (rectangularGroups N m)) sample outer
        (free outer) (rectangularGroups N m index) hGood
        (group_mem_groupUnionFamily (rectangularGroups N m) index)
    have hInjectivePair : forall left right, left ≠ right ->
        SubsetSumInjectiveWithin
          (free outer ∩
            (rectangularGroups N m left ∪ rectangularGroups N m right))
          (sample outer) := by
      intro left right _
      exact subsetSumInjectiveWithin_free_inter_of_goodOuter
        (groupUnionFamily (rectangularGroups N m)) sample outer
        (free outer)
        (rectangularGroups N m left ∪ rectangularGroups N m right) hGood
        (union_mem_groupUnionFamily (rectangularGroups N m) left right)
    have hTail := lowerTailMass_groupZeroIndicator_le_paper_bound
      (rectangularGroups N m) (free outer) (fixed outer)
      (sample outer) (residue outer) (label outer)
      target mean k c n L (hSupport outer hOuter)
      rectangularGroups_card_eq hInjectiveOne
      rectangularGroups_pairwiseDisjoint hInjectivePair
      hExactMean hMeanParameters hTargetParameters hc hn hL hkc
    dsimp [tailBound]
    unfold finiteMass
    unfold eventMass at hTail
    convert hTail using 1
    apply Finset.sum_congr rfl
    intro output _
    by_cases hEvent :
        indicatorSum N
            (groupZeroIndicator (rectangularGroups N m)) output < target <;>
      simp [hEvent]

/--
The exact-divisibility, power-of-two specialization.  Here the group width,
sample count, mean, and target are tied directly to natural-number parameters,
so the abstract exact-mean hypothesis of
`nested_lowerTailMass_rectangular_le` disappears.
-/
theorem nested_lowerTailMass_rectangular_exactParameters_le
    (outerWeight : Outer -> Rat)
    (sample : Outer -> (Fin N × Fin m) -> G)
    (free : Outer -> Finset (Fin N × Fin m))
    (fixed : Outer -> Mask (Fin N × Fin m))
    (residue : Outer -> G)
    (label : Outer -> Mask (Fin N × Fin m) -> Label)
    (k c n logN : Nat)
    (hOuterWeight : forall outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hUniform :
      HasUniformLocalMarginals
        (groupUnionFamily (rectangularGroups N m)) outerWeight sample)
    (hSupport : forall outer, outerWeight outer ≠ 0 ->
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer)).Nonempty)
    (hc : 0 < c) (hlogN : 0 < logN) (hkc : c < k)
    (hn : n = 2 ^ logN)
    (hWidth : m = c * logN)
    (hPartition : N * m = k * n ^ (c + 1)) :
    nestedFiniteMass outerWeight
        (fun outer =>
          labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              (free outer) (fixed outer) (sample outer) (residue outer))
            (label outer))
        (fun _ output =>
          indicatorSum N
              (groupZeroIndicator (rectangularGroups N m)) output <
            (n : Rat) / (logN : Rat)) <=
      (N ^ 2 : Rat) *
          (((3 ^ (2 * m) - 1 : Nat) : Rat) / (Fintype.card G : Rat)) +
        ((k : Rat) * (c : Rat) / ((k : Rat) - (c : Rat)) ^ 2) *
          ((logN : Rat) / (n : Rat)) := by
  have hm : 0 < m := by
    rw [hWidth]
    exact Nat.mul_pos hc hlogN
  have hnPos : 0 < n := by
    rw [hn]
    exact pow_pos (by norm_num) logN
  have hcRat : (0 : Rat) < (c : Rat) := by exact_mod_cast hc
  have hnRat : (0 : Rat) < (n : Rat) := by exact_mod_cast hnPos
  have hlogNRat : (0 : Rat) < (logN : Rat) := by exact_mod_cast hlogN
  have hkcRat : (c : Rat) < (k : Rat) := by exact_mod_cast hkc
  apply nested_lowerTailMass_rectangular_le outerWeight sample free fixed
    residue label
    ((n : Rat) / (logN : Rat))
    (((k : Rat) / (c : Rat)) * ((n : Rat) / (logN : Rat)))
    (k : Rat) (c : Rat) (n : Rat) (logN : Rat)
    hOuterWeight hOuterNormalized hUniform hSupport hm
  · exact exactMean_of_powerOfTwo_and_exactPartition
      N m k c n logN hc hlogN hn hWidth hPartition
  · rfl
  · rfl
  · exact hcRat
  · exact hnRat
  · exact hlogNRat
  · exact hkcRat

/-- Under explicit collision and Chebyshev budgets, the exact-parameter
finite model has lower-tail failure mass at most `1/2`.  This is a genuine
constant bound, but the two budget hypotheses and the power-of-two/exact-
partition assumptions remain visible rather than being attributed to the
paper's rounded parameters. -/
theorem nested_lowerTailMass_rectangular_exactParameters_le_half
    (outerWeight : Outer -> Rat)
    (sample : Outer -> (Fin N × Fin m) -> G)
    (free : Outer -> Finset (Fin N × Fin m))
    (fixed : Outer -> Mask (Fin N × Fin m))
    (residue : Outer -> G)
    (label : Outer -> Mask (Fin N × Fin m) -> Label)
    (k c n logN : Nat)
    (hOuterWeight : forall outer, 0 <= outerWeight outer)
    (hOuterNormalized : (∑ outer, outerWeight outer) = 1)
    (hUniform :
      HasUniformLocalMarginals
        (groupUnionFamily (rectangularGroups N m)) outerWeight sample)
    (hSupport : forall outer, outerWeight outer ≠ 0 ->
      (maskCoordinateSubcubeResidueFibre
        (free outer) (fixed outer) (sample outer) (residue outer)).Nonempty)
    (hc : 0 < c) (hlogN : 0 < logN) (hkc : c < k)
    (hn : n = 2 ^ logN)
    (hWidth : m = c * logN)
    (hPartition : N * m = k * n ^ (c + 1))
    (hCollisionBudget :
      4 * N ^ 2 * (3 ^ (2 * m) - 1) <= Fintype.card G)
    (hTailBudget :
      (4 : Rat) * (k : Rat) * (c : Rat) * (logN : Rat) <=
        ((k : Rat) - (c : Rat)) ^ 2 * (n : Rat)) :
    nestedFiniteMass outerWeight
        (fun outer =>
          labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              (free outer) (fixed outer) (sample outer) (residue outer))
            (label outer))
        (fun _ output =>
          indicatorSum N
              (groupZeroIndicator (rectangularGroups N m)) output <
            (n : Rat) / (logN : Rat)) <=
      1 / 2 := by
  have hnPos : 0 < n := by
    rw [hn]
    exact pow_pos (by norm_num) logN
  have hnRat : (0 : Rat) < (n : Rat) := by exact_mod_cast hnPos
  have hkcRat : (c : Rat) < (k : Rat) := by exact_mod_cast hkc
  calc
    nestedFiniteMass outerWeight
        (fun outer =>
          labelledBornWeight
            (maskCoordinateSubcubeResidueFibre
              (free outer) (fixed outer) (sample outer) (residue outer))
            (label outer))
        (fun _ output =>
          indicatorSum N
              (groupZeroIndicator (rectangularGroups N m)) output <
            (n : Rat) / (logN : Rat)) <=
        (N ^ 2 : Rat) *
            (((3 ^ (2 * m) - 1 : Nat) : Rat) /
              (Fintype.card G : Rat)) +
          ((k : Rat) * (c : Rat) /
              ((k : Rat) - (c : Rat)) ^ 2) *
            ((logN : Rat) / (n : Rat)) :=
      nested_lowerTailMass_rectangular_exactParameters_le
        outerWeight sample free fixed residue label k c n logN
        hOuterWeight hOuterNormalized hUniform hSupport hc hlogN hkc hn
        hWidth hPartition
    _ <= 1 / 4 + 1 / 4 := add_le_add
      (rectangularCollisionBound_le_quarter hCollisionBudget)
      (paperTailBound_le_quarter
        (k : Rat) (c : Rat) (n : Rat) (logN : Rat)
        hnRat hkcRat hTailBudget)
    _ = 1 / 2 := by norm_num

end SimonDCP.Probability.LemmaOneFiniteModel
