import SimonDCP.Probability.CoordinateSubcubeBorn
import SimonDCP.Probability.LemmaOneChebyshevParameters
import SimonDCP.Probability.PairwiseBernoulliTail

/-!
# Labelled Born weights and pairwise Bernoulli interfaces

This file places the labelled Walsh amplitudes on the common finite output
space `Mask I`.  It then packages the exact one-group and two-group Born
identities for coordinate-subcube residue fibres as the mean and pairwise
moment hypotheses used by the finite Chebyshev development.
-/

namespace SimonDCP.Probability.LabelledBornPairwiseTail

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.CoordinateSubcubeProjection
open SimonDCP.Probability.LabelledBornProbability
open SimonDCP.Probability.CoordinateSubcubeBorn
open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.LemmaOneChebyshevParameters

variable {I G Label : Type*}
  [Fintype I] [DecidableEq I]
  [AddCommGroup G] [DecidableEq G]
  [DecidableEq Label]

/-- The normalized labelled Born weight of one complete output mask. -/
noncomputable def labelledBornWeight
    (support : Finset (Mask I)) (label : Mask I → Label)
    (output : Mask I) : ℚ :=
  (labelledSquaredAmplitude support label output : ℚ) /
    labelledBornDenominator support

/-- Rational indicator that every output coordinate in `fixed` is zero. -/
noncomputable def zeroOnIndicator
    (fixed : Finset I) (output : Mask I) : ℚ :=
  if ∀ i ∈ fixed, output i = 0 then 1 else 0

omit [DecidableEq I] in
/-- Every labelled Born weight is nonnegative. -/
theorem labelledBornWeight_nonneg
    (support : Finset (Mask I)) (label : Mask I → Label)
    (output : Mask I) :
    0 ≤ labelledBornWeight support label output := by
  have hnumerator :
      0 ≤ labelledSquaredAmplitude support label output := by
    unfold labelledSquaredAmplitude
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hdenominator : 0 ≤ labelledBornDenominator support := by
    unfold labelledBornDenominator
    positivity
  exact div_nonneg (by exact_mod_cast hnumerator) hdenominator

/-- The all-zero indicator is idempotent. -/
theorem zeroOnIndicator_idempotent
    (fixed : Finset I) (output : Mask I) :
    zeroOnIndicator fixed output * zeroOnIndicator fixed output =
      zeroOnIndicator fixed output := by
  classical
  unfold zeroOnIndicator
  split_ifs <;> norm_num

/-- Summing a function over masks satisfying the zero-coordinate constraint
is the same as summing it over the corresponding subgroup subtype. -/
theorem sum_zeroOnIndicator_mul
    (fixed : Finset I) (f : Mask I → ℚ) :
    (∑ output : Mask I, zeroOnIndicator fixed output * f output) =
      ∑ output : MasksVanishingOn fixed, f output := by
  classical
  simp only [zeroOnIndicator]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  let e : {output : Mask I // ∀ i ∈ fixed, output i = 0} ≃
      MasksVanishingOn fixed :=
    { toFun := fun output ↦ ⟨output.1, output.2⟩
      invFun := fun output ↦ ⟨output.1, output.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa [e] using
    (e.sum_comp (fun output : MasksVanishingOn fixed ↦ f output))

/-- The expectation of the zero-coordinate indicator is exactly the
normalized labelled zero-event mass. -/
theorem weightedMean_zeroOnIndicator_eq_labelledZeroEventMass
    (fixed : Finset I) (support : Finset (Mask I))
    (label : Mask I → Label) :
    weightedMean (labelledBornWeight support label)
        (zeroOnIndicator fixed) =
      labelledZeroEventMass fixed support label := by
  classical
  unfold weightedMean labelledBornWeight
  calc
    (∑ output : Mask I,
        (labelledSquaredAmplitude support label output : ℚ) /
            labelledBornDenominator support *
          zeroOnIndicator fixed output) =
        (∑ output : Mask I,
            zeroOnIndicator fixed output *
              (labelledSquaredAmplitude support label output : ℚ)) /
          labelledBornDenominator support := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro output _
      ring
    _ = ((∑ output : MasksVanishingOn fixed,
          (labelledSquaredAmplitude support label output : ℚ)) /
            labelledBornDenominator support) := by
      rw [sum_zeroOnIndicator_mul fixed
        (fun output ↦
          (labelledSquaredAmplitude support label output : ℚ))]
    _ = labelledZeroEventMass fixed support label := by
      rw [labelledZeroEventMass]
      push_cast
      rfl

/-- A nonempty labelled Born support gives a normalized mass function on all
complete output masks. -/
theorem sum_labelledBornWeight_eq_one
    (support : Finset (Mask I)) (label : Mask I → Label)
    (hsupport : support.Nonempty) :
    (∑ output, labelledBornWeight support label output) = 1 := by
  have hmean :=
    weightedMean_zeroOnIndicator_eq_labelledZeroEventMass
      (∅ : Finset I) support label
  rw [labelledZeroEventMass_empty_eq_one support label hsupport] at hmean
  simpa [weightedMean, zeroOnIndicator] using hmean

/-- Exact mean of one all-zero group indicator on a coordinate-subcube
residue fibre. -/
theorem weightedMean_zeroOnIndicator_coordinateSubcube_eq
    (free fixedGroup : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hinjective : SubsetSumInjectiveWithin (free ∩ fixedGroup) sample) :
    weightedMean
        (labelledBornWeight
          (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
        (zeroOnIndicator fixedGroup) =
      (1 / 2 : ℚ) ^ fixedGroup.card := by
  rw [weightedMean_zeroOnIndicator_eq_labelledZeroEventMass]
  exact labelledZeroEventMass_maskCoordinateSubcubeResidueFibre_eq
    free fixedGroup fixed sample residue label hsupport hinjective

/-- Requiring two coordinate groups to vanish is the same Boolean event as
requiring their union to vanish. -/
theorem zeroOnIndicator_mul_eq_union
    (left right : Finset I) (output : Mask I) :
    zeroOnIndicator left output * zeroOnIndicator right output =
      zeroOnIndicator (left ∪ right) output := by
  classical
  unfold zeroOnIndicator
  by_cases hleft : ∀ i ∈ left, output i = 0
  · by_cases hright : ∀ i ∈ right, output i = 0
    · have hunion : ∀ i ∈ left ∪ right, output i = 0 := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hleft i hi
        · exact hright i hi
      rw [if_pos hleft, if_pos hright, if_pos hunion, one_mul]
    · have hunion : ¬ ∀ i ∈ left ∪ right, output i = 0 := by
        intro h
        apply hright
        intro i hi
        exact h i (Finset.mem_union_right left hi)
      rw [if_pos hleft, if_neg hright, if_neg hunion, mul_zero]
  · have hunion : ¬ ∀ i ∈ left ∪ right, output i = 0 := by
      intro h
      apply hleft
      intro i hi
      exact h i (Finset.mem_union_left right hi)
    rw [if_neg hleft, if_neg hunion, zero_mul]

/-- Exact pair moment of two disjoint all-zero group indicators.  Injectivity
is needed only on the free coordinates in the union. -/
theorem weightedMean_zeroOnIndicator_mul_coordinateSubcube_eq
    (free left right : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hdisjoint : Disjoint left right)
    (hinjective :
      SubsetSumInjectiveWithin (free ∩ (left ∪ right)) sample) :
    weightedMean
        (labelledBornWeight
          (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
        (fun output ↦
          zeroOnIndicator left output * zeroOnIndicator right output) =
      (1 / 2 : ℚ) ^ left.card * (1 / 2 : ℚ) ^ right.card := by
  rw [show (fun output ↦
      zeroOnIndicator left output * zeroOnIndicator right output) =
        zeroOnIndicator (left ∪ right) by
      funext output
      exact zeroOnIndicator_mul_eq_union left right output]
  rw [weightedMean_zeroOnIndicator_eq_labelledZeroEventMass]
  exact labelledZeroEventMass_disjoint_union_eq_mul
    free left right fixed sample residue label hsupport hdisjoint hinjective

section Family

variable {K r : ℕ}

/-- The all-zero indicator attached to one member of a finite coordinate
group family. -/
noncomputable def groupZeroIndicator
    (groups : Fin K → Finset I) (index : Fin K) (output : Mask I) : ℚ :=
  zeroOnIndicator (groups index) output

/-- Equal group sizes and local injectivity give every group the same exact
Bernoulli mean. -/
theorem groupZeroIndicator_mean_eq
    (groups : Fin K → Finset I)
    (free : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hcard : ∀ index, (groups index).card = r)
    (hinjective : ∀ index,
      SubsetSumInjectiveWithin (free ∩ groups index) sample) :
    ∀ index,
      weightedMean
          (labelledBornWeight
            (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
          (groupZeroIndicator groups index) =
        (1 / 2 : ℚ) ^ r := by
  intro index
  change weightedMean
      (labelledBornWeight
        (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
      (zeroOnIndicator (groups index)) = (1 / 2 : ℚ) ^ r
  rw [weightedMean_zeroOnIndicator_coordinateSubcube_eq
    free (groups index) fixed sample residue label hsupport
      (hinjective index), hcard index]

/-- Pairwise disjointness and injectivity on every two-group union give the
exact pair moment required by `PairwiseBernoulliTail`. -/
theorem groupZeroIndicator_pair_mean_eq
    (groups : Fin K → Finset I)
    (free : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hcard : ∀ index, (groups index).card = r)
    (hdisjoint : ∀ left right, left ≠ right →
      Disjoint (groups left) (groups right))
    (hinjective : ∀ left right, left ≠ right →
      SubsetSumInjectiveWithin
        (free ∩ (groups left ∪ groups right)) sample) :
    ∀ left right, left ≠ right →
      weightedMean
          (labelledBornWeight
            (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
          (fun output ↦
            groupZeroIndicator groups left output *
              groupZeroIndicator groups right output) =
        ((1 / 2 : ℚ) ^ r) ^ 2 := by
  intro left right hne
  change weightedMean
      (labelledBornWeight
        (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
      (fun output ↦
        zeroOnIndicator (groups left) output *
          zeroOnIndicator (groups right) output) =
    ((1 / 2 : ℚ) ^ r) ^ 2
  rw [weightedMean_zeroOnIndicator_mul_coordinateSubcube_eq
    free (groups left) (groups right) fixed sample residue label hsupport
      (hdisjoint left right hne) (hinjective left right hne),
    hcard left, hcard right]
  ring

/-- The coordinate-subcube labelled Born model supplies the four structural
hypotheses of the finite pairwise Bernoulli Chebyshev theorem. -/
theorem chebyshev_groupZeroIndicator_le_mean
    (groups : Fin K → Finset I)
    (free : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (threshold : ℚ)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hcard : ∀ index, (groups index).card = r)
    (hinjectiveOne : ∀ index,
      SubsetSumInjectiveWithin (free ∩ groups index) sample)
    (hdisjoint : ∀ left right, left ≠ right →
      Disjoint (groups left) (groups right))
    (hinjectivePair : ∀ left right, left ≠ right →
      SubsetSumInjectiveWithin
        (free ∩ (groups left ∪ groups right)) sample)
    (hthreshold : 0 < threshold) :
    eventMass
        (labelledBornWeight
          (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
        (fun output ↦
          threshold ≤
            |indicatorSum K (groupZeroIndicator groups) output -
              (K : ℚ) * (1 / 2 : ℚ) ^ r|) ≤
      ((K : ℚ) * (1 / 2 : ℚ) ^ r) / threshold ^ 2 := by
  apply chebyshev_indicatorSum_le_mean
  · exact fun output ↦
      labelledBornWeight_nonneg
        (maskCoordinateSubcubeResidueFibre free fixed sample residue)
        label output
  · exact sum_labelledBornWeight_eq_one
      (maskCoordinateSubcubeResidueFibre free fixed sample residue)
      label hsupport
  · exact fun index output ↦
      zeroOnIndicator_idempotent (groups index) output
  · exact groupZeroIndicator_mean_eq
      groups free fixed sample residue label hsupport hcard hinjectiveOne
  · exact groupZeroIndicator_pair_mean_eq
      groups free fixed sample residue label hsupport hcard hdisjoint
        hinjectivePair
  · positivity
  · exact hthreshold

/-- Paper-facing lower-tail bound for an equal-size family of disjoint
coordinate groups.  The exact mean hypothesis keeps divisibility and rounding
choices for the number of groups separate from the finite Born calculation. -/
theorem lowerTailMass_groupZeroIndicator_le_paper_bound
    (groups : Fin K → Finset I)
    (free : Finset I) (fixed : Mask I)
    (sample : I → G) (residue : G)
    (label : Mask I → Label)
    (target mean k c n L : ℚ)
    (hsupport :
      (maskCoordinateSubcubeResidueFibre
        free fixed sample residue).Nonempty)
    (hcard : ∀ index, (groups index).card = r)
    (hinjectiveOne : ∀ index,
      SubsetSumInjectiveWithin (free ∩ groups index) sample)
    (hdisjoint : ∀ left right, left ≠ right →
      Disjoint (groups left) (groups right))
    (hinjectivePair : ∀ left right, left ≠ right →
      SubsetSumInjectiveWithin
        (free ∩ (groups left ∪ groups right)) sample)
    (hExactMean : (K : ℚ) * (1 / 2 : ℚ) ^ r = mean)
    (hMeanParameters : mean = (k / c) * (n / L))
    (hTargetParameters : target = n / L)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    eventMass
        (labelledBornWeight
          (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
        (fun output ↦
          indicatorSum K (groupZeroIndicator groups) output < target) ≤
      (k * c / (k - c) ^ 2) * (L / n) := by
  apply lowerTailMass_le_paper_bound K
    (labelledBornWeight
      (maskCoordinateSubcubeResidueFibre free fixed sample residue) label)
    (groupZeroIndicator groups) ((1 / 2 : ℚ) ^ r)
    target mean k c n L
  · exact fun output ↦
      labelledBornWeight_nonneg
        (maskCoordinateSubcubeResidueFibre free fixed sample residue)
        label output
  · exact sum_labelledBornWeight_eq_one
      (maskCoordinateSubcubeResidueFibre free fixed sample residue)
      label hsupport
  · exact fun index output ↦
      zeroOnIndicator_idempotent (groups index) output
  · exact groupZeroIndicator_mean_eq
      groups free fixed sample residue label hsupport hcard hinjectiveOne
  · exact groupZeroIndicator_pair_mean_eq
      groups free fixed sample residue label hsupport hcard hdisjoint
        hinjectivePair
  · positivity
  · exact hExactMean
  · exact hMeanParameters
  · exact hTargetParameters
  · exact hc
  · exact hn
  · exact hL
  · exact hkc

end Family

end SimonDCP.Probability.LabelledBornPairwiseTail
