import SimonDCP.Probability.Lemma4Parameters

/-!
# A conditional repair interface for Lemma 4

The paper's balls-in-bins argument, if its conditional probability premises are
supplied, controls the number of state portions contributing to each low-part
bin. Such count control gives an additive comparison between the two high-bit
amplitudes. It does not by itself give the claimed multiplicative comparison,
because the common signed reference sum can cancel.

This file records the valid deterministic conclusion. The first theorem
compares two weighted amplitudes additively when both count functions are close
to the same mean. The second elementary theorem identifies the extra
anti-cancellation input needed to convert an additive estimate to a relative
one. The final theorem combines them into a repaired Lemma 4 interface.

All amplitudes here are real. This already captures the signed sums in the
proof sketch; a later complex-amplitude model can replace absolute values by
norms without changing the missing lower-bound obligation.
-/

namespace SimonDCP.Probability.Lemma4Repair

open scoped BigOperators

noncomputable section

/-- A finite weighted amplitude with one multiplicity for each low-part bin. -/
def weightedAmplitude
    {β : Type*} (bins : Finset β) (count coefficient : β → ℝ) : ℝ :=
  ∑ b ∈ bins, count b * coefficient b

/--
If the multiplicities for both high-bit branches are uniformly close to the
same mean, their signed weighted amplitudes are additively close. This is the
unconditional deterministic conclusion of the proposed balls-in-bins step.
-/
theorem weightedAmplitude_pair_additive
    {β : Type*} (bins : Finset β)
    (leftCount rightCount coefficient : β → ℝ)
    (mean error coefficientBound : ℝ)
    (herror : 0 ≤ error)
    (hleft : ∀ b ∈ bins, |leftCount b - mean| ≤ error)
    (hright : ∀ b ∈ bins, |rightCount b - mean| ≤ error)
    (hcoefficient : ∀ b ∈ bins, |coefficient b| ≤ coefficientBound) :
    |weightedAmplitude bins leftCount coefficient -
        weightedAmplitude bins rightCount coefficient| ≤
      2 * (bins.card : ℝ) * error * coefficientBound := by
  let reference := mean * ∑ b ∈ bins, coefficient b
  have hleftError :
      |weightedAmplitude bins leftCount coefficient - reference| ≤
        (bins.card : ℝ) * error * coefficientBound := by
    simpa only [weightedAmplitude, reference] using
      Lemma4Parameters.weightedSumErrorBound bins leftCount coefficient
        mean error coefficientBound herror hleft hcoefficient
  have hrightError :
      |reference - weightedAmplitude bins rightCount coefficient| ≤
        (bins.card : ℝ) * error * coefficientBound := by
    rw [abs_sub_comm]
    simpa only [weightedAmplitude, reference] using
      Lemma4Parameters.weightedSumErrorBound bins rightCount coefficient
        mean error coefficientBound herror hright hcoefficient
  calc
    |weightedAmplitude bins leftCount coefficient -
        weightedAmplitude bins rightCount coefficient| ≤
        |weightedAmplitude bins leftCount coefficient - reference| +
          |reference - weightedAmplitude bins rightCount coefficient| :=
      abs_sub_le _ _ _
    _ ≤ (bins.card : ℝ) * error * coefficientBound +
          (bins.card : ℝ) * error * coefficientBound :=
      add_le_add hleftError hrightError
    _ = 2 * (bins.card : ℝ) * error * coefficientBound := by ring

/--
An additive comparison becomes a relative comparison once the reference
amplitude is bounded away from zero. This is the anti-cancellation premise
missing from the multiplicative conclusion in the paper's Lemma 4 sketch.
-/
theorem relative_error_of_additive_error
    {reference comparison additiveError lowerBound : ℝ}
    (hlowerBound : 0 < lowerBound)
    (hreference : lowerBound ≤ |reference|)
    (hadditiveError : 0 ≤ additiveError)
    (hcomparison : |comparison - reference| ≤ additiveError) :
    |comparison / reference - 1| ≤ additiveError / lowerBound := by
  have habsReference : 0 < |reference| :=
    lt_of_lt_of_le hlowerBound hreference
  have hreferenceNe : reference ≠ 0 := abs_pos.mp habsReference
  calc
    |comparison / reference - 1| =
        |(comparison - reference) / reference| := by
      congr 1
      field_simp
    _ = |comparison - reference| / |reference| := abs_div _ _
    _ ≤ additiveError / |reference| :=
      (div_le_div_iff_of_pos_right habsReference).2 hcomparison
    _ ≤ additiveError / lowerBound :=
      div_le_div_of_nonneg_left hadditiveError hlowerBound hreference

/--
Conditional repaired form of the multiplicative step: near-uniform bin counts
give a relative amplitude estimate provided one high-bit branch also has a
positive amplitude lower bound. The paper supplies neither this lower bound
nor an equivalent phase-alignment argument.
-/
theorem weightedAmplitude_pair_relative
    {β : Type*} (bins : Finset β)
    (leftCount rightCount coefficient : β → ℝ)
    (mean error coefficientBound lowerBound : ℝ)
    (herror : 0 ≤ error)
    (hcoefficientBound : 0 ≤ coefficientBound)
    (hleft : ∀ b ∈ bins, |leftCount b - mean| ≤ error)
    (hright : ∀ b ∈ bins, |rightCount b - mean| ≤ error)
    (hcoefficient : ∀ b ∈ bins, |coefficient b| ≤ coefficientBound)
    (hlowerBound : 0 < lowerBound)
    (hantiCancellation :
      lowerBound ≤ |weightedAmplitude bins leftCount coefficient|) :
    |weightedAmplitude bins rightCount coefficient /
          weightedAmplitude bins leftCount coefficient - 1| ≤
      (2 * (bins.card : ℝ) * error * coefficientBound) / lowerBound := by
  apply relative_error_of_additive_error hlowerBound hantiCancellation
  · positivity
  · rw [abs_sub_comm]
    exact weightedAmplitude_pair_additive bins leftCount rightCount coefficient
      mean error coefficientBound herror hleft hright hcoefficient

end

end SimonDCP.Probability.Lemma4Repair
