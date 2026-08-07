import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quantitative parameter audit for Lemma 4

This file checks only the deterministic algebra in the parameter calculation on
pages 13--14 of IACR ePrint 2026/1591.  It does not assume or prove the paper's
conditional pairwise-independence, balls-in-bins, or anti-cancellation claims.

The parameter `faultLoss` denotes the exponent loss written in the paper as
`c * n / (c' * log n)`.  Keeping it abstract avoids imposing an analytic model
of `log n` on an exponent calculation that is purely algebraic.

If the mean count is `2 ^ meanExponent`, its standard deviation under the
paper's variance-equals-mean premise has half that exponent.  Multiplication by
`kappa' = 2 ^ n` therefore cancels the `-n` in the standard-deviation exponent.
The displayed page-14 formula retains an extra `+n`; the theorems below expose
that discrepancy exactly.
-/

namespace SimonDCP.Probability.Lemma4Parameters

open scoped BigOperators

noncomputable section

/-- Base-two exponent of the paper's mean `mu`. -/
def meanExponent (c n logN faultLoss : ℝ) : ℝ :=
  c * n - faultLoss - 2 * n - c * logN

/-- Base-two exponent of `sqrt(mu)`, under the stated variance premise. -/
def standardDeviationExponent (c n logN faultLoss : ℝ) : ℝ :=
  meanExponent c n logN faultLoss / 2

/-- Correct exponent after multiplying the standard deviation by `2 ^ n`. -/
def correctedBinDeviationExponent (c n logN faultLoss : ℝ) : ℝ :=
  n + standardDeviationExponent c n logN faultLoss

/-- Exponent printed on page 14; it contains one additional copy of `n`. -/
def printedBinDeviationExponent (c n logN faultLoss : ℝ) : ℝ :=
  c * n / 2 - faultLoss / 2 + n - c * logN / 2

/--
Aggregate exponent obtained using at most `2 ^ n` bins and the Lemma 3 bound
`2 ^ (3 * n / 2)` for each implicit amplitude portion.  Its use as an error
bound still requires the paper's unproved coefficientwise and conditional
probability premises.
-/
def correctedTotalDeviationExponent (c n logN faultLoss : ℝ) : ℝ :=
  correctedBinDeviationExponent c n logN faultLoss -
      meanExponent c n logN faultLoss + n + 3 * n / 2

/-- Aggregate exponent obtained from the page-14 printed bin deviation. -/
def printedTotalDeviationExponent (c n logN faultLoss : ℝ) : ℝ :=
  printedBinDeviationExponent c n logN faultLoss -
      meanExponent c n logN faultLoss + n + 3 * n / 2

theorem correctedBinDeviationExponent_eq
    (c n logN faultLoss : ℝ) :
    correctedBinDeviationExponent c n logN faultLoss =
      c * n / 2 - faultLoss / 2 - c * logN / 2 := by
  simp only [correctedBinDeviationExponent, standardDeviationExponent,
    meanExponent]
  ring

/-- The printed bin-deviation exponent exceeds the corrected one by exactly `n`. -/
theorem printedBinDeviationExponent_eq_corrected_add_n
    (c n logN faultLoss : ℝ) :
    printedBinDeviationExponent c n logN faultLoss =
      correctedBinDeviationExponent c n logN faultLoss + n := by
  rw [correctedBinDeviationExponent_eq]
  simp only [printedBinDeviationExponent]
  ring

theorem correctedTotalDeviationExponent_eq
    (c n logN faultLoss : ℝ) :
    correctedTotalDeviationExponent c n logN faultLoss =
      (9 - c) * n / 2 + faultLoss / 2 + c * logN / 2 := by
  simp only [correctedTotalDeviationExponent, correctedBinDeviationExponent,
    standardDeviationExponent, meanExponent]
  ring

theorem printedTotalDeviationExponent_eq_corrected_add_n
    (c n logN faultLoss : ℝ) :
    printedTotalDeviationExponent c n logN faultLoss =
      correctedTotalDeviationExponent c n logN faultLoss + n := by
  simp only [printedTotalDeviationExponent, correctedTotalDeviationExponent]
  rw [printedBinDeviationExponent_eq_corrected_add_n]
  ring

theorem printedTotalDeviationExponent_eq
    (c n logN faultLoss : ℝ) :
    printedTotalDeviationExponent c n logN faultLoss =
      (11 - c) * n / 2 + faultLoss / 2 + c * logN / 2 := by
  rw [printedTotalDeviationExponent_eq_corrected_add_n,
    correctedTotalDeviationExponent_eq]
  ring

theorem correctedTotalDeviationExponent_c12
    (n logN faultLoss : ℝ) :
    correctedTotalDeviationExponent 12 n logN faultLoss =
      -(3 * n / 2) + faultLoss / 2 + 6 * logN := by
  rw [correctedTotalDeviationExponent_eq]
  ring

theorem printedTotalDeviationExponent_c12
    (n logN faultLoss : ℝ) :
    printedTotalDeviationExponent 12 n logN faultLoss =
      -(n / 2) + faultLoss / 2 + 6 * logN := by
  rw [printedTotalDeviationExponent_eq_corrected_add_n,
    correctedTotalDeviationExponent_c12]
  ring

/-- An explicit sufficient condition for the corrected `c = 12` exponent to
be at most `-n`.  For the paper's intended substitution this obligation is
`12*n/(c' * log n) + 12*log n <= n`. -/
theorem corrected_c12_le_neg_n
    {n logN faultLoss : ℝ}
    (hbudget : faultLoss + 12 * logN ≤ n) :
    correctedTotalDeviationExponent 12 n logN faultLoss ≤ -n := by
  rw [correctedTotalDeviationExponent_c12]
  linarith

theorem corrected_c12_lt_neg_n
    {n logN faultLoss : ℝ}
    (hbudget : faultLoss + 12 * logN < n) :
    correctedTotalDeviationExponent 12 n logN faultLoss < -n := by
  rw [correctedTotalDeviationExponent_c12]
  linarith

/-- Exponent comparison converted into the corresponding base-two bound. -/
theorem corrected_c12_rpow_le
    {n logN faultLoss : ℝ}
    (hbudget : faultLoss + 12 * logN ≤ n) :
    (2 : ℝ) ^ correctedTotalDeviationExponent 12 n logN faultLoss ≤
      (2 : ℝ) ^ (-n) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (corrected_c12_le_neg_n hbudget)

/-- With nonnegative loss terms and positive `n`, the exponent printed in the
paper is strictly larger than `-n`, so that printed calculation cannot imply
the displayed `2 ^ (-n)` bound. -/
theorem printed_c12_gt_neg_n
    {n logN faultLoss : ℝ}
    (hn : 0 < n) (hlogN : 0 ≤ logN) (hfaultLoss : 0 ≤ faultLoss) :
    -n < printedTotalDeviationExponent 12 n logN faultLoss := by
  rw [printedTotalDeviationExponent_c12]
  linarith

/-- If one retains the page-14 printed exponent instead of correcting its
extra `+n`, a stronger parameter budget still recovers an exponent at most
`-n`.  With nonnegative correction terms this becomes useful from `c = 14`
onward; at `c = 14` its right side is exactly `n`. -/
theorem printed_le_neg_n_of_budget
    {c n logN faultLoss : ℝ}
    (hbudget : faultLoss + c * logN ≤ (c - 13) * n) :
    printedTotalDeviationExponent c n logN faultLoss ≤ -n := by
  rw [printedTotalDeviationExponent_eq]
  linarith

theorem printed_c14_le_neg_n
    {n logN faultLoss : ℝ}
    (hbudget : faultLoss + 14 * logN ≤ n) :
    printedTotalDeviationExponent 14 n logN faultLoss ≤ -n := by
  apply printed_le_neg_n_of_budget
  norm_num at hbudget ⊢
  exact hbudget

/-! ## The `mu` versus `|A_(g_a)|` coefficient -/

/-- If every bin contains exactly `mean` elements, the total cardinality is
`number of bins * mean`. -/
theorem uniformBinTotal
    {β : Type*} (bins : Finset β) (mean : ℕ) :
    (∑ _ ∈ bins, mean) = bins.card * mean := by
  simp

/-- Constant multiplicity factors out of a weighted sum as `mean`, not as the
total cardinality across all bins. -/
theorem constantMultiplicityWeightedSum
    {β : Type*} (bins : Finset β) (coefficient : β → ℝ) (mean : ℝ) :
    (∑ b ∈ bins, mean * coefficient b) =
      mean * ∑ b ∈ bins, coefficient b := by
  rw [Finset.mul_sum]

/-- Binwise count errors give additive control of a signed weighted sum.  This
does not give multiplicative control when the reference weighted sum is zero or
very small. -/
theorem weightedSumErrorBound
    {β : Type*} (bins : Finset β)
    (count coefficient : β → ℝ) (mean error coefficientBound : ℝ)
    (herror : 0 ≤ error)
    (hcount : ∀ b ∈ bins, |count b - mean| ≤ error)
    (hcoefficient : ∀ b ∈ bins, |coefficient b| ≤ coefficientBound) :
    |(∑ b ∈ bins, count b * coefficient b) -
        mean * ∑ b ∈ bins, coefficient b| ≤
      (bins.card : ℝ) * error * coefficientBound := by
  have rewriteDifference :
      (∑ b ∈ bins, count b * coefficient b) -
          mean * ∑ b ∈ bins, coefficient b =
        ∑ b ∈ bins, (count b - mean) * coefficient b := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [rewriteDifference]
  calc
    |∑ b ∈ bins, (count b - mean) * coefficient b| ≤
        ∑ b ∈ bins, |(count b - mean) * coefficient b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ bins, error * coefficientBound := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul (hcount b hb) (hcoefficient b hb)
        (abs_nonneg _) herror
    _ = (bins.card : ℝ) * error * coefficientBound := by
      simp [mul_assoc]

/-! ## Replacing the unsupported `n` bound by the corollary's `n^(3/2)` -/

/-- Polynomial exponent of the high-bin relative deviation in Lemma 4. -/
def highBinRelativeExponent (c : ℝ) : ℝ :=
  1 - (c - 1) / 2

/-- After summing at most order-`n` pairs, `amplitudePower` records an available
bound of order `n ^ amplitudePower` for each implicit amplitude. -/
def aggregatePolynomialExponent (c amplitudePower : ℝ) : ℝ :=
  highBinRelativeExponent c + amplitudePower + 1

theorem aggregatePolynomialExponent_using_n
    (c : ℝ) :
    aggregatePolynomialExponent c 1 = 7 / 2 - c / 2 := by
  simp only [aggregatePolynomialExponent, highBinRelativeExponent]
  ring

/-- Using the corollary's stated `n^(3/2)` bound weakens the aggregate exponent
by only `1/2`; it does not require the unsupported replacement by `n`. -/
theorem aggregatePolynomialExponent_using_n_three_halves
    (c : ℝ) :
    aggregatePolynomialExponent c (3 / 2) = 4 - c / 2 := by
  simp only [aggregatePolynomialExponent, highBinRelativeExponent]
  ring

theorem aggregatePolynomialExponent_c12_three_halves :
    aggregatePolynomialExponent 12 (3 / 2) = -2 := by
  norm_num [aggregatePolynomialExponent, highBinRelativeExponent]

/-- The corrected use of `n^(3/2)` still gives at least inverse-linear decay
whenever `c >= 10`, in particular for the paper's `c >= 12`. -/
theorem aggregatePolynomialExponent_three_halves_le_neg_one
    {c : ℝ} (hc : 10 ≤ c) :
    aggregatePolynomialExponent c (3 / 2) ≤ -1 := by
  rw [aggregatePolynomialExponent_using_n_three_halves]
  linarith

end

end SimonDCP.Probability.Lemma4Parameters
