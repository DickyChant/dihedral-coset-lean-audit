import Mathlib

/-!
# Pairwise-independent Bernoulli sums on a finite weighted space

This file isolates the elementary second-moment calculation needed by the
repaired proof of Lemma 1.  It deliberately uses finite sums over `ℚ`, rather
than measure theory: `weight` is a normalized nonnegative mass function and
`indicator i` is a `{0,1}`-valued random variable.
-/

namespace SimonDCP.Probability.PairwiseBernoulliTail

open scoped BigOperators

/-- Expectation with respect to a finite rational mass function. -/
def weightedMean {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (randomVariable : Ω → ℚ) : ℚ :=
  ∑ ω, weight ω * randomVariable ω

/-- The sum of a finite family of rational-valued random variables. -/
def indicatorSum {Ω : Type*} (G : ℕ)
    (indicator : Fin G → Ω → ℚ) (ω : Ω) : ℚ :=
  ∑ i, indicator i ω

/-- The total weight of an event in a finite weighted space. -/
def eventMass {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (event : Ω → Prop) [DecidablePred event] : ℚ :=
  ∑ ω, if event ω then weight ω else 0

lemma weightedMean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (weight : Ω → ℚ) (randomVariable : ι → Ω → ℚ) :
    weightedMean weight (fun ω => ∑ i, randomVariable i ω) =
      ∑ i, weightedMean weight (randomVariable i) := by
  classical
  simp only [weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma weightedMean_square_indicatorSum_eq_double_sum
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) :
    weightedMean weight (fun ω => (indicatorSum G indicator ω) ^ 2) =
      ∑ i, ∑ j, weightedMean weight (fun ω => indicator i ω * indicator j ω) := by
  classical
  simp only [weightedMean, indicatorSum, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma weightedMean_indicator_square
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℚ)
    (randomVariable : Ω → ℚ)
    (hIdempotent : ∀ ω, randomVariable ω * randomVariable ω = randomVariable ω) :
    weightedMean weight (fun ω => randomVariable ω * randomVariable ω) =
      weightedMean weight randomVariable := by
  unfold weightedMean
  apply Finset.sum_congr rfl
  intro ω _
  change weight ω * (randomVariable ω * randomVariable ω) =
    weight ω * randomVariable ω
  rw [hIdempotent]

lemma sum_if_eq_else_square (G : ℕ) (p : ℚ) :
    (∑ i : Fin G, ∑ j : Fin G, if i = j then p else p ^ 2) =
      (G : ℚ) * p + (G : ℚ) * ((G : ℚ) - 1) * p ^ 2 := by
  classical
  have hInner (i : Fin G) :
      (∑ j : Fin G, if i = j then p else p ^ 2) =
        p + ((G : ℚ) - 1) * p ^ 2 := by
    calc
      (∑ j : Fin G, if i = j then p else p ^ 2) =
          ∑ j : Fin G, (p ^ 2 + if i = j then p - p ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = (∑ _j : Fin G, p ^ 2) +
          ∑ j : Fin G, if i = j then p - p ^ 2 else 0 :=
        Finset.sum_add_distrib
      _ = (G : ℚ) * p ^ 2 + (p - p ^ 2) := by
        rw [Fintype.sum_ite_eq]
        simp
      _ = p + ((G : ℚ) - 1) * p ^ 2 := by ring
  simp_rw [hInner]
  simp
  ring

/-- Exact second moment of a sum of pairwise-independent Bernoulli variables. -/
theorem secondMoment_indicatorSum
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p : ℚ)
    (hIdempotent : ∀ i ω, indicator i ω * indicator i ω = indicator i ω)
    (hMean : ∀ i, weightedMean weight (indicator i) = p)
    (hPair : ∀ i j, i ≠ j →
      weightedMean weight (fun ω => indicator i ω * indicator j ω) = p ^ 2) :
    weightedMean weight (fun ω => (indicatorSum G indicator ω) ^ 2) =
      (G : ℚ) * p + (G : ℚ) * ((G : ℚ) - 1) * p ^ 2 := by
  rw [weightedMean_square_indicatorSum_eq_double_sum]
  calc
    (∑ i : Fin G, ∑ j : Fin G,
        weightedMean weight (fun ω => indicator i ω * indicator j ω)) =
        ∑ i : Fin G, ∑ j : Fin G, if i = j then p else p ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with hij
      · subst j
        rw [weightedMean_indicator_square weight (indicator i) (hIdempotent i), hMean]
      · exact hPair i j hij
    _ = (G : ℚ) * p + (G : ℚ) * ((G : ℚ) - 1) * p ^ 2 :=
      sum_if_eq_else_square G p

/-- Exact mean of the sum. -/
theorem mean_indicatorSum
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p : ℚ)
    (hMean : ∀ i, weightedMean weight (indicator i) = p) :
    weightedMean weight (indicatorSum G indicator) = (G : ℚ) * p := by
  change weightedMean weight (fun ω => ∑ i, indicator i ω) = (G : ℚ) * p
  rw [weightedMean_sum]
  simp_rw [hMean]
  simp

/-- A lower bound on every indicator mean adds to a lower bound on the sum. -/
theorem mean_indicatorSum_ge
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p : ℚ)
    (hMean : ∀ i, p ≤ weightedMean weight (indicator i)) :
    (G : ℚ) * p ≤ weightedMean weight (indicatorSum G indicator) := by
  change (G : ℚ) * p ≤ weightedMean weight (fun ω => ∑ i, indicator i ω)
  rw [weightedMean_sum]
  calc
    (G : ℚ) * p = ∑ _i : Fin G, p := by simp
    _ ≤ ∑ i : Fin G, weightedMean weight (indicator i) :=
      Finset.sum_le_sum fun i _ => hMean i

lemma weightedMean_centered_square
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℚ)
    (randomVariable : Ω → ℚ) (center : ℚ) :
    weightedMean weight (fun ω => (randomVariable ω - center) ^ 2) =
      weightedMean weight (fun ω => randomVariable ω ^ 2) -
        2 * center * weightedMean weight randomVariable +
        center ^ 2 * ∑ ω, weight ω := by
  unfold weightedMean
  calc
    (∑ ω, weight ω * (randomVariable ω - center) ^ 2) =
        ∑ ω, (weight ω * randomVariable ω ^ 2 -
          2 * center * (weight ω * randomVariable ω) + center ^ 2 * weight ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ ω, weight ω * randomVariable ω ^ 2) -
          2 * center * ∑ ω, weight ω * randomVariable ω +
          center ^ 2 * ∑ ω, weight ω := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Exact variance, written as a centered second moment. -/
theorem variance_indicatorSum
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p : ℚ)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hIdempotent : ∀ i ω, indicator i ω * indicator i ω = indicator i ω)
    (hMean : ∀ i, weightedMean weight (indicator i) = p)
    (hPair : ∀ i j, i ≠ j →
      weightedMean weight (fun ω => indicator i ω * indicator j ω) = p ^ 2) :
    weightedMean weight
        (fun ω => (indicatorSum G indicator ω - (G : ℚ) * p) ^ 2) =
      (G : ℚ) * p * (1 - p) := by
  have hFirst := mean_indicatorSum G weight indicator p hMean
  have hSecond := secondMoment_indicatorSum G weight indicator p hIdempotent hMean hPair
  rw [weightedMean_centered_square, hFirst, hSecond, hNormalized]
  ring

/-- The variance bound used as the numerator in Chebyshev's inequality. -/
theorem variance_indicatorSum_le
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p : ℚ)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hIdempotent : ∀ i ω, indicator i ω * indicator i ω = indicator i ω)
    (hMean : ∀ i, weightedMean weight (indicator i) = p)
    (hPair : ∀ i j, i ≠ j →
      weightedMean weight (fun ω => indicator i ω * indicator j ω) = p ^ 2)
    (hp : 0 ≤ p) :
    weightedMean weight
        (fun ω => (indicatorSum G indicator ω - (G : ℚ) * p) ^ 2) ≤
      (G : ℚ) * p := by
  rw [variance_indicatorSum G weight indicator p hNormalized hIdempotent hMean hPair]
  have hGpSq : 0 ≤ (G : ℚ) * p ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg p)
  have hGp : 0 ≤ (G : ℚ) * p := mul_nonneg (by positivity) hp
  nlinarith [hGp]

/-- Finite weighted Chebyshev inequality, proved directly from pointwise
nonnegativity.  Normalization is not needed for this form. -/
theorem finite_chebyshev
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℚ)
    (randomVariable : Ω → ℚ) (center threshold : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω) (hThreshold : 0 < threshold) :
    eventMass weight
        (fun ω => threshold ≤ |randomVariable ω - center|) ≤
      weightedMean weight (fun ω => (randomVariable ω - center) ^ 2) /
        threshold ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hThreshold)).2
  unfold eventMass weightedMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hEvent : threshold ≤ |randomVariable ω - center|
  · simp only [hEvent, if_true]
    apply mul_le_mul_of_nonneg_left _ (hWeight ω)
    apply (sq_le_sq).2
    simpa [abs_of_pos hThreshold] using hEvent
  · simp only [hEvent, if_false, zero_mul]
    exact mul_nonneg (hWeight ω) (sq_nonneg _)

/-- Chebyshev specialized to a pairwise-independent Bernoulli sum, with its
exact variance in the numerator. -/
theorem chebyshev_indicatorSum
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p threshold : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hIdempotent : ∀ i ω, indicator i ω * indicator i ω = indicator i ω)
    (hMean : ∀ i, weightedMean weight (indicator i) = p)
    (hPair : ∀ i j, i ≠ j →
      weightedMean weight (fun ω => indicator i ω * indicator j ω) = p ^ 2)
    (hThreshold : 0 < threshold) :
    eventMass weight (fun ω =>
        threshold ≤ |indicatorSum G indicator ω - (G : ℚ) * p|) ≤
      ((G : ℚ) * p * (1 - p)) / threshold ^ 2 := by
  calc
    eventMass weight (fun ω =>
        threshold ≤ |indicatorSum G indicator ω - (G : ℚ) * p|) ≤
        weightedMean weight
          (fun ω => (indicatorSum G indicator ω - (G : ℚ) * p) ^ 2) /
            threshold ^ 2 :=
      finite_chebyshev weight (indicatorSum G indicator) ((G : ℚ) * p)
        threshold hWeight hThreshold
    _ = ((G : ℚ) * p * (1 - p)) / threshold ^ 2 := by
      rw [variance_indicatorSum G weight indicator p hNormalized hIdempotent hMean hPair]

/-- A slightly weaker but often cleaner Chebyshev numerator. -/
theorem chebyshev_indicatorSum_le_mean
    {Ω : Type*} [Fintype Ω] (G : ℕ)
    (weight : Ω → ℚ) (indicator : Fin G → Ω → ℚ) (p threshold : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hIdempotent : ∀ i ω, indicator i ω * indicator i ω = indicator i ω)
    (hMean : ∀ i, weightedMean weight (indicator i) = p)
    (hPair : ∀ i j, i ≠ j →
      weightedMean weight (fun ω => indicator i ω * indicator j ω) = p ^ 2)
    (hp : 0 ≤ p) (hThreshold : 0 < threshold) :
    eventMass weight (fun ω =>
        threshold ≤ |indicatorSum G indicator ω - (G : ℚ) * p|) ≤
      ((G : ℚ) * p) / threshold ^ 2 := by
  calc
    eventMass weight (fun ω =>
        threshold ≤ |indicatorSum G indicator ω - (G : ℚ) * p|) ≤
        weightedMean weight
          (fun ω => (indicatorSum G indicator ω - (G : ℚ) * p) ^ 2) /
            threshold ^ 2 :=
      finite_chebyshev weight (indicatorSum G indicator) ((G : ℚ) * p)
        threshold hWeight hThreshold
    _ ≤ ((G : ℚ) * p) / threshold ^ 2 := by
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hThreshold)).2
      exact variance_indicatorSum_le G weight indicator p hNormalized hIdempotent hMean hPair hp

end SimonDCP.Probability.PairwiseBernoulliTail
