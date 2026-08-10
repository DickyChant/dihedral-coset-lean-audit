import SimonDCP.Probability.PairwiseBernoulliTail

/-!
# A first-moment bound for the number of faulty coordinates

This file isolates the part of the repaired Lemma 1 argument that converts a
small expected fault count into a high-probability lower bound on the number
of free coordinates.  No independence assumption is needed.

For nonnegative weights and a nonnegative random variable `X`, the finite
weighted Markov inequality gives

`P[t ≤ X] ≤ E[X] / t`.

At the paper's scale, if there are `Q` coordinates and

`E[faultCount] ≤ Q / (cPrime * L)`,

then the mass of outcomes with at least `Q / 2` faults is at most
`2 / (cPrime * L)`.  The event uses rational casts, so it has the intended
meaning even when `Q` is odd.
-/

namespace SimonDCP.Probability.FaultCountMarkov

open scoped BigOperators
open SimonDCP.Probability.PairwiseBernoulliTail

/-- Finite weighted Markov inequality.  Normalization of `weight` is not
needed: the same inequality holds for nonnegative subprobability masses. -/
theorem finite_markov
    {Ω : Type*} [Fintype Ω]
    (weight randomVariable : Ω → ℚ) (threshold : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hRandomVariable : ∀ ω, 0 ≤ randomVariable ω)
    (hThreshold : 0 < threshold) :
    eventMass weight (fun ω => threshold ≤ randomVariable ω) ≤
      weightedMean weight randomVariable / threshold := by
  apply (le_div_iff₀ hThreshold).2
  unfold eventMass weightedMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hEvent : threshold ≤ randomVariable ω
  · simp only [hEvent, if_true]
    exact mul_le_mul_of_nonneg_left hEvent (hWeight ω)
  · simp only [hEvent, if_false, zero_mul]
    exact mul_nonneg (hWeight ω) (hRandomVariable ω)

/-- The number of nonfaulty coordinates, with truncated natural subtraction.
In its intended use every fault count is at most `Q`. -/
def freeCount {Ω : Type*} (Q : ℕ) (faultCount : Ω → ℕ) (ω : Ω) : ℕ :=
  Q - faultCount ω

/-- A natural-number version of the deterministic half-free implication. -/
theorem half_le_freeCount_of_faultCount_le_half
    {Ω : Type*} (Q : ℕ) (faultCount : Ω → ℕ) (ω : Ω)
    (hGood : faultCount ω ≤ Q / 2) :
    Q / 2 ≤ freeCount Q faultCount ω := by
  unfold freeCount
  omega

/-- The same deterministic implication with the exact rational threshold
used by the Markov event. -/
theorem rational_half_le_freeCount_of_faultCount_le_half
    {Ω : Type*} (Q : ℕ) (faultCount : Ω → ℕ) (ω : Ω)
    (hGood : (faultCount ω : ℚ) ≤ (Q : ℚ) / 2) :
    (Q : ℚ) / 2 ≤ (freeCount Q faultCount ω : ℚ) := by
  have hFaultLeQCast : (faultCount ω : ℚ) ≤ (Q : ℚ) := by
    have hQNonnegative : (0 : ℚ) ≤ (Q : ℚ) := by positivity
    linarith
  have hFaultLeQ : faultCount ω ≤ Q := by
    exact_mod_cast hFaultLeQCast
  rw [freeCount, Nat.cast_sub hFaultLeQ]
  linarith

/-- Markov's inequality specialized to an arbitrary natural-valued fault
count and the threshold `Q / 2`.  The normalization hypothesis records that
the finite weighted space is a probability space, although Markov's
inequality itself only uses nonnegativity of the weights. -/
theorem rational_faultTailMass_le
    {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (faultCount : Ω → ℕ)
    (Q : ℕ) (cPrime L : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (_hNormalized : (∑ ω, weight ω) = 1)
    (hQ : 0 < Q) (hCPrime : 0 < cPrime) (hL : 0 < L)
    (hMean :
      weightedMean weight (fun ω => (faultCount ω : ℚ)) ≤
        (Q : ℚ) / (cPrime * L)) :
    eventMass weight
        (fun ω => (Q : ℚ) / 2 ≤ (faultCount ω : ℚ)) ≤
      2 / (cPrime * L) := by
  have hQCast : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
  have hThreshold : (0 : ℚ) < (Q : ℚ) / 2 := by positivity
  calc
    eventMass weight
        (fun ω => (Q : ℚ) / 2 ≤ (faultCount ω : ℚ)) ≤
        weightedMean weight (fun ω => (faultCount ω : ℚ)) /
          ((Q : ℚ) / 2) := by
      exact finite_markov weight (fun ω => (faultCount ω : ℚ))
        ((Q : ℚ) / 2) hWeight (fun _ => by positivity) hThreshold
    _ ≤ ((Q : ℚ) / (cPrime * L)) / ((Q : ℚ) / 2) :=
      (div_le_div_iff_of_pos_right hThreshold).2 hMean
    _ = 2 / (cPrime * L) := by
      field_simp [ne_of_gt hQCast, ne_of_gt hCPrime, ne_of_gt hL]

/-! ## From coordinate marginals to the expected fault count -/

/-- The number of coordinates declared faulty by a Boolean fault pattern. -/
def coordinateFaultCount {Ω : Type*} (Q : ℕ)
    (faulted : Fin Q → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ i, if faulted i ω = true then 1 else 0

/-- Rational indicator of a coordinate fault. -/
def faultIndicator {Ω ι : Type*}
    (faulted : ι → Ω → Bool) (i : ι) (ω : Ω) : ℚ :=
  if faulted i ω = true then 1 else 0

lemma weightedMean_faultIndicator_eq_eventMass
    {Ω ι : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (faulted : ι → Ω → Bool) (i : ι) :
    weightedMean weight (faultIndicator faulted i) =
      eventMass weight (fun ω => faulted i ω = true) := by
  unfold weightedMean eventMass faultIndicator
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hFault : faulted i ω = true <;> simp [hFault]

/-- Linearity of expectation turns per-coordinate marginal fault bounds into
an expected total-fault bound.  No relation between different coordinates is
assumed. -/
theorem mean_coordinateFaultCount_le_of_marginals
    {Ω : Type*} [Fintype Ω]
    (Q : ℕ) (weight : Ω → ℚ) (faulted : Fin Q → Ω → Bool) (p : ℚ)
    (hMarginal : ∀ i,
      eventMass weight (fun ω => faulted i ω = true) ≤ p) :
    weightedMean weight
        (fun ω => (coordinateFaultCount Q faulted ω : ℚ)) ≤
      (Q : ℚ) * p := by
  have hCountCast :
      (fun ω => (coordinateFaultCount Q faulted ω : ℚ)) =
        (fun ω => ∑ i, faultIndicator faulted i ω) := by
    funext ω
    simp [coordinateFaultCount, faultIndicator]
  rw [hCountCast, weightedMean_sum]
  calc
    (∑ i : Fin Q, weightedMean weight (faultIndicator faulted i)) ≤
        ∑ _i : Fin Q, p := by
      apply Finset.sum_le_sum
      intro i _
      rw [weightedMean_faultIndicator_eq_eventMass]
      exact hMarginal i
    _ = (Q : ℚ) * p := by simp

/-- Complete marginal-to-tail specialization at fault probability
`1 / (cPrime * L)` per coordinate. -/
theorem rational_faultTailMass_le_of_coordinate_marginals
    {Ω : Type*} [Fintype Ω]
    (Q : ℕ) (weight : Ω → ℚ) (faulted : Fin Q → Ω → Bool)
    (cPrime L : ℚ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hQ : 0 < Q) (hCPrime : 0 < cPrime) (hL : 0 < L)
    (hMarginal : ∀ i,
      eventMass weight (fun ω => faulted i ω = true) ≤
        1 / (cPrime * L)) :
    eventMass weight (fun ω =>
        (Q : ℚ) / 2 ≤ (coordinateFaultCount Q faulted ω : ℚ)) ≤
      2 / (cPrime * L) := by
  apply rational_faultTailMass_le weight (coordinateFaultCount Q faulted)
    Q cPrime L hWeight hNormalized hQ hCPrime hL
  calc
    weightedMean weight
        (fun ω => (coordinateFaultCount Q faulted ω : ℚ)) ≤
        (Q : ℚ) * (1 / (cPrime * L)) :=
      mean_coordinateFaultCount_le_of_marginals Q weight faulted
        (1 / (cPrime * L)) hMarginal
    _ = (Q : ℚ) / (cPrime * L) := by ring

end SimonDCP.Probability.FaultCountMarkov
