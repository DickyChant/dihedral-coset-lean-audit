import SimonDCP.Probability.PairwiseBernoulliTail

/-!
# Chebyshev parameters for the repaired Lemma 1

This file turns the two-sided deviation estimate from
`PairwiseBernoulliTail` into the lower-tail estimate used in the repaired
proof of Lemma 1.  It also records the rational identity obtained after
substituting the paper's mean and target parameters.
-/

namespace SimonDCP.Probability.LemmaOneChebyshevParameters

open SimonDCP.Probability.PairwiseBernoulliTail

/-- Falling below `target` forces a deviation of at least `mean - target`
from a larger mean. -/
theorem lowerTailMass_le_deviationMass
    {Omega : Type*} [Fintype Omega] (G : Nat)
    (weight : Omega -> Rat) (indicator : Fin G -> Omega -> Rat)
    (p target : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hTarget : target < (G : Rat) * p) :
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
      eventMass weight (fun omega =>
        (G : Rat) * p - target <=
          |indicatorSum G indicator omega - (G : Rat) * p|) := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro omega _
  by_cases hLower : indicatorSum G indicator omega < target
  · have hBelowMean : indicatorSum G indicator omega - (G : Rat) * p <= 0 := by
      linarith
    have hDeviation :
        (G : Rat) * p - target <=
          |indicatorSum G indicator omega - (G : Rat) * p| := by
      rw [abs_of_nonpos hBelowMean]
      linarith
    simp only [hLower, hDeviation, if_true]
    exact le_rfl
  · by_cases hDeviation :
        (G : Rat) * p - target <=
          |indicatorSum G indicator omega - (G : Rat) * p|
    · simp only [hLower, hDeviation, if_false, if_true]
      exact hWeight omega
    · simp only [hLower, hDeviation, if_false]
      exact le_rfl

/-- The lower-tail form of Chebyshev needed by Lemma 1.  No divisibility
assumption on `G` is needed: the exact mean is simply `(G : Rat) * p`. -/
theorem lowerTailMass_le_mean_div_gap_sq
    {Omega : Type*} [Fintype Omega] (G : Nat)
    (weight : Omega -> Rat) (indicator : Fin G -> Omega -> Rat)
    (p target : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hNormalized : Finset.univ.sum weight = 1)
    (hIdempotent : forall i omega,
      indicator i omega * indicator i omega = indicator i omega)
    (hMean : forall i, weightedMean weight (indicator i) = p)
    (hPair : forall i j, Ne i j ->
      weightedMean weight (fun omega => indicator i omega * indicator j omega) = p ^ 2)
    (hp : 0 <= p) (hTarget : target < (G : Rat) * p) :
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
      ((G : Rat) * p) / ((G : Rat) * p - target) ^ 2 := by
  have hGap : 0 < (G : Rat) * p - target := sub_pos.mpr hTarget
  calc
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
        eventMass weight (fun omega =>
          (G : Rat) * p - target <=
            |indicatorSum G indicator omega - (G : Rat) * p|) :=
      lowerTailMass_le_deviationMass G weight indicator p target hWeight hTarget
    _ <= ((G : Rat) * p) / ((G : Rat) * p - target) ^ 2 :=
      chebyshev_indicatorSum_le_mean G weight indicator p
        ((G : Rat) * p - target) hWeight hNormalized hIdempotent hMean hPair hp hGap

/-- Rational simplification of the paper's Chebyshev ratio:

`mean = (k / c) * (n / L)` and `target = n / L` imply

`mean / (mean - target)^2 = (k*c/(k-c)^2) * (L/n)`.
-/
theorem paper_chebyshev_ratio
    (mean target k c n L : Rat)
    (hMean : mean = (k / c) * (n / L))
    (hTarget : target = n / L)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    mean / (mean - target) ^ 2 =
      (k * c / (k - c) ^ 2) * (L / n) := by
  rw [hMean, hTarget]
  have hc0 : Ne c 0 := ne_of_gt hc
  have hn0 : Ne n 0 := ne_of_gt hn
  have hL0 : Ne L 0 := ne_of_gt hL
  have hkc0 : Ne (k - c) 0 := ne_of_gt (sub_pos.mpr hkc)
  field_simp

/-- The parameterized lower-tail estimate in the exact form used by the
paper.  The hypothesis `hExactMean` separates the probabilistic theorem from
integer divisibility and rounding choices for the number of groups. -/
theorem lowerTailMass_le_paper_bound
    {Omega : Type*} [Fintype Omega] (G : Nat)
    (weight : Omega -> Rat) (indicator : Fin G -> Omega -> Rat)
    (p target mean k c n L : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hNormalized : Finset.univ.sum weight = 1)
    (hIdempotent : forall i omega,
      indicator i omega * indicator i omega = indicator i omega)
    (hIndicatorMean : forall i, weightedMean weight (indicator i) = p)
    (hPair : forall i j, Ne i j ->
      weightedMean weight (fun omega => indicator i omega * indicator j omega) = p ^ 2)
    (hp : 0 <= p)
    (hExactMean : (G : Rat) * p = mean)
    (hMeanParameters : mean = (k / c) * (n / L))
    (hTargetParameters : target = n / L)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
      (k * c / (k - c) ^ 2) * (L / n) := by
  have hTargetBelowMean : target < mean := by
    rw [hMeanParameters, hTargetParameters]
    have hncL : 0 < n / (c * L) := div_pos hn (mul_pos hc hL)
    calc
      n / L = c * (n / (c * L)) := by field_simp
      _ < k * (n / (c * L)) := mul_lt_mul_of_pos_right hkc hncL
      _ = (k / c) * (n / L) := by field_simp
  calc
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
        ((G : Rat) * p) / ((G : Rat) * p - target) ^ 2 :=
      lowerTailMass_le_mean_div_gap_sq G weight indicator p target hWeight
        hNormalized hIdempotent hIndicatorMean hPair hp
        (hExactMean.symm ▸ hTargetBelowMean)
    _ = mean / (mean - target) ^ 2 := by rw [hExactMean]
    _ = (k * c / (k - c) ^ 2) * (L / n) :=
      paper_chebyshev_ratio mean target k c n L hMeanParameters
        hTargetParameters hc hn hL hkc

end SimonDCP.Probability.LemmaOneChebyshevParameters
