import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A lower-tail estimate from a bounded first moment

This file gives the elementary finite weighted-sum inequality used by the
inverse-polynomial repair strategy for Lemma 1.  It deliberately avoids
measure theory: a finite family of nonnegative weights of total mass one is
enough for both uniform counting distributions and rational probability
weights.

If a random variable `value` is bounded above by `upper`, then

`mean value ≤ threshold + (upper - threshold) * P[value ≥ threshold]`.

Consequently, a lower bound `mean value ≥ mu > threshold` forces

`P[value ≥ threshold] ≥ (mu - threshold) / (upper - threshold)`.
-/

namespace SimonDCP.Probability.BoundedTail

open scoped BigOperators

section LinearOrderedField

variable {𝕜 Ω : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Total mass of a finite weighted space. -/
def weightedMass (space : Finset Ω) (weight : Ω → 𝕜) : 𝕜 :=
  ∑ ω ∈ space, weight ω

/-- Unnormalised first moment of `value` in a finite weighted space. -/
def weightedMean (space : Finset Ω) (weight value : Ω → 𝕜) : 𝕜 :=
  ∑ ω ∈ space, weight ω * value ω

/-- Weight of the closed upper-tail event `threshold ≤ value`. -/
noncomputable def upperTailMass
    (space : Finset Ω) (weight value : Ω → 𝕜) (threshold : 𝕜) : 𝕜 :=
  ∑ ω ∈ space.filter fun ω => threshold ≤ value ω, weight ω

/--
The first moment of an upper-bounded variable is controlled by the mass of
its closed upper tail.  Normalisation is intentionally not assumed here, so
the lemma is also useful for subprobability weights and intermediate sums.
-/
theorem weightedMean_le_threshold_mul_mass_add_tail
    (space : Finset Ω) (weight value : Ω → 𝕜) (threshold upper : 𝕜)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hupper : ∀ ω ∈ space, value ω ≤ upper) :
    weightedMean space weight value ≤
      threshold * weightedMass space weight +
        (upper - threshold) * upperTailMass space weight value threshold := by
  classical
  have hpointwise : ∀ ω ∈ space,
      weight ω * value ω ≤
        threshold * weight ω +
          (upper - threshold) * (if threshold ≤ value ω then weight ω else 0) := by
    intro ω hω
    by_cases htail : threshold ≤ value ω
    · calc
        weight ω * value ω ≤ weight ω * upper :=
          mul_le_mul_of_nonneg_left (hupper ω hω) (hweight ω hω)
        _ = threshold * weight ω +
              (upper - threshold) * (if threshold ≤ value ω then weight ω else 0) := by
          simp [htail]
          ring
    · have hbelow : value ω ≤ threshold := le_of_not_ge htail
      calc
        weight ω * value ω ≤ weight ω * threshold :=
          mul_le_mul_of_nonneg_left hbelow (hweight ω hω)
        _ = threshold * weight ω +
              (upper - threshold) * (if threshold ≤ value ω then weight ω else 0) := by
          simp [htail, mul_comm]
  calc
    weightedMean space weight value = ∑ ω ∈ space, weight ω * value ω := rfl
    _ ≤ ∑ ω ∈ space,
          (threshold * weight ω +
            (upper - threshold) *
              (if threshold ≤ value ω then weight ω else 0)) := by
      exact Finset.sum_le_sum fun ω hω => hpointwise ω hω
    _ = threshold * weightedMass space weight +
          (upper - threshold) * upperTailMass space weight value threshold := by
      simp only [weightedMass, upperTailMass, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      rw [Finset.sum_filter]
      simp only [mul_ite, mul_zero]

/-- An upper bound on `value` also bounds its unnormalised first moment. -/
theorem weightedMean_le_upper_mul_mass
    (space : Finset Ω) (weight value : Ω → 𝕜) (upper : 𝕜)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hupper : ∀ ω ∈ space, value ω ≤ upper) :
    weightedMean space weight value ≤ upper * weightedMass space weight := by
  calc
    weightedMean space weight value = ∑ ω ∈ space, weight ω * value ω := rfl
    _ ≤ ∑ ω ∈ space, weight ω * upper := by
      exact Finset.sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left (hupper ω hω) (hweight ω hω)
    _ = upper * weightedMass space weight := by
      simp only [weightedMass, Finset.mul_sum, mul_comm]

/--
Finite weighted version of the bounded-tail inequality.  It applies over both
`ℚ` and `ℝ`: nonnegative weights have total mass one, `value` is bounded above
by `upper`, and its weighted mean is at least `mu`.
-/
theorem upperTailMass_ge_of_mean_ge
    (space : Finset Ω) (weight value : Ω → 𝕜)
    (threshold mu upper : 𝕜)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hmass : weightedMass space weight = 1)
    (hupper : ∀ ω ∈ space, value ω ≤ upper)
    (hmean : mu ≤ weightedMean space weight value)
    (hthreshold : threshold < upper) :
    (mu - threshold) / (upper - threshold) ≤
      upperTailMass space weight value threshold := by
  have hmeanUpper :=
    weightedMean_le_threshold_mul_mass_add_tail
      space weight value threshold upper hweight hupper
  rw [hmass, mul_one] at hmeanUpper
  apply (div_le_iff₀ (sub_pos.mpr hthreshold)).2
  linarith

/--
The bounded-tail inequality in its usual hypothesis form.  The premise
`threshold < mu` and the moment assumptions force `threshold < upper`, so no
separate nonzero-denominator premise is needed.
-/
theorem upperTailMass_ge_of_mean_ge_of_threshold_lt_mu
    (space : Finset Ω) (weight value : Ω → 𝕜)
    (threshold mu upper : 𝕜)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hmass : weightedMass space weight = 1)
    (hupper : ∀ ω ∈ space, value ω ≤ upper)
    (hmean : mu ≤ weightedMean space weight value)
    (hmu : threshold < mu) :
    (mu - threshold) / (upper - threshold) ≤
      upperTailMass space weight value threshold := by
  have hmeanUpper : weightedMean space weight value ≤ upper := by
    calc
      weightedMean space weight value ≤ upper * weightedMass space weight :=
        weightedMean_le_upper_mul_mass space weight value upper hweight hupper
      _ = upper := by rw [hmass, mul_one]
  have hthreshold : threshold < upper :=
    lt_of_lt_of_le hmu (hmean.trans hmeanUpper)
  exact upperTailMass_ge_of_mean_ge
    space weight value threshold mu upper hweight hmass hupper hmean hthreshold

/-- If `mu` is strictly above the threshold, the forced tail mass is positive. -/
theorem upperTailMass_pos_of_mean_ge
    (space : Finset Ω) (weight value : Ω → 𝕜)
    (threshold mu upper : 𝕜)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hmass : weightedMass space weight = 1)
    (hupper : ∀ ω ∈ space, value ω ≤ upper)
    (hmean : mu ≤ weightedMean space weight value)
    (hmu : threshold < mu) (hthreshold : threshold < upper) :
    0 < upperTailMass space weight value threshold := by
  have hbound := upperTailMass_ge_of_mean_ge
    space weight value threshold mu upper hweight hmass hupper hmean hthreshold
  have hratio : 0 < (mu - threshold) / (upper - threshold) :=
    div_pos (sub_pos.mpr hmu) (sub_pos.mpr hthreshold)
  exact lt_of_lt_of_le hratio hbound

end LinearOrderedField

/-! ## Rational specialization for the Lemma 1 parameter scale -/

section RationalSpecialization

variable {Ω : Type*}

/--
Algebraic simplification of the ratio arising from the Lemma 1 scale.

Here `a` is the target count, `k / c` is the multiplicative mean gain, and
`N` is the factor between the target count and the deterministic upper bound.
The assumption `1 ≤ N` is the natural regime in which that upper bound is at
least as large as the mean scale.
-/
theorem rational_scaled_tail_ratio
    (a c k N : ℚ) (ha : 0 < a) (hc : 0 < c) (hck : c < k) (hN : 1 ≤ N) :
    ((k / c) * a - a) / ((k / c) * (N * a) - a) =
      (k - c) / (k * N - c) := by
  have hk : 0 < k := lt_trans hc hck
  have hk_le_kN : k ≤ k * N := by
    nlinarith [mul_le_mul_of_nonneg_left hN (le_of_lt hk)]
  have hden : 0 < k * N - c := sub_pos.mpr (lt_of_lt_of_le hck hk_le_kN)
  have hrawDen : 0 < (k / c) * (N * a) - a := by
    have hfactor : (k / c) * (N * a) - a = a * (k * N - c) / c := by
      field_simp [ne_of_gt hc]
    rw [hfactor]
    exact div_pos (mul_pos ha hden) hc
  field_simp [ne_of_gt hc, ne_of_gt hden, ne_of_gt hrawDen]

/-- The simplified inverse-polynomial lower bound is strictly positive. -/
theorem rational_scaled_tail_ratio_pos
    (c k N : ℚ) (hc : 0 < c) (hck : c < k) (hN : 1 ≤ N) :
    0 < (k - c) / (k * N - c) := by
  have hk : 0 < k := lt_trans hc hck
  have hk_le_kN : k ≤ k * N := by
    nlinarith [mul_le_mul_of_nonneg_left hN (le_of_lt hk)]
  exact div_pos (sub_pos.mpr hck)
    (sub_pos.mpr (lt_of_lt_of_le hck hk_le_kN))

/--
Direct `ℚ`-valued bounded-tail corollary at the Lemma 1 parameter scale.

If the mean count is at least `(k / c) * a` and every count is at most
`(k / c) * (N * a)`, then the probability of reaching the target `a` is at
least `(k - c) / (k * N - c)`.  No integrality assumptions are needed at this
stage; later applications may cast natural count parameters into `ℚ`.
-/
theorem rational_upperTailMass_ge_scaled_parameters
    (space : Finset Ω) (weight value : Ω → ℚ) (a c k N : ℚ)
    (hweight : ∀ ω ∈ space, 0 ≤ weight ω)
    (hmass : weightedMass space weight = 1)
    (hupper : ∀ ω ∈ space, value ω ≤ (k / c) * (N * a))
    (hmean : (k / c) * a ≤ weightedMean space weight value)
    (ha : 0 < a) (hc : 0 < c) (hck : c < k) (hN : 1 ≤ N) :
    (k - c) / (k * N - c) ≤ upperTailMass space weight value a := by
  have hgain : 1 < k / c := by
    apply (lt_div_iff₀ hc).2
    simpa using hck
  have hmu : a < (k / c) * a := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hgain ha
  have hbound := upperTailMass_ge_of_mean_ge_of_threshold_lt_mu
    space weight value a ((k / c) * a) ((k / c) * (N * a))
      hweight hmass hupper hmean hmu
  rw [rational_scaled_tail_ratio a c k N ha hc hck hN] at hbound
  exact hbound

end RationalSpecialization

end SimonDCP.Probability.BoundedTail
