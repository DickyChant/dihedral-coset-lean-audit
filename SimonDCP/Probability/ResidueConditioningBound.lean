import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rational Bayes bound for residue conditioning

This file isolates the algebraic conditioning estimate used in the proposed
repair of Lemma 1.  No probabilistic library is needed: `joint` and `marginal`
are rational masses, and the proof consists of division by a positive
marginal followed by an exact normalization identity.

The second theorem replaces the exceptional probabilities by the uniform
dyadic bounds that arise from an affine Boolean support of dimension `R`.
The notation `dyadicDecay (R - r)` represents `2 ^ (r - R)` when `r <= R`.
-/

namespace SimonDCP.Probability.ResidueConditioningBound

/-- The rational quantity `2 ^ (-exponent)`. -/
def dyadicDecay (exponent : ℕ) : ℚ :=
  ((2 : ℚ) ^ exponent)⁻¹

/-- A dyadic decay factor is strictly positive. -/
theorem dyadicDecay_pos (exponent : ℕ) : 0 < dyadicDecay exponent := by
  unfold dyadicDecay
  positivity

/-- A nontrivial dyadic decay factor is strictly below one. -/
theorem dyadicDecay_lt_one {exponent : ℕ} (hexponent : 0 < exponent) :
    dyadicDecay exponent < 1 := by
  unfold dyadicDecay
  exact inv_lt_one_of_one_lt₀
    (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (Nat.ne_of_gt hexponent))

/--
Pure rational form of the Bayes estimate in equation (7) of
`LEMMA1_REPAIR.md`.

The interval assumptions record the intended probabilistic interpretation.
Algebraically, the estimate itself only needs a positive modulus and a
positive marginal.  In particular, no assumption on the indicator is needed
for this exact form once positivity of `marginal` is supplied explicitly.
-/
theorem rational_bayes_residue_bound
    (p delta epsilon modulus indicator joint marginal : ℚ)
    (_hp_nonneg : 0 ≤ p) (_hp_le_one : p ≤ 1)
    (_hdelta_nonneg : 0 ≤ delta) (_hdelta_le_one : delta ≤ 1)
    (_hepsilon_nonneg : 0 ≤ epsilon) (_hepsilon_le_one : epsilon ≤ 1)
    (hmodulus : 0 < modulus)
    (hjoint :
      joint ≤ p * ((1 - delta) / modulus + delta))
    (hmarginal :
      marginal = (1 - epsilon) / modulus + epsilon * indicator)
    (hmarginal_pos : 0 < marginal) :
    joint / marginal ≤
      p * (1 + (modulus - 1) * delta) /
        (1 - epsilon + modulus * epsilon * indicator) := by
  have hdenominator_pos :
      0 < 1 - epsilon + modulus * epsilon * indicator := by
    calc
      0 < modulus * marginal := mul_pos hmodulus hmarginal_pos
      _ = 1 - epsilon + modulus * epsilon * indicator := by
        rw [hmarginal]
        field_simp [ne_of_gt hmodulus]
  calc
    joint / marginal ≤
        (p * ((1 - delta) / modulus + delta)) / marginal :=
      (div_le_div_iff_of_pos_right hmarginal_pos).2 hjoint
    _ = p * (1 + (modulus - 1) * delta) /
        (1 - epsilon + modulus * epsilon * indicator) := by
      rw [hmarginal]
      field_simp [ne_of_gt hmodulus, ne_of_gt hdenominator_pos]
      ring

/--
Uniform dyadic specialization of `rational_bayes_residue_bound`.

The assumptions `delta <= dyadicDecay (R - r)` and
`epsilon <= dyadicDecay R` are the rational forms of
`delta <= 2 ^ (r - R)` and `epsilon <= 2 ^ (-R)`.  Nonnegativity of the
indicator covers both values of the residue-zero indicator and lets us drop
its favorable contribution from the denominator.
-/
theorem rational_bayes_residue_bound_of_dyadic
    (R r : ℕ)
    (p delta epsilon modulus indicator joint marginal : ℚ)
    (hR_pos : 0 < R) (_hrR : r ≤ R)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hmodulus : 1 ≤ modulus) (hindicator_nonneg : 0 ≤ indicator)
    (hdelta : delta ≤ dyadicDecay (R - r))
    (hepsilon : epsilon ≤ dyadicDecay R)
    (hjoint :
      joint ≤ p * ((1 - delta) / modulus + delta))
    (hmarginal :
      marginal = (1 - epsilon) / modulus + epsilon * indicator) :
    joint / marginal ≤
      p * (1 + (modulus - 1) * dyadicDecay (R - r)) /
        (1 - dyadicDecay R) := by
  have hmodulus_pos : 0 < modulus := lt_of_lt_of_le zero_lt_one hmodulus
  have hepsilon_lt_one : epsilon < 1 :=
    lt_of_le_of_lt hepsilon (dyadicDecay_lt_one hR_pos)
  have hmarginal_pos : 0 < marginal := by
    rw [hmarginal]
    exact add_pos_of_pos_of_nonneg
      (div_pos (sub_pos.mpr hepsilon_lt_one) hmodulus_pos)
      (mul_nonneg hepsilon_nonneg hindicator_nonneg)
  have hexact := rational_bayes_residue_bound
    p delta epsilon modulus indicator joint marginal
      hp_nonneg hp_le_one hdelta_nonneg hdelta_le_one
      hepsilon_nonneg hepsilon_le_one hmodulus_pos
      hjoint hmarginal hmarginal_pos
  have hdyadic_denominator_pos : 0 < 1 - dyadicDecay R :=
    sub_pos.mpr (dyadicDecay_lt_one hR_pos)
  have hdenominator_lower :
      1 - dyadicDecay R ≤
        1 - epsilon + modulus * epsilon * indicator := by
    have hexceptional_nonneg :
        0 ≤ modulus * epsilon * indicator :=
      mul_nonneg (mul_nonneg (le_of_lt hmodulus_pos) hepsilon_nonneg)
        hindicator_nonneg
    linarith
  have hcoefficient_nonneg : 0 ≤ modulus - 1 := sub_nonneg.mpr hmodulus
  have hnumerator_nonneg :
      0 ≤ p * (1 + (modulus - 1) * delta) := by
    exact mul_nonneg hp_nonneg
      (by positivity [hcoefficient_nonneg, hdelta_nonneg])
  have hnumerator_le :
      p * (1 + (modulus - 1) * delta) ≤
        p * (1 + (modulus - 1) * dyadicDecay (R - r)) := by
    apply mul_le_mul_of_nonneg_left _ hp_nonneg
    simpa only [add_comm] using
      add_le_add_left
        (mul_le_mul_of_nonneg_left hdelta hcoefficient_nonneg) 1
  calc
    joint / marginal ≤
        p * (1 + (modulus - 1) * delta) /
          (1 - epsilon + modulus * epsilon * indicator) := hexact
    _ ≤ p * (1 + (modulus - 1) * delta) /
          (1 - dyadicDecay R) :=
      div_le_div_of_nonneg_left hnumerator_nonneg
        hdyadic_denominator_pos hdenominator_lower
    _ ≤ p * (1 + (modulus - 1) * dyadicDecay (R - r)) /
          (1 - dyadicDecay R) :=
      div_le_div_of_nonneg_right hnumerator_le hdyadic_denominator_pos.le

end SimonDCP.Probability.ResidueConditioningBound
