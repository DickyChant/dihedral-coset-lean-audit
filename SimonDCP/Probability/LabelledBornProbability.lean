import SimonDCP.Probability.ProjectionInjectivity
import Mathlib.Tactic.FieldSimp

/-!
# Normalized zero-coordinate mass for labelled Boolean amplitudes

This file supplies the rational normalization bridge for the swap-free repair
of Lemma 1.  The finite labelled squared amplitudes have total denominator
`2^Q * |support|`.  Combining that denominator with labelled restricted
Parseval proves that any chosen output-coordinate set is all zero with
probability at least `2^(-|fixed|)`.
-/

namespace SimonDCP.Probability.LabelledBornProbability

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval
open SimonDCP.Probability.LabelledParseval
open SimonDCP.Probability.ProjectionInjectivity

variable {ι Label : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Label]

/-- The standard Step-4 normalization denominator `2^Q * |support|`. -/
def labelledBornDenominator (support : Finset (Mask ι)) : ℚ :=
  (2 : ℚ) ^ Fintype.card ι * support.card

/--
Conditional mass of outputs that vanish on every coordinate in `fixed`, after
summing the squared amplitudes of all occupied complete labels.
-/
noncomputable def labelledZeroEventMass (fixed : Finset ι)
    (support : Finset (Mask ι)) (label : Mask ι → Label) : ℚ :=
  ((∑ mask : MasksVanishingOn fixed,
      labelledSquaredAmplitude support label mask : ℤ) : ℚ) /
    labelledBornDenominator support

/-- The surviving-mask ratio before simplifying it to `2^(-|fixed|)`. -/
def uniformZeroBaseline (fixed : Finset ι) : ℚ :=
  (2 : ℚ) ^ (Fintype.card ι - fixed.card) /
    (2 : ℚ) ^ Fintype.card ι

omit [DecidableEq ι] in
/-- Every finite coordinate set has cardinality at most the ambient type. -/
theorem fixed_card_le_fintype_card (fixed : Finset ι) :
    fixed.card ≤ Fintype.card ι := by
  simpa only [Finset.card_univ] using Finset.card_le_univ fixed

omit [DecidableEq ι] in
/-- The surviving-mask ratio is exactly the uniform all-zero probability. -/
theorem uniformZeroBaseline_eq (fixed : Finset ι) :
    uniformZeroBaseline fixed = (1 / 2 : ℚ) ^ fixed.card := by
  have hcard := fixed_card_le_fintype_card fixed
  have hsplit : Fintype.card ι - fixed.card + fixed.card = Fintype.card ι :=
    Nat.sub_add_cancel hcard
  have hleft : (2 : ℚ) ^ (Fintype.card ι - fixed.card) ≠ 0 := by
    positivity
  have hpow : (2 : ℚ) ^ Fintype.card ι =
      (2 : ℚ) ^ (Fintype.card ι - fixed.card) *
        (2 : ℚ) ^ fixed.card := by
    rw [← pow_add, hsplit]
  rw [uniformZeroBaseline, hpow]
  calc
    (2 : ℚ) ^ (Fintype.card ι - fixed.card) /
          ((2 : ℚ) ^ (Fintype.card ι - fixed.card) *
            (2 : ℚ) ^ fixed.card) =
        1 / (2 : ℚ) ^ fixed.card := by
      simpa only [mul_one] using
        (mul_div_mul_left (1 : ℚ) ((2 : ℚ) ^ fixed.card) hleft)
    _ = (1 / 2 : ℚ) ^ fixed.card :=
      (one_div_pow (2 : ℚ) fixed.card).symm

/--
The diagonal Parseval contribution yields the uniform baseline after dividing
by the exact Step-4 denominator.
-/
theorem uniformZeroBaseline_le_labelledZeroEventMass
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) (hsupport : support.Nonempty) :
    uniformZeroBaseline fixed ≤ labelledZeroEventMass fixed support label := by
  have hraw := labelled_restricted_sum_ge_diagonal_pow fixed support label
  have hrawQ :
      (2 : ℚ) ^ (Fintype.card ι - fixed.card) * support.card ≤
        ((∑ mask : MasksVanishingOn fixed,
          labelledSquaredAmplitude support label mask : ℤ) : ℚ) := by
    exact_mod_cast hraw
  have hsupportCard : (0 : ℚ) < support.card := by
    exact_mod_cast (Finset.card_pos.mpr hsupport)
  have hpow : (0 : ℚ) < (2 : ℚ) ^ Fintype.card ι := by
    positivity
  have hdenominator :
      0 < (2 : ℚ) ^ Fintype.card ι * support.card :=
    mul_pos hpow hsupportCard
  calc
    uniformZeroBaseline fixed =
        ((2 : ℚ) ^ (Fintype.card ι - fixed.card) * support.card) /
          ((2 : ℚ) ^ Fintype.card ι * support.card) := by
      rw [uniformZeroBaseline]
      field_simp
    _ ≤ ((∑ mask : MasksVanishingOn fixed,
          labelledSquaredAmplitude support label mask : ℤ) : ℚ) /
          ((2 : ℚ) ^ Fintype.card ι * support.card) :=
      (div_le_div_iff_of_pos_right hdenominator).2 hrawQ
    _ = labelledZeroEventMass fixed support label := by
      rfl

/--
Normalized form used by Lemma 1: every selected coordinate set is all zero
with conditional mass at least `2^(-|fixed|)`.
-/
theorem pow_le_labelledZeroEventMass
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) (hsupport : support.Nonempty) :
    (1 / 2 : ℚ) ^ fixed.card ≤ labelledZeroEventMass fixed support label := by
  rw [← uniformZeroBaseline_eq fixed]
  exact uniformZeroBaseline_le_labelledZeroEventMass
    fixed support label hsupport

/-- The labelled finite model has total normalized mass one. -/
theorem labelledZeroEventMass_empty_eq_one
    (support : Finset (Mask ι)) (label : Mask ι → Label)
    (hsupport : support.Nonempty) :
    labelledZeroEventMass ∅ support label = 1 := by
  have hcardNat : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport
  have hcardRat : (support.card : ℚ) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [labelledZeroEventMass,
    labelled_restricted_parseval_eq_diagonal ∅ support label
      (labelwiseProjectionInjective_empty support label)]
  simp [labelledBornDenominator, hcardRat]

end SimonDCP.Probability.LabelledBornProbability
