import SimonDCP.Probability.RestrictedParseval

/-!
# Restricted Parseval with occupied coherent labels

This file packages the one-fibre Parseval identity in the form needed after
Step 4 of the paper.  A finite hidden support is partitioned by its complete
orthogonal label.  Amplitudes add within a label fibre and probabilities add
between distinct labels.  The paper's extra sign `(-1)^(h*d_n)` is constant
inside each complete-label fibre, so multiplying a whole fibre by that unit
sign does not change any squared amplitude; unit coefficients therefore model
the remaining Walsh sum exactly.

The main lower bound is deterministic: for every finite hidden support, every
label map, and every set of output coordinates forced to zero, diagonal pairs
alone contribute the uniform baseline.  No independence or distributional
assumption on the measured Fourier samples is used.
-/

namespace SimonDCP.Probability.LabelledParseval

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval

variable {ι Label : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Label]

/-- Hidden terms in one occupied coherent-label fibre. -/
def labelFibre (support : Finset (Mask ι)) (label : Mask ι → Label)
    (labelValue : Label) : Finset (Mask ι) :=
  support.filter fun phi ↦ label phi = labelValue

/-- Complete labels occupied by at least one supported hidden term. -/
def occupiedLabels (support : Finset (Mask ι))
    (label : Mask ι → Label) : Finset Label :=
  support.image label

/--
Raw probability numerator at one output mask: signed amplitudes add inside a
complete-label fibre, and their squares add across orthogonal labels.
-/
def labelledSquaredAmplitude (support : Finset (Mask ι))
    (label : Mask ι → Label) (mask : Mask ι) : ℤ :=
  ∑ labelValue ∈ occupiedLabels support label,
    (signedAmplitude (labelFibre support label labelValue)
      (fun _ ↦ 1) mask) ^ 2

omit [Fintype ι] [DecidableEq ι] in
/-- The occupied label fibres form an exact partition of `support`. -/
theorem sum_card_labelFibre
    (support : Finset (Mask ι)) (label : Mask ι → Label) :
    ∑ labelValue ∈ occupiedLabels support label,
        (labelFibre support label labelValue).card = support.card := by
  simpa [occupiedLabels, labelFibre] using
    (Finset.card_eq_sum_card_image label support).symm

/--
Labelled restricted Parseval.  The right-hand side counts projection
collisions separately inside every occupied coherent-label fibre.
-/
theorem labelled_restricted_parseval
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) :
    (∑ mask : MasksVanishingOn fixed,
        labelledSquaredAmplitude support label mask) =
      (Fintype.card (MasksVanishingOn fixed) : ℤ) *
        ∑ labelValue ∈ occupiedLabels support label,
          (projectionCollisionCount fixed
            (labelFibre support label labelValue) : ℤ) := by
  classical
  calc
    (∑ mask : MasksVanishingOn fixed,
        labelledSquaredAmplitude support label mask) =
        ∑ labelValue ∈ occupiedLabels support label,
          ∑ mask : MasksVanishingOn fixed,
            (signedAmplitude (labelFibre support label labelValue)
              (fun _ ↦ 1) mask) ^ 2 := by
      simp only [labelledSquaredAmplitude]
      rw [Finset.sum_comm]
    _ = ∑ labelValue ∈ occupiedLabels support label,
          (Fintype.card (MasksVanishingOn fixed) : ℤ) *
            (projectionCollisionCount fixed
              (labelFibre support label labelValue) : ℤ) := by
      apply Finset.sum_congr rfl
      intro labelValue hlabelValue
      exact restricted_parseval_unit fixed
        (labelFibre support label labelValue)
    _ = (Fintype.card (MasksVanishingOn fixed) : ℤ) *
          ∑ labelValue ∈ occupiedLabels support label,
            (projectionCollisionCount fixed
              (labelFibre support label labelValue) : ℤ) := by
      rw [Finset.mul_sum]

/--
Universal diagonal lower bound after summing all occupied complete labels.
This is the algebraic core of `Pr[D_A = 0 | Y,z'] ≥ 2^(-|A|)`.
-/
theorem labelled_restricted_sum_ge_diagonal
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) :
    (Fintype.card (MasksVanishingOn fixed) : ℤ) * support.card ≤
      ∑ mask : MasksVanishingOn fixed,
        labelledSquaredAmplitude support label mask := by
  rw [labelled_restricted_parseval]
  apply mul_le_mul_of_nonneg_left
  · calc
      (support.card : ℤ) =
          ∑ labelValue ∈ occupiedLabels support label,
            ((labelFibre support label labelValue).card : ℤ) := by
        exact_mod_cast (sum_card_labelFibre support label).symm
      _ ≤ ∑ labelValue ∈ occupiedLabels support label,
          (projectionCollisionCount fixed
            (labelFibre support label labelValue) : ℤ) := by
        apply Finset.sum_le_sum
        intro labelValue hlabelValue
        exact_mod_cast support_card_le_projectionCollisionCount fixed
          (labelFibre support label labelValue)
  · exact Int.natCast_nonneg _

/-- The same universal lower bound with the mask-space cardinality evaluated. -/
theorem labelled_restricted_sum_ge_diagonal_pow
    (fixed : Finset ι) (support : Finset (Mask ι))
    (label : Mask ι → Label) :
    (2 : ℤ) ^ (Fintype.card ι - fixed.card) * support.card ≤
      ∑ mask : MasksVanishingOn fixed,
        labelledSquaredAmplitude support label mask := by
  have hcard : (Fintype.card (MasksVanishingOn fixed) : ℤ) =
      (2 : ℤ) ^ (Fintype.card ι - fixed.card) := by
    exact_mod_cast card_masksVanishingOn fixed
  rw [← hcard]
  exact labelled_restricted_sum_ge_diagonal fixed support label

end SimonDCP.Probability.LabelledParseval
