import SimonDCP.Probability.LemmaThreeSectorRefinement

/-!
# A conservative adaptive-fibre bound for Lemma 3

This module gives a sound upper bound for coherent sectors whose label may
depend on the measured outcome.  Cauchy--Schwarz bounds the squared magnitude
of a coherent sum by the size of its fibre times the incoherent energy in that
fibre.  Summing over all labels and outcomes therefore costs at most the
largest fibre size.

Unlike an orthogonal-refinement argument, this theorem allows the bucket map
to depend arbitrarily on the later outcome and can therefore model the paper's
operator order once the concrete fine amplitudes and their total-energy bound
are supplied.  Those identification and normalization premises are not
automatic.  If the total fine-amplitude energy is at most one and an adaptive
fibre can contain `2^(c*n)` fine paths, then a safe
squared threshold is `2^((c+1)*n)` for a joint `2^(-n)` tail.  This is much
larger than the paper's `2^(3*n)` threshold when `c = 12`; improving it
requires genuine information about the concrete fibres, signs, or subsequent
filters.
-/

namespace SimonDCP.Probability.LemmaThreeAdaptiveFibreUpperBound

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreeSectorRefinement

variable {Outcome Fine Bucket : Type*}

/-- Complex Cauchy--Schwarz on a finite sum, written using `normSq`. -/
theorem normSq_sum_le_card_mul_sum_normSq
    {α : Type*} (s : Finset α) (amplitude : α -> Complex) :
    Complex.normSq (∑ x ∈ s, amplitude x) <=
      (s.card : Real) * ∑ x ∈ s, Complex.normSq (amplitude x) := by
  classical
  have hRe := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun x => (amplitude x).re)
  have hIm := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun x => (amplitude x).im)
  rw [Complex.normSq_apply]
  simp only [Complex.re_sum, Complex.im_sum]
  calc
    (∑ x ∈ s, (amplitude x).re) * (∑ x ∈ s, (amplitude x).re) +
        (∑ x ∈ s, (amplitude x).im) * (∑ x ∈ s, (amplitude x).im) =
      (∑ x ∈ s, (amplitude x).re) ^ 2 +
        (∑ x ∈ s, (amplitude x).im) ^ 2 := by ring
    _ <= (s.card : Real) * ∑ x ∈ s, (amplitude x).re ^ 2 +
        (s.card : Real) * ∑ x ∈ s, (amplitude x).im ^ 2 :=
      add_le_add hRe hIm
    _ = (s.card : Real) * ∑ x ∈ s, Complex.normSq (amplitude x) := by
      simp_rw [Complex.normSq_apply]
      rw [Finset.sum_add_distrib]
      ring_nf

/-- Fine paths carrying one outcome-dependent bucket label. -/
noncomputable def adaptiveFibre
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (outcome : Outcome) (bucket : Bucket) : Finset Fine :=
  Finset.univ.filter fun fine => bucketOf outcome fine = bucket

/-- Every adaptive fibre is bounded by the size of the fine-label space. -/
theorem adaptiveFibre_card_le
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (outcome : Outcome) (bucket : Bucket) :
    (adaptiveFibre bucketOf outcome bucket).card <= Fintype.card Fine := by
  simpa [adaptiveFibre] using
    Finset.card_filter_le (Finset.univ : Finset Fine)
      (fun fine => bucketOf outcome fine = bucket)

/-- Coherent amplitude in an outcome-dependent bucket. -/
noncomputable def adaptiveBucketAmplitude
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine) : SectorAmplitude Outcome Bucket :=
  fun outcome bucket =>
    ∑ fine ∈ adaptiveFibre bucketOf outcome bucket, amplitude outcome fine

/-- Pointwise Cauchy bound for one adaptive bucket. -/
theorem adaptiveBucket_normSq_le
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) (bucket : Bucket) :
    Complex.normSq (adaptiveBucketAmplitude bucketOf amplitude outcome bucket) <=
      ((adaptiveFibre bucketOf outcome bucket).card : Real) *
        ∑ fine ∈ adaptiveFibre bucketOf outcome bucket,
          Complex.normSq (amplitude outcome fine) := by
  exact normSq_sum_le_card_mul_sum_normSq
    (adaptiveFibre bucketOf outcome bucket) (amplitude outcome)

/-- The adaptive fibres partition all fine labels for each fixed outcome. -/
theorem sum_adaptiveFibre_normSq
    [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) :
    (∑ bucket, ∑ fine ∈ adaptiveFibre bucketOf outcome bucket,
        Complex.normSq (amplitude outcome fine)) =
      ∑ fine, Complex.normSq (amplitude outcome fine) := by
  classical
  simp only [adaptiveFibre, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/--
If every outcome-dependent fibre contains at most `R` fine paths, coherent
aggregation increases total energy by at most the factor `R`.
-/
theorem totalSectorEnergy_adaptiveBucket_le
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (R : Nat)
    (hFibre : ∀ outcome bucket,
      (adaptiveFibre bucketOf outcome bucket).card <= R) :
    totalSectorEnergy (adaptiveBucketAmplitude bucketOf amplitude) <=
      (R : Real) * totalSectorEnergy amplitude := by
  classical
  unfold totalSectorEnergy sectorEnergy
  calc
    (∑ outcome, ∑ bucket,
        Complex.normSq
          (adaptiveBucketAmplitude bucketOf amplitude outcome bucket)) <=
      ∑ outcome, ∑ bucket,
        (R : Real) *
          ∑ fine ∈ adaptiveFibre bucketOf outcome bucket,
            Complex.normSq (amplitude outcome fine) := by
      apply Finset.sum_le_sum
      intro outcome _
      apply Finset.sum_le_sum
      intro bucket _
      calc
        Complex.normSq
            (adaptiveBucketAmplitude bucketOf amplitude outcome bucket) <=
          ((adaptiveFibre bucketOf outcome bucket).card : Real) *
            ∑ fine ∈ adaptiveFibre bucketOf outcome bucket,
              Complex.normSq (amplitude outcome fine) :=
          adaptiveBucket_normSq_le bucketOf amplitude outcome bucket
        _ <= (R : Real) *
            ∑ fine ∈ adaptiveFibre bucketOf outcome bucket,
              Complex.normSq (amplitude outcome fine) := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hFibre outcome bucket)
            (Finset.sum_nonneg fun fine _ =>
              Complex.normSq_nonneg (amplitude outcome fine))
    _ = (R : Real) * ∑ outcome, ∑ fine,
          Complex.normSq (amplitude outcome fine) := by
      simp_rw [← Finset.mul_sum]
      apply congrArg ((R : Real) * ·)
      apply Finset.sum_congr rfl
      intro outcome _
      exact sum_adaptiveFibre_normSq bucketOf amplitude outcome

/--
A normalized fine-path model and a uniform fibre-cardinality bound give a
joint adaptive-sector tail of `R / thresholdSq`.
-/
theorem adaptiveBucketTail_le_fibreCard
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (R : Nat) (thresholdSq : Real)
    (hThreshold : 0 < thresholdSq)
    (hFibre : ∀ outcome bucket,
      (adaptiveFibre bucketOf outcome bucket).card <= R)
    (hFineEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude) thresholdSq) <=
      (R : Real) / thresholdSq := by
  apply largeNormalizedSectorMass_le_budget
  · exact hThreshold
  · exact (totalSectorEnergy_adaptiveBucket_le
      bucketOf amplitude R hFibre).trans (by
        simpa using mul_le_mul_of_nonneg_left hFineEnergy (Nat.cast_nonneg R))

/--
Dyadic maximum-fibre bound.  Under the explicit fine-energy premise, fibres
of size at most `2^(c*n)` are safe at squared threshold `2^((c+1)*n)`, yielding
joint bad mass at most `2^(-n)`.
-/
theorem adaptiveBucketTail_le_dyadicFibreBound
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (c n : Nat)
    (hFibre : ∀ outcome bucket,
      (adaptiveFibre bucketOf outcome bucket).card <= 2 ^ (c * n))
    (hFineEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude)
          ((2 : Real) ^ ((c + 1) * n))) <=
      1 / ((2 : Real) ^ n) := by
  calc
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude)
          ((2 : Real) ^ ((c + 1) * n))) <=
      ((2 ^ (c * n) : Nat) : Real) / (2 : Real) ^ ((c + 1) * n) := by
        apply adaptiveBucketTail_le_fibreCard
        · positivity
        · exact hFibre
        · exact hFineEnergy
    _ = 1 / ((2 : Real) ^ n) := by
      norm_num [Nat.cast_pow]
      rw [show (c + 1) * n = c * n + n by simp [Nat.add_mul], pow_add]
      field_simp

/--
Fully generic cardinality specialization.  It needs no structural property of
the outcome-dependent bucket map beyond a bound on the entire fine space.
-/
theorem adaptiveBucketTail_le_of_fineCard
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Outcome -> Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (c n : Nat)
    (hFineCard : Fintype.card Fine <= 2 ^ (c * n))
    (hFineEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude)
          ((2 : Real) ^ ((c + 1) * n))) <=
      1 / ((2 : Real) ^ n) := by
  apply adaptiveBucketTail_le_dyadicFibreBound
  · intro outcome bucket
    exact (adaptiveFibre_card_le bucketOf outcome bucket).trans hFineCard
  · exact hFineEnergy

end SimonDCP.Probability.LemmaThreeAdaptiveFibreUpperBound
