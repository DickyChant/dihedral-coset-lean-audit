import SimonDCP.Probability.LemmaThreeBornBounds

/-!
# Budgeted sector refinements for the Lemma 3 audit

This file packages the second Born-size-biased estimate from
`LemmaThreeBornBounds` for complex, unnormalized sector amplitudes.  A complete
outcome may be refined by an exact sector, such as an implicit value of `z*`.
The squared magnitude of a sector amplitude is its unnormalized sector energy.
The event that a normalized component is large is stated without division or
square roots:

```text
thresholdSq * outcomeMass outcome < sectorEnergy outcome sector.
```

Fine sectors may also be aggregated by an arbitrary map `bucketOf`.  Complex
amplitudes always add coherently inside a bucket.  Their squared magnitudes do
not add automatically.  Consequently every transfer of an energy bound from
fine sectors to buckets below retains an explicit additivity or domination
hypothesis.  In an application, that hypothesis is supplied by orthogonality
of the corresponding sectors and completeness (or contractivity) of the
measurement instrument.

This qualification is substantive for the paper.  Its implicit value `z*`
uses the adaptively selected set `A(D)`, so the sector assignment depends on
the measured outcome `D`.  Completeness of the underlying measurement does
not by itself normalize such an outcome-dependent refinement.  The finite
counterexample below has normalized coarse Born mass but refined sector energy
`3/2`.  Any application to `z*(D)` must therefore prove the total-sector-energy
premise separately.
-/

namespace SimonDCP.Probability.LemmaThreeSectorRefinement

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeBornBounds

variable {Outcome Fine Bucket : Type*}

/-- A complex amplitude attached to one complete outcome and one refined
sector.  It is unnormalized: its squared magnitude already includes the Born
weight of the complete outcome. -/
abbrev SectorAmplitude (Outcome Sector : Type*) := Outcome -> Sector -> Complex

/-- The real energy of one unnormalized complex sector amplitude. -/
def sectorEnergy (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) (fine : Fine) : Real :=
  Complex.normSq (amplitude outcome fine)

/-- The total energy of all refined sector amplitudes. -/
noncomputable def totalSectorEnergy
    [Fintype Outcome] [Fintype Fine]
    (amplitude : SectorAmplitude Outcome Fine) : Real :=
  ∑ outcome, ∑ fine, sectorEnergy amplitude outcome fine

/-- The coherent amplitude obtained after forgetting the refined sector. -/
noncomputable def coarseAmplitude
    [Fintype Fine] (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) : Complex :=
  ∑ fine, amplitude outcome fine

/-- The Born mass of the coherently aggregated coarse outcome. -/
noncomputable def coarseOutcomeMass
    [Fintype Fine] (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) : Real :=
  Complex.normSq (coarseAmplitude amplitude outcome)

/-- A refined component is large after normalization by the supplied coarse
outcome mass.  The multiplication-only definition is meaningful even when the
coarse outcome has zero mass. -/
def largeNormalizedSectorEvent
    [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (thresholdSq : Real) (outcome : Outcome) : Prop :=
  ∃ fine,
    thresholdSq * outcomeMass outcome < sectorEnergy amplitude outcome fine

/-- The sector event is exactly the generic normalized-component event from
`LemmaThreeBornBounds`. -/
theorem largeNormalizedSectorEvent_eq
    [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (thresholdSq : Real) :
    largeNormalizedSectorEvent outcomeMass amplitude thresholdSq =
      largeNormalizedComponentEvent outcomeMass
        (sectorEnergy amplitude) thresholdSq :=
  rfl

/-- A normalized sector tail is controlled solely by total unnormalized
sector energy.  No independence assumption is present.  The total-energy
hypothesis is not automatic when the sector assignment depends on the
outcome. -/
theorem largeNormalizedSectorMass_le
    [Fintype Outcome] [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (thresholdSq : Real)
    (hThreshold : 0 < thresholdSq)
    (hTotalEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude thresholdSq) <=
      1 / thresholdSq := by
  rw [largeNormalizedSectorEvent_eq]
  apply largeNormalizedComponentMass_le
  · exact hThreshold
  · intro outcome fine
    exact Complex.normSq_nonneg (amplitude outcome fine)
  · exact hTotalEnergy

/-- Budgeted version of the sector tail.  This makes the remaining semantic
obligation quantitative: total refined energy `budget` gives event mass at
most `budget / thresholdSq`. -/
theorem largeNormalizedSectorMass_le_budget
    [Fintype Outcome] [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (thresholdSq budget : Real)
    (hThreshold : 0 < thresholdSq)
    (hTotalEnergy : totalSectorEnergy amplitude <= budget) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude thresholdSq) <=
      budget / thresholdSq := by
  classical
  unfold realFiniteMass
  have hPointwise (outcome : Outcome) :
      (if largeNormalizedSectorEvent outcomeMass amplitude thresholdSq outcome
        then outcomeMass outcome else 0) <=
        (∑ fine, sectorEnergy amplitude outcome fine) / thresholdSq := by
    by_cases hLarge :
        largeNormalizedSectorEvent outcomeMass amplitude thresholdSq outcome
    · simp only [hLarge, if_true]
      obtain ⟨fine, hFine⟩ := hLarge
      have hFineLe :
          sectorEnergy amplitude outcome fine <=
            ∑ candidate, sectorEnergy amplitude outcome candidate := by
        exact Finset.single_le_sum
          (fun candidate _ =>
            Complex.normSq_nonneg (amplitude outcome candidate))
          (Finset.mem_univ fine)
      have hProduct :
          thresholdSq * outcomeMass outcome <
            ∑ candidate, sectorEnergy amplitude outcome candidate :=
        lt_of_lt_of_le hFine hFineLe
      exact le_of_lt ((lt_div_iff₀ hThreshold).2 (by
        simpa only [mul_comm] using hProduct))
    · simp only [hLarge, if_false]
      exact div_nonneg
        (Finset.sum_nonneg fun fine _ =>
          Complex.normSq_nonneg (amplitude outcome fine))
        (le_of_lt hThreshold)
  calc
    (∑ outcome,
        if largeNormalizedSectorEvent outcomeMass amplitude thresholdSq outcome
          then outcomeMass outcome else 0) <=
        ∑ outcome,
          (∑ fine, sectorEnergy amplitude outcome fine) / thresholdSq := by
      exact Finset.sum_le_sum fun outcome _ => hPointwise outcome
    _ = totalSectorEnergy amplitude / thresholdSq := by
      unfold totalSectorEnergy
      rw [Finset.sum_div]
    _ <= budget / thresholdSq :=
      (div_le_div_iff_of_pos_right hThreshold).2 hTotalEnergy

/-- Paper-facing name for the substantive adaptive-sector obligation.  The
outcome-dependent refinement is safe once its total energy is bounded by the
explicit budget `energyBudget`. -/
theorem adaptiveSectorTail_le_energyBudget
    [Fintype Outcome] [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (thresholdSq energyBudget : Real)
    (hThreshold : 0 < thresholdSq)
    (hEnergyBudget : totalSectorEnergy amplitude <= energyBudget) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude thresholdSq) <=
      energyBudget / thresholdSq :=
  largeNormalizedSectorMass_le_budget outcomeMass amplitude
    thresholdSq energyBudget hThreshold hEnergyBudget

/-- Conditional unit-energy specialization at squared threshold `2^(3n)`.
It gives a `2^(-3n)` upper tail when the explicit total-sector-energy premise
holds; that premise is not automatic for the paper's adaptive `z*`. -/
theorem exactSectorMass_le_paperThreshold
    [Fintype Outcome] [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat)
    (hTotalEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude
          ((2 : Real) ^ (3 * n))) <=
      1 / ((2 : Real) ^ (3 * n)) := by
  rw [largeNormalizedSectorEvent_eq]
  apply largeNormalizedComponentMass_le_paperThreshold
  · intro outcome fine
    exact Complex.normSq_nonneg (amplitude outcome fine)
  · exact hTotalEnergy

/-- It is enough for exact sectors to have total energy at most `2^(2n)`.
At the paper's squared threshold `2^(3n)`, the resulting event mass is at most
`2^(-n)`. -/
theorem exactSectorMass_le_of_dyadicBudget
    [Fintype Outcome] [Fintype Fine]
    (outcomeMass : Outcome -> Real)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat)
    (hTotalEnergy :
      totalSectorEnergy amplitude <= (2 : Real) ^ (2 * n)) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude
          ((2 : Real) ^ (3 * n))) <=
      1 / ((2 : Real) ^ n) := by
  calc
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass amplitude
          ((2 : Real) ^ (3 * n))) <=
        (2 : Real) ^ (2 * n) / (2 : Real) ^ (3 * n) := by
      apply largeNormalizedSectorMass_le_budget
      · positivity
      · exact hTotalEnergy
    _ = 1 / ((2 : Real) ^ n) := by
      rw [show 3 * n = 2 * n + n by omega, pow_add]
      field_simp

/-! ## An outcome-dependent refinement can increase total energy -/

/--
A two-path Hadamard-style counterexample.  At outcome `false`, the two path
contributions are grouped into one sector and add to `1`.  At outcome `true`,
the contributions `1/2` and `-1/2` are kept in different sectors.  Forgetting
the sectors gives coarse amplitudes `1` and `0`, while retaining the adaptive
sectors gives total energy `1 + 1/4 + 1/4 = 3/2`.
-/
noncomputable def outcomeDependentCounterexampleAmplitude :
    SectorAmplitude Bool Bool
  | false, false => 1
  | false, true => 0
  | true, false => (1 : Complex) / 2
  | true, true => -(1 : Complex) / 2

/-- The coarse outcome distribution in the adaptive counterexample is
normalized. -/
theorem outcomeDependentCounterexample_coarseMass_sum :
    (∑ outcome,
      coarseOutcomeMass outcomeDependentCounterexampleAmplitude outcome) = 1 := by
  norm_num [coarseOutcomeMass, coarseAmplitude,
    outcomeDependentCounterexampleAmplitude, Complex.normSq]

/-- The refined sector energy nevertheless equals `3/2`. -/
theorem outcomeDependentCounterexample_totalSectorEnergy :
    totalSectorEnergy outcomeDependentCounterexampleAmplitude =
      (3 : Real) / 2 := by
  norm_num [totalSectorEnergy, sectorEnergy,
    outcomeDependentCounterexampleAmplitude, Complex.normSq]

/-- Hence normalized coarse Born mass does not imply normalized energy for an
outcome-dependent sector refinement. -/
theorem outcomeDependentCounterexample_not_energy_normalized :
    ¬ (totalSectorEnergy outcomeDependentCounterexampleAmplitude <= 1) := by
  rw [outcomeDependentCounterexample_totalSectorEnergy]
  norm_num

/-!
The next example is the success-only fragment of the concrete three-singleton
audit.  Outcomes `0`, `1`, and `2` represent the masks `011`, `101`, and
`110`.  Thus `A(D)` is the singleton containing the unique zero coordinate.
For the state `|---⟩`, refinement by the adaptive bit `z = x_(A(D))` gives
sector amplitudes `1/2` and `-1/2` at each accepted mask.  They cancel in the
coarse amplitude, even though their retained energy is nonzero.
-/

/-- The accepted mask whose unique zero is at `zeroAt`. -/
def firstZeroAcceptedMask (zeroAt : Fin 3) : Fin 3 -> Bool :=
  fun coordinate => decide (coordinate ≠ zeroAt)

@[simp]
theorem firstZeroAcceptedMask_at_zero (zeroAt : Fin 3) :
    firstZeroAcceptedMask zeroAt zeroAt = false := by
  simp [firstZeroAcceptedMask]

theorem firstZeroAcceptedMask_away_from_zero
    (zeroAt coordinate : Fin 3) (hne : coordinate ≠ zeroAt) :
    firstZeroAcceptedMask zeroAt coordinate = true := by
  simp [firstZeroAcceptedMask, hne]

/-- Adaptive-sector amplitudes of the three accepted singleton-zero masks. -/
noncomputable def firstZeroSuccessSectorAmplitude : SectorAmplitude (Fin 3) Bool :=
  fun _outcome sector =>
    if sector then -(1 : Complex) / 2 else (1 : Complex) / 2

/-- Every accepted coarse amplitude cancels, so its total accepted Born mass
is zero. -/
theorem firstZeroSuccess_coarseMass_sum :
    (∑ outcome,
      coarseOutcomeMass firstZeroSuccessSectorAmplitude outcome) = 0 := by
  norm_num [coarseOutcomeMass, coarseAmplitude,
    firstZeroSuccessSectorAmplitude, Complex.normSq]

/-- Each of the three accepted masks retains sector energy `1/2`, for total
adaptive sector energy `3/2`. -/
theorem firstZeroSuccess_totalSectorEnergy :
    totalSectorEnergy firstZeroSuccessSectorAmplitude =
      (3 : Real) / 2 := by
  norm_num [totalSectorEnergy, sectorEnergy,
    firstZeroSuccessSectorAmplitude, Complex.normSq]

/-- The concrete success-only adaptive refinement therefore cannot obtain its
energy normalization from the vanishing coarse accepted mass. -/
theorem firstZeroSuccess_not_energy_normalized :
    ¬ (totalSectorEnergy firstZeroSuccessSectorAmplitude <= 1) := by
  rw [firstZeroSuccess_totalSectorEnergy]
  norm_num

/-! ## Coherent aggregation into arbitrary buckets -/

/-- The coherent sum of all fine amplitudes assigned to one bucket. -/
noncomputable def bucketAmplitude
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) (bucket : Bucket) : Complex :=
  ∑ fine, if bucketOf fine = bucket then amplitude outcome fine else 0

/-- The real energy of one coherently aggregated bucket amplitude. -/
noncomputable def bucketEnergy
    [Fintype Fine] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) (bucket : Bucket) : Real :=
  Complex.normSq (bucketAmplitude bucketOf amplitude outcome bucket)

/-- Total energy of the coherently aggregated bucket amplitudes. -/
noncomputable def totalBucketEnergy
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine) : Real :=
  ∑ outcome, ∑ bucket, bucketEnergy bucketOf amplitude outcome bucket

/-- Forgetting a fine label can always be expressed as first summing inside
each bucket and then summing the bucket amplitudes.  This is an amplitude
identity; it does not assert any corresponding identity of energies. -/
theorem sum_bucketAmplitude_eq_coarseAmplitude
    [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (outcome : Outcome) :
    (∑ bucket, bucketAmplitude bucketOf amplitude outcome bucket) =
      coarseAmplitude amplitude outcome := by
  classical
  unfold bucketAmplitude coarseAmplitude
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro fine _
  simp

/-- Global energy additivity for a bucket refinement.  This is the explicit
orthogonality premise: after summing over complete outcomes, the energy in
each coherently aggregated bucket equals the sum of the energies of its fine
sectors.  It is deliberately not derived from the amplitude aggregation
identity. -/
def BucketEnergyAdditive
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine) : Prop :=
  ∀ bucket,
    (∑ outcome, bucketEnergy bucketOf amplitude outcome bucket) =
      ∑ fine,
        if bucketOf fine = bucket then
          ∑ outcome, sectorEnergy amplitude outcome fine
        else 0

/-- Under the explicit global orthogonality premise, arbitrary bucket labels
preserve total refined energy exactly. -/
theorem totalBucketEnergy_eq_totalSectorEnergy_of_additive
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (hAdditive : BucketEnergyAdditive bucketOf amplitude) :
    totalBucketEnergy bucketOf amplitude = totalSectorEnergy amplitude := by
  classical
  unfold totalBucketEnergy totalSectorEnergy
  calc
    (∑ outcome, ∑ bucket,
        bucketEnergy bucketOf amplitude outcome bucket) =
        ∑ bucket, ∑ outcome,
          bucketEnergy bucketOf amplitude outcome bucket :=
      Finset.sum_comm
    _ = ∑ bucket, ∑ fine,
        if bucketOf fine = bucket then
          ∑ outcome, sectorEnergy amplitude outcome fine
        else 0 := by
      apply Finset.sum_congr rfl
      intro bucket _
      exact hAdditive bucket
    _ = ∑ fine, ∑ outcome, sectorEnergy amplitude outcome fine := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro fine _
      simp
    _ = ∑ outcome, ∑ fine, sectorEnergy amplitude outcome fine :=
      Finset.sum_comm

/-- Minimal energy premise for coherent bucket aggregation.  It is useful for
postselected or contractive instruments, where equality need not be available
but total bucket energy is still bounded by total fine-sector energy. -/
def BucketEnergyControlled
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine) : Prop :=
  totalBucketEnergy bucketOf amplitude <= totalSectorEnergy amplitude

/-- Global energy additivity implies the weaker domination premise. -/
theorem bucketEnergyControlled_of_additive
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (hAdditive : BucketEnergyAdditive bucketOf amplitude) :
    BucketEnergyControlled bucketOf amplitude := by
  unfold BucketEnergyControlled
  rw [totalBucketEnergy_eq_totalSectorEnergy_of_additive
    bucketOf amplitude hAdditive]

/-- A normalized total fine-sector energy bound transfers to buckets under
the explicit domination premise. -/
theorem totalBucketEnergy_le_one_of_controlled
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (hControlled : BucketEnergyControlled bucketOf amplitude)
    (hTotalEnergy : totalSectorEnergy amplitude <= 1) :
    totalBucketEnergy bucketOf amplitude <= 1 :=
  hControlled.trans hTotalEnergy

/-- Bucket-sector tail at squared threshold `n^3`.  The total bucket-energy
bound remains explicit because coherent bucket sums do not satisfy a generic
`normSq` additivity law. -/
theorem bucketSectorMass_le_bucketThreshold
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (hn : 0 < n)
    (hTotalBucketEnergy : totalBucketEnergy bucketOf amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
      1 / ((n : Real) ^ 3) := by
  rw [largeNormalizedSectorEvent_eq]
  apply largeNormalizedComponentMass_le_bucketThreshold
  · exact hn
  · intro outcome bucket
    exact Complex.normSq_nonneg
      (bucketAmplitude bucketOf amplitude outcome bucket)
  · exact hTotalBucketEnergy

/-- A quadratic bucket-energy budget is sufficient for the joint bucket tail:
at squared threshold `n^3`, total bucket energy at most `n^2` gives event mass
at most `1/n`. -/
theorem bucketSectorMass_le_of_quadraticBudget
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (hn : 0 < n)
    (hTotalBucketEnergy :
      totalBucketEnergy bucketOf amplitude <= (n : Real) ^ 2) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
      1 / (n : Real) := by
  have hBudget :
      realFiniteMass outcomeMass
          (largeNormalizedSectorEvent outcomeMass
            (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
        (n : Real) ^ 2 / (n : Real) ^ 3 := by
    apply largeNormalizedSectorMass_le_budget
    · positivity
    · simpa [totalSectorEnergy, sectorEnergy, totalBucketEnergy, bucketEnergy]
        using hTotalBucketEnergy
  calc
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
        (n : Real) ^ 2 / (n : Real) ^ 3 := hBudget
    _ = 1 / (n : Real) := by
      have hnReal : (n : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hnReal]

/-- The bucket tail follows from a normalized fine-sector model plus an
explicit energy-domination certificate. -/
theorem bucketSectorMass_le_bucketThreshold_of_controlled
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (hn : 0 < n)
    (hControlled : BucketEnergyControlled bucketOf amplitude)
    (hTotalEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
      1 / ((n : Real) ^ 3) := by
  apply bucketSectorMass_le_bucketThreshold
  · exact hn
  · exact totalBucketEnergy_le_one_of_controlled
      bucketOf amplitude hControlled hTotalEnergy

/-- Orthogonal bucket sectors are a directly usable sufficient condition for
the bucket tail. -/
theorem bucketSectorMass_le_bucketThreshold_of_additive
    [Fintype Outcome] [Fintype Fine] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Fine -> Bucket)
    (amplitude : SectorAmplitude Outcome Fine)
    (n : Nat) (hn : 0 < n)
    (hAdditive : BucketEnergyAdditive bucketOf amplitude)
    (hTotalEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (bucketAmplitude bucketOf amplitude) ((n : Real) ^ 3)) <=
      1 / ((n : Real) ^ 3) := by
  apply bucketSectorMass_le_bucketThreshold_of_controlled
  · exact hn
  · exact bucketEnergyControlled_of_additive bucketOf amplitude hAdditive
  · exact hTotalEnergy

end SimonDCP.Probability.LemmaThreeSectorRefinement
