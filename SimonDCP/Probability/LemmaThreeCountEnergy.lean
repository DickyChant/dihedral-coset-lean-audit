import SimonDCP.Probability.LemmaThreeToFourL2
import Mathlib.Tactic.FieldSimp

/-!
# Count-energy identities for the Lemma 3 L2 route

This file isolates the exact second-moment obligation on the A-side residue
counts.  For a fixed transcript, there is no random hash seed left: the count
energy is a deterministic quantity.  Its natural centre is the actual number
of selected paths divided by the number of buckets.  Changing that centre to
an externally predicted mean incurs an exact additional square.

The weighted theorem below explains precisely what is needed to recover the
usual balls-in-bins second moment after outcome-dependent selection.  It is
not enough that the unselected bucket labels are pairwise independent.  The
selected-pair collision moment must still factor by
`1 / numberOfBuckets` under the supplied weights.  The algebraic theorem does
not assume that those weights are a probability distribution; interpreting
the premise as a conditional collision probability additionally requires
nonnegative normalized weights and positive selected-pair mass.  No assertion
is made here that the paper's adaptive selection or Born-weighted transcript
law satisfies this premise.
-/

namespace SimonDCP.Probability.LemmaThreeCountEnergy

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeToFourL2

variable {Ball Bin Seed : Type*}

/-! ## Deterministic bucket counts -/

/-- The number of elements of `balls` assigned to one bucket, as a real
number. -/
noncomputable def bucketCount [DecidableEq Bin]
    (balls : Finset Ball) (bucket : Ball -> Bin) (z : Bin) : Real :=
  ∑ x ∈ balls, if bucket x = z then 1 else 0

/-- The number of ordered pairs of selected elements assigned to the same
bucket. -/
noncomputable def orderedCollisionCount [DecidableEq Bin]
    (balls : Finset Ball) (bucket : Ball -> Bin) : Real :=
  ∑ x ∈ balls, ∑ y ∈ balls, if bucket x = bucket y then 1 else 0

/-- Bucket counts sum to the total number of selected elements. -/
theorem sum_bucketCount [Fintype Bin] [DecidableEq Bin]
    (balls : Finset Ball) (bucket : Ball -> Bin) :
    (∑ z, bucketCount balls bucket z) = (balls.card : Real) := by
  classical
  unfold bucketCount
  rw [Finset.sum_comm]
  simp

/-- The sum of squared bucket counts is the ordered collision count. -/
theorem sum_sq_bucketCount_eq_orderedCollisionCount
    [Fintype Bin] [DecidableEq Bin]
    (balls : Finset Ball) (bucket : Ball -> Bin) :
    (∑ z, (bucketCount balls bucket z) ^ 2) =
      orderedCollisionCount balls bucket := by
  classical
  unfold bucketCount orderedCollisionCount
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : bucket x = bucket y
  · rw [hxy]
    simp
  · simp [hxy]

/-- Expansion of count error around an arbitrary centre. -/
theorem countErrorEnergy_eq_sum_sq_sub
    [Fintype Bin]
    (count : Bin -> Real) (mean : Real) :
    countErrorEnergy count mean =
      (∑ z, (count z) ^ 2) - 2 * mean * (∑ z, count z) +
        (Fintype.card Bin : Real) * mean ^ 2 := by
  classical
  unfold countErrorEnergy
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum,
    Finset.card_univ]
  simp only [mul_comm, mul_left_comm]

/--
Exact change-of-centre identity.  The first term uses the actual average
`total / numberOfBuckets`; the second term is the cost of replacing it by an
external mean.
-/
theorem countErrorEnergy_centering_identity
    [Fintype Bin] [Nonempty Bin]
    (count : Bin -> Real) (total mean : Real)
    (hTotal : (∑ z, count z) = total) :
    countErrorEnergy count mean =
      countErrorEnergy count
          (total / (Fintype.card Bin : Real)) +
        (Fintype.card Bin : Real) *
          (total / (Fintype.card Bin : Real) - mean) ^ 2 := by
  have hCardNat : Fintype.card Bin ≠ 0 := Fintype.card_ne_zero
  have hCardReal : (Fintype.card Bin : Real) ≠ 0 := by
    exact_mod_cast hCardNat
  rw [countErrorEnergy_eq_sum_sq_sub,
    countErrorEnergy_eq_sum_sq_sub, hTotal]
  field_simp
  ring

/-- The deterministic count energy at its actual mean is exactly the ordered
collision count minus the uniform collision baseline. -/
theorem countErrorEnergy_bucketCount_actualMean
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (balls : Finset Ball) (bucket : Ball -> Bin) :
    countErrorEnergy (bucketCount balls bucket)
        ((balls.card : Real) / (Fintype.card Bin : Real)) =
      orderedCollisionCount balls bucket -
        (balls.card : Real) ^ 2 / (Fintype.card Bin : Real) := by
  rw [countErrorEnergy_eq_sum_sq_sub,
    sum_sq_bucketCount_eq_orderedCollisionCount,
    sum_bucketCount]
  have hCardNat : Fintype.card Bin ≠ 0 := Fintype.card_ne_zero
  have hCardReal : (Fintype.card Bin : Real) ≠ 0 := by
    exact_mod_cast hCardNat
  field_simp
  ring

/-! ## Weighted adaptive selection -/

/-- Finite real-weighted expectation. -/
noncomputable def weightedMeanReal [Fintype Seed]
    (weight : Seed -> Real) (randomVariable : Seed -> Real) : Real :=
  ∑ seed, weight seed * randomVariable seed

/-- The selected balls at one seed/transcript. -/
noncomputable def selectedBalls [Fintype Ball]
    (selected : Seed -> Ball -> Bool) (seed : Seed) : Finset Ball :=
  Finset.univ.filter fun ball => selected seed ball = true

/-- The actual selected population size at one seed/transcript. -/
noncomputable def selectedTotal [Fintype Ball]
    (selected : Seed -> Ball -> Bool) (seed : Seed) : Real :=
  ((selectedBalls selected seed).card : Real)

/-- The bucket counts after outcome-dependent selection. -/
noncomputable def selectedBucketCount
    [Fintype Ball] [DecidableEq Bin]
    (selected : Seed -> Ball -> Bool) (bucket : Seed -> Ball -> Bin)
    (seed : Seed) (z : Bin) : Real :=
  bucketCount (selectedBalls selected seed) (bucket seed) z

/-- Ordered same-bucket collisions after outcome-dependent selection. -/
noncomputable def selectedCollisionCount
    [Fintype Ball] [DecidableEq Bin]
    (selected : Seed -> Ball -> Bool) (bucket : Seed -> Ball -> Bin)
    (seed : Seed) : Real :=
  orderedCollisionCount (selectedBalls selected seed) (bucket seed)

/-- The selected count energy at the actual per-seed mean has the exact
collision expansion. -/
theorem selectedCountErrorEnergy_actualMean
    [Fintype Ball] [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (selected : Seed -> Ball -> Bool) (bucket : Seed -> Ball -> Bin)
    (seed : Seed) :
    countErrorEnergy (selectedBucketCount selected bucket seed)
        (selectedTotal selected seed / (Fintype.card Bin : Real)) =
      selectedCollisionCount selected bucket seed -
        (selectedTotal selected seed) ^ 2 /
          (Fintype.card Bin : Real) := by
  exact countErrorEnergy_bucketCount_actualMean
    (selectedBalls selected seed) (bucket seed)

/-! ## The exact weighted pair-collision premise -/

/-- Indicator that one ball is selected at a seed/transcript. -/
def selectedIndicator
    (selected : Seed -> Ball -> Bool) (seed : Seed) (ball : Ball) : Real :=
  if selected seed ball = true then 1 else 0

/-- Indicator that two distinct candidate balls are both selected. -/
def selectedPairIndicator
    (selected : Seed -> Ball -> Bool)
    (seed : Seed) (left right : Ball) : Real :=
  if selected seed left = true ∧ selected seed right = true then 1 else 0

/-- Indicator that two candidate balls are both selected and collide. -/
def selectedPairCollisionIndicator [DecidableEq Bin]
    (selected : Seed -> Ball -> Bool) (bucket : Seed -> Ball -> Bin)
    (seed : Seed) (left right : Ball) : Real :=
  if selected seed left = true ∧ selected seed right = true ∧
      bucket seed left = bucket seed right then 1 else 0

/--
The correct moment-factorization replacement for bare pairwise independence:
for every distinct pair, the weighted selected-and-colliding moment is exactly
`1 / card Bin` times the weighted selected-pair moment.  Selection is inside
both sides of the equality.  With nonnegative normalized weights and positive
pair-selection mass, this is equivalent to the corresponding conditional
collision probability statement.
-/
def WeightedPairCollisionUniform
    [Fintype Seed] [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool)
    (bucket : Seed -> Ball -> Bin) : Prop :=
  ∀ left right, left ≠ right ->
    weightedMeanReal weight
        (fun seed => selectedPairCollisionIndicator selected bucket
          seed left right) =
      ((Fintype.card Bin : Real)⁻¹) *
        weightedMeanReal weight
          (fun seed => selectedPairIndicator selected seed left right)

/-- The selected population is the sum of the selection indicators. -/
theorem selectedTotal_eq_sum_indicator
    [Fintype Ball]
    (selected : Seed -> Ball -> Bool) (seed : Seed) :
    selectedTotal selected seed =
      ∑ ball, selectedIndicator selected seed ball := by
  classical
  unfold selectedTotal selectedBalls selectedIndicator
  rw [← Finset.sum_filter]
  simp

/-- The square of the selected population is the ordered selected-pair
indicator sum. -/
theorem selectedTotal_sq_eq_pairIndicatorSum
    [Fintype Ball]
    (selected : Seed -> Ball -> Bool) (seed : Seed) :
    (selectedTotal selected seed) ^ 2 =
      ∑ left, ∑ right,
        selectedPairIndicator selected seed left right := by
  classical
  rw [selectedTotal_eq_sum_indicator]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  unfold selectedIndicator selectedPairIndicator
  by_cases hLeft : selected seed left = true <;>
    by_cases hRight : selected seed right = true <;>
      simp [hLeft, hRight]

/-- The ordered collision count is the ordered selected-pair collision
indicator sum over the ambient ball type. -/
theorem selectedCollisionCount_eq_pairCollisionIndicatorSum
    [Fintype Ball] [DecidableEq Bin]
    (selected : Seed -> Ball -> Bool) (bucket : Seed -> Ball -> Bin)
    (seed : Seed) :
    selectedCollisionCount selected bucket seed =
      ∑ left, ∑ right,
        selectedPairCollisionIndicator selected bucket seed left right := by
  classical
  unfold selectedCollisionCount orderedCollisionCount selectedBalls
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro left _
  by_cases hLeft : selected seed left = true
  · simp only [hLeft, if_true]
    apply Finset.sum_congr rfl
    intro right _
    by_cases hRight : selected seed right = true
    · simp [selectedPairCollisionIndicator, hLeft, hRight]
    · simp [selectedPairCollisionIndicator, hLeft, hRight]
  · simp [selectedPairCollisionIndicator, hLeft]

/-- Weighted expectation commutes with a finite sum. -/
theorem weightedMeanReal_sum
    [Fintype Seed] [Fintype Ball]
    (weight : Seed -> Real) (value : Ball -> Seed -> Real) :
    weightedMeanReal weight (fun seed => ∑ ball, value ball seed) =
      ∑ ball, weightedMeanReal weight (value ball) := by
  classical
  unfold weightedMeanReal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Expected selected population, expanded ball by ball. -/
theorem weightedMeanReal_selectedTotal_eq_sum
    [Fintype Seed] [Fintype Ball]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool) :
    weightedMeanReal weight (selectedTotal selected) =
      ∑ ball, weightedMeanReal weight
        (fun seed => selectedIndicator selected seed ball) := by
  classical
  unfold weightedMeanReal
  simp_rw [selectedTotal_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Expected square of the selected population, expanded over ordered
pairs. -/
theorem weightedMeanReal_selectedTotal_sq_eq_pairIndicatorSum
    [Fintype Seed] [Fintype Ball]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool) :
    weightedMeanReal weight (fun seed => (selectedTotal selected seed) ^ 2) =
      ∑ left, ∑ right,
        weightedMeanReal weight
          (fun seed => selectedPairIndicator selected seed left right) := by
  classical
  unfold weightedMeanReal
  simp_rw [selectedTotal_sq_eq_pairIndicatorSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]

/-- Expected selected collision count, expanded over ordered pairs. -/
theorem weightedMeanReal_selectedCollisionCount_eq_pairSum
    [Fintype Seed] [Fintype Ball] [DecidableEq Bin]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool)
    (bucket : Seed -> Ball -> Bin) :
    weightedMeanReal weight (selectedCollisionCount selected bucket) =
      ∑ left, ∑ right,
        weightedMeanReal weight
          (fun seed => selectedPairCollisionIndicator selected bucket
            seed left right) := by
  classical
  unfold weightedMeanReal
  simp_rw [selectedCollisionCount_eq_pairCollisionIndicatorSum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]

/--
Under weighted pair-collision uniformity, the expected selected collision
count is the diagonal contribution plus the uniform fraction of the
off-diagonal selected pairs.
-/
theorem expected_selectedCollisionCount_eq
    [Fintype Seed] [Fintype Ball] [Fintype Bin] [DecidableEq Bin]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool)
    (bucket : Seed -> Ball -> Bin)
    (hPair : WeightedPairCollisionUniform weight selected bucket) :
    weightedMeanReal weight (selectedCollisionCount selected bucket) =
      ((Fintype.card Bin : Real)⁻¹) *
          weightedMeanReal weight
            (fun seed => (selectedTotal selected seed) ^ 2) +
        (1 - (Fintype.card Bin : Real)⁻¹) *
          weightedMeanReal weight (selectedTotal selected) := by
  classical
  rw [weightedMeanReal_selectedCollisionCount_eq_pairSum]
  rw [weightedMeanReal_selectedTotal_sq_eq_pairIndicatorSum]
  rw [weightedMeanReal_selectedTotal_eq_sum]
  let inverseBucketCount : Real := (Fintype.card Bin : Real)⁻¹
  have hTerm (left right : Ball) :
      weightedMeanReal weight
          (fun seed => selectedPairCollisionIndicator selected bucket
            seed left right) =
        inverseBucketCount *
            weightedMeanReal weight
              (fun seed => selectedPairIndicator selected seed left right) +
          if left = right then
            (1 - inverseBucketCount) *
              weightedMeanReal weight
                (fun seed => selectedIndicator selected seed left)
          else 0 := by
    by_cases hEqual : left = right
    · subst right
      have hCollisionDiagonal :
          weightedMeanReal weight
              (fun seed => selectedPairCollisionIndicator selected bucket
                seed left left) =
            weightedMeanReal weight
              (fun seed => selectedIndicator selected seed left) := by
        unfold weightedMeanReal selectedPairCollisionIndicator
          selectedIndicator
        apply Finset.sum_congr rfl
        intro seed _
        by_cases hSelected : selected seed left = true <;>
          simp [hSelected]
      have hPairDiagonal :
          weightedMeanReal weight
              (fun seed => selectedPairIndicator selected seed left left) =
            weightedMeanReal weight
              (fun seed => selectedIndicator selected seed left) := by
        unfold weightedMeanReal selectedPairIndicator selectedIndicator
        apply Finset.sum_congr rfl
        intro seed _
        by_cases hSelected : selected seed left = true <;>
          simp [hSelected]
      rw [hCollisionDiagonal, hPairDiagonal]
      simp only [if_pos]
      ring
    · simp only [if_neg hEqual, add_zero]
      exact hPair left right hEqual
  calc
    (∑ left, ∑ right,
        weightedMeanReal weight
          (fun seed => selectedPairCollisionIndicator selected bucket
            seed left right)) =
      ∑ left, ∑ right,
        (inverseBucketCount *
            weightedMeanReal weight
              (fun seed => selectedPairIndicator selected seed left right) +
          if left = right then
            (1 - inverseBucketCount) *
              weightedMeanReal weight
                (fun seed => selectedIndicator selected seed left)
          else 0) := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      exact hTerm left right
    _ = inverseBucketCount *
          (∑ left, ∑ right,
            weightedMeanReal weight
              (fun seed => selectedPairIndicator selected seed left right)) +
        (1 - inverseBucketCount) *
          ∑ left, weightedMeanReal weight
            (fun seed => selectedIndicator selected seed left) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum,
        Fintype.sum_ite_eq]
    _ = ((Fintype.card Bin : Real)⁻¹) *
          (∑ left, ∑ right,
            weightedMeanReal weight
              (fun seed => selectedPairIndicator selected seed left right)) +
        (1 - (Fintype.card Bin : Real)⁻¹) *
          ∑ left, weightedMeanReal weight
            (fun seed => selectedIndicator selected seed left) := by
      rfl

/--
The exact adaptive balls-in-bins second moment.  The count vector is centred
at its actual per-seed mean, so fluctuations in the total selected population
do not appear.  The result is linear in the expected selected population.
-/
theorem expected_selectedCountErrorEnergy_actualMean_eq
    [Fintype Seed] [Fintype Ball] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (weight : Seed -> Real) (selected : Seed -> Ball -> Bool)
    (bucket : Seed -> Ball -> Bin)
    (hPair : WeightedPairCollisionUniform weight selected bucket) :
    weightedMeanReal weight (fun seed =>
        countErrorEnergy (selectedBucketCount selected bucket seed)
          (selectedTotal selected seed / (Fintype.card Bin : Real))) =
      (1 - (Fintype.card Bin : Real)⁻¹) *
        weightedMeanReal weight (selectedTotal selected) := by
  have hCardNat : Fintype.card Bin ≠ 0 := Fintype.card_ne_zero
  have hCardReal : (Fintype.card Bin : Real) ≠ 0 := by
    exact_mod_cast hCardNat
  calc
    weightedMeanReal weight (fun seed =>
        countErrorEnergy (selectedBucketCount selected bucket seed)
          (selectedTotal selected seed / (Fintype.card Bin : Real))) =
      weightedMeanReal weight (selectedCollisionCount selected bucket) -
        (Fintype.card Bin : Real)⁻¹ *
          weightedMeanReal weight
            (fun seed => (selectedTotal selected seed) ^ 2) := by
      unfold weightedMeanReal
      simp_rw [selectedCountErrorEnergy_actualMean]
      calc
        (∑ seed, weight seed *
            (selectedCollisionCount selected bucket seed -
              selectedTotal selected seed ^ 2 /
                (Fintype.card Bin : Real))) =
          ∑ seed,
            (weight seed * selectedCollisionCount selected bucket seed -
              (Fintype.card Bin : Real)⁻¹ *
                (weight seed * selectedTotal selected seed ^ 2)) := by
            apply Finset.sum_congr rfl
            intro seed _
            field_simp
        _ = (∑ seed,
              weight seed * selectedCollisionCount selected bucket seed) -
            (Fintype.card Bin : Real)⁻¹ *
              ∑ seed, weight seed * selectedTotal selected seed ^ 2 := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (1 - (Fintype.card Bin : Real)⁻¹) *
        weightedMeanReal weight (selectedTotal selected) := by
      rw [expected_selectedCollisionCount_eq weight selected bucket hPair]
      ring

/-! ## Conditioning can destroy the count moment -/

/-- Two independent Boolean bucket labels on the unconditioned four-point
seed space. -/
def twoBitHash (seed : Bool × Bool) (ball : Bool) : Bool :=
  if ball then seed.2 else seed.1

/-- Every requested pair of bucket labels has exactly one preimage before
conditioning.  Thus the two ball labels are jointly uniform, and in
particular pairwise independent, on the full seed space. -/
theorem twoBitHash_jointFiber_card_eq_one (left right : Bool) :
    ((Finset.univ.filter fun seed : Bool × Bool =>
      twoBitHash seed false = left ∧
        twoBitHash seed true = right).card) = 1 := by
  cases left <;> cases right <;> native_decide

/-- The postselected seed space on which the two formerly independent labels
are equal. -/
abbrev EqualBitSeed := {seed : Bool × Bool // seed.1 = seed.2}

/-- After conditioning on equality, both balls always enter the same bucket.
The actual mean is one, but the count energy is two. -/
theorem equalBitCondition_countErrorEnergy_eq_two (seed : EqualBitSeed) :
    countErrorEnergy
        (bucketCount (Finset.univ : Finset Bool)
          (twoBitHash seed.1)) 1 = 2 := by
  rcases seed with ⟨⟨left, right⟩, hEqual⟩
  change left = right at hEqual
  subst right
  cases left <;> norm_num [countErrorEnergy, bucketCount, twoBitHash]

/-- The pairwise-independent two-ball/two-bucket baseline would be one, so
the equality postselection doubles the second moment. -/
theorem twoBall_twoBucket_pairwiseBaseline_eq_one :
    (2 : Real) * (1 - (Fintype.card Bool : Real)⁻¹) = 1 := by
  norm_num

end SimonDCP.Probability.LemmaThreeCountEnergy
