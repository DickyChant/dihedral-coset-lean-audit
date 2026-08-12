import SimonDCP.Probability.LemmaThreeAdaptiveFibreUpperBound

/-!
# Boolean fine-path specialization of the adaptive-fibre bound

This module specializes the conservative adaptive-fibre estimate to a fine
path consisting of `c * n` Boolean coordinates.  The fine-path space has
exactly `2 ^ (c * n)` elements, so an arbitrary outcome-dependent coarsening
has joint large-sector mass at most `2 ^ (-n)` when the squared threshold is
`2 ^ ((c + 1) * n)`.

For the paper-scale choice `c = 12`, the conservative squared threshold is
therefore `2 ^ (13 * n)`.  No property of the adaptive bucket map is used.
-/

namespace SimonDCP.Probability.LemmaThreeBooleanFinePathUpperBound

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreeSectorRefinement
open SimonDCP.Probability.LemmaThreeAdaptiveFibreUpperBound

/-- A fine path with `c * n` Boolean coordinates. -/
abbrev BooleanFinePath (c n : Nat) := Fin (c * n) -> Bool

/-- The Boolean fine-path space has exactly `2 ^ (c * n)` elements. -/
theorem card_booleanFinePath (c n : Nat) :
    Fintype.card (BooleanFinePath c n) = 2 ^ (c * n) := by
  simp [BooleanFinePath]

/--
An arbitrary outcome-dependent bucket map on `c * n` Boolean fine-path bits
has joint bad mass at most `2 ^ (-n)` at squared threshold
`2 ^ ((c + 1) * n)`, provided the fine-path energy is normalized.
-/
theorem booleanFinePath_adaptiveBucketTail_le
    {Outcome Bucket : Type*}
    {c n : Nat}
    [Fintype Outcome] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Outcome -> BooleanFinePath c n -> Bucket)
    (amplitude : SectorAmplitude Outcome (BooleanFinePath c n))
    (hFineEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude)
          ((2 : Real) ^ ((c + 1) * n))) <=
      1 / ((2 : Real) ^ n) := by
  apply adaptiveBucketTail_le_of_fineCard
      outcomeMass bucketOf amplitude c n
  · exact (card_booleanFinePath c n).le
  · exact hFineEnergy

/--
For `12 * n` Boolean fine-path bits, the conservative squared threshold is
explicitly `2 ^ (13 * n)`.
-/
theorem twelveBooleanBlocks_adaptiveBucketTail_le
    {Outcome Bucket : Type*}
    {n : Nat}
    [Fintype Outcome] [Fintype Bucket] [DecidableEq Bucket]
    (outcomeMass : Outcome -> Real)
    (bucketOf : Outcome -> BooleanFinePath 12 n -> Bucket)
    (amplitude : SectorAmplitude Outcome (BooleanFinePath 12 n))
    (hFineEnergy : totalSectorEnergy amplitude <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedSectorEvent outcomeMass
          (adaptiveBucketAmplitude bucketOf amplitude)
          ((2 : Real) ^ (13 * n))) <=
      1 / ((2 : Real) ^ n) := by
  simpa using
    (booleanFinePath_adaptiveBucketTail_le
      outcomeMass bucketOf amplitude hFineEnergy)

end SimonDCP.Probability.LemmaThreeBooleanFinePathUpperBound
