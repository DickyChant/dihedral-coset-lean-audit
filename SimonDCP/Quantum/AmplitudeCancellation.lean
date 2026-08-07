import Mathlib.Tactic.NormNum

/-!
# Cardinality bounds do not control signed amplitudes

The proof sketch of Lemma 4 passes from estimates on numbers of state portions
to multiplicative estimates on amplitudes.  That inference is unavailable in
the presence of cancellation unless the coefficients satisfy an additional
positivity, phase-alignment, or anti-cancellation hypothesis.

The finite examples below isolate the obstruction over the integers.  This is
already enough because integer amplitudes embed in the complex amplitudes used
by the quantum calculation.
-/

namespace SimonDCP.Quantum.AmplitudeCancellation

/-- A toy signed amplitude: the sum of all contributions. -/
def signedAmplitude (weights : List ℤ) : ℤ := weights.sum

/-- Equal numbers of contributions can have different amplitudes because of cancellation. -/
theorem equal_cardinality_does_not_determine_amplitude :
    ∃ left right : List ℤ,
      left.length = right.length ∧
      signedAmplitude left = 0 ∧
      signedAmplitude right = 2 := by
  refine ⟨[1, -1], [1, 1], ?_⟩
  norm_num [signedAmplitude]

/-- Replacing only one of two unit-magnitude terms can change zero amplitude to two. -/
theorem one_term_change_can_escape_any_multiplicative_zero_bound
    (factor : ℤ) :
    |signedAmplitude [1, 1]| > factor * |signedAmplitude [1, -1]| := by
  norm_num [signedAmplitude]

end SimonDCP.Quantum.AmplitudeCancellation
