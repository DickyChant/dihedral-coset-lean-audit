import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalizing finite conditioning counts

This file bridges the natural-number counting statements used by the finite
one-time-pad argument to the rational masses expected by
`ResidueConditioningBound`.

The auxiliary count `R` avoids subtraction in `Nat`: the hypotheses
`R + D = S` and `R + E = S` say that `R` is respectively the regular or the
nonzero part of a selection support of size `S`.
-/

namespace SimonDCP.Probability.FiniteConditioningMass

/--
Normalize a joint-event count bound.

There are `S` selections, `I` inside samples, and `O` outside samples.  Of the
inside samples, `B` satisfy the local event.  The `D` exceptional selections
may contribute all outside samples to one residue, whereas each of the `R`
regular selections contributes a `1 / M` share after multiplying counts by
the residue-space size `M`.
-/
theorem joint_mass_le_of_count_bound
    (M S I O B D R J : ℕ)
    (hM : 0 < M) (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hpartition : R + D = S)
    (hcount : M * J ≤ B * O * (R + M * D)) :
    (J : ℚ) / ((S : ℚ) * (I : ℚ) * (O : ℚ)) ≤
      ((B : ℚ) / (I : ℚ)) *
        (((1 : ℚ) - (D : ℚ) / (S : ℚ)) / (M : ℚ) +
          (D : ℚ) / (S : ℚ)) := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hSq : (0 : ℚ) < S := by exact_mod_cast hS
  have hIq : (0 : ℚ) < I := by exact_mod_cast hI
  have hOq : (0 : ℚ) < O := by exact_mod_cast hO
  have hpartitionq : (R : ℚ) + (D : ℚ) = (S : ℚ) := by
    exact_mod_cast hpartition
  have hregularExceptional : (0 : ℚ) < (R : ℚ) + (D : ℚ) := by
    rw [hpartitionq]
    exact hSq
  have hcountq :
      (M : ℚ) * (J : ℚ) ≤
        (B : ℚ) * (O : ℚ) * ((R : ℚ) + (M : ℚ) * (D : ℚ)) := by
    exact_mod_cast hcount
  have hjoint :
      (J : ℚ) ≤
        ((B : ℚ) * (O : ℚ) * ((R : ℚ) + (M : ℚ) * (D : ℚ))) /
          (M : ℚ) := by
    apply (le_div_iff₀ hMq).2
    simpa [mul_comm] using hcountq
  have htotal :
      (0 : ℚ) < (S : ℚ) * (I : ℚ) * (O : ℚ) := by
    positivity
  calc
    (J : ℚ) / ((S : ℚ) * (I : ℚ) * (O : ℚ)) ≤
        (((B : ℚ) * (O : ℚ) * ((R : ℚ) + (M : ℚ) * (D : ℚ))) /
            (M : ℚ)) /
          ((S : ℚ) * (I : ℚ) * (O : ℚ)) :=
      (div_le_div_iff_of_pos_right htotal).2 hjoint
    _ = ((B : ℚ) / (I : ℚ)) *
        (((1 : ℚ) - (D : ℚ) / (S : ℚ)) / (M : ℚ) +
          (D : ℚ) / (S : ℚ)) := by
      rw [← hpartitionq]
      field_simp [ne_of_gt hMq, ne_of_gt hIq, ne_of_gt hOq,
        ne_of_gt hregularExceptional]
      ring

/--
Normalize an exact marginal count.

Among `S` selections, `E` are the zero selection.  Every nonzero selection
has a uniform residue, while a zero selection contributes only when
`indicator` is one.  The theorem is algebraic and therefore does not need to
assume that `indicator` is Boolean.
-/
theorem marginal_mass_eq_of_count_identity
    (M S I O E R K indicator : ℕ)
    (hM : 0 < M) (hS : 0 < S) (hI : 0 < I) (hO : 0 < O)
    (hpartition : R + E = S)
    (hcount : M * K = I * O * (R + M * E * indicator)) :
    (K : ℚ) / ((S : ℚ) * (I : ℚ) * (O : ℚ)) =
      ((1 : ℚ) - (E : ℚ) / (S : ℚ)) / (M : ℚ) +
        ((E : ℚ) / (S : ℚ)) * (indicator : ℚ) := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hSq : (0 : ℚ) < S := by exact_mod_cast hS
  have hIq : (0 : ℚ) < I := by exact_mod_cast hI
  have hOq : (0 : ℚ) < O := by exact_mod_cast hO
  have hpartitionq : (R : ℚ) + (E : ℚ) = (S : ℚ) := by
    exact_mod_cast hpartition
  have hnonzeroZero : (0 : ℚ) < (R : ℚ) + (E : ℚ) := by
    rw [hpartitionq]
    exact hSq
  have hcountq :
      (M : ℚ) * (K : ℚ) =
        (I : ℚ) * (O : ℚ) *
          ((R : ℚ) + (M : ℚ) * (E : ℚ) * (indicator : ℚ)) := by
    exact_mod_cast hcount
  have hmarginal :
      (K : ℚ) =
        ((I : ℚ) * (O : ℚ) *
          ((R : ℚ) + (M : ℚ) * (E : ℚ) * (indicator : ℚ))) /
            (M : ℚ) := by
    apply (eq_div_iff (ne_of_gt hMq)).2
    simpa [mul_comm] using hcountq
  rw [hmarginal, ← hpartitionq]
  field_simp [ne_of_gt hMq, ne_of_gt hIq, ne_of_gt hOq,
    ne_of_gt hnonzeroZero]
  ring

end SimonDCP.Probability.FiniteConditioningMass
