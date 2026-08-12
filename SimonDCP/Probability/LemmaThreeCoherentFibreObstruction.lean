import Mathlib

/-!
# Coherent-fibre collision lower bound for Lemma 3

This module isolates a deterministic factor that remains after the repaired
Born-energy estimates for Lemma 3.  A finite domain partitioned into labelled
fibres necessarily has many collisions: the sum of the squared fibre sizes is
at least the square of the domain size divided by the number of labels.

For equal-magnitude paths that add with the same phase inside each fibre, this
is exactly a lower bound on the coherent fibre energy.  It exposes the
potential coherent contribution of the paper's adaptive `A`-side fibres.

This result is deliberately not presented as a lower bound for the paper's
full quantity `C_n`.  In that quantity, `B`-side signs can cancel, and later
measurement filters can remove or regroup paths.  Those effects require a
separate bridge from the concrete Step 3--7 circuit to the abstract fibres
used here.
-/

namespace SimonDCP.Probability.LemmaThreeCoherentFibreObstruction

open scoped BigOperators

variable {Domain Label : Type*} [Fintype Domain] [Fintype Label]

/-- Number of domain points carrying one label. -/
noncomputable def fibreCard (f : Domain -> Label) (label : Label) : Nat := by
  classical
  exact (Finset.univ.filter fun x => f x = label).card

/-- The labelled fibres partition the whole domain. -/
theorem sum_fibreCard (f : Domain -> Label) :
    (∑ label, fibreCard f label) = Fintype.card Domain := by
  classical
  unfold fibreCard
  simpa using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset Domain))
      (t := (Finset.univ : Finset Label)) f)

/--
Cleared-denominator Cauchy collision bound.  This formulation remains valid
when `Label` is empty (in which case `Domain` is necessarily empty).
-/
theorem card_mul_sum_sq_fibreCard_ge (f : Domain -> Label) :
    (Fintype.card Domain) ^ 2 <=
      Fintype.card Label * ∑ label, (fibreCard f label) ^ 2 := by
  classical
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Label))
    (f := fun label => fibreCard f label)
  simpa [sum_fibreCard f] using h

/-- Real-valued form of the exact partition identity. -/
theorem sum_fibreCard_real (f : Domain -> Label) :
    (∑ label, (fibreCard f label : Real)) = Fintype.card Domain := by
  exact_mod_cast sum_fibreCard f

/--
Normalized real collision bound.  Nonemptiness makes the label-cardinality
denominator strictly positive.
-/
theorem card_sq_div_le_sum_sq_fibreCard [Nonempty Label]
    (f : Domain -> Label) :
    (Fintype.card Domain : Real) ^ 2 / Fintype.card Label <=
      ∑ label, (fibreCard f label : Real) ^ 2 := by
  classical
  have hCauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Label))
    (f := fun label => (fibreCard f label : Real))
  rw [sum_fibreCard_real f] at hCauchy
  apply (div_le_iff₀ (by positivity : (0 : Real) < Fintype.card Label)).2
  simpa [mul_comm] using hCauchy

/--
Coherent energy of equal-magnitude, equal-phase paths grouped by `f`.
`scale` is the common squared magnitude of one fine path.
-/
noncomputable def equalAmplitudeFibreEnergy
    (scale : Real) (f : Domain -> Label) : Real :=
  scale * ∑ label, (fibreCard f label : Real) ^ 2

/-- Equal-amplitude coherent fibre energy inherits the collision lower bound. -/
theorem equalAmplitudeFibreEnergy_lower_bound [Nonempty Label]
    (scale : Real) (f : Domain -> Label) (hScale : 0 <= scale) :
    scale * ((Fintype.card Domain : Real) ^ 2 / Fintype.card Label) <=
      equalAmplitudeFibreEnergy scale f := by
  unfold equalAmplitudeFibreEnergy
  exact mul_le_mul_of_nonneg_left (card_sq_div_le_sum_sq_fibreCard f) hScale

/--
Power-of-two specialization in a subtraction-free natural-number form.  If
the domain has `2^(c*n)` points and at most `2^(2*n)` labels, then multiplying
the collision sum by `2^(2*n)` still leaves at least the square of the domain
cardinality.  Equivalently over a field, the average collision size is at
least `2^(2*c*n) / 2^(2*n)`.
-/
theorem powTwo_cleared_collision_lower_bound
    (f : Domain -> Label) (c n : Nat)
    (hDomain : Fintype.card Domain = 2 ^ (c * n))
    (hLabel : Fintype.card Label <= 2 ^ (2 * n)) :
    (2 ^ (c * n)) ^ 2 <=
      2 ^ (2 * n) * ∑ label, (fibreCard f label) ^ 2 := by
  calc
    (2 ^ (c * n)) ^ 2 = (Fintype.card Domain) ^ 2 := by rw [hDomain]
    _ <= Fintype.card Label * ∑ label, (fibreCard f label) ^ 2 :=
      card_mul_sum_sq_fibreCard_ge f
    _ <= 2 ^ (2 * n) * ∑ label, (fibreCard f label) ^ 2 := by
      exact Nat.mul_le_mul_right _ hLabel

end SimonDCP.Probability.LemmaThreeCoherentFibreObstruction
