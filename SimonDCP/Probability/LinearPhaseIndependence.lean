import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Uniform binary linear phases

This file isolates the unconditional finite-field counting statement that is
available to a phase-randomness argument.  A mask is sampled from the complete
space `ι → ZMod 2`; no set of coordinates is selected as a function of that
same mask.

For a nonzero coefficient vector, every fiber of the associated binary linear
form has the same cardinality.  For two distinct nonzero coefficient vectors,
every joint fiber of the two forms has the same cardinality.  The latter is the
exact counting formulation of joint uniformity (and therefore of pairwise
independence under the uniform distribution on masks).

These theorems do not survive arbitrary conditioning.  In particular, they do
not apply when an adaptive set `A` is defined from the sampled mask and the
proof then conditions on `A`: such conditioning may reveal some or all of a
linear form.
-/

namespace SimonDCP.Probability.LinearPhaseIndependence

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Binary masks indexed by a finite type. -/
abbrev Mask (ι : Type*) := ι → ZMod 2

/-- The binary dot product used in a Walsh phase. -/
def dot (phi mask : Mask ι) : ZMod 2 :=
  ∑ i, phi i * mask i

/-- A mask supported at one coordinate. -/
def singleMask [DecidableEq ι] (i : ι) (value : ZMod 2) : Mask ι :=
  Pi.single i value

@[simp]
theorem dot_zero (phi : Mask ι) : dot phi 0 = 0 := by
  simp [dot]

theorem dot_add (phi left right : Mask ι) :
    dot phi (left + right) = dot phi left + dot phi right := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul (scalar : ZMod 2) (phi mask : Mask ι) :
    dot phi (scalar • mask) = scalar * dot phi mask := by
  simp [dot, Finset.mul_sum, mul_left_comm]

@[simp]
theorem dot_singleMask [DecidableEq ι]
    (phi : Mask ι) (i : ι) (value : ZMod 2) :
    dot phi (singleMask i value) = phi i * value := by
  classical
  unfold dot singleMask
  rw [Fintype.sum_eq_single i, Pi.single_eq_same]
  intro j hji
  rw [Pi.single_eq_of_ne hji, mul_zero]

/-- A binary dot product as an additive homomorphism. -/
def dotHom (phi : Mask ι) : Mask ι →+ ZMod 2 where
  toFun := dot phi
  map_zero' := dot_zero phi
  map_add' := dot_add phi

@[simp]
theorem dotHom_apply (phi mask : Mask ι) : dotHom phi mask = dot phi mask :=
  rfl

/-- The two-output homomorphism associated with a pair of linear forms. -/
def pairDotHom (phi psi : Mask ι) : Mask ι →+ ZMod 2 × ZMod 2 :=
  (dotHom phi).prod (dotHom psi)

@[simp]
theorem pairDotHom_apply (phi psi mask : Mask ι) :
    pairDotHom phi psi mask = (dot phi mask, dot psi mask) :=
  rfl

/-- The exact finite fiber of a binary linear form. -/
def fiber [DecidableEq ι] (phi : Mask ι) (value : ZMod 2) : Finset (Mask ι) :=
  Finset.univ.filter fun mask => dot phi mask = value

/-- The exact finite joint fiber of two binary linear forms. -/
def jointFiber [DecidableEq ι]
    (phi psi : Mask ι) (left right : ZMod 2) : Finset (Mask ι) :=
  Finset.univ.filter fun mask => dot phi mask = left ∧ dot psi mask = right

/-- Surjectivity of a finite additive homomorphism makes all of its fibers
equinumerous.  This is a counting theorem, with no probability-space layer. -/
theorem hom_fiber_card_eq_of_surjective
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (a b : H) :
    (Finset.univ.filter fun x => f x = a).card =
      (Finset.univ.filter fun x => f x = b).card := by
  obtain ⟨shift, hshift⟩ := hf (b - a)
  let e : {x : G // f x = a} ≃ {x : G // f x = b} :=
    { toFun := fun x => ⟨x.1 + shift, by simp [x.2, hshift]⟩
      invFun := fun y => ⟨y.1 - shift, by simp [y.2, hshift]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        simp }
  calc
    (Finset.univ.filter fun x => f x = a).card =
        Fintype.card {x : G // f x = a} :=
      (Fintype.card_subtype fun x : G => f x = a).symm
    _ = Fintype.card {x : G // f x = b} := Fintype.card_congr e
    _ = (Finset.univ.filter fun x => f x = b).card :=
      Fintype.card_subtype fun x : G => f x = b

theorem exists_coordinate_ne_zero (phi : Mask ι) (hphi : phi ≠ 0) :
    ∃ i, phi i ≠ 0 := by
  by_contra h
  apply hphi
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmodTwo_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 :=
  (zmodTwo_eq_zero_or_one x).resolve_left hx

@[simp]
theorem zmodTwo_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  change (2 : ZMod 2) = 0
  exact ZMod.natCast_self 2

theorem zmodTwo_distinct_orientation {x y : ZMod 2} (hxy : x ≠ y) :
    (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by
  rcases zmodTwo_eq_zero_or_one x with hx | hx
  · rcases zmodTwo_eq_zero_or_one y with hy | hy
    · exact (hxy (hx.trans hy.symm)).elim
    · exact Or.inr ⟨hx, hy⟩
  · rcases zmodTwo_eq_zero_or_one y with hy | hy
    · exact Or.inl ⟨hx, hy⟩
    · exact (hxy (hx.trans hy.symm)).elim

theorem exists_coordinate_eq_one (phi : Mask ι) (hphi : phi ≠ 0) :
    ∃ i, phi i = 1 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero phi hphi
  exact ⟨i, zmodTwo_eq_one_of_ne_zero hi⟩

theorem exists_coordinate_distinguishing
    (phi psi : Mask ι) (hne : phi ≠ psi) :
    ∃ i, phi i ≠ psi i := by
  by_contra h
  apply hne
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

/-- Every nonzero binary linear form reaches both output values. -/
theorem dotHom_surjective_of_ne_zero (phi : Mask ι) (hphi : phi ≠ 0) :
    Function.Surjective (dotHom phi) := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero phi hphi
  have hiOne : phi i = 1 := zmodTwo_eq_one_of_ne_zero hi
  intro value
  refine ⟨singleMask i value, ?_⟩
  rw [dotHom_apply, dot_singleMask, hiOne, one_mul]

/-- A nonzero binary linear form is balanced: every requested output has the
same number of masks.  Taking `left = 0` and `right = 1` gives the usual
balanced-bit statement. -/
theorem nonzero_dot_fiber_card_eq
    [DecidableEq ι] (phi : Mask ι) (hphi : phi ≠ 0) (left right : ZMod 2) :
    (fiber phi left).card = (fiber phi right).card := by
  simpa [fiber] using
    hom_fiber_card_eq_of_surjective
      (dotHom phi) (dotHom_surjective_of_ne_zero phi hphi) left right

theorem nonzero_dot_balanced
    [DecidableEq ι] (phi : Mask ι) (hphi : phi ≠ 0) :
    (fiber phi 0).card = (fiber phi 1).card :=
  nonzero_dot_fiber_card_eq phi hphi 0 1

/-- Two masks whose evaluations are `(1, 0)` and `(0, 1)` make the pair of
linear forms surjective.  This lemma exposes the precise algebraic obligation
behind joint uniformity. -/
theorem pairDotHom_surjective_of_dual_masks
    (phi psi u v : Mask ι)
    (huPhi : dot phi u = 1) (huPsi : dot psi u = 0)
    (hvPhi : dot phi v = 0) (hvPsi : dot psi v = 1) :
    Function.Surjective (pairDotHom phi psi) := by
  rintro ⟨left, right⟩
  refine ⟨left • u + right • v, ?_⟩
  apply Prod.ext
  · simp [dot_add, dot_smul, huPhi, hvPhi]
  · simp [dot_add, dot_smul, huPsi, hvPsi]

/-- Distinct nonzero coefficient vectors over `ZMod 2` have dual masks. -/
theorem exists_dual_masks_of_distinct_nonzero
    (phi psi : Mask ι) (hphi : phi ≠ 0) (hpsi : psi ≠ 0) (hne : phi ≠ psi) :
    ∃ u v : Mask ι,
      dot phi u = 1 ∧ dot psi u = 0 ∧ dot phi v = 0 ∧ dot psi v = 1 := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_distinguishing phi psi hne
  rcases zmodTwo_distinct_orientation hj with hj | hj
  · obtain ⟨k, hpsiK⟩ := exists_coordinate_eq_one psi hpsi
    by_cases hphiK : phi k = 0
    · refine ⟨singleMask j 1, singleMask k 1, ?_⟩
      simp [hj.1, hj.2, hphiK, hpsiK]
    · have hphiK' : phi k = 1 := zmodTwo_eq_one_of_ne_zero hphiK
      refine ⟨singleMask j 1, singleMask k 1 + singleMask j 1, ?_⟩
      simp [dot_add, hj.1, hj.2, hphiK', hpsiK]
  · obtain ⟨k, hphiK⟩ := exists_coordinate_eq_one phi hphi
    by_cases hpsiK : psi k = 0
    · refine ⟨singleMask k 1, singleMask j 1, ?_⟩
      simp [hj.1, hj.2, hphiK, hpsiK]
    · have hpsiK' : psi k = 1 := zmodTwo_eq_one_of_ne_zero hpsiK
      refine ⟨singleMask k 1 + singleMask j 1, singleMask j 1, ?_⟩
      simp [dot_add, hj.1, hj.2, hphiK, hpsiK']

/-- Distinct nonzero binary linear forms give a surjective pair of outputs. -/
theorem pairDotHom_surjective_of_distinct_nonzero
    (phi psi : Mask ι) (hphi : phi ≠ 0) (hpsi : psi ≠ 0) (hne : phi ≠ psi) :
    Function.Surjective (pairDotHom phi psi) := by
  obtain ⟨u, v, huPhi, huPsi, hvPhi, hvPsi⟩ :=
    exists_dual_masks_of_distinct_nonzero phi psi hphi hpsi hne
  exact pairDotHom_surjective_of_dual_masks
    phi psi u v huPhi huPsi hvPhi hvPsi

/-- Exact joint uniformity: every output pair has the same number of preimages.
For a uniform mask this is stronger than, and implies, pairwise independence of
the two output bits. -/
theorem distinct_nonzero_joint_fiber_card_eq
    [DecidableEq ι]
    (phi psi : Mask ι) (hphi : phi ≠ 0) (hpsi : psi ≠ 0) (hne : phi ≠ psi)
    (left right left' right' : ZMod 2) :
    (jointFiber phi psi left right).card =
      (jointFiber phi psi left' right').card := by
  have hsurj := pairDotHom_surjective_of_distinct_nonzero phi psi hphi hpsi hne
  simpa only [jointFiber, pairDotHom_apply, Prod.mk.injEq] using
    hom_fiber_card_eq_of_surjective
      (pairDotHom phi psi) hsurj (left, right) (left', right')

end SimonDCP.Probability.LinearPhaseIndependence
