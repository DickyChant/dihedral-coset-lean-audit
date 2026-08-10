import SimonDCP.Probability.LinearPhaseIndependence

/-!
# Restricted Walsh orthogonality and Parseval

This file proves the finite algebraic identity needed by a direct Fourier
approach to Lemma 1.  Walsh masks are constrained to vanish on a chosen set of
coordinates.  Averaging over the remaining coordinates kills every
off-diagonal pair whose coefficient masks differ there.

The results are purely finite counting identities over `ZMod 2`; they do not
make any independence claim after adaptive conditioning.
-/

namespace SimonDCP.Probability.RestrictedParseval

open scoped BigOperators

open SimonDCP.Probability.LinearPhaseIndependence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer-valued sign character of the additive group `ZMod 2`. -/
def phaseSign (bit : ZMod 2) : ℤ :=
  if bit = 0 then 1 else -1

@[simp]
theorem phaseSign_zero : phaseSign 0 = 1 := by
  simp [phaseSign]

@[simp]
theorem phaseSign_one : phaseSign 1 = -1 := by
  norm_num [phaseSign]

/-- The sign character turns addition in `ZMod 2` into multiplication. -/
theorem phaseSign_add (left right : ZMod 2) :
    phaseSign (left + right) = phaseSign left * phaseSign right := by
  rcases zmodTwo_eq_zero_or_one left with rfl | rfl <;>
    rcases zmodTwo_eq_zero_or_one right with rfl | rfl <;>
      simp [phaseSign, zmodTwo_one_add_one]

/-- The integer-valued Walsh character indexed by `phi`. -/
def walsh (phi mask : Mask ι) : ℤ :=
  phaseSign (dot phi mask)

omit [DecidableEq ι] in
@[simp]
theorem walsh_zero_mask (phi : Mask ι) : walsh phi 0 = 1 := by
  simp [walsh]

omit [DecidableEq ι] in
theorem dot_add_coefficients (phi psi mask : Mask ι) :
    dot (phi + psi) mask = dot phi mask + dot psi mask := by
  simp [dot, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem walsh_add_mask (phi left right : Mask ι) :
    walsh phi (left + right) = walsh phi left * walsh phi right := by
  simp [walsh, dot_add, phaseSign_add]

omit [DecidableEq ι] in
theorem walsh_add_coefficients (phi psi mask : Mask ι) :
    walsh (phi + psi) mask = walsh phi mask * walsh psi mask := by
  simp [walsh, dot_add_coefficients, phaseSign_add]

/-- The additive subgroup of masks forced to be zero on `fixed`. -/
def MasksVanishingOn (fixed : Finset ι) : AddSubgroup (Mask ι) where
  carrier := {mask | ∀ i ∈ fixed, mask i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro left right hleft hright i hi
    simp [hleft i hi, hright i hi]
  neg_mem' := by
    intro mask hmask i hi
    simp [hmask i hi]

noncomputable instance masksVanishingOnFintype (fixed : Finset ι) :
    Fintype (MasksVanishingOn fixed) :=
  Fintype.ofFinite (MasksVanishingOn fixed)

/-- Coordinates on which a mask vanishing on `fixed` remains free. -/
abbrev FreeCoordinate (fixed : Finset ι) :=
  {i : ι // i ∉ fixed}

/-- A mask vanishing on `fixed` is exactly a binary assignment on the
complementary coordinates. -/
def masksVanishingOnEquivFreeCoordinates (fixed : Finset ι) :
    MasksVanishingOn fixed ≃ (FreeCoordinate fixed → ZMod 2) where
  toFun := fun mask i => (mask : Mask ι) i.1
  invFun := fun values =>
    ⟨fun i => if hi : i ∈ fixed then 0 else values ⟨i, hi⟩, by
      intro i hi
      simp [hi]⟩
  left_inv := by
    intro mask
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ fixed
    · simp [hi, mask.property i hi]
    · simp [hi]
  right_inv := by
    intro values
    funext i
    simp [i.property]

/-- There are exactly two choices for every coordinate outside `fixed`. -/
theorem card_masksVanishingOn (fixed : Finset ι) :
    Fintype.card (MasksVanishingOn fixed) =
      2 ^ (Fintype.card ι - fixed.card) := by
  classical
  have hfixed : Fintype.card {i : ι // i ∈ fixed} = fixed.card := by
    rw [Fintype.card_subtype]
    simp
  calc
    Fintype.card (MasksVanishingOn fixed) =
        Fintype.card (FreeCoordinate fixed → ZMod 2) :=
      Fintype.card_congr (masksVanishingOnEquivFreeCoordinates fixed)
    _ = Fintype.card (ZMod 2) ^ Fintype.card (FreeCoordinate fixed) :=
      Fintype.card_fun
    _ = 2 ^ Fintype.card (FreeCoordinate fixed) := by rw [ZMod.card]
    _ = 2 ^ (Fintype.card ι - fixed.card) := by
      congr 1
      unfold FreeCoordinate
      rw [Fintype.card_subtype_compl (fun i : ι => i ∈ fixed), hfixed]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_masksVanishingOn {fixed : Finset ι} {mask : Mask ι} :
    mask ∈ MasksVanishingOn fixed ↔ ∀ i ∈ fixed, mask i = 0 :=
  Iff.rfl

/-- Restriction of a binary dot product to masks vanishing on `fixed`. -/
def restrictedDotHom (fixed : Finset ι) (phi : Mask ι) :
    MasksVanishingOn fixed →+ ZMod 2 :=
  (dotHom phi).comp (MasksVanishingOn fixed).subtype

omit [DecidableEq ι] in
@[simp]
theorem restrictedDotHom_apply
    (fixed : Finset ι) (phi : Mask ι) (mask : MasksVanishingOn fixed) :
    restrictedDotHom fixed phi mask = dot phi mask :=
  rfl

/-- A free nonzero coordinate makes the restricted dot product surjective. -/
theorem restrictedDotHom_surjective_of_exists_free
    (fixed : Finset ι) (phi : Mask ι)
    (hfree : ∃ i, i ∉ fixed ∧ phi i ≠ 0) :
    Function.Surjective (restrictedDotHom fixed phi) := by
  classical
  obtain ⟨i, hiFixed, hiPhi⟩ := hfree
  have hiOne : phi i = 1 := zmodTwo_eq_one_of_ne_zero hiPhi
  intro value
  let witness : Mask ι := singleMask i value
  have hwitness : witness ∈ MasksVanishingOn fixed := by
    intro j hj
    have hji : j ≠ i := by
      intro h
      apply hiFixed
      simpa [h] using hj
    simp [witness, singleMask, hji]
  refine ⟨⟨witness, hwitness⟩, ?_⟩
  change dot phi witness = value
  rw [dot_singleMask, hiOne, one_mul]

/-- A nontrivial Walsh character sums to zero on the restricted mask group. -/
theorem restricted_character_sum_eq_zero
    (fixed : Finset ι) (phi : Mask ι)
    (hfree : ∃ i, i ∉ fixed ∧ phi i ≠ 0) :
    ∑ mask : MasksVanishingOn fixed, walsh phi mask = 0 := by
  classical
  obtain ⟨shift, hshift⟩ :=
    restrictedDotHom_surjective_of_exists_free fixed phi hfree (1 : ZMod 2)
  let translate : MasksVanishingOn fixed ≃ MasksVanishingOn fixed :=
    { toFun := fun mask => mask + shift
      invFun := fun mask => mask - shift
      left_inv := by intro mask; simp
      right_inv := by intro mask; simp }
  have hsum :
      (∑ mask : MasksVanishingOn fixed, walsh phi (mask + shift)) =
        ∑ mask : MasksVanishingOn fixed, walsh phi mask := by
    simpa [translate] using
      translate.sum_comp (fun mask : MasksVanishingOn fixed => walsh phi mask)
  have hterm (mask : MasksVanishingOn fixed) :
      walsh phi (mask + shift) = -walsh phi mask := by
    rw [walsh_add_mask]
    have : walsh phi shift = -1 := by
      have hdot : dot phi shift = 1 := by simpa using hshift
      simp [walsh, hdot]
    simp [this]
  simp_rw [hterm] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  exact CharZero.neg_eq_self_iff.mp hsum

/-- Two coefficient masks agree on every coordinate that remains free. -/
def AgreeOutside (fixed : Finset ι) (phi psi : Mask ι) : Prop :=
  ∀ i, i ∉ fixed → phi i = psi i

local instance agreeOutsideDecidable (fixed : Finset ι) :
    DecidableRel (AgreeOutside fixed) := fun _ _ => by
  unfold AgreeOutside
  infer_instance

theorem sum_eq_zero_of_agreeOutside
    (fixed : Finset ι) (phi psi : Mask ι)
    (hagree : AgreeOutside fixed phi psi)
    (mask : MasksVanishingOn fixed) :
    dot (phi + psi) mask = 0 := by
  classical
  unfold dot
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hifixed : i ∈ fixed
  · have hmask : (mask : Mask ι) i = 0 := mask.property i hifixed
    simp [hmask]
  · have hcoeff : phi i = psi i := hagree i hifixed
    rw [Pi.add_apply, hcoeff]
    rcases zmodTwo_eq_zero_or_one (psi i) with hzero | hone
    · simp [hzero]
    · simp [hone]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_free_sum_ne_zero_of_not_agreeOutside
    (fixed : Finset ι) (phi psi : Mask ι)
    (hagree : ¬ AgreeOutside fixed phi psi) :
    ∃ i, i ∉ fixed ∧ (phi + psi) i ≠ 0 := by
  classical
  simp only [AgreeOutside, not_forall] at hagree
  obtain ⟨i, hi⟩ := hagree
  obtain ⟨hiFree, hiNe⟩ := hi
  refine ⟨i, hiFree, ?_⟩
  rcases zmodTwo_distinct_orientation hiNe with horient | horient
  · simp [horient.1, horient.2]
  · simp [horient.1, horient.2]

/-- Restricted Walsh orthogonality.  Only equality on the free coordinates
survives the sum over masks vanishing on `fixed`. -/
theorem restricted_character_orthogonality
    (fixed : Finset ι) (phi psi : Mask ι) :
    (∑ mask : MasksVanishingOn fixed, walsh phi mask * walsh psi mask) =
      if AgreeOutside fixed phi psi then
        (Fintype.card (MasksVanishingOn fixed) : ℤ)
      else 0 := by
  classical
  by_cases hagree : AgreeOutside fixed phi psi
  · rw [if_pos hagree]
    calc
      (∑ mask : MasksVanishingOn fixed, walsh phi mask * walsh psi mask) =
          ∑ mask : MasksVanishingOn fixed, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro mask hmask
        rw [← walsh_add_coefficients]
        simp [walsh, sum_eq_zero_of_agreeOutside fixed phi psi hagree mask]
      _ = (Fintype.card (MasksVanishingOn fixed) : ℤ) := by simp
  · rw [if_neg hagree]
    rw [← restricted_character_sum_eq_zero fixed (phi + psi)
      (exists_free_sum_ne_zero_of_not_agreeOutside fixed phi psi hagree)]
    apply Finset.sum_congr rfl
    intro mask hmask
    rw [walsh_add_coefficients]

/-- The signed amplitude of a finite family at one Walsh mask. -/
def signedAmplitude
    (support : Finset (Mask ι)) (coefficient : Mask ι → ℤ)
    (mask : Mask ι) : ℤ :=
  ∑ phi ∈ support, coefficient phi * walsh phi mask

/-- Restricted Parseval: squared signed amplitudes equal the weighted collision
sum for restrictions to the complement of `fixed`. -/
theorem restricted_parseval
    (fixed : Finset ι) (support : Finset (Mask ι))
    (coefficient : Mask ι → ℤ) :
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support coefficient mask) ^ 2) =
      (Fintype.card (MasksVanishingOn fixed) : ℤ) *
        ∑ phi ∈ support, ∑ psi ∈ support,
          if AgreeOutside fixed phi psi then coefficient phi * coefficient psi else 0 := by
  classical
  calc
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support coefficient mask) ^ 2) =
        ∑ mask : MasksVanishingOn fixed,
          ∑ phi ∈ support, ∑ psi ∈ support,
            (coefficient phi * coefficient psi) *
              (walsh phi mask * walsh psi mask) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      simp only [signedAmplitude, pow_two]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro phi hphi
      apply Finset.sum_congr rfl
      intro psi hpsi
      ac_rfl
    _ = ∑ phi ∈ support, ∑ psi ∈ support,
          (coefficient phi * coefficient psi) *
            ∑ mask : MasksVanishingOn fixed,
              walsh phi mask * walsh psi mask := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro phi hphi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro psi hpsi
      rw [Finset.mul_sum]
    _ = ∑ phi ∈ support, ∑ psi ∈ support,
          (coefficient phi * coefficient psi) *
            (if AgreeOutside fixed phi psi then
              (Fintype.card (MasksVanishingOn fixed) : ℤ)
            else 0) := by
      apply Finset.sum_congr rfl
      intro phi hphi
      apply Finset.sum_congr rfl
      intro psi hpsi
      rw [restricted_character_orthogonality]
    _ = ∑ phi ∈ support, ∑ psi ∈ support,
          (Fintype.card (MasksVanishingOn fixed) : ℤ) *
            (if AgreeOutside fixed phi psi then
              coefficient phi * coefficient psi
            else 0) := by
      apply Finset.sum_congr rfl
      intro phi hphi
      apply Finset.sum_congr rfl
      intro psi hpsi
      by_cases hagree : AgreeOutside fixed phi psi <;> simp [hagree]
      ac_rfl
    _ = (Fintype.card (MasksVanishingOn fixed) : ℤ) *
          ∑ phi ∈ support, ∑ psi ∈ support,
            if AgreeOutside fixed phi psi then coefficient phi * coefficient psi else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro phi hphi
      rw [Finset.mul_sum]

/-- The number of ordered pairs in `support` with the same restriction to the
coordinates outside `fixed`. -/
def projectionCollisionCount
    (fixed : Finset ι) (support : Finset (Mask ι)) : ℕ :=
  ∑ phi ∈ support, (support.filter fun psi => AgreeOutside fixed phi psi).card

/-- The natural collision count is the integer indicator sum appearing in the
unit-coefficient Parseval identity. -/
theorem projectionCollisionCount_cast
    (fixed : Finset ι) (support : Finset (Mask ι)) :
    (projectionCollisionCount fixed support : ℤ) =
      ∑ phi ∈ support, ∑ psi ∈ support,
        if AgreeOutside fixed phi psi then 1 else 0 := by
  classical
  simp only [projectionCollisionCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro phi hphi
  exact (Finset.sum_boole (AgreeOutside fixed phi) support).symm

/-- Every support point contributes its diagonal pair to the projection
collision count. -/
theorem support_card_le_projectionCollisionCount
    (fixed : Finset ι) (support : Finset (Mask ι)) :
    support.card ≤ projectionCollisionCount fixed support := by
  classical
  calc
    support.card = ∑ phi ∈ support, 1 := by simp
    _ ≤ ∑ phi ∈ support,
        (support.filter fun psi => AgreeOutside fixed phi psi).card := by
      apply Finset.sum_le_sum
      intro phi hphi
      rw [Finset.one_le_card]
      exact ⟨phi, by simp [hphi, AgreeOutside]⟩
    _ = projectionCollisionCount fixed support := rfl

/-- Parseval specialized to unit coefficients: the squared-amplitude mass is
exactly the mask-space cardinality times the projection collision count. -/
theorem restricted_parseval_unit
    (fixed : Finset ι) (support : Finset (Mask ι)) :
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support (fun _ => 1) mask) ^ 2) =
      (Fintype.card (MasksVanishingOn fixed) : ℤ) *
        (projectionCollisionCount fixed support : ℤ) := by
  calc
    (∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support (fun _ => 1) mask) ^ 2) =
      (Fintype.card (MasksVanishingOn fixed) : ℤ) *
        ∑ phi ∈ support, ∑ psi ∈ support,
          if AgreeOutside fixed phi psi then (1 : ℤ) * 1 else 0 :=
      restricted_parseval fixed support (fun _ => 1)
    _ = (Fintype.card (MasksVanishingOn fixed) : ℤ) *
        (projectionCollisionCount fixed support : ℤ) := by
      simp only [one_mul]
      rw [projectionCollisionCount_cast]

/-- The diagonal contribution gives a universal lower bound for unit
coefficients. -/
theorem restricted_squaredAmplitude_sum_ge_diagonal
    (fixed : Finset ι) (support : Finset (Mask ι)) :
    (Fintype.card (MasksVanishingOn fixed) : ℤ) * support.card ≤
      ∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support (fun _ => 1) mask) ^ 2 := by
  rw [restricted_parseval_unit]
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast support_card_le_projectionCollisionCount fixed support
  · exact Int.natCast_nonneg _

/-- The diagonal lower bound with the restricted mask-space cardinality made
explicit. -/
theorem restricted_squaredAmplitude_sum_ge_diagonal_pow
    (fixed : Finset ι) (support : Finset (Mask ι)) :
    (2 : ℤ) ^ (Fintype.card ι - fixed.card) * support.card ≤
      ∑ mask : MasksVanishingOn fixed,
        (signedAmplitude support (fun _ => 1) mask) ^ 2 := by
  have hcard : (Fintype.card (MasksVanishingOn fixed) : ℤ) =
      (2 : ℤ) ^ (Fintype.card ι - fixed.card) := by
    exact_mod_cast card_masksVanishingOn fixed
  rw [← hcard]
  exact restricted_squaredAmplitude_sum_ge_diagonal fixed support

end SimonDCP.Probability.RestrictedParseval
