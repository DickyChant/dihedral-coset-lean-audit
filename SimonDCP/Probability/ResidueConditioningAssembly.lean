import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SimonDCP.Probability.AffineResidueCounting
import SimonDCP.Probability.FiniteConditioningMass
import SimonDCP.Probability.ResidueConditioningBound

/-!
# Assembling the finite residue-conditioning bound

This file connects three layers of the repaired Lemma 1 argument:

* `AffineResidueCounting` supplies unnormalized finite counts;
* `FiniteConditioningMass` turns those counts into rational masses;
* `ResidueConditioningBound` applies the Bayes quotient estimate.

The distinction between the two exceptional ratios is explicit.  For a
fixed coordinate set `A`, `exceptionalSelectionMass` is the fraction of
selection masks supported inside `A`.  By contrast, `zeroSelectionMass` is
the fraction of globally zero masks and controls the unconditional residue
marginal.
-/

namespace SimonDCP.Probability.ResidueConditioningAssembly

open SimonDCP.Probability.OneTimePadCounting
open SimonDCP.Probability.AffineResidueCounting
open SimonDCP.Probability.FiniteConditioningMass
open SimonDCP.Probability.ResidueConditioningBound

section FiniteAdditiveGroup

variable {I G : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Splitting a sample into its coordinates inside and outside `A`. -/
def insideOutsideSampleEquiv (A : Finset I) :
    (InsideSample A G × OutsideSample A G) ≃ (I → G) where
  toFun sample i :=
    if hi : i ∈ A then sample.1 ⟨i, hi⟩ else sample.2 ⟨i, hi⟩
  invFun sample :=
    (fun i => sample i.1, fun i => sample i.1)
  left_inv sample := by
    rcases sample with ⟨inside, outside⟩
    apply Prod.ext
    · funext i
      simp [i.property]
    · funext i
      simp [i.property]
  right_inv sample := by
    funext i
    by_cases hi : i ∈ A <;> simp [hi]

omit [DecidableEq G] [AddCommGroup G] in
/-- Inside and outside assignments together have the full sample cardinality. -/
theorem card_inside_mul_card_outside_eq (A : Finset I) :
    Fintype.card (InsideSample A G) * Fintype.card (OutsideSample A G) =
      Fintype.card (I → G) := by
  simpa using Fintype.card_congr (insideOutsideSampleEquiv (G := G) A)

/-- The normalized prior mass of a finite set of inside assignments. -/
noncomputable def priorBadMass
    (A : Finset I) (badInside : Finset (InsideSample A G)) : ℚ :=
  (badInside.card : ℚ) / (Fintype.card (InsideSample A G) : ℚ)

/--
The exceptional-selection ratio after fixing `A`: this is the parameter
`delta`, not the globally-zero ratio `epsilon`.
-/
noncomputable def exceptionalSelectionMass
    (support : Finset (I → Bool)) (A : Finset I) : ℚ :=
  ((exceptionalSelections support A).card : ℚ) / (support.card : ℚ)

/-- The globally-zero selection ratio `epsilon`. -/
noncomputable def zeroSelectionMass
    (support : Finset (I → Bool)) : ℚ :=
  (zeroSelectionCount support : ℚ) / (support.card : ℚ)

/-- The rational indicator of the zero residue. -/
def residueZeroIndicator (residue : G) : ℚ :=
  if residue = 0 then 1 else 0

/--
The joint mass of a bad inside assignment and a prescribed residue, under
uniform choices of a support mask and a full sample.
-/
noncomputable def normalizedBadResidueMass
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) : ℚ :=
  (badResidueCount support A badInside residue : ℚ) /
    ((support.card : ℚ) *
      (Fintype.card (InsideSample A G) : ℚ) *
      (Fintype.card (OutsideSample A G) : ℚ))

/-- The unique assignment on the empty set of inside coordinates. -/
def emptyInsideSample : InsideSample (∅ : Finset I) G :=
  fun _ => 0

/-- The full-sample residue count, expressed by the empty inside split. -/
noncomputable def fullSampleResidueCount
    (support : Finset (I → Bool)) (residue : G) : ℕ :=
  aggregateResidueCount support (∅ : Finset I)
    (emptyInsideSample (I := I) (G := G)) residue

/-- The normalized marginal mass of a prescribed residue. -/
noncomputable def normalizedFullSampleResidueMass
    (support : Finset (I → Bool)) (residue : G) : ℚ :=
  (fullSampleResidueCount support residue : ℚ) /
    ((support.card : ℚ) *
      (Fintype.card (OutsideSample (∅ : Finset I) G) : ℚ))

/--
The affine counting bound normalized as the joint premise of the Bayes
estimate.  Its exceptional parameter is exactly
`|exceptionalSelections support A| / |support|`.
-/
theorem normalizedBadResidueMass_le
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G)
    (hsupport : support.Nonempty) :
    normalizedBadResidueMass support A badInside residue ≤
      priorBadMass A badInside *
        (((1 : ℚ) - exceptionalSelectionMass support A) /
            (Fintype.card G : ℚ) +
          exceptionalSelectionMass support A) := by
  have hM : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hS : 0 < support.card := Finset.card_pos.mpr hsupport
  have hI : 0 < Fintype.card (InsideSample A G) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hO : 0 < Fintype.card (OutsideSample A G) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hpartition := regular_card_add_exceptional_card support A
  have hcount := card_mul_badResidueCount_le_regular_exceptional
    support A badInside residue
  simpa [normalizedBadResidueMass, priorBadMass,
    exceptionalSelectionMass] using
      (joint_mass_le_of_count_bound
        (Fintype.card G) support.card
        (Fintype.card (InsideSample A G))
        (Fintype.card (OutsideSample A G)) badInside.card
        (exceptionalSelections support A).card
        (regularSelections support A).card
        (badResidueCount support A badInside residue)
        hM hS hI hO hpartition hcount)

/--
The exact full-sample marginal.  Here `epsilon` is the globally-zero mask
ratio, and the final factor is `1` exactly when the requested residue is zero.
-/
theorem normalizedFullSampleResidueMass_eq
    (support : Finset (I → Bool)) (residue : G)
    (hsupport : support.Nonempty) :
    normalizedFullSampleResidueMass support residue =
      ((1 : ℚ) - zeroSelectionMass support) /
          (Fintype.card G : ℚ) +
        zeroSelectionMass support * residueZeroIndicator residue := by
  let M := Fintype.card G
  let S := support.card
  let O := Fintype.card (OutsideSample (∅ : Finset I) G)
  let E := zeroSelectionCount support
  let R := support.card - zeroSelectionCount support
  let K := fullSampleResidueCount support residue
  let indicator : ℕ := if residue = 0 then 1 else 0
  have hM : 0 < M := Fintype.card_pos_iff.mpr ⟨0⟩
  have hS : 0 < S := Finset.card_pos.mpr hsupport
  have hO : 0 < O := Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hzero_le : zeroSelectionCount support ≤ support.card := by
    unfold zeroSelectionCount
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hpartition : R + E = S := by
    dsimp [R, E, S]
    exact Nat.sub_add_cancel hzero_le
  have hcount : M * K = 1 * O * (R + M * E * indicator) := by
    dsimp [M, K]
    unfold fullSampleResidueCount
    rw [card_mul_fullSampleResidueCount_eq]
    dsimp [O, R, E, indicator, fullSampleResidueCount]
    by_cases hresidue : residue = 0
    · simp [hresidue]
      ring
    · simp [hresidue]
      ring
  have hnormalized := marginal_mass_eq_of_count_identity
    M S 1 O E R K indicator hM hS (by simp) hO hpartition hcount
  simpa [normalizedFullSampleResidueMass, zeroSelectionMass,
    residueZeroIndicator, M, S, O, E, R, K, indicator] using hnormalized

/--
The complete finite Bayes estimate.  The only extra analytic premise is that
the chosen residue has positive marginal mass; this excludes conditioning on
an impossible residue.
-/
theorem normalizedConditionalBadResidueMass_le
    (support : Finset (I → Bool)) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G)
    (hsupport : support.Nonempty)
    (hmarginal_pos : 0 < normalizedFullSampleResidueMass support residue) :
    normalizedBadResidueMass support A badInside residue /
        normalizedFullSampleResidueMass support residue ≤
      priorBadMass A badInside *
        (1 + ((Fintype.card G : ℚ) - 1) *
          exceptionalSelectionMass support A) /
        (1 - zeroSelectionMass support +
          (Fintype.card G : ℚ) * zeroSelectionMass support *
            residueZeroIndicator residue) := by
  classical
  have hMnat : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hMq : (0 : ℚ) < (Fintype.card G : ℚ) := by exact_mod_cast hMnat
  have hInat : 0 < Fintype.card (InsideSample A G) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hIq : (0 : ℚ) < (Fintype.card (InsideSample A G) : ℚ) := by
    exact_mod_cast hInat
  have hSnat : 0 < support.card := Finset.card_pos.mpr hsupport
  have hSq : (0 : ℚ) < (support.card : ℚ) := by exact_mod_cast hSnat
  have hbad_le : badInside.card ≤ Fintype.card (InsideSample A G) := by
    simpa [← Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ badInside)
  have hexceptional_le :
      (exceptionalSelections support A).card ≤ support.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hzero_le : zeroSelectionCount support ≤ support.card := by
    unfold zeroSelectionCount
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hp_nonneg : 0 ≤ priorBadMass A badInside := by
    exact div_nonneg (by positivity) hIq.le
  have hp_le_one : priorBadMass A badInside ≤ 1 := by
    apply (div_le_one hIq).2
    exact_mod_cast hbad_le
  have hdelta_nonneg : 0 ≤ exceptionalSelectionMass support A := by
    exact div_nonneg (by positivity) hSq.le
  have hdelta_le_one : exceptionalSelectionMass support A ≤ 1 := by
    apply (div_le_one hSq).2
    exact_mod_cast hexceptional_le
  have hepsilon_nonneg : 0 ≤ zeroSelectionMass support := by
    exact div_nonneg (by positivity) hSq.le
  have hepsilon_le_one : zeroSelectionMass support ≤ 1 := by
    apply (div_le_one hSq).2
    exact_mod_cast hzero_le
  exact rational_bayes_residue_bound
    (priorBadMass A badInside)
    (exceptionalSelectionMass support A)
    (zeroSelectionMass support)
    (Fintype.card G : ℚ)
    (residueZeroIndicator residue)
    (normalizedBadResidueMass support A badInside residue)
    (normalizedFullSampleResidueMass support residue)
    hp_nonneg hp_le_one hdelta_nonneg hdelta_le_one
    hepsilon_nonneg hepsilon_le_one hMq
    (normalizedBadResidueMass_le support A badInside residue hsupport)
    (normalizedFullSampleResidueMass_eq support residue hsupport)
    hmarginal_pos

end FiniteAdditiveGroup

end SimonDCP.Probability.ResidueConditioningAssembly
