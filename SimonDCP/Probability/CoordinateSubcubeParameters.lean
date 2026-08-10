import SimonDCP.Probability.CoordinateSubcubeSupport
import SimonDCP.Probability.ResidueConditioningBound

/-!
# Dyadic parameters of a coordinate-subcube support

This file connects the exact coordinate-subcube counts to the abstract
parameters in the residue-conditioning bound.  If a coordinate subcube has
at least `R` free coordinates and a local set `A` has at most `r`
coordinates, then at least `R - r` free coordinates remain outside `A`.
Consequently, its globally-zero and `A`-exceptional selection masses are at
most `2 ^ (-R)` and `2 ^ (-(R-r))`, respectively.
-/

namespace SimonDCP.Probability.CoordinateSubcubeParameters

open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.OneTimePadCounting
open SimonDCP.Probability.AffineResidueCounting
open SimonDCP.Probability.ResidueConditioningAssembly
open SimonDCP.Probability.ResidueConditioningBound

section Parameters

variable {I : Type*} [DecidableEq I]

/-- Increasing the exponent can only decrease a dyadic decay factor. -/
theorem dyadicDecay_anti {a b : ℕ} (hab : a ≤ b) :
    dyadicDecay b ≤ dyadicDecay a := by
  unfold dyadicDecay
  apply inv_anti₀
  · positivity
  · exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hab

/--
At least `R-r` free coordinates lie outside a set of cardinality at most
`r`, provided that the full free-coordinate set has cardinality at least
`R`.
-/
theorem rank_sub_le_card_sdiff
    (free A : Finset I) (R r : ℕ)
    (hRfree : R ≤ free.card) (hAr : A.card ≤ r) :
    R - r ≤ (free \ A).card := by
  have hinter : (free ∩ A).card ≤ A.card :=
    Finset.card_le_card Finset.inter_subset_right
  apply Nat.sub_le_iff_le_add.mpr
  calc
    R ≤ free.card := hRfree
    _ = (free \ A).card + (free ∩ A).card :=
      (Finset.card_sdiff_add_card_inter free A).symm
    _ ≤ (free \ A).card + A.card := Nat.add_le_add_left hinter _
    _ ≤ (free \ A).card + r := Nat.add_le_add_left hAr _

variable [Fintype I]

/--
The globally-zero selection mass of a coordinate subcube is bounded by the
dyadic decay associated with any lower bound on its number of free
coordinates.
-/
theorem zeroSelectionMass_coordinateSubcube_le_dyadicDecay
    (free : Finset I) (fixed : I → Bool) (R : ℕ)
    (hRfree : R ≤ free.card) :
    zeroSelectionMass (coordinateSubcube free fixed) ≤ dyadicDecay R := by
  rw [zeroSelectionMass_coordinateSubcube]
  split_ifs
  · simpa [dyadicDecay, one_div] using
      (dyadicDecay_anti hRfree)
  · exact (dyadicDecay_pos R).le

/--
The `A`-exceptional selection mass is bounded by `2 ^ (-(R-r))` whenever
`R` lower-bounds the number of free coordinates and `r` upper-bounds
`|A|`.
-/
theorem exceptionalSelectionMass_coordinateSubcube_le_dyadicDecay
    (free : Finset I) (fixed : I → Bool) (A : Finset I) (R r : ℕ)
    (hRfree : R ≤ free.card) (hAr : A.card ≤ r) :
    exceptionalSelectionMass (coordinateSubcube free fixed) A ≤
      dyadicDecay (R - r) := by
  calc
    exceptionalSelectionMass (coordinateSubcube free fixed) A ≤
        1 / (2 ^ (free \ A).card : ℚ) :=
      exceptionalSelectionMass_coordinateSubcube_le free fixed A
    _ = dyadicDecay (free \ A).card := by
      simp [dyadicDecay, one_div]
    _ ≤ dyadicDecay (R - r) :=
      dyadicDecay_anti
        (rank_sub_le_card_sdiff free A R r hRfree hAr)

end Parameters

section Conditioning

variable {I G : Type*}
  [Fintype I] [DecidableEq I]
  [AddCommGroup G] [Fintype G] [DecidableEq G]

/--
The finite conditioning theorem specialized all the way to a coordinate
subcube.  Its only size assumptions are `R ≤ |free|` and `|A| ≤ r`; the
exact counting identities supply every other Bayes premise.
-/
theorem normalizedConditionalBadResidueMass_coordinateSubcube_le_dyadic
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (badInside : Finset (InsideSample A G)) (residue : G) (R r : ℕ)
    (hR_pos : 0 < R) (hrR : r ≤ R)
    (hRfree : R ≤ free.card) (hAr : A.card ≤ r) :
    normalizedBadResidueMass (coordinateSubcube free fixed) A
          badInside residue /
        normalizedFullSampleResidueMass (coordinateSubcube free fixed)
          residue ≤
      priorBadMass A badInside *
          (1 + ((Fintype.card G : ℚ) - 1) * dyadicDecay (R - r)) /
        (1 - dyadicDecay R) := by
  classical
  let support := coordinateSubcube free fixed
  have hsupport : support.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [support]
    rw [card_coordinateSubcube]
    positivity
  have hMnat : 0 < Fintype.card G :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hM : (1 : ℚ) ≤ Fintype.card G := by
    exact_mod_cast hMnat
  have hInat : 0 < Fintype.card (InsideSample A G) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  have hIq : (0 : ℚ) < Fintype.card (InsideSample A G) := by
    exact_mod_cast hInat
  have hSnat : 0 < support.card := Finset.card_pos.mpr hsupport
  have hSq : (0 : ℚ) < support.card := by
    exact_mod_cast hSnat
  have hbad_le : badInside.card ≤ Fintype.card (InsideSample A G) := by
    simpa [← Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ badInside)
  have hexceptional_le :
      (exceptionalSelections support A).card ≤ support.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hzero_le : zeroSelectionCount support ≤ support.card := by
    unfold zeroSelectionCount
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hp_nonneg : 0 ≤ priorBadMass A badInside :=
    div_nonneg (by positivity) hIq.le
  have hp_le_one : priorBadMass A badInside ≤ 1 := by
    apply (div_le_one hIq).2
    exact_mod_cast hbad_le
  have hdelta_nonneg : 0 ≤ exceptionalSelectionMass support A :=
    div_nonneg (by positivity) hSq.le
  have hdelta_le_one : exceptionalSelectionMass support A ≤ 1 := by
    apply (div_le_one hSq).2
    exact_mod_cast hexceptional_le
  have hepsilon_nonneg : 0 ≤ zeroSelectionMass support :=
    div_nonneg (by positivity) hSq.le
  have hepsilon_le_one : zeroSelectionMass support ≤ 1 := by
    apply (div_le_one hSq).2
    exact_mod_cast hzero_le
  have hindicator_nonneg : 0 ≤ residueZeroIndicator residue := by
    by_cases hresidue : residue = 0 <;>
      simp [residueZeroIndicator, hresidue]
  have hdelta :
      exceptionalSelectionMass support A ≤ dyadicDecay (R - r) := by
    dsimp [support]
    exact exceptionalSelectionMass_coordinateSubcube_le_dyadicDecay
      free fixed A R r hRfree hAr
  have hepsilon : zeroSelectionMass support ≤ dyadicDecay R := by
    dsimp [support]
    exact zeroSelectionMass_coordinateSubcube_le_dyadicDecay
      free fixed R hRfree
  exact rational_bayes_residue_bound_of_dyadic
    R r
    (priorBadMass A badInside)
    (exceptionalSelectionMass support A)
    (zeroSelectionMass support)
    (Fintype.card G : ℚ)
    (residueZeroIndicator residue)
    (normalizedBadResidueMass support A badInside residue)
    (normalizedFullSampleResidueMass support residue)
    hR_pos hrR hp_nonneg hp_le_one hdelta_nonneg hdelta_le_one
    hepsilon_nonneg hepsilon_le_one hM hindicator_nonneg hdelta hepsilon
    (normalizedBadResidueMass_le support A badInside residue hsupport)
    (normalizedFullSampleResidueMass_eq support residue hsupport)

end Conditioning

end SimonDCP.Probability.CoordinateSubcubeParameters
