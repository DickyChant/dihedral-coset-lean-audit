import SimonDCP.Probability.TernaryProjectionBridge
import SimonDCP.Probability.CoordinateSubcubeParameters

/-!
# Conditional local injectivity on a coordinate subcube

The ternary collision estimate controls a uniformly random sample on the
coordinates in `free ∩ A`.  The residue-conditioning argument, however,
uses an inside sample on all of `A`.  This file integrates out the remaining
coordinates exactly: splitting an inside sample into its `free ∩ A` and
`A \ free` restrictions shows that the latter coordinates contribute the
same cardinality factor to both numerator and denominator.

The final theorem inserts the resulting explicit local ternary bound into
the coordinate-subcube Bayes estimate.
-/

namespace SimonDCP.Probability.CoordinateSubcubeConditionalInjectivity

open SimonDCP.Probability.OneTimePadCounting
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.TernaryProjectionBridge
open SimonDCP.Probability.ResidueConditioningAssembly
open SimonDCP.Probability.ResidueConditioningBound
open SimonDCP.Probability.CoordinateSubcubeParameters
open SimonDCP.Probability.CoordinateSubcubeSupport

variable {I G : Type*}

section SampleSplit

variable [DecidableEq I]

/-- Restrict an inside sample on `A` to the free coordinates in `A`. -/
def restrictInsideSample
    (free A : Finset I) (inside : InsideSample A G) :
    ↑(free ∩ A) → G :=
  fun i => inside ⟨i.1, (Finset.mem_inter.mp i.2).2⟩

/-- Restrict an inside sample on `A` to the coordinates that are not free. -/
def restrictInsideSampleOutsideFree
    (free A : Finset I) (inside : InsideSample A G) :
    ↑(A \ free) → G :=
  fun i => inside ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩

/-- An inside sample splits into independent assignments on `free ∩ A` and
`A \ free`. -/
def insideSampleSplitEquiv (free A : Finset I) :
    InsideSample A G ≃ ((↑(free ∩ A) → G) × (↑(A \ free) → G)) where
  toFun inside :=
    (restrictInsideSample free A inside,
      restrictInsideSampleOutsideFree free A inside)
  invFun split i :=
    if hi : i.1 ∈ free then
      split.1 ⟨i.1, Finset.mem_inter.mpr ⟨hi, i.2⟩⟩
    else
      split.2 ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩
  left_inv inside := by
    funext i
    by_cases hi : i.1 ∈ free
    · simp [restrictInsideSample, hi]
    · simp [restrictInsideSampleOutsideFree, hi]
  right_inv split := by
    rcases split with ⟨insideFree, insideFixed⟩
    apply Prod.ext
    · funext i
      have hi : i.1 ∈ free := (Finset.mem_inter.mp i.2).1
      simp [restrictInsideSample, hi]
    · funext i
      have hi : i.1 ∉ free := (Finset.mem_sdiff.mp i.2).2
      simp [restrictInsideSampleOutsideFree, hi]

end SampleSplit

section FiniteSamples

variable [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Inside assignments whose free restriction has a noninjective Boolean
subset-sum map.  The product presentation makes the exact integration over
`A \ free` explicit. -/
noncomputable def badInsideSamples (free A : Finset I) :
    Finset (InsideSample A G) := by
  classical
  exact
    ((localNonInjectiveSamples (G := G) (free ∩ A)).product Finset.univ).map
      (insideSampleSplitEquiv (G := G) free A).symm.toEmbedding

omit [Fintype I] in
/-- Membership in `badInsideSamples` has the intended semantic meaning. -/
@[simp]
theorem mem_badInsideSamples (free A : Finset I)
    (inside : InsideSample A G) :
    inside ∈ badInsideSamples (G := G) free A ↔
      ¬ Function.Injective
        (booleanSubsetSum (restrictInsideSample free A inside)) := by
  classical
  simp [badInsideSamples, mem_localNonInjectiveSamples,
    insideSampleSplitEquiv]

/-- The unrestricted coordinates in `A \ free` contribute a full function
space factor to the bad-inside count. -/
theorem card_badInsideSamples (free A : Finset I) :
    (badInsideSamples (G := G) free A).card =
      (localNonInjectiveSamples (G := G) (free ∩ A)).card *
        Fintype.card (↑(A \ free) → G) := by
  classical
  simp [badInsideSamples]

omit [DecidableEq G] [AddCommGroup G] in
/-- The same split factors the full inside-sample space. -/
theorem card_insideSample_eq_mul (free A : Finset I) :
    Fintype.card (InsideSample A G) =
      Fintype.card (↑(free ∩ A) → G) *
        Fintype.card (↑(A \ free) → G) := by
  simpa using Fintype.card_congr (insideSampleSplitEquiv (G := G) free A)

/-- After normalization, all coordinates of `A` outside `free` cancel
exactly. -/
theorem priorBadMass_badInsideSamples_eq (free A : Finset I) :
    priorBadMass A (badInsideSamples (G := G) free A) =
      ((localNonInjectiveSamples (G := G) (free ∩ A)).card : Rat) /
        (Fintype.card (↑(free ∩ A) → G) : Rat) := by
  rw [priorBadMass, card_badInsideSamples,
    card_insideSample_eq_mul (G := G) free A]
  have hfreeCard :
      (0 : Rat) < Fintype.card (↑(free ∩ A) → G) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩ :
      0 < Fintype.card (↑(free ∩ A) → G))
  have hfixedCard :
      (0 : Rat) < Fintype.card (↑(A \ free) → G) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩ :
      0 < Fintype.card (↑(A \ free) → G))
  simp only [Nat.cast_mul]
  field_simp [ne_of_gt hfreeCard, ne_of_gt hfixedCard]

/-- The prior bad-inside mass pays only for ternary relations on
`free ∩ A`; all other inside coordinates have been integrated out. -/
theorem priorBadMass_badInsideSamples_le (free A : Finset I) :
    priorBadMass A (badInsideSamples (G := G) free A) ≤
      ((3 ^ (free ∩ A).card - 1 : Nat) : Rat) /
        (Fintype.card G : Rat) := by
  rw [priorBadMass_badInsideSamples_eq]
  by_cases hlocal : (free ∩ A).Nonempty
  · exact uniform_localNonInjectiveSamples_le (G := G) (free ∩ A) hlocal
  · have hempty : free ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hlocal
    have hinjective (sample : ↑(free ∩ A) → G) :
        Function.Injective (booleanSubsetSum sample) := by
      intro left right _
      funext i
      have : False := by simpa [hempty] using i.2
      exact this.elim
    have hbadEmpty :
        localNonInjectiveSamples (G := G) (free ∩ A) = ∅ := by
      ext sample
      constructor
      · intro hsample
        exact ((mem_localNonInjectiveSamples (G := G) (free ∩ A) sample).mp
          hsample (hinjective sample)).elim
      · simp
    rw [hbadEmpty]
    simp [hempty]

end FiniteSamples

section ConditionalBound

variable [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- A one-set conditional failure bound with an explicit ternary prior.
The coordinate-subcube factor records the exact conditioning loss, while
the first factor counts only relations on `free ∩ A`. -/
theorem normalizedConditionalBadResidueMass_badInsideSamples_le_dyadic
    (free : Finset I) (fixed : I → Bool) (A : Finset I)
    (residue : G) (R r : Nat)
    (hR_pos : 0 < R) (hrR : r ≤ R)
    (hRfree : R ≤ free.card) (hAr : A.card ≤ r) :
    normalizedBadResidueMass (coordinateSubcube free fixed) A
          (badInsideSamples (G := G) free A) residue /
        normalizedFullSampleResidueMass (coordinateSubcube free fixed)
          residue ≤
      (((3 ^ (free ∩ A).card - 1 : Nat) : Rat) /
          (Fintype.card G : Rat)) *
        (1 + ((Fintype.card G : Rat) - 1) * dyadicDecay (R - r)) /
        (1 - dyadicDecay R) := by
  have hbase :=
    normalizedConditionalBadResidueMass_coordinateSubcube_le_dyadic
      free fixed A (badInsideSamples (G := G) free A) residue R r
      hR_pos hrR hRfree hAr
  have hprior := priorBadMass_badInsideSamples_le (G := G) free A
  have hMnat : 0 < Fintype.card G :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hM : (1 : Rat) ≤ Fintype.card G := by
    exact_mod_cast hMnat
  have hnumerator :
      0 ≤ 1 + ((Fintype.card G : Rat) - 1) * dyadicDecay (R - r) := by
    exact add_nonneg (by norm_num)
      (mul_nonneg (sub_nonneg.mpr hM) (dyadicDecay_pos (R - r)).le)
  have hdenominator : 0 < 1 - dyadicDecay R :=
    sub_pos.mpr (dyadicDecay_lt_one hR_pos)
  calc
    normalizedBadResidueMass (coordinateSubcube free fixed) A
          (badInsideSamples (G := G) free A) residue /
        normalizedFullSampleResidueMass (coordinateSubcube free fixed)
          residue ≤
      priorBadMass A (badInsideSamples (G := G) free A) *
          (1 + ((Fintype.card G : Rat) - 1) * dyadicDecay (R - r)) /
        (1 - dyadicDecay R) := hbase
    _ ≤
      (((3 ^ (free ∩ A).card - 1 : Nat) : Rat) /
          (Fintype.card G : Rat)) *
        (1 + ((Fintype.card G : Rat) - 1) * dyadicDecay (R - r)) /
        (1 - dyadicDecay R) := by
      apply div_le_div_of_nonneg_right _ hdenominator.le
      exact mul_le_mul_of_nonneg_right hprior hnumerator

end ConditionalBound

end SimonDCP.Probability.CoordinateSubcubeConditionalInjectivity
