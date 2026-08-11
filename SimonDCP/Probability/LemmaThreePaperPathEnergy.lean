import SimonDCP.Probability.LemmaThreePaperPathBridge

/-!
# Common-path energy for the paper-shaped Lemma 3 model

The paper-facing path relation stores a complete measured transcript together
with one compatible hidden Step-2 state.  Although this relation is not a
function from hidden states to transcripts, compatibility makes each path
uniquely determined by its hidden state and its measured Walsh mask `D`: the
records `Y`, `W`, `S`, and `hPrime` are deterministic functions of those two
coordinates.

Consequently the surviving paths inject into `Hidden × D`.  Combining this
injection with the `1 / (card D * card Low)` squared Hadamard factor proves a
slightly stronger normalization statement: if the diagonal Step-2 energy is
at most one, then the total surviving common-path energy is at most
`1 / card Low`, hence at most one.  Within this compatibility-subset model,
acceptance and record filters only remove paths and therefore cannot increase
this diagonal energy.  Identifying the model with the actual circuit remains
a separate premise.
-/

namespace SimonDCP.Probability.LemmaThreePaperPathEnergy

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePaperPathBridge
open SimonDCP.Probability.LemmaThreePathRefinement
open SimonDCP.Probability.LemmaThreeTranscriptModel

variable {Hidden Y D W S Low : Type*}

private theorem stepSevenTranscript_ext
    (left right : StepSevenTranscript Y D W S)
    (hY : left.y = right.y) (hD : left.d = right.d)
    (hW : left.w = right.w) (hS : left.s = right.s)
    (hHPrime : left.hPrime = right.hPrime) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Forget every deterministic record except the hidden state and Walsh mask. -/
def paperHiddenAndD
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S)
    (path : PaperStepSevenPath model) : Hidden × D :=
  (path.hidden, path.transcript.d)

/--
Compatibility reconstructs the complete measured transcript from the hidden
state and `D`; hence `paperHiddenAndD` is injective on surviving paths.
-/
theorem paperHiddenAndD_injective
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    (model : PaperStepSevenModel Hidden Y D W S) :
    Function.Injective (paperHiddenAndD model) := by
  intro path₁ path₂ h
  have hHidden : path₁.hidden = path₂.hidden := congrArg Prod.fst h
  have hD : path₁.transcript.d = path₂.transcript.d := congrArg Prod.snd h
  have hCompat₁ := path₁.compatible_property
  have hCompat₂ := path₂.compatible_property
  have hY : path₁.transcript.y = path₂.transcript.y := by
    rw [← hCompat₁.2.1, ← hCompat₂.2.1, hHidden]
  have hW : path₁.transcript.w = path₂.transcript.w := by
    rw [← hCompat₁.2.2.2.1, ← hCompat₂.2.2.2.1, hHidden, hD]
  have hS : path₁.transcript.s = path₂.transcript.s := by
    rw [← hCompat₁.2.2.1, ← hCompat₂.2.2.1, hHidden, hD]
  have hHPrime : path₁.transcript.hPrime = path₂.transcript.hPrime := by
    rw [← hCompat₁.2.2.2.2, ← hCompat₂.2.2.2.2, hHidden, hD]
  have hTranscript : path₁.transcript = path₂.transcript :=
    stepSevenTranscript_ext path₁.transcript path₂.transcript
      hY hD hW hS hHPrime
  apply Subtype.ext
  exact Prod.ext hTranscript hHidden

/-- Exact squared magnitude of the two normalized Hadamard factors. -/
theorem normSq_paperHadamardFactor
    (D Low : Type*) [Fintype D] [Fintype Low]
    [Nonempty D] [Nonempty Low] :
    Complex.normSq (paperHadamardFactor D Low) =
      (((Fintype.card D : Real) * Fintype.card Low)⁻¹) := by
  unfold paperHadamardFactor
  rw [Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt]
  positivity

variable [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
  [Fintype Low]
  [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]

/--
The surviving paper paths have total diagonal common-path energy at most
`1 / card Low`.  This is the strongest bound obtained solely from unit
Step-2 diagonal energy and the two Hadamard normalization factors.
-/
theorem sum_normSq_paperCommonPathAmplitude_le_inv_card_low
    [Nonempty D] [Nonempty Low]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (hStepTwoEnergy :
      (∑ phi : Hidden,
        Complex.normSq (stepTwoAmplitude (model.yOf phi))) <= 1) :
    (∑ path : PaperStepSevenPath model,
        Complex.normSq
          (paperCommonPathAmplitude (Low := Low) stepTwoAmplitude
            path.transcript)) <=
      (Fintype.card Low : Real)⁻¹ := by
  classical
  let weight : Hidden × D -> Real := fun pair =>
    Complex.normSq
      (stepTwoAmplitude (model.yOf pair.1) * paperHadamardFactor D Low)
  have hPathToImage :
      (∑ path : PaperStepSevenPath model,
          Complex.normSq
            (paperCommonPathAmplitude (Low := Low) stepTwoAmplitude
              path.transcript)) =
        ∑ path : PaperStepSevenPath model,
          weight (paperHiddenAndD model path) := by
    apply Finset.sum_congr rfl
    intro path _
    unfold paperCommonPathAmplitude weight paperHiddenAndD
    rw [← path.compatible_property.2.1]
  calc
    (∑ path : PaperStepSevenPath model,
        Complex.normSq
          (paperCommonPathAmplitude (Low := Low) stepTwoAmplitude
            path.transcript)) =
        ∑ path : PaperStepSevenPath model,
          weight (paperHiddenAndD model path) := hPathToImage
    _ = (Finset.univ.image (paperHiddenAndD model)).sum weight :=
      (Finset.sum_image (paperHiddenAndD_injective model).injOn).symm
    _ <= Finset.univ.sum weight := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun pair _ _ => Complex.normSq_nonneg _)
    _ = (Fintype.card D : Real) *
          Complex.normSq (paperHadamardFactor D Low) *
          ∑ phi : Hidden,
            Complex.normSq (stepTwoAmplitude (model.yOf phi)) := by
      unfold weight
      rw [Fintype.sum_prod_type]
      simp_rw [Complex.normSq_mul]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ <= (Fintype.card D : Real) *
          Complex.normSq (paperHadamardFactor D Low) := by
      have h := mul_le_mul_of_nonneg_left hStepTwoEnergy
        (mul_nonneg (Nat.cast_nonneg (Fintype.card D))
          (Complex.normSq_nonneg (paperHadamardFactor D Low)))
      simpa only [mul_one] using h
    _ = (Fintype.card Low : Real)⁻¹ := by
      rw [normSq_paperHadamardFactor]
      have hD : (Fintype.card D : Real) ≠ 0 := by positivity
      have hLow : (Fintype.card Low : Real) ≠ 0 := by positivity
      field_simp

/-- The preceding sharper bound implies the unit path-energy premise. -/
theorem sum_normSq_paperCommonPathAmplitude_le_one
    [Nonempty D] [Nonempty Low]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (hStepTwoEnergy :
      (∑ phi : Hidden,
        Complex.normSq (stepTwoAmplitude (model.yOf phi))) <= 1) :
    (∑ path : PaperStepSevenPath model,
        Complex.normSq
          (paperCommonPathAmplitude (Low := Low) stepTwoAmplitude
            path.transcript)) <= 1 := by
  exact (sum_normSq_paperCommonPathAmplitude_le_inv_card_low
    model stepTwoAmplitude hStepTwoEnergy).trans (by
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance))

/--
Paper-shaped joint form of the repaired first clause.  Every residual
`hStar` branch being below the squared signed-count threshold has total
unnormalized transcript Born mass at most `2^(-n)`.
-/
theorem paperPaths_allBranchesSmall_mass_le
    [Nonempty D] [Nonempty Low]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (n : Nat)
    (hStepTwoEnergy :
      (∑ phi : Hidden,
        Complex.normSq (stepTwoAmplitude (model.yOf phi))) <= 1) :
    realFiniteMass
        (transcriptBornWeight
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model)
          (fun transcript (_hStar : Bool) =>
            paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript))
        (allStepSevenBranchesSmall
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model) n) <=
      (2 : Real)⁻¹ ^ n := by
  apply compatiblePaths_allBranchesSmall_mass_le
    (paperCompatible model) (paperBranch model) (paperPositive model)
      (fun transcript (_hStar : Bool) =>
        paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript) n
  simpa using
    sum_normSq_paperCommonPathAmplitude_le_one model stepTwoAmplitude hStepTwoEnergy

end SimonDCP.Probability.LemmaThreePaperPathEnergy
