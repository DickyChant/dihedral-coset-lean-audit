import SimonDCP.Probability.LemmaThreePaperPathEnergy
import SimonDCP.Probability.LemmaThreePostselection

/-!
# Budgeted first-clause bounds for Lemma 3

The small-branch argument scales with the available incoherent path-energy
budget.  If every coherent branch energy is at most `epsilonSq` times its
incoherent path energy and the total incoherent energy is at most
`energyBudget`, then the bad mass is at most
`epsilonSq * energyBudget`.

For the paper-shaped finite analytic model, the common-path energy estimate is
the sharper `1 / card Low`, rather than merely one.  Keeping that factor gives
joint bad mass at most

```text
2^(-n) / card Low.
```

Consequently, conditioning on an accepted mass at least
`kappa / card Low` cancels the same normalization factor and costs only
`1 / kappa`.  These statements concern the finite analytic transcript model;
identification with the circuit Born distribution and orthogonality of the
residual circuit branches are separate semantic bridge obligations.
-/

namespace SimonDCP.Probability.LemmaThreeBudgetedFirstClause

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePaperPathBridge
open SimonDCP.Probability.LemmaThreePaperPathEnergy
open SimonDCP.Probability.LemmaThreePathRefinement
open SimonDCP.Probability.LemmaThreePostselection
open SimonDCP.Probability.LemmaThreeTranscriptModel

/-- Budgeted form of the Born-size-biased branch-energy estimate. -/
theorem branchEnergy_badMass_le_budget
    {Omega Branch : Type*} [Fintype Omega] [Fintype Branch]
    (coherentEnergy incoherentEnergy : Omega -> Branch -> Real)
    (epsilonSq energyBudget : Real) (event : Omega -> Prop)
    (hEvent : forall omega, event omega -> forall branch,
      coherentEnergy omega branch <=
        epsilonSq * incoherentEnergy omega branch)
    (hIncoherent : forall omega branch, 0 <= incoherentEnergy omega branch)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalIncoherent :
      (∑ omega, ∑ branch, incoherentEnergy omega branch) <= energyBudget) :
    realFiniteMass
        (fun omega => ∑ branch, coherentEnergy omega branch) event <=
      epsilonSq * energyBudget := by
  classical
  unfold realFiniteMass
  have hPointwise (omega : Omega) :
      (if event omega then
          ∑ branch, coherentEnergy omega branch
        else 0) <=
        epsilonSq * (∑ branch, incoherentEnergy omega branch) := by
    by_cases hBad : event omega
    · simp only [hBad, if_true]
      calc
        (∑ branch, coherentEnergy omega branch) <=
            ∑ branch, epsilonSq * incoherentEnergy omega branch := by
          exact Finset.sum_le_sum fun branch _ => hEvent omega hBad branch
        _ = epsilonSq * (∑ branch, incoherentEnergy omega branch) := by
          rw [Finset.mul_sum]
    · simp only [hBad, if_false]
      exact mul_nonneg hEpsilon (Finset.sum_nonneg fun branch _ =>
        hIncoherent omega branch)
  calc
    (∑ omega,
        if event omega then
          ∑ branch, coherentEnergy omega branch
        else 0) <=
        ∑ omega,
          epsilonSq * (∑ branch, incoherentEnergy omega branch) := by
      exact Finset.sum_le_sum fun omega _ => hPointwise omega
    _ = epsilonSq *
        (∑ omega, ∑ branch, incoherentEnergy omega branch) := by
      rw [Finset.mul_sum]
    _ <= epsilonSq * energyBudget :=
      mul_le_mul_of_nonneg_left hTotalIncoherent hEpsilon

/-- Count-level budgeted small-branch estimate. -/
theorem countSmallBranchMass_le_budget
    {Omega Branch : Type*} [Fintype Omega] [Fintype Branch]
    (scale : Omega -> Branch -> Real)
    (positive negative : Omega -> Branch -> Nat)
    (epsilonSq energyBudget : Real)
    (hScale : forall omega branch, 0 <= scale omega branch)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalIncoherent :
      (∑ omega, ∑ branch,
        scale omega branch *
          pathCount (positive omega branch) (negative omega branch)) <=
        energyBudget) :
    realFiniteMass
        (fun omega => ∑ branch,
          scale omega branch *
            signedCountSq (positive omega branch) (negative omega branch))
        (countSmallBranchEvent positive negative epsilonSq) <=
      epsilonSq * energyBudget := by
  apply branchEnergy_badMass_le_budget
    (fun omega branch =>
      scale omega branch *
        signedCountSq (positive omega branch) (negative omega branch))
    (fun omega branch =>
      scale omega branch *
        pathCount (positive omega branch) (negative omega branch))
    epsilonSq energyBudget
      (countSmallBranchEvent positive negative epsilonSq)
  · intro omega hSmall branch
    have h := mul_le_mul_of_nonneg_left (hSmall branch) (hScale omega branch)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · intro omega branch
    have hPath :
        0 <= pathCount (positive omega branch) (negative omega branch) := by
      unfold pathCount
      exact_mod_cast Nat.zero_le (positive omega branch + negative omega branch)
    exact mul_nonneg (hScale omega branch) hPath
  · exact hEpsilon
  · exact hTotalIncoherent

/-- Complete-transcript form of the budgeted small-branch estimate. -/
theorem allBranchesSmall_mass_le_budget
    {Path Transcript Branch : Type*}
    [Fintype Path] [Fintype Transcript] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (transcriptOf : Path -> Transcript) (branchOf : Path -> Branch)
    (positive : Path -> Bool) (commonAmplitude : Transcript -> Branch -> Complex)
    (epsilonSq energyBudget : Real)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalPathEnergy :
      (∑ path,
        Complex.normSq
          (commonAmplitude (transcriptOf path) (branchOf path))) <=
        energyBudget) :
    realFiniteMass
        (transcriptBornWeight transcriptOf branchOf positive commonAmplitude)
        (countSmallBranchEvent
          (positivePathCount transcriptOf branchOf positive)
          (negativePathCount transcriptOf branchOf positive)
          epsilonSq) <=
      epsilonSq * energyBudget := by
  rw [show
    transcriptBornWeight transcriptOf branchOf positive commonAmplitude =
      fun transcript => ∑ branch,
        Complex.normSq (commonAmplitude transcript branch) *
          signedCountSq
            (positivePathCount transcriptOf branchOf positive transcript branch)
            (negativePathCount transcriptOf branchOf positive transcript branch) by
      funext transcript
      exact transcriptBornWeight_eq_scaledSignedCounts
        transcriptOf branchOf positive commonAmplitude transcript]
  apply countSmallBranchMass_le_budget
  · intro transcript branch
    exact Complex.normSq_nonneg _
  · exact hEpsilon
  · rw [totalIncoherentPathEnergy_eq transcriptOf branchOf positive]
    exact hTotalPathEnergy

/-- Relational specialization for compatible hidden paths. -/
theorem compatiblePaths_allBranchesSmall_mass_le_budget
    {Transcript Hidden Branch : Type*}
    [Fintype Transcript] [Fintype Hidden] [Fintype Branch]
    [DecidableEq Transcript] [DecidableEq Branch]
    (compatible : Transcript -> Hidden -> Prop)
    [DecidablePred fun pair : Transcript × Hidden => compatible pair.1 pair.2]
    (branchOf : CompatibleStepSevenPath Transcript Hidden compatible -> Branch)
    (positive : CompatibleStepSevenPath Transcript Hidden compatible -> Bool)
    (commonAmplitude : Transcript -> Branch -> Complex)
    (epsilonSq energyBudget : Real)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalPathEnergy :
      (∑ path : CompatibleStepSevenPath Transcript Hidden compatible,
        Complex.normSq
          (commonAmplitude path.transcript (branchOf path))) <=
        energyBudget) :
    realFiniteMass
        (transcriptBornWeight
          CompatibleStepSevenPath.transcript branchOf positive commonAmplitude)
        (countSmallBranchEvent
          (positivePathCount CompatibleStepSevenPath.transcript branchOf positive)
          (negativePathCount CompatibleStepSevenPath.transcript branchOf positive)
          epsilonSq) <=
      epsilonSq * energyBudget := by
  exact allBranchesSmall_mass_le_budget
    CompatibleStepSevenPath.transcript branchOf positive commonAmplitude
      epsilonSq energyBudget hEpsilon hTotalPathEnergy

variable {Hidden Y D W S Low : Type*}

/--
The joint small-branch mass in the paper-shaped finite analytic model retains
the full `1 / card Low` common-path energy gain.
-/
theorem paperPaths_allBranchesSmall_mass_le_inv_card_low
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
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
      (2 : Real)⁻¹ ^ n * (Fintype.card Low : Real)⁻¹ := by
  unfold allStepSevenBranchesSmall
  exact compatiblePaths_allBranchesSmall_mass_le_budget
      (paperCompatible model) (paperBranch model) (paperPositive model)
      (fun transcript (_hStar : Bool) =>
        paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript)
      ((2 : Real)⁻¹ ^ n) ((Fintype.card Low : Real)⁻¹)
      (by positivity)
      (sum_normSq_paperCommonPathAmplitude_le_inv_card_low
        model stepTwoAmplitude hStepTwoEnergy)

/--
If accepted mass is at least `kappa / card Low`, postselection cancels the
same `card Low` factor in the joint bad-mass estimate.
-/
theorem paperPaths_conditional_allBranchesSmall_mass_le
    [Fintype Hidden] [Fintype Y] [Fintype D] [Fintype W] [Fintype S]
    [Fintype Low]
    [DecidableEq Y] [DecidableEq D] [DecidableEq W] [DecidableEq S]
    [Nonempty D] [Nonempty Low]
    (model : PaperStepSevenModel Hidden Y D W S)
    (stepTwoAmplitude : Y -> Complex)
    (accept : StepSevenTranscript Y D W S -> Prop)
    (n : Nat) (kappa : Real)
    (hStepTwoEnergy :
      (∑ phi : Hidden,
        Complex.normSq (stepTwoAmplitude (model.yOf phi))) <= 1)
    (hKappa : 0 < kappa)
    (hAcceptedMass :
      kappa / (Fintype.card Low : Real) <=
        finiteAcceptanceMass
          (transcriptBornWeight
            CompatibleStepSevenPath.transcript
            (paperBranch model) (paperPositive model)
            (fun transcript (_hStar : Bool) =>
              paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript))
          accept) :
    finiteConditionalBadMass
        (transcriptBornWeight
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model)
          (fun transcript (_hStar : Bool) =>
            paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript))
        accept
        (allStepSevenBranchesSmall
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model) n) <=
      ((2 : Real)⁻¹ ^ n) / kappa := by
  classical
  let weight : StepSevenTranscript Y D W S -> Real :=
    transcriptBornWeight
      CompatibleStepSevenPath.transcript
      (paperBranch model) (paperPositive model)
      (fun transcript (_hStar : Bool) =>
        paperCommonPathAmplitude (Low := Low) stepTwoAmplitude transcript)
  let bad : StepSevenTranscript Y D W S -> Prop :=
    allStepSevenBranchesSmall
      CompatibleStepSevenPath.transcript
      (paperBranch model) (paperPositive model) n
  have hWeight : forall transcript, 0 <= weight transcript := by
    intro transcript
    unfold weight transcriptBornWeight
    exact Finset.sum_nonneg fun branch _ =>
      Complex.normSq_nonneg
        (rawBranchAmplitude
          CompatibleStepSevenPath.transcript
          (paperBranch model) (paperPositive model)
          (fun measured (_hStar : Bool) =>
            paperCommonPathAmplitude (Low := Low) stepTwoAmplitude measured)
          transcript branch)
  have hBadMass :
      realFiniteMass weight bad <=
        (2 : Real)⁻¹ ^ n * (Fintype.card Low : Real)⁻¹ := by
    simpa [weight, bad] using
      paperPaths_allBranchesSmall_mass_le_inv_card_low
        (Low := Low) model stepTwoAmplitude n hStepTwoEnergy
  have hJoint :
      finiteJointBadMass weight accept bad <=
        (2 : Real)⁻¹ ^ n * (Fintype.card Low : Real)⁻¹ := by
    apply le_trans (b := realFiniteMass weight bad)
    · unfold finiteJointBadMass realFiniteMass
      apply Finset.sum_le_sum
      intro transcript _
      by_cases hAccept : accept transcript <;>
        by_cases hBad : bad transcript <;>
          simp [hAccept, hBad, hWeight transcript]
    · exact hBadMass
  have hLowPos : (0 : Real) < Fintype.card Low := by positivity
  have hRho : 0 < kappa / (Fintype.card Low : Real) :=
    div_pos hKappa hLowPos
  calc
    finiteConditionalBadMass weight accept bad <=
        ((2 : Real)⁻¹ ^ n * (Fintype.card Low : Real)⁻¹) /
          (kappa / (Fintype.card Low : Real)) := by
      apply finiteConditionalBadMass_le_bound_div_rho
      · exact hWeight
      · exact hJoint
      · exact hRho
      · simpa [weight] using hAcceptedMass
    _ = ((2 : Real)⁻¹ ^ n) / kappa := by
      field_simp [ne_of_gt hKappa, ne_of_gt hLowPos]

end SimonDCP.Probability.LemmaThreeBudgetedFirstClause
