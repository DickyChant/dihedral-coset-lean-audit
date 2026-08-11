import Mathlib

/-!
# Born-size-biased bounds for a repaired Lemma 3

The proof sketch of Lemma 3 treats Walsh signs as pairwise independent after
an adaptive measurement record has been fixed.  That independence assertion
is not available.  The two elementary estimates below isolate a replacement
that does not use independence.

The first estimate applies when the Born mass of an outcome is a sum of
coherent branch energies.  If every branch energy is small compared with its
corresponding incoherent path energy, then the total Born mass of such outcomes
is small.  This is the precise finite-sum version of Born size bias.

The second estimate concerns an implicit decomposition of an amplitude into
labelled components.  If a component is large after normalization by the
outcome mass, the outcome mass is bounded by that component energy divided by
the squared threshold.  Summing over all labels gives a tail bound from the
total labelled energy.  The total-energy premise must be proved for the
particular labels.  It is automatic for a fixed orthogonal refinement, but not
for the paper's outcome-dependent label `z*(A(D))`; the latter is a coherent
regrouping made before the conjugate-basis outcome `D` is known.

Neither theorem assumes independence, identical distributions, or that the
event was chosen independently of the amplitudes.
-/

namespace SimonDCP.Probability.LemmaThreeBornBounds

open scoped BigOperators
open Finset

/-- Total mass of an event in a finite real-weighted space. -/
noncomputable def realFiniteMass {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (event : Omega -> Prop) : Real := by
  classical
  exact ∑ omega, if event omega then weight omega else 0

/--
Born-size-biased small-branch bound.  The event may depend arbitrarily on the
outcome.  Its only required property is the displayed pointwise comparison
between coherent and incoherent branch energies.
-/
theorem branchEnergy_badMass_le
    {Omega Branch : Type*} [Fintype Omega] [Fintype Branch]
    (coherentEnergy incoherentEnergy : Omega -> Branch -> Real)
    (epsilonSq : Real) (event : Omega -> Prop)
    (hEvent : forall omega, event omega -> forall branch,
      coherentEnergy omega branch <=
        epsilonSq * incoherentEnergy omega branch)
    (hIncoherent : forall omega branch, 0 <= incoherentEnergy omega branch)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalIncoherent :
      (∑ omega, ∑ branch, incoherentEnergy omega branch) <= 1) :
    realFiniteMass
        (fun omega => ∑ branch, coherentEnergy omega branch) event <=
      epsilonSq := by
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
    _ <= epsilonSq * 1 :=
      mul_le_mul_of_nonneg_left hTotalIncoherent hEpsilon
    _ = epsilonSq := by ring

/-- Squared signed imbalance of two finite path counts. -/
def signedCountSq (positive negative : Nat) : Real :=
  ((positive : Real) - (negative : Real)) ^ 2

/-- Incoherent number of paths represented by two signed path counts. -/
def pathCount (positive negative : Nat) : Real :=
  (positive + negative : Nat)

/-- Every branch has squared imbalance at most `epsilonSq` times its path count. -/
def countSmallBranchEvent
    {Omega Branch : Type*} [Fintype Branch]
    (positive negative : Omega -> Branch -> Nat)
    (epsilonSq : Real) (omega : Omega) : Prop :=
  forall branch,
    signedCountSq (positive omega branch) (negative omega branch) <=
      epsilonSq * pathCount (positive omega branch) (negative omega branch)

/--
Count-level specialization of `branchEnergy_badMass_le`.  `scale` is the
squared magnitude common to the paths in one outcome branch.  This is the
form directly matching the signed path counts in the paper's definition of a
well-behaved outcome.
-/
theorem countSmallBranchMass_le
    {Omega Branch : Type*} [Fintype Omega] [Fintype Branch]
    (scale : Omega -> Branch -> Real)
    (positive negative : Omega -> Branch -> Nat)
    (epsilonSq : Real)
    (hScale : forall omega branch, 0 <= scale omega branch)
    (hEpsilon : 0 <= epsilonSq)
    (hTotalIncoherent :
      (∑ omega, ∑ branch,
        scale omega branch *
          pathCount (positive omega branch) (negative omega branch)) <= 1) :
    realFiniteMass
        (fun omega => ∑ branch,
          scale omega branch *
            signedCountSq (positive omega branch) (negative omega branch))
        (countSmallBranchEvent positive negative epsilonSq) <=
      epsilonSq := by
  apply branchEnergy_badMass_le
    (fun omega branch =>
      scale omega branch *
        signedCountSq (positive omega branch) (negative omega branch))
    (fun omega branch =>
      scale omega branch *
        pathCount (positive omega branch) (negative omega branch))
    epsilonSq (countSmallBranchEvent positive negative epsilonSq)
  · intro omega hSmall branch
    have h := mul_le_mul_of_nonneg_left (hSmall branch) (hScale omega branch)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · intro omega branch
    have hPath :
        0 <= pathCount (positive omega branch) (negative omega branch) := by
      unfold pathCount
      exact_mod_cast Nat.zero_le
        (positive omega branch + negative omega branch)
    exact mul_nonneg (hScale omega branch) hPath
  · exact hEpsilon
  · exact hTotalIncoherent

/--
At the paper's squared well-behaved threshold `2^(-n)`, the Born mass of
outcomes for which every branch is below threshold is at most `2^(-n)`.
This is the exact, constant-free replacement for the first probabilistic step
of Lemma 3, subject only to normalization of the refined path energy.
-/
theorem countSmallBranchMass_le_paperThreshold
    {Omega Branch : Type*} [Fintype Omega] [Fintype Branch]
    (scale : Omega -> Branch -> Real)
    (positive negative : Omega -> Branch -> Nat)
    (n : Nat)
    (hScale : forall omega branch, 0 <= scale omega branch)
    (hTotalIncoherent :
      (∑ omega, ∑ branch,
        scale omega branch *
          pathCount (positive omega branch) (negative omega branch)) <= 1) :
    realFiniteMass
        (fun omega => ∑ branch,
          scale omega branch *
            signedCountSq (positive omega branch) (negative omega branch))
        (countSmallBranchEvent positive negative ((2 : Real)⁻¹ ^ n)) <=
      (2 : Real)⁻¹ ^ n := by
  apply countSmallBranchMass_le scale positive negative
  · exact hScale
  · positivity
  · exact hTotalIncoherent

/--
An outcome has a component whose squared magnitude is larger than
`thresholdSq` times the outcome's Born mass.  This multiplication-only form
also handles zero-mass outcomes without division.
-/
def largeNormalizedComponentEvent
    {Omega Index : Type*} [Fintype Index]
    (outcomeMass : Omega -> Real) (componentEnergy : Omega -> Index -> Real)
    (thresholdSq : Real) (omega : Omega) : Prop :=
  exists index,
    thresholdSq * outcomeMass omega < componentEnergy omega index

/--
Self-normalized component tail bound.  The event mass is at most the total
labelled component energy divided by the squared threshold.  The outcome mass
need not be independent of the component family.
-/
theorem largeNormalizedComponentMass_le
    {Omega Index : Type*} [Fintype Omega] [Fintype Index]
    (outcomeMass : Omega -> Real) (componentEnergy : Omega -> Index -> Real)
    (thresholdSq : Real)
    (hThreshold : 0 < thresholdSq)
    (hComponent : forall omega index, 0 <= componentEnergy omega index)
    (hTotalComponent :
      (∑ omega, ∑ index, componentEnergy omega index) <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedComponentEvent outcomeMass componentEnergy thresholdSq) <=
      1 / thresholdSq := by
  classical
  unfold realFiniteMass
  have hPointwise (omega : Omega) :
      (if largeNormalizedComponentEvent outcomeMass componentEnergy thresholdSq omega
        then outcomeMass omega else 0) <=
        (∑ index, componentEnergy omega index) / thresholdSq := by
    by_cases hLarge :
        largeNormalizedComponentEvent outcomeMass componentEnergy thresholdSq omega
    · simp only [hLarge, if_true]
      obtain ⟨index, hIndex⟩ := hLarge
      have hIndexLe :
          componentEnergy omega index <=
            ∑ candidate, componentEnergy omega candidate := by
        exact Finset.single_le_sum
          (fun candidate _ => hComponent omega candidate)
          (Finset.mem_univ index)
      have hProduct :
          thresholdSq * outcomeMass omega <
            ∑ candidate, componentEnergy omega candidate :=
        lt_of_lt_of_le hIndex hIndexLe
      exact le_of_lt ((lt_div_iff₀ hThreshold).2 (by
        simpa only [mul_comm] using hProduct))
    · simp only [hLarge, if_false]
      exact div_nonneg
        (Finset.sum_nonneg fun index _ => hComponent omega index)
        (le_of_lt hThreshold)
  calc
    (∑ omega,
        if largeNormalizedComponentEvent outcomeMass componentEnergy thresholdSq omega
          then outcomeMass omega else 0) <=
        ∑ omega,
          (∑ index, componentEnergy omega index) / thresholdSq := by
      exact Finset.sum_le_sum fun omega _ => hPointwise omega
    _ = (∑ omega, ∑ index, componentEnergy omega index) /
        thresholdSq := by
      rw [Finset.sum_div]
    _ <= 1 / thresholdSq :=
      (div_le_div_iff_of_pos_right hThreshold).2 hTotalComponent

/--
At the squared threshold `2^(3n)`, a component family whose total energy is at
most one has tail at most `2^(-3n)`.  This conditional estimate is stronger
than the `O(2^(-n))` scale requested by the paper's second Lemma 3 conclusion;
the adaptive paper component does not automatically satisfy the energy
premise.
-/
theorem largeNormalizedComponentMass_le_paperThreshold
    {Omega Index : Type*} [Fintype Omega] [Fintype Index]
    (outcomeMass : Omega -> Real) (componentEnergy : Omega -> Index -> Real)
    (n : Nat)
    (hComponent : forall omega index, 0 <= componentEnergy omega index)
    (hTotalComponent :
      (∑ omega, ∑ index, componentEnergy omega index) <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedComponentEvent outcomeMass componentEnergy
          ((2 : Real) ^ (3 * n))) <=
      1 / ((2 : Real) ^ (3 * n)) := by
  apply largeNormalizedComponentMass_le
  · positivity
  · exact hComponent
  · exact hTotalComponent

/--
The same conditional argument at squared threshold `n^3` gives an `n^(-3)`
tail when the total coherent bucket energy is at most one.  The index type may
directly represent coarse buckets, avoiding a union bound over their exact
residue members, but the coherent bucket-energy premise remains substantive.
-/
theorem largeNormalizedComponentMass_le_bucketThreshold
    {Omega Index : Type*} [Fintype Omega] [Fintype Index]
    (outcomeMass : Omega -> Real) (componentEnergy : Omega -> Index -> Real)
    (n : Nat) (hn : 0 < n)
    (hComponent : forall omega index, 0 <= componentEnergy omega index)
    (hTotalComponent :
      (∑ omega, ∑ index, componentEnergy omega index) <= 1) :
    realFiniteMass outcomeMass
        (largeNormalizedComponentEvent outcomeMass componentEnergy
          ((n : Real) ^ 3)) <=
      1 / ((n : Real) ^ 3) := by
  apply largeNormalizedComponentMass_le
  · positivity
  · exact hComponent
  · exact hTotalComponent

end SimonDCP.Probability.LemmaThreeBornBounds
