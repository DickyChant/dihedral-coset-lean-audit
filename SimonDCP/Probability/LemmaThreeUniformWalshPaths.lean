import SimonDCP.Probability.LemmaThreePathRefinement

/-!
# Uniform Walsh paths for the first clause of Lemma 3

After Step 2, the hidden Boolean selections in one reachable fibre have equal
magnitude.  A normalized Walsh transform sends every hidden selection to every
Hadamard outcome with the same squared path magnitude

```text
1 / (card Hidden * card Hadamard).
```

Any later filtering represented by a compatibility predicate retains a subset
of the pairs `(hidden, hadamard)`.  This module proves that the total diagonal
energy of any such surviving relation is at most one, and feeds that fact
directly into the independence-free small-branch theorem.  Additional coherent
transforms must first be included as further fine-path coordinates; they are
not silently treated as Boolean deletion.  The maps to the complete transcript
and residual branch remain arbitrary, so they may contain the adaptive choice
`A(D)`.
-/

namespace SimonDCP.Probability.LemmaThreeUniformWalshPaths

open scoped BigOperators

open SimonDCP.Probability.LemmaThreeBornBounds
open SimonDCP.Probability.LemmaThreePathRefinement

/-- A surviving fine path is a hidden selection, a Walsh outcome, and a proof
that all later postselection constraints accept that pair. -/
abbrev UniformWalshPath
    (Hidden Hadamard : Type*)
    (survives : Hidden -> Hadamard -> Prop)
    [DecidablePred fun pair : Hidden × Hadamard => survives pair.1 pair.2] :=
  {pair : Hidden × Hadamard // survives pair.1 pair.2}

/-- Squared magnitude of one path in a normalized equal-amplitude hidden state
followed by a normalized Walsh transform. -/
noncomputable def uniformWalshPathScale (Hidden Hadamard : Type*)
    [Fintype Hidden] [Fintype Hadamard] : Real :=
  1 / ((Fintype.card Hidden : Real) * Fintype.card Hadamard)

/-- Every surviving path has nonnegative squared magnitude. -/
theorem uniformWalshPathScale_nonneg
    (Hidden Hadamard : Type*) [Fintype Hidden] [Fintype Hadamard] :
    0 <= uniformWalshPathScale Hidden Hadamard := by
  unfold uniformWalshPathScale
  positivity

/--
Deleting arbitrary hidden/outcome pairs through the supplied compatibility
predicate cannot increase the total diagonal path energy above one.
-/
theorem sum_uniformWalshPathScale_le_one
    (Hidden Hadamard : Type*) [Fintype Hidden] [Fintype Hadamard]
    [Nonempty Hidden] [Nonempty Hadamard]
    (survives : Hidden -> Hadamard -> Prop)
    [DecidablePred fun pair : Hidden × Hadamard => survives pair.1 pair.2] :
    (∑ _path : UniformWalshPath Hidden Hadamard survives,
      uniformWalshPathScale Hidden Hadamard) <= 1 := by
  let Path := UniformWalshPath Hidden Hadamard survives
  have hCard : Fintype.card Path <= Fintype.card (Hidden × Hadamard) :=
    Fintype.card_le_of_injective (fun path : Path => path.1) Subtype.val_injective
  have hCast : (Fintype.card Path : Real) <=
      (Fintype.card Hidden : Real) * Fintype.card Hadamard := by
    exact_mod_cast (by simpa using hCard)
  have hDenom : 0 <
      (Fintype.card Hidden : Real) * Fintype.card Hadamard := by
    positivity
  simp only [uniformWalshPathScale, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [mul_one_div]
  exact (div_le_one hDenom).2 hCast

variable {Hidden Hadamard Transcript Branch : Type*}

/--
Equal-amplitude Walsh-path model of the first-clause inequality.  Its left
side is a finite model mass of surviving transcripts on which every residual
branch misses the squared threshold `2^(-n) * pathCount`.  It becomes an
actual joint Born mass only after the model amplitudes and orthogonal branches
are identified with the concrete circuit.
-/
theorem uniformWalshPaths_smallBranchMass_le
    [Fintype Hidden] [Fintype Hadamard]
    [Fintype Transcript] [Fintype Branch]
    [Nonempty Hidden] [Nonempty Hadamard]
    [DecidableEq Transcript] [DecidableEq Branch]
    (survives : Hidden -> Hadamard -> Prop)
    [DecidablePred fun pair : Hidden × Hadamard => survives pair.1 pair.2]
    (transcriptOf : UniformWalshPath Hidden Hadamard survives -> Transcript)
    (branchOf : UniformWalshPath Hidden Hadamard survives -> Branch)
    (positive : UniformWalshPath Hidden Hadamard survives -> Bool)
    (n : Nat) :
    realFiniteMass
        (fun transcript => ∑ branch,
          uniformWalshPathScale Hidden Hadamard *
            signedCountSq
              (positivePathCount transcriptOf branchOf positive transcript branch)
              (negativePathCount transcriptOf branchOf positive transcript branch))
        (countSmallBranchEvent
          (positivePathCount transcriptOf branchOf positive)
          (negativePathCount transcriptOf branchOf positive)
          ((2 : Real)⁻¹ ^ n)) <=
      (2 : Real)⁻¹ ^ n := by
  apply pathModel_smallBranchMass_le_paperThreshold
    transcriptOf branchOf positive
      (fun _transcript _branch => uniformWalshPathScale Hidden Hadamard) n
  · intro _transcript _branch
    exact uniformWalshPathScale_nonneg Hidden Hadamard
  · exact sum_uniformWalshPathScale_le_one Hidden Hadamard survives

end SimonDCP.Probability.LemmaThreeUniformWalshPaths
