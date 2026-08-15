import SimonDCP.Probability.Lemma4AverageDecoder
import SimonDCP.Probability.LemmaThreeStepSevenRegrouping

/-!
# Step-7 path-sum specialization of the average Lemma 4 decoder

`LemmaThreeStepSevenRegrouping` proves that an explicit finite double path sum
is exactly a count-weighted coefficient amplitude.  This file connects that
identity to the expectation-level `H ⊗ I` decoder repair.

The first theorem uses the exact energy of the coherently grouped right-side
coefficient.  The second eliminates that abstract coefficient-energy quantity
using the universal bound

```text
coefficient energy <= number of right paths * total right-path energy.
```

The first two theorems keep one honest semantic premise: the actual Step-7
state coordinates must equal the displayed finite double path sums.  They do
not claim that the paper's circuit has already been identified with this
model.  The final theorem additionally exposes the adaptive collision and
equal-population premises, and its two branches deliberately share the same
B-side path family, residue map, and term coefficients.  All three make the
price of a purely diagonal coefficient estimate explicit; if the number of
compatible right paths is exponential, a sharper Parseval or orthogonality
argument is still needed.
-/

namespace SimonDCP.Probability.Lemma4StepSevenAverage

open scoped BigOperators
open QuantumAlg
open SimonDCP.Probability.LemmaThreeCountEnergy
open SimonDCP.Probability.LemmaThreeToFourL2
open SimonDCP.Probability.LemmaThreeStepSevenRegrouping
open SimonDCP.Probability.Lemma4AverageDecoder
open SimonDCP.Quantum.ApproximateReadout

noncomputable section

variable {Ω APath BPath Residue : Type*}

/-- The left-side residue counts occurring in the Step-7 regrouping. -/
def stepSevenCount
    {Outer : Type*} [DecidableEq Residue]
    (aPaths : Ω → Outer → Finset APath)
    (aResidue : Ω → Outer → APath → Residue)
    (ω : Ω) (outer : Outer) : Residue → ℝ :=
  aResidueCount (aPaths ω outer) (aResidue ω outer)

/-- The coherently grouped right-side coefficient family. -/
def stepSevenCoefficient
    {Outer : Type*} [DecidableEq Residue]
    (bPaths : Ω → Outer → Finset BPath)
    (bResidue : Ω → Outer → BPath → Residue)
    (term : Ω → Outer → BPath → ℂ)
    (ω : Ω) (outer : Outer) : Residue → ℂ :=
  bResidueCoefficient (bPaths ω outer) (bResidue ω outer) (term ω outer)

/-- Exact scale-times-coefficient energy for one residual pair. -/
def stepSevenExactMultiplier
    {Outer : Type*} [Fintype Residue] [DecidableEq Residue]
    (scale : Ω → Outer → ℂ)
    (bPaths : Ω → Outer → Finset BPath)
    (bResidue : Ω → Outer → BPath → Residue)
    (term : Ω → Outer → BPath → ℂ)
    (ω : Ω) (outer : Outer) : ℝ :=
  Complex.normSq (scale ω outer) *
    coefficientEnergy
      (stepSevenCoefficient bPaths bResidue term ω outer)

/-- Universal diagonal upper bound for the preceding exact multiplier. -/
def stepSevenDiagonalMultiplier
    {Outer : Type*}
    (scale : Ω → Outer → ℂ)
    (bPaths : Ω → Outer → Finset BPath)
    (term : Ω → Outer → BPath → ℂ)
    (ω : Ω) (outer : Outer) : ℝ :=
  Complex.normSq (scale ω outer) *
    ((bPaths ω outer).card : ℝ) *
      ∑ b ∈ bPaths ω outer, Complex.normSq (term ω outer b)

theorem stepSevenExactMultiplier_nonneg
    {Outer : Type*} [Fintype Residue] [DecidableEq Residue]
    (scale : Ω → Outer → ℂ)
    (bPaths : Ω → Outer → Finset BPath)
    (bResidue : Ω → Outer → BPath → Residue)
    (term : Ω → Outer → BPath → ℂ)
    (ω : Ω) (outer : Outer) :
    0 ≤ stepSevenExactMultiplier scale bPaths bResidue term ω outer := by
  unfold stepSevenExactMultiplier coefficientEnergy
  exact mul_nonneg (Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun z _ => Complex.normSq_nonneg _)

theorem stepSevenExactMultiplier_le_diagonal
    {Outer : Type*} [Fintype Residue] [DecidableEq Residue]
    (scale : Ω → Outer → ℂ)
    (bPaths : Ω → Outer → Finset BPath)
    (bResidue : Ω → Outer → BPath → Residue)
    (term : Ω → Outer → BPath → ℂ)
    (ω : Ω) (outer : Outer) :
    stepSevenExactMultiplier scale bPaths bResidue term ω outer ≤
      stepSevenDiagonalMultiplier scale bPaths term ω outer := by
  unfold stepSevenExactMultiplier stepSevenDiagonalMultiplier
  have hCoefficient :=
    coefficientEnergy_bResidueCoefficient_le_card_mul_sum_normSq
      (bPaths ω outer) (bResidue ω outer) (term ω outer)
  simpa [stepSevenCoefficient, mul_assoc] using
    mul_le_mul_of_nonneg_left hCoefficient
      (Complex.normSq_nonneg (scale ω outer))

/--
Average gate-level decoder theorem with the Step-7 weighted-amplitude
coordinates discharged by the exact finite regrouping identity.
-/
theorem average_decoder_success_ge_of_stepSeven_exact_energy
    [Fintype Ω] {n : ℕ} [Fintype Residue] [DecidableEq Residue]
    (weight : Ω → ℝ) (state : Ω → PureState (Qubits (1 + n)))
    (dBit : Bool) (scale : Ω → Fin (2 ^ n) → ℂ)
    (leftPaths rightPaths : Ω → Fin (2 ^ n) → Finset APath)
    (bPaths : Ω → Fin (2 ^ n) → Finset BPath)
    (leftResidue rightResidue :
      Ω → Fin (2 ^ n) → APath → Residue)
    (bResidue : Ω → Fin (2 ^ n) → BPath → Residue)
    (term : Ω → Fin (2 ^ n) → BPath → ℂ)
    (mean : Ω → Fin (2 ^ n) → ℝ) (budget : ℝ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hZeroDirect : ∀ ω outer,
      state ω (prodEquiv ((0 : Fin (2 ^ 1)), outer)) =
        scaledDirectAmplitude (scale ω outer)
          (leftPaths ω outer) (bPaths ω outer)
          (leftResidue ω outer) (bResidue ω outer) (term ω outer))
    (hOneDirect : ∀ ω outer,
      state ω (prodEquiv ((1 : Fin (2 ^ 1)), outer)) =
        targetSign dBit *
          scaledDirectAmplitude (scale ω outer)
            (rightPaths ω outer) (bPaths ω outer)
            (rightResidue ω outer) (bResidue ω outer) (term ω outer))
    (hExpected :
      expectedBranchCountBudget weight
        (stepSevenExactMultiplier scale bPaths bResidue term)
        (stepSevenCount leftPaths leftResidue)
        (stepSevenCount rightPaths rightResidue) mean ≤ budget) :
    1 - budget ≤ averageCorrectProbability weight state dBit := by
  apply average_state_labelled_decoder_success_ge_of_branch_count_energy
    weight state dBit scale
    (stepSevenCount leftPaths leftResidue)
    (stepSevenCount rightPaths rightResidue)
    (stepSevenCoefficient bPaths bResidue term)
    mean (stepSevenExactMultiplier scale bPaths bResidue term) budget
    hWeight hNormalized
  · intro ω outer
    simpa [scaledDirectAmplitude, stepSevenCount, stepSevenCoefficient,
      directDoubleSum_eq_weightedAmplitude] using hZeroDirect ω outer
  · intro ω outer
    simpa [scaledDirectAmplitude, stepSevenCount, stepSevenCoefficient,
      directDoubleSum_eq_weightedAmplitude, mul_assoc] using hOneDirect ω outer
  · exact stepSevenExactMultiplier_nonneg scale bPaths bResidue term
  · intro ω outer
    exact le_rfl
  · exact hExpected

/--
Diagonal-energy specialization.  This removes the abstract coefficient-energy
premise entirely, at the explicit cost of the number of compatible right
paths in each residual pair.
-/
theorem average_decoder_success_ge_of_stepSeven_diagonal_energy
    [Fintype Ω] {n : ℕ} [Fintype Residue] [DecidableEq Residue]
    (weight : Ω → ℝ) (state : Ω → PureState (Qubits (1 + n)))
    (dBit : Bool) (scale : Ω → Fin (2 ^ n) → ℂ)
    (leftPaths rightPaths : Ω → Fin (2 ^ n) → Finset APath)
    (bPaths : Ω → Fin (2 ^ n) → Finset BPath)
    (leftResidue rightResidue :
      Ω → Fin (2 ^ n) → APath → Residue)
    (bResidue : Ω → Fin (2 ^ n) → BPath → Residue)
    (term : Ω → Fin (2 ^ n) → BPath → ℂ)
    (mean : Ω → Fin (2 ^ n) → ℝ) (budget : ℝ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hZeroDirect : ∀ ω outer,
      state ω (prodEquiv ((0 : Fin (2 ^ 1)), outer)) =
        scaledDirectAmplitude (scale ω outer)
          (leftPaths ω outer) (bPaths ω outer)
          (leftResidue ω outer) (bResidue ω outer) (term ω outer))
    (hOneDirect : ∀ ω outer,
      state ω (prodEquiv ((1 : Fin (2 ^ 1)), outer)) =
        targetSign dBit *
          scaledDirectAmplitude (scale ω outer)
            (rightPaths ω outer) (bPaths ω outer)
            (rightResidue ω outer) (bResidue ω outer) (term ω outer))
    (hExpected :
      expectedBranchCountBudget weight
        (stepSevenDiagonalMultiplier scale bPaths term)
        (stepSevenCount leftPaths leftResidue)
        (stepSevenCount rightPaths rightResidue) mean ≤ budget) :
    1 - budget ≤ averageCorrectProbability weight state dBit := by
  apply average_state_labelled_decoder_success_ge_of_branch_count_energy
    weight state dBit scale
    (stepSevenCount leftPaths leftResidue)
    (stepSevenCount rightPaths rightResidue)
    (stepSevenCoefficient bPaths bResidue term)
    mean (stepSevenDiagonalMultiplier scale bPaths term) budget
    hWeight hNormalized
  · intro ω outer
    simpa [scaledDirectAmplitude, stepSevenCount, stepSevenCoefficient,
      directDoubleSum_eq_weightedAmplitude] using hZeroDirect ω outer
  · intro ω outer
    simpa [scaledDirectAmplitude, stepSevenCount, stepSevenCoefficient,
      directDoubleSum_eq_weightedAmplitude, mul_assoc] using hOneDirect ω outer
  · intro ω outer
    exact (stepSevenExactMultiplier_nonneg scale bPaths bResidue term
      ω outer).trans (stepSevenExactMultiplier_le_diagonal
        scale bPaths bResidue term ω outer)
  · exact stepSevenExactMultiplier_le_diagonal scale bPaths bResidue term
  · exact hExpected

/--
Fully composed finite Step-7 repair.  The A-side paths may be selected
adaptively from each classical record.  Selected-pair collision uniformity
supplies their expected count energies, while a record-uniform diagonal bound
controls the coherently grouped B-side coefficients.  The conclusion is the
overall correct probability of the concrete `H ⊗ I` decoder.

What remains semantic is stated explicitly: the actual state coordinates must
equal the two direct path sums with a common B-side path/residue/term family,
and the paper must prove the selected-pair and uniform diagonal bounds after
all conditioning.
-/
theorem average_decoder_success_ge_of_stepSeven_selected_pair_collision
    [Fintype Ω] [Fintype APath]
    {n : ℕ} [Fintype Residue] [DecidableEq Residue] [Nonempty Residue]
    (weight : Ω → ℝ) (state : Ω → PureState (Qubits (1 + n)))
    (dBit : Bool) (scale : Ω → Fin (2 ^ n) → ℂ)
    (leftSelected rightSelected :
      Fin (2 ^ n) → Ω → APath → Bool)
    (leftResidue rightResidue :
      Fin (2 ^ n) → Ω → APath → Residue)
    (bPaths : Ω → Fin (2 ^ n) → Finset BPath)
    (bResidue : Ω → Fin (2 ^ n) → BPath → Residue)
    (term : Ω → Fin (2 ^ n) → BPath → ℂ)
    (multiplier : Fin (2 ^ n) → ℝ)
    (hWeight : ∀ ω, 0 ≤ weight ω)
    (hNormalized : (∑ ω, weight ω) = 1)
    (hZeroDirect : ∀ ω outer,
      state ω (prodEquiv ((0 : Fin (2 ^ 1)), outer)) =
        scaledDirectAmplitude (scale ω outer)
          (selectedBalls (leftSelected outer) ω) (bPaths ω outer)
          (leftResidue outer ω) (bResidue ω outer) (term ω outer))
    (hOneDirect : ∀ ω outer,
      state ω (prodEquiv ((1 : Fin (2 ^ 1)), outer)) =
        targetSign dBit *
          scaledDirectAmplitude (scale ω outer)
            (selectedBalls (rightSelected outer) ω) (bPaths ω outer)
            (rightResidue outer ω) (bResidue ω outer) (term ω outer))
    (hMultiplier : ∀ outer, 0 ≤ multiplier outer)
    (hDiagonalBound : ∀ ω outer,
      stepSevenDiagonalMultiplier scale bPaths term ω outer ≤
        multiplier outer)
    (hSameTotal : ∀ ω outer,
      selectedTotal (leftSelected outer) ω =
        selectedTotal (rightSelected outer) ω)
    (hLeftPair : ∀ outer,
      WeightedPairCollisionUniform weight
        (leftSelected outer) (leftResidue outer))
    (hRightPair : ∀ outer,
      WeightedPairCollisionUniform weight
        (rightSelected outer) (rightResidue outer)) :
    1 - selectedPairCollisionBranchBudget Residue weight multiplier
          leftSelected rightSelected ≤
      averageCorrectProbability weight state dBit := by
  apply average_state_labelled_decoder_success_ge_of_selected_pair_collision
    weight state dBit scale
    (stepSevenCoefficient bPaths bResidue term) multiplier
    leftSelected rightSelected leftResidue rightResidue
    hWeight hNormalized
  · intro ω outer
    rw [hZeroDirect ω outer]
    unfold scaledDirectAmplitude
    rw [directDoubleSum_eq_weightedAmplitude]
    rfl
  · intro ω outer
    rw [hOneDirect ω outer]
    unfold scaledDirectAmplitude
    rw [directDoubleSum_eq_weightedAmplitude]
    simp only [mul_assoc]
    rfl
  · exact hMultiplier
  · intro ω outer
    have hExactToDiagonal := stepSevenExactMultiplier_le_diagonal
      scale bPaths bResidue term ω outer
    exact (show stepSevenExactMultiplier scale bPaths bResidue term ω outer ≤
        multiplier outer from hExactToDiagonal.trans (hDiagonalBound ω outer))
  · exact hSameTotal
  · exact hLeftPair
  · exact hRightPair

end

end SimonDCP.Probability.Lemma4StepSevenAverage
