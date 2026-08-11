import SimonDCP.Probability.LemmaThreeToFourL2

/-!
# Finite Step-7 regrouping by the low residue

This module isolates the smallest algebraic bridge needed by the L2 route
from Lemma 3 to Lemma 4.  Let `APath` be a finite set of left-side paths and
let `BPath` be a finite set of right-side paths.  Both sides carry a low
residue `z`.  The left side contributes only the number of paths in each
residue bucket, while the right side contributes the complex coefficient

```text
C_z = sum_{b in B_z} term(b).
```

The explicit double path sum is proved to be exactly `weightedAmplitude`
applied to these counts and coefficients.  A raw common path amplitude
`scale : Complex` can then be pulled outside the regrouping, and the additive
error made by replacing every left count by a common mean is controlled by
the count and coefficient L2 budgets from `LemmaThreeToFourL2`.

For the paper, `APath` is intended to retain the accepted Step-3--4 data,
`BPath` the compatible Step-5--7 continuation data, `Residue` the low value
called `z`, and `term` the signed right-side contribution to `C_z`.  The
`scale` parameter is the raw common amplitude, before outcome-dependent
postmeasurement normalization.

This file does not instantiate the actual circuit.  That application still
has to identify the concrete path types and residue maps, prove that the
circuit amplitude is the scaled double sum below, and supply the conditioned
count-error and coefficient-energy budgets (for example through a suitable
Parseval or collision calculation).
-/

namespace SimonDCP.Probability.LemmaThreeStepSevenRegrouping

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeToFourL2

variable {APath BPath Residue : Type*}

/-- The real cardinality of the left-side bucket with low residue `z`.
It is written as a sum of indicators so that finite regrouping is
definitionally transparent. -/
def aResidueCount [DecidableEq Residue]
    (aPaths : Finset APath) (aResidue : APath -> Residue)
    (z : Residue) : Real :=
  ∑ a ∈ aPaths, if aResidue a = z then 1 else 0

/-- The indicator definition of `aResidueCount` is exactly the cardinality
of the corresponding finite fibre. -/
theorem aResidueCount_eq_card [DecidableEq Residue]
    (aPaths : Finset APath) (aResidue : APath -> Residue)
    (z : Residue) :
    aResidueCount aPaths aResidue z =
      ((aPaths.filter fun a => aResidue a = z).card : Real) := by
  classical
  unfold aResidueCount
  rw [← Finset.sum_filter]
  simp

/-- The right-side coefficient `C_z`, obtained by coherently summing all
right paths in the low-residue bucket `z`. -/
def bResidueCoefficient [DecidableEq Residue]
    (bPaths : Finset BPath) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) (z : Residue) : Complex :=
  ∑ b ∈ bPaths.filter (fun b => bResidue b = z), term b

/-- The direct finite double sum before regrouping by the low residue. -/
def directDoubleSum [DecidableEq Residue]
    (aPaths : Finset APath) (bPaths : Finset BPath)
    (aResidue : APath -> Residue) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) : Complex :=
  ∑ a ∈ aPaths,
    ∑ b ∈ bPaths.filter (fun b => bResidue b = aResidue a), term b

/-- Regrouping the direct double path sum by `z` gives exactly the
count-weighted coefficient amplitude used by the L2 comparison. -/
theorem directDoubleSum_eq_weightedAmplitude
    [Fintype Residue] [DecidableEq Residue]
    (aPaths : Finset APath) (bPaths : Finset BPath)
    (aResidue : APath -> Residue) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) :
    directDoubleSum aPaths bPaths aResidue bResidue term =
      weightedAmplitude (aResidueCount aPaths aResidue)
        (bResidueCoefficient bPaths bResidue term) := by
  classical
  unfold directDoubleSum weightedAmplitude aResidueCount bResidueCoefficient
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (aResidue a)]
  · simp
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

/-- The direct amplitude after restoring one raw common path amplitude. -/
def scaledDirectAmplitude [DecidableEq Residue]
    (scale : Complex)
    (aPaths : Finset APath) (bPaths : Finset BPath)
    (aResidue : APath -> Residue) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) : Complex :=
  scale * directDoubleSum aPaths bPaths aResidue bResidue term

/-- The ideal amplitude obtained by replacing every left bucket count by the
same mean, with the raw common amplitude restored. -/
def scaledMeanAmplitude [Fintype Residue] [DecidableEq Residue]
    (scale : Complex) (mean : Real)
    (bPaths : Finset BPath) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) : Complex :=
  scale * meanAmplitude mean (bResidueCoefficient bPaths bResidue term)

/--
Budgeted Step-7 L2 bridge.  No pointwise upper bound on `C_z` is used: only
the total squared count error and total squared coefficient energy enter.
-/
theorem scaledDirect_sub_scaledMean_normSq_le_budget
    [Fintype Residue] [DecidableEq Residue]
    (scale : Complex)
    (aPaths : Finset APath) (bPaths : Finset BPath)
    (aResidue : APath -> Residue) (bResidue : BPath -> Residue)
    (term : BPath -> Complex)
    (mean countBudget coefficientBudget : Real)
    (hCountBudget :
      countErrorEnergy (aResidueCount aPaths aResidue) mean <= countBudget)
    (hCoefficientBudget :
      coefficientEnergy (bResidueCoefficient bPaths bResidue term) <=
        coefficientBudget)
    (hCountBudgetNonneg : 0 <= countBudget) :
    Complex.normSq
        (scaledDirectAmplitude scale aPaths bPaths aResidue bResidue term -
          scaledMeanAmplitude scale mean bPaths bResidue term) <=
      Complex.normSq scale * countBudget * coefficientBudget := by
  have hL2 := weightedAmplitude_error_normSq_le_budget
    (aResidueCount aPaths aResidue) mean
    (bResidueCoefficient bPaths bResidue term)
    countBudget coefficientBudget hCountBudget hCoefficientBudget
    hCountBudgetNonneg
  rw [scaledDirectAmplitude, scaledMeanAmplitude,
    directDoubleSum_eq_weightedAmplitude]
  rw [show
    scale * weightedAmplitude (aResidueCount aPaths aResidue)
          (bResidueCoefficient bPaths bResidue term) -
        scale * meanAmplitude mean
          (bResidueCoefficient bPaths bResidue term) =
      scale *
        (weightedAmplitude (aResidueCount aPaths aResidue)
            (bResidueCoefficient bPaths bResidue term) -
          meanAmplitude mean
            (bResidueCoefficient bPaths bResidue term)) by ring]
  rw [Complex.normSq_mul]
  calc
    Complex.normSq scale *
        Complex.normSq
          (weightedAmplitude (aResidueCount aPaths aResidue)
              (bResidueCoefficient bPaths bResidue term) -
            meanAmplitude mean
              (bResidueCoefficient bPaths bResidue term)) <=
        Complex.normSq scale * (countBudget * coefficientBudget) :=
      mul_le_mul_of_nonneg_left hL2 (Complex.normSq_nonneg scale)
    _ = Complex.normSq scale * countBudget * coefficientBudget := by ring

/-! ## Optional collision expansion of the coefficient energy -/

/-- Squared norm of a finite complex sum, expanded as a sum over ordered
collisions. -/
theorem normSq_finsetSum_eq_collisionSum
    (paths : Finset BPath) (term : BPath -> Complex) :
    Complex.normSq (∑ b ∈ paths, term b) =
      ∑ left ∈ paths, ∑ right ∈ paths,
        ((starRingEnd Complex) (term left) * term right).re := by
  classical
  have hComplex :
      ((Complex.normSq (∑ b ∈ paths, term b) : Real) : Complex) =
        ∑ left ∈ paths, ∑ right ∈ paths,
          (starRingEnd Complex) (term left) * term right := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
  have hReal := congrArg Complex.re hComplex
  simpa using hReal

/-- The coefficient energy is exactly the sum of all within-residue ordered
collisions of right-side path terms. -/
theorem coefficientEnergy_bResidueCoefficient_eq_collisionSum
    [Fintype Residue] [DecidableEq Residue]
    (bPaths : Finset BPath) (bResidue : BPath -> Residue)
    (term : BPath -> Complex) :
    coefficientEnergy (bResidueCoefficient bPaths bResidue term) =
      ∑ z, ∑ left ∈ bPaths.filter (fun b => bResidue b = z),
        ∑ right ∈ bPaths.filter (fun b => bResidue b = z),
          ((starRingEnd Complex) (term left) * term right).re := by
  classical
  unfold coefficientEnergy bResidueCoefficient
  apply Finset.sum_congr rfl
  intro z _
  exact normSq_finsetSum_eq_collisionSum
    (bPaths.filter fun b => bResidue b = z) term

end SimonDCP.Probability.LemmaThreeStepSevenRegrouping
