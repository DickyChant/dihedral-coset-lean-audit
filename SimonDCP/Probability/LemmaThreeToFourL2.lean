import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Ring
import SimonDCP.Probability.RestrictedParseval

/-!
# An L2 comparison route from Lemma 3 to Lemma 4

The pointwise bound on every implicit amplitude used in the draft is stronger
than what the final weighted comparison needs.  For finitely many labels, the
error is an inner product between the vector of count deviations and the
vector of complex coefficients.  Cauchy--Schwarz controls it using only their
two total squared energies.

This additive Cauchy bound remains valid in the presence of cancellation and
does not require a maximum bound for each coefficient.  A multiplicative
comparison still requires a noncancellation or reference-amplitude lower
bound.  An application to the paper must also prove
that its Step-5--7 coefficient `C_z` is the coefficient function below, and
must supply an upper bound for its total energy.  The existing restricted and
labelled Parseval theorems are plausible sources for such an energy identity,
but only after that semantic identification has been established.
-/

namespace SimonDCP.Probability.LemmaThreeToFourL2

open scoped BigOperators
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.RestrictedParseval

variable {Label : Type*}

/-- The squared L2 error of the label counts from a common mean. -/
def countErrorEnergy [Fintype Label]
    (count : Label -> Real) (mean : Real) : Real :=
  ∑ label, (count label - mean) ^ 2

/-- The total squared energy of a finite family of complex coefficients. -/
def coefficientEnergy [Fintype Label]
    (coefficient : Label -> Complex) : Real :=
  ∑ label, Complex.normSq (coefficient label)

/-- The actual amplitude obtained by weighting each coefficient by its count. -/
def weightedAmplitude [Fintype Label]
    (count : Label -> Real) (coefficient : Label -> Complex) : Complex :=
  ∑ label, (count label : Complex) * coefficient label

/-- The ideal amplitude obtained by replacing every count by its mean. -/
def meanAmplitude [Fintype Label]
    (mean : Real) (coefficient : Label -> Complex) : Complex :=
  (mean : Complex) * ∑ label, coefficient label

/--
Finite complex Cauchy--Schwarz with real weights, expressed using `normSq`.
This version over an arbitrary finset is the algebraic core of the repair.
-/
theorem normSq_sum_real_mul_le
    (labels : Finset Label)
    (weight : Label -> Real) (coefficient : Label -> Complex) :
    Complex.normSq
        (∑ label ∈ labels, (weight label : Complex) * coefficient label) <=
      (∑ label ∈ labels, (weight label) ^ 2) *
        ∑ label ∈ labels, Complex.normSq (coefficient label) := by
  classical
  have hRe := Finset.sum_mul_sq_le_sq_mul_sq labels weight
    (fun label => (coefficient label).re)
  have hIm := Finset.sum_mul_sq_le_sq_mul_sq labels weight
    (fun label => (coefficient label).im)
  have hRealPart :
      (∑ label ∈ labels,
          (weight label : Complex) * coefficient label).re =
        ∑ label ∈ labels, weight label * (coefficient label).re := by
    simp
  have hImaginaryPart :
      (∑ label ∈ labels,
          (weight label : Complex) * coefficient label).im =
        ∑ label ∈ labels, weight label * (coefficient label).im := by
    simp
  rw [Complex.normSq_apply, hRealPart, hImaginaryPart]
  calc
    (∑ x ∈ labels, weight x * (coefficient x).re) *
          (∑ x ∈ labels, weight x * (coefficient x).re) +
        (∑ x ∈ labels, weight x * (coefficient x).im) *
          (∑ x ∈ labels, weight x * (coefficient x).im) =
      (∑ x ∈ labels, weight x * (coefficient x).re) ^ 2 +
        (∑ x ∈ labels, weight x * (coefficient x).im) ^ 2 := by ring
    _ <=
      ((∑ x ∈ labels, weight x ^ 2) *
          ∑ x ∈ labels, (coefficient x).re ^ 2) +
        ((∑ x ∈ labels, weight x ^ 2) *
          ∑ x ∈ labels, (coefficient x).im ^ 2) :=
      add_le_add hRe hIm
    _ = (∑ x ∈ labels, weight x ^ 2) *
        ∑ x ∈ labels, Complex.normSq (coefficient x) := by
      simp_rw [Complex.normSq_apply, pow_two]
      rw [Finset.sum_add_distrib]
      rw [mul_add]

/-- The actual-minus-mean amplitude is the count-error inner product. -/
theorem weightedAmplitude_sub_meanAmplitude
    [Fintype Label]
    (count : Label -> Real) (mean : Real)
    (coefficient : Label -> Complex) :
    weightedAmplitude count coefficient - meanAmplitude mean coefficient =
      ∑ label, ((count label - mean : Real) : Complex) * coefficient label := by
  classical
  simp only [weightedAmplitude, meanAmplitude, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro label _
  push_cast
  ring

/--
Paper-facing L2 comparison.  The weighted error needs only the total count
error and total coefficient energy; no pointwise `max_z |C_z|` premise occurs.
-/
theorem weightedAmplitude_error_normSq_le
    [Fintype Label]
    (count : Label -> Real) (mean : Real)
    (coefficient : Label -> Complex) :
    Complex.normSq
        (weightedAmplitude count coefficient - meanAmplitude mean coefficient) <=
      countErrorEnergy count mean * coefficientEnergy coefficient := by
  classical
  rw [weightedAmplitude_sub_meanAmplitude]
  simpa [countErrorEnergy, coefficientEnergy] using
    normSq_sum_real_mul_le (Finset.univ : Finset Label)
      (fun label => count label - mean) coefficient

/--
A budgeted form convenient for a probabilistic or Parseval instantiation.
The nonnegativity assumptions are explicit because the supplied budgets may
be loose upper bounds rather than the actual squared energies.
-/
theorem weightedAmplitude_error_normSq_le_budget
    [Fintype Label]
    (count : Label -> Real) (mean : Real)
    (coefficient : Label -> Complex)
    (countBudget coefficientBudget : Real)
    (hCountBudget : countErrorEnergy count mean <= countBudget)
    (hCoefficientBudget : coefficientEnergy coefficient <= coefficientBudget)
    (hCountBudgetNonneg : 0 <= countBudget) :
    Complex.normSq
        (weightedAmplitude count coefficient - meanAmplitude mean coefficient) <=
      countBudget * coefficientBudget := by
  calc
    Complex.normSq
        (weightedAmplitude count coefficient - meanAmplitude mean coefficient) <=
      countErrorEnergy count mean * coefficientEnergy coefficient :=
        weightedAmplitude_error_normSq_le count mean coefficient
    _ <= countBudget * coefficientBudget := by
      exact mul_le_mul hCountBudget hCoefficientBudget
        (by exact Finset.sum_nonneg fun label _ =>
          Complex.normSq_nonneg (coefficient label))
        hCountBudgetNonneg

/--
Parseval-facing form: any exact energy identity can discharge the coefficient
budget by rewriting.  In the intended use, `hEnergyIdentity` is where a
restricted/labelled Parseval theorem and the concrete Step-5--7 bridge enter.
-/
theorem weightedAmplitude_error_normSq_le_of_energy_identity
    [Fintype Label]
    (count : Label -> Real) (mean : Real)
    (coefficient : Label -> Complex)
    (countBudget parsevalEnergy : Real)
    (hCountBudget : countErrorEnergy count mean <= countBudget)
    (hEnergyIdentity : coefficientEnergy coefficient = parsevalEnergy)
    (hCountBudgetNonneg : 0 <= countBudget) :
    Complex.normSq
        (weightedAmplitude count coefficient - meanAmplitude mean coefficient) <=
      countBudget * parsevalEnergy := by
  rw [← hEnergyIdentity]
  exact weightedAmplitude_error_normSq_le_budget count mean coefficient
    countBudget (coefficientEnergy coefficient) hCountBudget le_rfl
    hCountBudgetNonneg

/-! ## A concrete restricted-Parseval energy source -/

/-- Multiplying every coefficient by one common amplitude scales its energy
by the squared magnitude of that amplitude. -/
theorem coefficientEnergy_const_mul
    [Fintype Label]
    (scale : Complex) (coefficient : Label -> Complex) :
    coefficientEnergy (fun label => scale * coefficient label) =
      Complex.normSq scale * coefficientEnergy coefficient := by
  classical
  simp only [coefficientEnergy, Complex.normSq_mul]
  rw [Finset.mul_sum]

/-- The complex coefficient family obtained from an integer restricted Walsh
amplitude. -/
def restrictedWalshCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fixed : Finset ι) (support : Finset (Mask ι))
    (integerCoefficient : Mask ι -> Int)
    (mask : MasksVanishingOn fixed) : Complex :=
  (signedAmplitude support integerCoefficient mask : Int)

local instance l2AgreeOutsideDecidable
    {ι : Type*} [Fintype ι] [DecidableEq ι] (fixed : Finset ι) :
    DecidableRel (AgreeOutside fixed) := fun _ _ => by
  unfold AgreeOutside
  infer_instance

/--
The existing restricted Parseval theorem computes exactly the coefficient
energy needed by the L2 comparison when the paper coefficient has been
identified with a restricted Walsh amplitude.  This theorem is algebraic; it
does not assert that the Step-5--7 coefficient has this form.
-/
theorem coefficientEnergy_restrictedWalshCoefficient_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fixed : Finset ι) (support : Finset (Mask ι))
    (integerCoefficient : Mask ι -> Int) :
    coefficientEnergy
        (restrictedWalshCoefficient fixed support integerCoefficient) =
      (((Fintype.card (MasksVanishingOn fixed) : Int) *
          ∑ phi ∈ support, ∑ psi ∈ support,
            if AgreeOutside fixed phi psi then
              integerCoefficient phi * integerCoefficient psi
            else 0 : Int) : Real) := by
  classical
  have hParseval := congrArg (fun value : Int => (value : Real))
    (restricted_parseval fixed support integerCoefficient)
  simpa [coefficientEnergy, restrictedWalshCoefficient, pow_two] using
    hParseval

/--
Restricted-Parseval specialization of the paper-facing comparison.  The only
probabilistic input is an L2 count-deviation budget; the coefficient side is
the exact Walsh collision energy rather than a pointwise maximum.
-/
theorem weightedAmplitude_restrictedWalsh_error_normSq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fixed : Finset ι) (support : Finset (Mask ι))
    (integerCoefficient : Mask ι -> Int)
    (count : MasksVanishingOn fixed -> Real) (mean countBudget : Real)
    (hCountBudget : countErrorEnergy count mean <= countBudget)
    (hCountBudgetNonneg : 0 <= countBudget) :
    Complex.normSq
        (weightedAmplitude count
            (restrictedWalshCoefficient fixed support integerCoefficient) -
          meanAmplitude mean
            (restrictedWalshCoefficient fixed support integerCoefficient)) <=
      countBudget *
        (((Fintype.card (MasksVanishingOn fixed) : Int) *
          ∑ phi ∈ support, ∑ psi ∈ support,
            if AgreeOutside fixed phi psi then
              integerCoefficient phi * integerCoefficient psi
            else 0 : Int) : Real) := by
  apply weightedAmplitude_error_normSq_le_of_energy_identity
  · exact hCountBudget
  · exact coefficientEnergy_restrictedWalshCoefficient_eq
      fixed support integerCoefficient
  · exact hCountBudgetNonneg

end SimonDCP.Probability.LemmaThreeToFourL2
