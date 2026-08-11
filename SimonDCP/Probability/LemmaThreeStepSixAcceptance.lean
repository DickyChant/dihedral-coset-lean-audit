import QuantumAlg.Core.Components.Kets

/-!
# Step-6 Hadamard acceptance in Lemma 3

This file isolates the probability calculation behind the Step-6 claim that
postselecting the all-zero outcome of a Hadamard transform on a finite low
register costs the reciprocal of the register cardinality.

For a coherent input amplitude `amplitude : Low -> Complex`, the all-zero
outcome mass is

```text
(card Low)⁻¹ * normSq (sum x, amplitude x).
```

It is not, in general, `(card Low)⁻¹` times the diagonal input mass.  The
normalized two-term input `(1, -1) / sqrt 2` has diagonal mass one and
all-zero outcome mass zero.  A second finite example shows that even when an
unconditional average over a uniform environment has the expected value
`1 / 2`, conditioning on an environment-dependent retained event can reduce
the corresponding joint mass to zero.

The last theorem records the robust alternative for one qubit: retaining all
Hadamard outcomes preserves the complete diagonal mass.  It does not justify
postselecting one distinguished outcome.  It repairs acceptance accounting
only; the separate two-copy spectral audit shows that retaining the low
outcome does not by itself produce a decoding bias.
-/

namespace SimonDCP.Probability.LemmaThreeStepSixAcceptance

open scoped BigOperators

/-! ## The exact all-zero mass -/

/-- The amplitude of the all-zero output after the normalized finite
Hadamard row is applied to `amplitude`. -/
noncomputable def allZeroHadamardAmplitude
    {Low : Type*} [Fintype Low] (amplitude : Low -> Complex) : Complex :=
  (((Real.sqrt (Fintype.card Low : Real))⁻¹ : Real) : Complex) *
    ∑ low, amplitude low

/-- The Born mass of the all-zero Hadamard output. -/
noncomputable def allZeroHadamardMass
    {Low : Type*} [Fintype Low] (amplitude : Low -> Complex) : Real :=
  Complex.normSq (allZeroHadamardAmplitude amplitude)

/-- Exact finite-register formula for the all-zero Hadamard mass. -/
theorem allZeroHadamardMass_eq
    {Low : Type*} [Fintype Low] [Nonempty Low]
    (amplitude : Low -> Complex) :
    allZeroHadamardMass amplitude =
      (Fintype.card Low : Real)⁻¹ *
        Complex.normSq (∑ low, amplitude low) := by
  unfold allZeroHadamardMass allZeroHadamardAmplitude
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← mul_inv,
    Real.mul_self_sqrt]
  positivity

/-- The diagonal mass before the final Hadamard transform. -/
noncomputable def diagonalInputMass
    {Low : Type*} [Fintype Low] (amplitude : Low -> Complex) : Real :=
  ∑ low, Complex.normSq (amplitude low)

/-! ## A normalized destructive-interference counterexample -/

/-- The normalized two-term amplitude `(1, -1) / sqrt 2`. -/
noncomputable def destructiveBoolAmplitude (low : Bool) : Complex :=
  if low then -QuantumAlg.PureState.invSqrt2
  else QuantumAlg.PureState.invSqrt2

/-- Each component of the destructive example has squared magnitude `1/2`. -/
theorem normSq_destructiveBoolAmplitude (low : Bool) :
    Complex.normSq (destructiveBoolAmplitude low) = (2 : Real)⁻¹ := by
  cases low <;>
    simp [destructiveBoolAmplitude, Complex.normSq_eq_norm_sq]

/-- The destructive two-term input is normalized. -/
theorem diagonalInputMass_destructiveBoolAmplitude :
    diagonalInputMass destructiveBoolAmplitude = 1 := by
  simp [diagonalInputMass, normSq_destructiveBoolAmplitude]

/-- The two normalized terms cancel exactly in the all-zero Hadamard row. -/
theorem sum_destructiveBoolAmplitude_eq_zero :
    (∑ low : Bool, destructiveBoolAmplitude low) = 0 := by
  simp [destructiveBoolAmplitude]

/-- The all-zero output of the normalized destructive input has mass zero. -/
theorem allZeroHadamardMass_destructiveBoolAmplitude_eq_zero :
    allZeroHadamardMass destructiveBoolAmplitude = 0 := by
  rw [allZeroHadamardMass_eq, sum_destructiveBoolAmplitude_eq_zero]
  simp

/-- Hence no generic reciprocal-cardinality lower bound can follow from
normalization alone. -/
theorem allZeroHadamardMass_destructiveBoolAmplitude_lt_uniformBaseline :
    allZeroHadamardMass destructiveBoolAmplitude <
      (Fintype.card Bool : Real)⁻¹ *
        diagonalInputMass destructiveBoolAmplitude := by
  rw [allZeroHadamardMass_destructiveBoolAmplitude_eq_zero,
    diagonalInputMass_destructiveBoolAmplitude]
  norm_num

/-! ## An environment-conditioning counterexample -/

/-- In environment `false` the low register is `|+>`; in environment `true`
it is `|->`. -/
noncomputable def environmentAmplitude
    (environment low : Bool) : Complex :=
  if environment then destructiveBoolAmplitude low
  else QuantumAlg.PureState.invSqrt2

/-- Both environment-conditioned low-register inputs are normalized. -/
theorem diagonalInputMass_environmentAmplitude (environment : Bool) :
    diagonalInputMass (environmentAmplitude environment) = 1 := by
  cases environment
  · have hInvSqrt :
        Complex.normSq QuantumAlg.PureState.invSqrt2 = (2 : Real)⁻¹ := by
      simpa only [Complex.normSq_eq_norm_sq] using
        QuantumAlg.PureState.norm_sq_invSqrt2
    rw [diagonalInputMass, Fintype.sum_bool]
    change
      Complex.normSq QuantumAlg.PureState.invSqrt2 +
        Complex.normSq QuantumAlg.PureState.invSqrt2 = 1
    rw [hInvSqrt]
    norm_num
  · rw [show environmentAmplitude true = destructiveBoolAmplitude by
      funext low
      simp [environmentAmplitude]]
    exact diagonalInputMass_destructiveBoolAmplitude

/-- The constructive environment has all-zero Hadamard mass one. -/
theorem allZeroHadamardMass_environmentAmplitude_false :
    allZeroHadamardMass (environmentAmplitude false) = 1 := by
  have hAmplitude :
      environmentAmplitude false =
        fun _low => QuantumAlg.PureState.invSqrt2 := by
    funext low
    simp [environmentAmplitude]
  have hInvSqrt :
      Complex.normSq QuantumAlg.PureState.invSqrt2 = (2 : Real)⁻¹ := by
    simpa only [Complex.normSq_eq_norm_sq] using
      QuantumAlg.PureState.norm_sq_invSqrt2
  rw [hAmplitude]
  rw [allZeroHadamardMass_eq]
  rw [Fintype.sum_bool]
  rw [show
    QuantumAlg.PureState.invSqrt2 + QuantumAlg.PureState.invSqrt2 =
      (2 : Complex) * QuantumAlg.PureState.invSqrt2 by ring]
  rw [Complex.normSq_mul, hInvSqrt]
  norm_num

/-- The destructive environment has all-zero Hadamard mass zero. -/
theorem allZeroHadamardMass_environmentAmplitude_true :
    allZeroHadamardMass (environmentAmplitude true) = 0 := by
  rw [show environmentAmplitude true = destructiveBoolAmplitude by
    funext low
    simp [environmentAmplitude]]
  exact allZeroHadamardMass_destructiveBoolAmplitude_eq_zero

/-- Uniform probability weight on the two environments. -/
noncomputable def uniformBoolEnvironmentWeight (_environment : Bool) : Real :=
  (2 : Real)⁻¹

/-- Retain exactly the destructive environment. -/
def retainDestructiveEnvironment (environment : Bool) : Bool :=
  environment

/-- Before conditioning, the expected all-zero mass is the uniform baseline
`1 / 2`. -/
theorem average_allZeroHadamardMass_environmentAmplitude_eq_half :
    (∑ environment : Bool,
      uniformBoolEnvironmentWeight environment *
        allZeroHadamardMass (environmentAmplitude environment)) =
      (2 : Real)⁻¹ := by
  rw [Fintype.sum_bool]
  rw [allZeroHadamardMass_environmentAmplitude_false,
    allZeroHadamardMass_environmentAmplitude_true]
  norm_num [uniformBoolEnvironmentWeight]

/-- The retained environment itself has mass `1 / 2`. -/
theorem retainedDestructiveEnvironment_mass_eq_half :
    (∑ environment : Bool,
      if retainDestructiveEnvironment environment = true then
        uniformBoolEnvironmentWeight environment
      else 0) = (2 : Real)⁻¹ := by
  rw [Fintype.sum_bool]
  norm_num [retainDestructiveEnvironment, uniformBoolEnvironmentWeight]

/-- After retaining only the destructive environment, the joint all-zero
mass is zero. -/
theorem retainedDestructiveEnvironment_joint_allZeroMass_eq_zero :
    (∑ environment : Bool,
      if retainDestructiveEnvironment environment = true then
        uniformBoolEnvironmentWeight environment *
          allZeroHadamardMass (environmentAmplitude environment)
      else 0) = 0 := by
  rw [Fintype.sum_bool]
  simp [retainDestructiveEnvironment,
    allZeroHadamardMass_environmentAmplitude_true]

/-- The conditional counterexample violates the putative retained-mass
baseline by a strict amount. -/
theorem retained_joint_allZeroMass_lt_half_retainedMass :
    (∑ environment : Bool,
      if retainDestructiveEnvironment environment = true then
        uniformBoolEnvironmentWeight environment *
          allZeroHadamardMass (environmentAmplitude environment)
      else 0) <
      (2 : Real)⁻¹ *
        (∑ environment : Bool,
          if retainDestructiveEnvironment environment = true then
            uniformBoolEnvironmentWeight environment
          else 0) := by
  rw [retainedDestructiveEnvironment_joint_allZeroMass_eq_zero,
    retainedDestructiveEnvironment_mass_eq_half]
  norm_num

/-! ## Keeping every Walsh outcome -/

/-- The normalized one-bit Walsh/Hadamard transform. -/
noncomputable def boolHadamardAmplitude
    (amplitude : Bool -> Complex) (outcome : Bool) : Complex :=
  QuantumAlg.PureState.invSqrt2 *
    (amplitude false + if outcome then -amplitude true else amplitude true)

/-- Summing both Hadamard outcomes preserves the complete input mass.  This
is the two-point Parseval identity. -/
theorem sum_normSq_boolHadamardAmplitude
    (amplitude : Bool -> Complex) :
    (∑ outcome : Bool,
      Complex.normSq (boolHadamardAmplitude amplitude outcome)) =
      diagonalInputMass amplitude := by
  have hInvSqrt :
      Complex.normSq QuantumAlg.PureState.invSqrt2 = (2 : Real)⁻¹ := by
    simpa only [Complex.normSq_eq_norm_sq] using
      QuantumAlg.PureState.norm_sq_invSqrt2
  rw [Fintype.sum_bool]
  simp only [boolHadamardAmplitude, Bool.false_eq_true, reduceIte]
  rw [show amplitude false + -amplitude true =
    amplitude false - amplitude true by ring]
  rw [diagonalInputMass, Fintype.sum_bool]
  rw [Complex.normSq_mul, Complex.normSq_mul, hInvSqrt,
    Complex.normSq_add, Complex.normSq_sub]
  ring

end SimonDCP.Probability.LemmaThreeStepSixAcceptance
