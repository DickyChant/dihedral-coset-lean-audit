import SimonDCP.Quantum.FaultPatternFourierProduct

/-!
# Actual mixed correct/fault amplitudes after the position DFT

This file refines `FaultPatternFourierProduct`, which deliberately omits the
secret-dependent phase of a correct DCP sample.  We condition on a fixed fault
pattern:

* `free` is the set of correct samples;
* `fixed i` is the sampled branch bit at a faulty coordinate;
* `positions i` is the base position `x_i`; and
* `secret` is the common DCP shift `d`.

At a correct coordinate the pre-DFT state is

`(1 / sqrt 2) * sum_b |b, x_i + b d>`,

whereas at a faulty coordinate it is the basis state
`|fixed i, x_i>`.  Thus a correct selected branch `b` has position-DFT phase
`positionPhase (x_i + b d) y_i`, while a faulty coordinate has phase
`positionPhase x_i y_i` and no secret shift.

Mathlib's DFT uses a negative exponent, so these phases are the complex
conjugates of the positive-exponent convention displayed in the preprint.
This convention change has no effect on support or Born probabilities.

The main results show that the actual amplitude is the existing surrogate
amplitude times an explicit unit-modulus secret phase.  Consequently its
pointwise support, pointwise squared norm, and position-frequency marginal
are exactly those already proved for the coordinate-subcube model.
-/

namespace SimonDCP.Quantum.MixedFaultPatternFourierProduct

open QuantumAlg
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Quantum.FaultyBasisSample
open SimonDCP.Quantum.FaultPatternProductAmplitude
open SimonDCP.Quantum.FaultPatternFourierProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {N : ℕ} [NeZero N]

/-- The displacement `b d` selected by a Boolean branch bit. -/
def selectedSecretShift (selection : Bool) (secret : ZMod N) : ZMod N :=
  if selection = true then secret else 0

/--
The actual input position at one coordinate.  Only a correct coordinate
contains a coherent secret shift; a faulty coordinate remains at its sampled
basis position, irrespective of its fixed branch bit.
-/
def mixedInputPosition
    (free : Finset I) (positions : I → ZMod N) (secret : ZMod N)
    (selection : I → Bool) (i : I) : ZMod N :=
  if i ∈ free then
    positions i + selectedSecretShift (selection i) secret
  else
    positions i

/--
The actual local amplitude after the normalized position DFT, conditioned on
one fault pattern.  `coordinateSelectionAmplitude` supplies `1 / sqrt 2` at a
correct coordinate and the fixed-bit indicator at a faulty coordinate.
-/
def mixedCoordinatePostPositionDftAmplitude
    (free : Finset I) (fixed selection : I → Bool)
    (positions : I → ZMod N) (secret : ZMod N)
    (frequencies : I → ZMod N) (i : I) : ℂ :=
  coordinateSelectionAmplitude free fixed selection i *
    (invSqrtModulus N *
      positionPhase
        (mixedInputPosition free positions secret selection i)
        (frequencies i))

omit [Fintype I] in
/-- At a correct coordinate, both branches occur with the DCP normalization. -/
theorem mixedCoordinatePostPositionDftAmplitude_of_mem
    {free : Finset I} {fixed selection : I → Bool}
    (positions : I → ZMod N) (secret : ZMod N)
    (frequencies : I → ZMod N) {i : I} (hi : i ∈ free) :
    mixedCoordinatePostPositionDftAmplitude
        free fixed selection positions secret frequencies i =
      PureState.invSqrt2 *
        (invSqrtModulus N *
          positionPhase
            (positions i + selectedSecretShift (selection i) secret)
            (frequencies i)) := by
  simp [mixedCoordinatePostPositionDftAmplitude, mixedInputPosition,
    coordinateSelectionAmplitude, hi]

omit [Fintype I] in
/-- At a faulty coordinate, only its sampled fixed branch bit has support. -/
theorem mixedCoordinatePostPositionDftAmplitude_of_not_mem
    {free : Finset I} {fixed selection : I → Bool}
    (positions : I → ZMod N) (secret : ZMod N)
    (frequencies : I → ZMod N) {i : I} (hi : i ∉ free) :
    mixedCoordinatePostPositionDftAmplitude
        free fixed selection positions secret frequencies i =
      if selection i = fixed i then
        invSqrtModulus N * positionPhase (positions i) (frequencies i)
      else 0 := by
  simp [mixedCoordinatePostPositionDftAmplitude, mixedInputPosition,
    coordinateSelectionAmplitude, hi]

/-- The secret-dependent character contributed by one correct selected bit. -/
def mixedCoordinateSecretPhase
    (free : Finset I) (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) (i : I) : ℂ :=
  if i ∈ free then
    if selection i = true then positionPhase secret (frequencies i) else 1
  else
    1

omit [Fintype I] in
/-- Every local secret phase has unit modulus. -/
@[simp]
theorem norm_mixedCoordinateSecretPhase
    (free : Finset I) (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) (i : I) :
    ‖mixedCoordinateSecretPhase free secret selection frequencies i‖ = 1 := by
  by_cases hi : i ∈ free
  · by_cases hselection : selection i = true
    · simp [mixedCoordinateSecretPhase, hi, hselection,
        norm_positionPhase]
    · simp [mixedCoordinateSecretPhase, hi, hselection]
  · simp [mixedCoordinateSecretPhase, hi]

/-- The product secret phase attached to a complete Boolean selection. -/
def mixedProductSecretPhase
    (free : Finset I) (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) : ℂ :=
  ∏ i : I, mixedCoordinateSecretPhase free secret selection frequencies i

/-- The complete secret-dependent phase has unit modulus. -/
@[simp]
theorem norm_mixedProductSecretPhase
    (free : Finset I) (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    ‖mixedProductSecretPhase free secret selection frequencies‖ = 1 := by
  classical
  rw [mixedProductSecretPhase, norm_prod]
  simp only [norm_mixedCoordinateSecretPhase, Finset.prod_const_one]

/-- In particular, the complete secret phase never vanishes. -/
theorem mixedProductSecretPhase_ne_zero
    (free : Finset I) (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    mixedProductSecretPhase free secret selection frequencies ≠ 0 := by
  intro hzero
  have hnorm :=
    norm_mixedProductSecretPhase free secret selection frequencies
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Translation by the secret factors off its DFT character. -/
theorem positionPhase_add_selectedSecretShift
    (position secret frequency : ZMod N) (selection : Bool) :
    positionPhase (position + selectedSecretShift selection secret) frequency =
      positionPhase position frequency *
        (if selection = true then positionPhase secret frequency else 1) := by
  by_cases hselection : selection = true
  · simp only [selectedSecretShift, hselection, if_pos]
    simp only [positionPhase]
    rw [add_mul, neg_add, AddChar.map_add_eq_mul]
  · simp [selectedSecretShift, hselection]

omit [Fintype I] in
/--
The actual local amplitude is the surrogate local amplitude multiplied by
the secret character of the selected correct branch.
-/
theorem mixedCoordinatePostPositionDftAmplitude_eq_surrogate_mul_phase
    (free : Finset I) (fixed selection : I → Bool)
    (positions : I → ZMod N) (secret : ZMod N)
    (frequencies : I → ZMod N) (i : I) :
    mixedCoordinatePostPositionDftAmplitude
        free fixed selection positions secret frequencies i =
      (coordinateSelectionAmplitude free fixed selection i *
        (invSqrtModulus N *
          positionPhase (positions i) (frequencies i))) *
        mixedCoordinateSecretPhase free secret selection frequencies i := by
  classical
  by_cases hi : i ∈ free
  · rw [mixedCoordinatePostPositionDftAmplitude_of_mem
      positions secret frequencies hi]
    rw [positionPhase_add_selectedSecretShift]
    simp [coordinateSelectionAmplitude, mixedCoordinateSecretPhase, hi,
      mul_assoc]
  · rw [mixedCoordinatePostPositionDftAmplitude_of_not_mem
      positions secret frequencies hi]
    by_cases hselection : selection i = fixed i
    · simp [coordinateSelectionAmplitude, mixedCoordinateSecretPhase,
        hi, hselection]
    · simp [coordinateSelectionAmplitude, mixedCoordinateSecretPhase,
        hi, hselection]

/-- The product of the actual local amplitudes at every sample coordinate. -/
def mixedPostPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (label : FourierProductLabel I N) : ℂ :=
  ∏ i : I,
    mixedCoordinatePostPositionDftAmplitude
      free fixed label.1 positions secret label.2 i

/--
Exact comparison with the surrogate amplitude: the missing factor is an
explicit unit-modulus secret character.
-/
theorem mixedPostPositionDftProductAmplitude_eq_surrogate_mul_phase
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies) =
      postPositionDftProductAmplitude
          free fixed positions (selection, frequencies) *
        mixedProductSecretPhase free secret selection frequencies := by
  classical
  rw [mixedPostPositionDftProductAmplitude]
  simp_rw [mixedCoordinatePostPositionDftAmplitude_eq_surrogate_mul_phase]
  rw [Finset.prod_mul_distrib]
  rw [postPositionDftProductAmplitude, productSelectionAmplitude,
    productPositionDftAmplitude, mixedProductSecretPhase]
  congr 1
  rw [Finset.prod_mul_distrib]

/-- The actual mixed amplitude and the surrogate have the same norm. -/
theorem norm_mixedPostPositionDftProductAmplitude_eq_surrogate
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    ‖mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies)‖ =
      ‖postPositionDftProductAmplitude
        free fixed positions (selection, frequencies)‖ := by
  rw [mixedPostPositionDftProductAmplitude_eq_surrogate_mul_phase,
    norm_mul, norm_mixedProductSecretPhase, mul_one]

/-- Its Boolean support is exactly the coordinate subcube of the fault pattern. -/
theorem mixedPostPositionDftProductAmplitude_ne_zero_iff
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies) ≠ 0 ↔
      selection ∈ coordinateSubcube free fixed := by
  rw [mixedPostPositionDftProductAmplitude_eq_surrogate_mul_phase,
    mul_ne_zero_iff]
  constructor
  · rintro ⟨hsurrogate, _⟩
    exact (postPositionDftProductAmplitude_ne_zero_iff
      free fixed positions selection frequencies).mp hsurrogate
  · intro hselection
    exact ⟨
      (postPositionDftProductAmplitude_ne_zero_iff
        free fixed positions selection frequencies).mpr hselection,
      mixedProductSecretPhase_ne_zero
        free secret selection frequencies⟩

/-- Pointwise squared norm agrees exactly with the surrogate amplitude. -/
theorem normSq_mixedPostPositionDftProductAmplitude_eq_surrogate
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    ‖mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies)‖ ^ 2 =
      ‖postPositionDftProductAmplitude
        free fixed positions (selection, frequencies)‖ ^ 2 := by
  rw [norm_mixedPostPositionDftProductAmplitude_eq_surrogate]

/-- Exact pointwise Born mass, including labels outside the support. -/
theorem normSq_mixedPostPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (selection : I → Bool)
    (frequencies : I → ZMod N) :
    ‖mixedPostPositionDftProductAmplitude
        free fixed positions secret (selection, frequencies)‖ ^ 2 =
      if selection ∈ coordinateSubcube free fixed then
        (1 / 2 : ℝ) ^ free.card *
          ((N : ℝ)⁻¹) ^ Fintype.card I
      else 0 := by
  rw [normSq_mixedPostPositionDftProductAmplitude_eq_surrogate,
    normSq_postPositionDftProductAmplitude]

/--
After summing out the Boolean selection, the actual and surrogate
position-frequency marginals agree pointwise.
-/
theorem sum_selection_normSq_mixedPostPositionDftProductAmplitude_eq_surrogate
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (frequencies : I → ZMod N) :
    ∑ selection : I → Bool,
        ‖mixedPostPositionDftProductAmplitude
          free fixed positions secret (selection, frequencies)‖ ^ 2 =
      ∑ selection : I → Bool,
        ‖postPositionDftProductAmplitude
          free fixed positions (selection, frequencies)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro selection _
  exact normSq_mixedPostPositionDftProductAmplitude_eq_surrogate
    free fixed positions secret selection frequencies

/-- The common position-frequency marginal is uniform and secret-independent. -/
theorem sum_selection_normSq_mixedPostPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (secret : ZMod N) (frequencies : I → ZMod N) :
    ∑ selection : I → Bool,
        ‖mixedPostPositionDftProductAmplitude
          free fixed positions secret (selection, frequencies)‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ Fintype.card I := by
  rw [sum_selection_normSq_mixedPostPositionDftProductAmplitude_eq_surrogate,
    sum_selection_normSq_postPositionDftProductAmplitude]

end

end SimonDCP.Quantum.MixedFaultPatternFourierProduct
