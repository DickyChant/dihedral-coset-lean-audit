import SimonDCP.Quantum.FaultPatternProductAmplitude

/-!
# Position-DFT product amplitudes for a fixed fault pattern

This file extends the explicit selection-amplitude model for a fixed fault
pattern by adjoining the normalized position-DFT amplitude at every
coordinate.  It is intentionally an amplitude-level model rather than a
gate-level circuit construction.

The Boolean selection support remains exactly the coordinate subcube fixed by
the fault pattern.  Every supported joint label has squared norm
`2 ^ (-|free|) * N ^ (-|I|)`.  Consequently, summing out the Boolean
selection leaves the uniform distribution on all position-frequency labels,
independently of the free set, the fixed bits, and the input positions.
-/

namespace SimonDCP.Quantum.FaultPatternFourierProduct

open QuantumAlg
open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Quantum.FaultyBasisSample
open SimonDCP.Quantum.FaultPatternProductAmplitude

noncomputable section

variable {I : Type*} [Fintype I]
variable {N : ℕ} [NeZero N]

/-- A joint output label consists of a Boolean selection and one frequency
label in `ZMod N` at every coordinate. -/
abbrev FourierProductLabel (I : Type*) (N : ℕ) :=
  (I → Bool) × (I → ZMod N)

/-- The product of the normalized position-DFT amplitudes at all coordinates. -/
def productPositionDftAmplitude
    (positions frequencies : I → ZMod N) : ℂ :=
  ∏ i : I,
    invSqrtModulus N * positionPhase (positions i) (frequencies i)

/-- The position-DFT product factor is nonzero at every frequency label. -/
theorem productPositionDftAmplitude_ne_zero
    (positions frequencies : I → ZMod N) :
    productPositionDftAmplitude positions frequencies ≠ 0 := by
  classical
  rw [productPositionDftAmplitude]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply mul_ne_zero
  · rw [invSqrtModulus]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))))
  · intro hzero
    have hnorm := norm_positionPhase (positions i) (frequencies i)
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm

/-- Every position-frequency label has squared norm `N ^ (-|I|)`. -/
theorem normSq_productPositionDftAmplitude
    (positions frequencies : I → ZMod N) :
    ‖productPositionDftAmplitude positions frequencies‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ Fintype.card I := by
  classical
  rw [productPositionDftAmplitude, norm_prod]
  simp_rw [norm_mul, norm_positionPhase, mul_one]
  rw [Finset.prod_const, Finset.card_univ]
  calc
    (‖invSqrtModulus N‖ ^ Fintype.card I) ^ 2 =
        (‖invSqrtModulus N‖ ^ 2) ^ Fintype.card I := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ((N : ℝ)⁻¹) ^ Fintype.card I := by
      rw [norm_sq_invSqrtModulus]

variable [DecidableEq I]

/-- The explicit post-position-DFT amplitude for a fixed fault pattern. -/
def postPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (label : FourierProductLabel I N) : ℂ :=
  productSelectionAmplitude free fixed label.1 *
    productPositionDftAmplitude positions label.2

/-- For every frequency label, the Boolean support is exactly the coordinate
subcube determined by `free` and `fixed`. -/
theorem postPositionDftProductAmplitude_ne_zero_iff
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (selection : I → Bool) (frequencies : I → ZMod N) :
    postPositionDftProductAmplitude free fixed positions
        (selection, frequencies) ≠ 0 ↔
      selection ∈ coordinateSubcube free fixed := by
  rw [postPositionDftProductAmplitude, mul_ne_zero_iff]
  constructor
  · rintro ⟨hselection, _⟩
    exact
      (productSelectionAmplitude_ne_zero_iff free fixed selection).mp hselection
  · intro hselection
    exact ⟨
      (productSelectionAmplitude_ne_zero_iff free fixed selection).mpr hselection,
      productPositionDftAmplitude_ne_zero positions frequencies⟩

/-- Every supported joint label has the expected product Born mass. -/
theorem normSq_postPositionDftProductAmplitude_of_mem
    {free : Finset I} {fixed selection : I → Bool}
    (positions frequencies : I → ZMod N)
    (hselection : selection ∈ coordinateSubcube free fixed) :
    ‖postPositionDftProductAmplitude free fixed positions
        (selection, frequencies)‖ ^ 2 =
      (1 / 2 : ℝ) ^ free.card *
        ((N : ℝ)⁻¹) ^ Fintype.card I := by
  rw [postPositionDftProductAmplitude, norm_mul, mul_pow,
    normSq_productSelectionAmplitude_of_mem_coordinateSubcube hselection,
    normSq_productPositionDftAmplitude]

/-- Exact pointwise Born mass, including selections outside the support. -/
theorem normSq_postPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N)
    (selection : I → Bool) (frequencies : I → ZMod N) :
    ‖postPositionDftProductAmplitude free fixed positions
        (selection, frequencies)‖ ^ 2 =
      if selection ∈ coordinateSubcube free fixed then
        (1 / 2 : ℝ) ^ free.card *
          ((N : ℝ)⁻¹) ^ Fintype.card I
      else 0 := by
  rw [postPositionDftProductAmplitude, norm_mul, mul_pow,
    normSq_productSelectionAmplitude,
    normSq_productPositionDftAmplitude]
  split <;> simp_all

/-- Summing out the Boolean selection gives the uniform mass at every
position-frequency label. -/
theorem sum_selection_normSq_postPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions frequencies : I → ZMod N) :
    ∑ selection : I → Bool,
        ‖postPositionDftProductAmplitude free fixed positions
          (selection, frequencies)‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ Fintype.card I := by
  simp_rw [postPositionDftProductAmplitude, norm_mul, mul_pow]
  rw [← Finset.sum_mul, sum_normSq_productSelectionAmplitude,
    one_mul, normSq_productPositionDftAmplitude]

/-- The complete joint product amplitude has total Born mass one. -/
theorem sum_normSq_postPositionDftProductAmplitude
    (free : Finset I) (fixed : I → Bool) (positions : I → ZMod N) :
    ∑ label : FourierProductLabel I N,
        ‖postPositionDftProductAmplitude free fixed positions label‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [sum_selection_normSq_postPositionDftProductAmplitude]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Nat.cast_pow]
  rw [← mul_pow]
  simp [NeZero.ne N]

end

end SimonDCP.Quantum.FaultPatternFourierProduct
