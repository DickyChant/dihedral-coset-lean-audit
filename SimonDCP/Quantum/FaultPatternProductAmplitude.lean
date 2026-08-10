import SimonDCP.Probability.CoordinateSubcubeSupport
import SimonDCP.Quantum.FaultyBasisSample

/-!
# Product amplitudes for a fixed fault pattern

Fix a set `free` of coherent Boolean coordinates.  Every free coordinate
contributes the normalized amplitude `1 / sqrt 2` for either bit, while a
coordinate outside `free` contributes amplitude one at its prescribed bit
and zero at the other bit.  The resulting product amplitude is supported
exactly on the coordinate subcube determined by `free` and `fixed`.

This is a purely amplitude-level model.  It deliberately contains no Fourier
transform, residue conditioning, or Step-2 phase.
-/

namespace SimonDCP.Quantum.FaultPatternProductAmplitude

open QuantumAlg
open SimonDCP.Probability.CoordinateSubcubeSupport

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/--
The local selection amplitude at one coordinate.  A free coordinate accepts
both bits with amplitude `1 / sqrt 2`; a fixed coordinate accepts only its
prescribed bit, with amplitude one.
-/
def coordinateSelectionAmplitude
    (free : Finset I) (fixed selection : I → Bool) (i : I) : ℂ :=
  if i ∈ free then PureState.invSqrt2
  else if selection i = fixed i then 1 else 0

/-- The product of all local amplitudes for a Boolean selection. -/
def productSelectionAmplitude
    (free : Finset I) (fixed selection : I → Bool) : ℂ :=
  ∏ i : I, coordinateSelectionAmplitude free fixed selection i

/-- A nonzero product selection must agree with every prescribed fixed bit. -/
theorem mem_coordinateSubcube_of_productSelectionAmplitude_ne_zero
    {free : Finset I} {fixed selection : I → Bool}
    (hamplitude : productSelectionAmplitude free fixed selection ≠ 0) :
    selection ∈ coordinateSubcube free fixed := by
  classical
  apply mem_coordinateSubcube_iff.mpr
  intro i hifree
  by_contra hfixed
  apply hamplitude
  rw [productSelectionAmplitude]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [coordinateSelectionAmplitude, hifree, hfixed]

/-- Every selection in the coordinate subcube has nonzero product amplitude. -/
theorem productSelectionAmplitude_ne_zero_of_mem_coordinateSubcube
    {free : Finset I} {fixed selection : I → Bool}
    (hselection : selection ∈ coordinateSubcube free fixed) :
    productSelectionAmplitude free fixed selection ≠ 0 := by
  classical
  rw [productSelectionAmplitude]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hifree : i ∈ free
  · simp [coordinateSelectionAmplitude, hifree, PureState.invSqrt2_ne_zero]
  · have hfixed := (mem_coordinateSubcube_iff.mp hselection) i hifree
    simp [coordinateSelectionAmplitude, hifree, hfixed]

/-- The amplitude support is exactly the fault-pattern coordinate subcube. -/
theorem productSelectionAmplitude_ne_zero_iff
    (free : Finset I) (fixed selection : I → Bool) :
    productSelectionAmplitude free fixed selection ≠ 0 ↔
      selection ∈ coordinateSubcube free fixed := by
  constructor
  · exact mem_coordinateSubcube_of_productSelectionAmplitude_ne_zero
  · exact productSelectionAmplitude_ne_zero_of_mem_coordinateSubcube

/-- On its support, the product has one `1 / sqrt 2` factor per free bit. -/
theorem productSelectionAmplitude_eq_pow_of_mem_coordinateSubcube
    {free : Finset I} {fixed selection : I → Bool}
    (hselection : selection ∈ coordinateSubcube free fixed) :
    productSelectionAmplitude free fixed selection =
      PureState.invSqrt2 ^ free.card := by
  classical
  have hcoordinate : ∀ i : I,
      coordinateSelectionAmplitude free fixed selection i =
        if i ∈ free then PureState.invSqrt2 else 1 := by
    intro i
    by_cases hifree : i ∈ free
    · simp [coordinateSelectionAmplitude, hifree]
    · have hfixed := (mem_coordinateSubcube_iff.mp hselection) i hifree
      simp [coordinateSelectionAmplitude, hifree, hfixed]
  rw [productSelectionAmplitude]
  simp_rw [hcoordinate]
  simp

/-- Exact pointwise form of the product amplitude. -/
theorem productSelectionAmplitude_eq_ite
    (free : Finset I) (fixed selection : I → Bool) :
    productSelectionAmplitude free fixed selection =
      if selection ∈ coordinateSubcube free fixed then
        PureState.invSqrt2 ^ free.card
      else 0 := by
  classical
  by_cases hselection : selection ∈ coordinateSubcube free fixed
  · rw [if_pos hselection]
    exact productSelectionAmplitude_eq_pow_of_mem_coordinateSubcube hselection
  · rw [if_neg hselection]
    by_contra hamplitude
    exact hselection
      (mem_coordinateSubcube_of_productSelectionAmplitude_ne_zero hamplitude)

/-- Every supported selection has squared norm exactly `2 ^ (-|free|)`. -/
theorem normSq_productSelectionAmplitude_of_mem_coordinateSubcube
    {free : Finset I} {fixed selection : I → Bool}
    (hselection : selection ∈ coordinateSubcube free fixed) :
    ‖productSelectionAmplitude free fixed selection‖ ^ 2 =
      (1 / 2 : ℝ) ^ free.card := by
  rw [productSelectionAmplitude_eq_pow_of_mem_coordinateSubcube hselection,
    norm_pow]
  calc
    (‖PureState.invSqrt2‖ ^ free.card) ^ 2 =
        (‖PureState.invSqrt2‖ ^ 2) ^ free.card := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (1 / 2 : ℝ) ^ free.card := by
      simp [one_div]

/-- Exact pointwise squared norm, including selections outside the support. -/
theorem normSq_productSelectionAmplitude
    (free : Finset I) (fixed selection : I → Bool) :
    ‖productSelectionAmplitude free fixed selection‖ ^ 2 =
      if selection ∈ coordinateSubcube free fixed then
        (1 / 2 : ℝ) ^ free.card
      else 0 := by
  classical
  by_cases hselection : selection ∈ coordinateSubcube free fixed
  · rw [if_pos hselection]
    exact normSq_productSelectionAmplitude_of_mem_coordinateSubcube hselection
  · rw [if_neg hselection, productSelectionAmplitude_eq_ite,
      if_neg hselection, norm_zero, zero_pow]
    norm_num

/-- The squared norms of all product amplitudes sum to one. -/
theorem sum_normSq_productSelectionAmplitude
    (free : Finset I) (fixed : I → Bool) :
    ∑ selection : I → Bool,
        ‖productSelectionAmplitude free fixed selection‖ ^ 2 = 1 := by
  classical
  simp_rw [normSq_productSelectionAmplitude]
  change
    Finset.univ.sum (fun selection : I → Bool =>
        if selection ∈ coordinateSubcube free fixed then
          (1 / 2 : ℝ) ^ free.card
        else 0) = 1
  rw [← Finset.sum_filter]
  have hfilter :
      Finset.univ.filter
          (fun selection : I → Bool =>
            selection ∈ coordinateSubcube free fixed) =
        coordinateSubcube free fixed := by
    ext selection
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, card_coordinateSubcube]
  norm_num [← mul_pow]

section PureState

variable {J : Type} [Fintype J] [DecidableEq J]

/-- A finite register whose basis labels are complete Boolean selections. -/
abbrev selectionRegister (J : Type) [Fintype J] [DecidableEq J] : Register where
  Index := J → Bool
  fintype := inferInstance
  decEq := inferInstance

/-- The product amplitudes packaged as a state vector. -/
def faultPatternProductVec
    (free : Finset J) (fixed : J → Bool) :
    StateVector (selectionRegister J) :=
  WithLp.toLp 2 fun selection ↦
    productSelectionAmplitude free fixed selection

/-- The product-amplitude vector has unit norm. -/
theorem norm_faultPatternProductVec
    (free : Finset J) (fixed : J → Bool) :
    ‖faultPatternProductVec free fixed‖ = 1 := by
  rw [faultPatternProductVec, EuclideanSpace.norm_eq,
    sum_normSq_productSelectionAmplitude, Real.sqrt_one]

/-- The normalized pure state associated with a fixed fault pattern. -/
def faultPatternProductState
    (free : Finset J) (fixed : J → Bool) :
    PureState (selectionRegister J) :=
  PureState.ofVec
    (faultPatternProductVec free fixed)
    (norm_faultPatternProductVec free fixed)

@[simp]
theorem faultPatternProductState_apply
    (free : Finset J) (fixed selection : J → Bool) :
    faultPatternProductState free fixed selection =
      productSelectionAmplitude free fixed selection :=
  rfl

/-- The state's computational-basis Born distribution is uniform on the subcube. -/
@[simp]
theorem probOutcome_faultPatternProductState
    (free : Finset J) (fixed selection : J → Bool) :
    PureState.probOutcome (faultPatternProductState free fixed) selection =
      if selection ∈ coordinateSubcube free fixed then
        (1 / 2 : ℝ) ^ free.card
      else 0 := by
  change ‖productSelectionAmplitude free fixed selection‖ ^ 2 = _
  exact normSq_productSelectionAmplitude free fixed selection

end PureState

end

end SimonDCP.Quantum.FaultPatternProductAmplitude
