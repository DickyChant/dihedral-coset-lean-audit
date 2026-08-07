import QuantumAlg.Core.Components.Kets
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-!
# Ideal dihedral coset samples

This file gives the exact, noise-free input state assumed by the dihedral
coset problem.  The computational basis keeps the branch bit as part of its
label, so `(false, x)` and `(true, x + d)` are distinct even when `d = 0`.

The construction is register-polymorphic in the positive cyclic modulus.  It
does not model an oracle or an intermediate measurement: it only specifies the
normalized pure state delivered by an ideal coset-state sampler and proves its
computational-basis Born probabilities.
-/

namespace SimonDCP.Quantum.IdealCosetSample

open QuantumAlg

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A dihedral basis label consists of a branch bit and a cyclic coordinate. -/
abbrev Label (N : ℕ) := Bool × ZMod N

/-- The finite register whose computational basis is `Bool × ZMod N`. -/
abbrev dihedralRegister (N : ℕ) [NeZero N] : Register where
  Index := Label N
  fintype := inferInstance
  decEq := inferInstance

/-- The branch-zero basis label of an ideal coset state. -/
def leftLabel (x : ZMod N) : Label N := (false, x)

/-- The branch-one basis label translated by the hidden shift. -/
def rightLabel (x d : ZMod N) : Label N := (true, x + d)

/-- The two labelled support points are distinct independently of the shift. -/
theorem leftLabel_ne_rightLabel (x d : ZMod N) :
    leftLabel x ≠ rightLabel x d := by
  intro h
  have hbit : false = true := congrArg Prod.fst h
  simp at hbit

/-- The raw ideal coset vector
`(|false, x⟩ + |true, x + d⟩) / √2`. -/
def idealCosetVec (x d : ZMod N) : StateVector (dihedralRegister N) :=
  PureState.invSqrt2 •
    ((PureState.ket (R := dihedralRegister N) (leftLabel x) :
        StateVector (dihedralRegister N)) +
      (PureState.ket (R := dihedralRegister N) (rightLabel x d) :
        StateVector (dihedralRegister N)))

/-- Pointwise amplitudes of the ideal coset vector. -/
@[simp]
theorem idealCosetVec_apply (x d : ZMod N) (z : Label N) :
    idealCosetVec x d z =
      if z = leftLabel x then PureState.invSqrt2
      else if z = rightLabel x d then PureState.invSqrt2
      else 0 := by
  simp only [idealCosetVec, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
    PureState.ket_apply]
  by_cases hleft : z = leftLabel x
  · have hright : z ≠ rightLabel x d := by
      intro hz
      exact leftLabel_ne_rightLabel x d (hleft.symm.trans hz)
    simp only [if_pos hleft, if_neg hright, add_zero, mul_one]
  · by_cases hright : z = rightLabel x d
    · simp only [if_neg hleft, if_pos hright, zero_add, mul_one]
    · simp only [if_neg hleft, if_neg hright, add_zero, mul_zero]

/-- Distinct computational-basis kets in the two branches are orthogonal. -/
private theorem inner_left_right_eq_zero (x d : ZMod N) :
    inner ℂ
        (PureState.ket (R := dihedralRegister N) (leftLabel x) :
          StateVector (dihedralRegister N))
        (PureState.ket (R := dihedralRegister N) (rightLabel x d) :
          StateVector (dihedralRegister N)) = 0 := by
  change inner ℂ
      (EuclideanSpace.single (leftLabel x) (1 : ℂ))
      (EuclideanSpace.single (rightLabel x d) (1 : ℂ)) = 0
  rw [EuclideanSpace.inner_single_left]
  simp [leftLabel_ne_rightLabel]

/-- The unscaled sum of the two labelled basis kets has norm `√2`. -/
private theorem norm_basisPair (x d : ZMod N) :
    ‖(PureState.ket (R := dihedralRegister N) (leftLabel x) :
        StateVector (dihedralRegister N)) +
        (PureState.ket (R := dihedralRegister N) (rightLabel x d) :
          StateVector (dihedralRegister N))‖ =
      Real.sqrt 2 := by
  let u : StateVector (dihedralRegister N) :=
    PureState.ket (R := dihedralRegister N) (leftLabel x)
  let v : StateVector (dihedralRegister N) :=
    PureState.ket (R := dihedralRegister N) (rightLabel x d)
  have hu : ‖u‖ = 1 := by
    simpa [u] using PureState.norm_ket (R := dihedralRegister N) (leftLabel x)
  have hv : ‖v‖ = 1 := by
    simpa [v] using PureState.norm_ket (R := dihedralRegister N) (rightLabel x d)
  have huv : inner ℂ u v = 0 := by
    simpa [u, v] using inner_left_right_eq_zero x d
  have hnormSq : ‖u + v‖ * ‖u + v‖ = 2 := by
    calc
      ‖u + v‖ * ‖u + v‖ = ‖u‖ * ‖u‖ + ‖v‖ * ‖v‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v huv
      _ = 2 := by rw [hu, hv]; norm_num
  have hsqrtSq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hnormNonneg : 0 ≤ ‖u + v‖ := norm_nonneg _
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  change ‖u + v‖ = Real.sqrt 2
  nlinarith

/-- The raw ideal coset vector has unit norm. -/
theorem norm_idealCosetVec (x d : ZMod N) : ‖idealCosetVec x d‖ = 1 := by
  rw [idealCosetVec, norm_smul, PureState.norm_invSqrt2, norm_basisPair,
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

/-- An ideal dihedral coset sample as a normalized pure state. -/
def idealCosetState (x d : ZMod N) : PureState (dihedralRegister N) :=
  PureState.ofVec (idealCosetVec x d) (norm_idealCosetVec x d)

/-- Pointwise amplitudes of the normalized ideal coset state. -/
@[simp]
theorem idealCosetState_apply (x d : ZMod N) (z : Label N) :
    idealCosetState x d z =
      if z = leftLabel x then PureState.invSqrt2
      else if z = rightLabel x d then PureState.invSqrt2
      else 0 := by
  change idealCosetVec x d z = _
  exact idealCosetVec_apply x d z

/-- The amplitude support consists exactly of the two labelled coset points. -/
theorem idealCosetState_ne_zero_iff (x d : ZMod N) (z : Label N) :
    idealCosetState x d z ≠ 0 ↔
      z = leftLabel x ∨ z = rightLabel x d := by
  rw [idealCosetState_apply]
  by_cases hleft : z = leftLabel x
  · simp [hleft, PureState.invSqrt2_ne_zero]
  · by_cases hright : z = rightLabel x d
    · simp [hleft, hright, PureState.invSqrt2_ne_zero]
    · simp [hleft, hright]

/-- Exact computational-basis Born distribution of an ideal coset sample. -/
@[simp]
theorem probOutcome_idealCosetState (x d : ZMod N) (z : Label N) :
    PureState.probOutcome (idealCosetState x d) z =
      if z = leftLabel x then (1 / 2 : ℝ)
      else if z = rightLabel x d then (1 / 2 : ℝ)
      else 0 := by
  change ‖idealCosetState x d z‖ ^ 2 = _
  rw [idealCosetState_apply]
  by_cases hleft : z = leftLabel x
  · simp [hleft, PureState.norm_sq_invSqrt2]
  · by_cases hright : z = rightLabel x d
    · simp [hleft, hright, PureState.norm_sq_invSqrt2]
    · simp [hleft, hright]

/-- The branch-zero label is observed with probability one half. -/
theorem probOutcome_leftLabel (x d : ZMod N) :
    PureState.probOutcome (idealCosetState x d) (leftLabel x) = (1 / 2 : ℝ) := by
  simp [leftLabel_ne_rightLabel]

/-- The translated branch-one label is observed with probability one half. -/
theorem probOutcome_rightLabel (x d : ZMod N) :
    PureState.probOutcome (idealCosetState x d) (rightLabel x d) = (1 / 2 : ℝ) := by
  simp [leftLabel_ne_rightLabel]

/-- Every other computational-basis label has probability zero. -/
theorem probOutcome_eq_zero_of_ne
    (x d : ZMod N) (z : Label N)
    (hleft : z ≠ leftLabel x) (hright : z ≠ rightLabel x d) :
    PureState.probOutcome (idealCosetState x d) z = 0 := by
  simp [hleft, hright]

end

end SimonDCP.Quantum.IdealCosetSample
