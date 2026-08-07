import SimonDCP.Basic
import Mathlib.Analysis.Fourier.ZMod

/-!
# Algebraic Fourier shifts on `ZMod`

This file isolates the finite-Fourier algebra used by an ideal dihedral-coset
sample.  Mathlib's `ZMod.dft` is the *unnormalized* transform

`dft f k = ∑ j, stdAddChar (-(j * k)) • f j`.

Consequently, translating a function by `a`, in the convention
`translate a f j = f (j - a)`, contributes the character
`stdAddChar (-(a * k))`.  The minus sign is therefore part of Mathlib's DFT
convention, rather than an additional assumption about the DCP.

These are deterministic identities of finite sums.  They do not model a
quantum measurement, its normalization, or its outcome distribution.
-/

namespace SimonDCP.Quantum.FourierShift

open Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

/-- Right translation: a point originally at `x` is moved to `x + a`. -/
def translate (a : ZMod N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  fun j ↦ f (j - a)

/--
With Mathlib's negative-exponent DFT convention, right translation by `a`
multiplies frequency `k` by `stdAddChar (-(a * k))`.
-/
theorem dft_translate (a k : ZMod N) (f : ZMod N → ℂ) :
    ZMod.dft (translate a f) k =
      ZMod.stdAddChar (-(a * k)) • ZMod.dft f k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    ∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) * translate a f j =
        ∑ j : ZMod N,
          ZMod.stdAddChar (-((j + a) * k)) * translate a f (j + a) := by
      exact (Equiv.sum_comp (Equiv.addRight a)
        (fun j : ZMod N ↦ ZMod.stdAddChar (-(j * k)) * translate a f j)).symm
    _ = ∑ j : ZMod N,
          ZMod.stdAddChar (-(a * k)) *
            (ZMod.stdAddChar (-(j * k)) * f j) := by
      apply Fintype.sum_congr
      intro j
      simp only [translate, add_sub_cancel_right, add_mul, neg_add,
        AddChar.map_add_eq_mul]
      ac_rfl
    _ = ZMod.stdAddChar (-(a * k)) *
          ∑ j : ZMod N, ZMod.stdAddChar (-(j * k)) * f j := by
      rw [mul_sum]

/-- The unit point mass at `x`. -/
def pointMass (x : ZMod N) : ZMod N → ℂ :=
  fun j ↦ if j = x then 1 else 0

/-- The unnormalized DFT of a point mass is exactly its additive character. -/
theorem dft_pointMass (x k : ZMod N) :
    ZMod.dft (pointMass x) k = ZMod.stdAddChar (-(x * k)) := by
  classical
  rw [ZMod.dft_apply]
  simp [pointMass, smul_eq_mul]

/-- Translating a point mass agrees definitionally with moving its label. -/
theorem translate_pointMass (a x : ZMod N) :
    translate a (pointMass x) = pointMass (x + a) := by
  funext j
  simp only [translate, pointMass, sub_eq_iff_eq_add]

/--
The Fourier amplitude at the translated label differs from that at `x` by
the phase `stdAddChar (-(d * k))`.
-/
theorem pointMass_relative_phase (x d k : ZMod N) :
    ZMod.dft (pointMass (x + d)) k =
      ZMod.stdAddChar (-(d * k)) * ZMod.dft (pointMass x) k := by
  rw [dft_pointMass, dft_pointMass]
  rw [add_mul, neg_add, AddChar.map_add_eq_mul]
  exact mul_comm _ _

/-- The algebraic (unnormalized) superposition supported at `x` and `x + d`. -/
def twoPoint (x d : ZMod N) : ZMod N → ℂ :=
  pointMass x + pointMass (x + d)

/--
The DFT of the two labels factors into a global phase and the relative DCP
phase.  A normalized quantum state would multiply both sides by the same
normalization scalar.
-/
theorem dft_twoPoint (x d k : ZMod N) :
    ZMod.dft (twoPoint x d) k =
      ZMod.stdAddChar (-(x * k)) *
        (1 + ZMod.stdAddChar (-(d * k))) := by
  change ZMod.dft (pointMass x + pointMass (x + d)) k = _
  rw [map_add, Pi.add_apply, dft_pointMass, dft_pointMass]
  have hphase :
      ZMod.stdAddChar (-((x + d) * k)) =
        ZMod.stdAddChar (-(x * k)) * ZMod.stdAddChar (-(d * k)) := by
    simp only [add_mul, neg_add, AddChar.map_add_eq_mul]
  rw [hphase, mul_add, mul_one]

end SimonDCP.Quantum.FourierShift
