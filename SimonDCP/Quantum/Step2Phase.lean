import SimonDCP.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Complex.Basic

/-!
# Phase extraction in Step 2

This file isolates the sound algebraic part of Step 2 in Simon's preprint.
Let the modulus be `N = 2 ^ n`, and let `omega` be a complex number whose
`N / 2`-th power is `-1`.  Writing an `n`-bit value as

`z = zLow + h * 2 ^ (n - 1)`

separates its phase into a low-part phase and a sign.  The sign depends on
`d` only through `d % 2`, its last bit.

The root identity is an explicit hypothesis.  Thus none of the results below
assumes, without proof, that an arbitrary complex number is a primitive root
of unity.  The main factorization is proved for a natural-number coefficient
`h`; a Boolean specialization records that the coefficient is a bit in the
algorithm.
-/

namespace SimonDCP.Quantum.Step2Phase

/-- The last (least significant) bit of a natural number, encoded as `0` or `1`. -/
def lastBit (d : ℕ) : ℕ :=
  d % 2

/-- The value returned by `lastBit` is always either zero or one. -/
theorem lastBit_eq_zero_or_one (d : ℕ) :
    lastBit d = 0 ∨ lastBit d = 1 := by
  simpa [lastBit] using Nat.mod_two_eq_zero_or_one d

/-- Powers of `-1` depend only on the last bit of their exponent. -/
theorem negOnePow_eq_lastBit (d : ℕ) :
    (-1 : ℂ) ^ d = (-1 : ℂ) ^ lastBit d := by
  simpa [lastBit] using (neg_one_pow_eq_pow_mod_two (R := ℂ) d)

/--
If an exponent is multiplied by `h`, its sign still depends on `d` only
through the last bit of `d`.
-/
theorem negOnePow_mul_eq_lastBit (h d : ℕ) :
    (-1 : ℂ) ^ (h * d) = (-1 : ℂ) ^ (h * lastBit d) := by
  calc
    (-1 : ℂ) ^ (h * d) = ((-1 : ℂ) ^ d) ^ h :=
      pow_mul' (-1 : ℂ) h d
    _ = ((-1 : ℂ) ^ lastBit d) ^ h := by
      rw [negOnePow_eq_lastBit]
    _ = (-1 : ℂ) ^ (lastBit d * h) :=
      (pow_mul (-1 : ℂ) (lastBit d) h).symm
    _ = (-1 : ℂ) ^ (h * lastBit d) :=
      congrArg (fun exponent : ℕ ↦ (-1 : ℂ) ^ exponent)
        (Nat.mul_comm (lastBit d) h)

/--
The phase contributed by a multiple of the high-bit place is a sign.

The positive-width hypothesis makes the intended `n`-bit interpretation
explicit.  Algebraically, the stated root identity is the only property of
`omega` used by the proof.
-/
theorem highPart_phase
    {n : ℕ} (_hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (h d : ℕ) :
    omega ^ ((h * 2 ^ (n - 1)) * d) = (-1 : ℂ) ^ (h * d) := by
  calc
    omega ^ ((h * 2 ^ (n - 1)) * d) =
        omega ^ (2 ^ (n - 1) * (h * d)) :=
      congrArg (fun exponent : ℕ ↦ omega ^ exponent) (by ac_rfl)
    _ = (omega ^ (2 ^ (n - 1))) ^ (h * d) := by
      rw [pow_mul]
    _ = (-1 : ℂ) ^ (h * d) := by
      rw [root]

/--
Factoring the Step 2 phase after the split
`z = zLow + h * 2 ^ (n - 1)`.
-/
theorem phase_factor
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (zLow h d : ℕ) :
    omega ^ ((zLow + h * 2 ^ (n - 1)) * d) =
      omega ^ (zLow * d) * (-1 : ℂ) ^ (h * d) := by
  calc
    omega ^ ((zLow + h * 2 ^ (n - 1)) * d) =
        omega ^ (zLow * d) * omega ^ ((h * 2 ^ (n - 1)) * d) := by
      rw [Nat.add_mul, pow_add]
    _ = omega ^ (zLow * d) * (-1 : ℂ) ^ (h * d) :=
      congrArg (fun phase : ℂ ↦ omega ^ (zLow * d) * phase)
        (highPart_phase hn omega root h d)

/-- The Step 2 factorization with the sign reduced to the last bit of `d`. -/
theorem phase_factor_lastBit
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (zLow h d : ℕ) :
    omega ^ ((zLow + h * 2 ^ (n - 1)) * d) =
      omega ^ (zLow * d) * (-1 : ℂ) ^ (h * lastBit d) := by
  calc
    omega ^ ((zLow + h * 2 ^ (n - 1)) * d) =
        omega ^ (zLow * d) * (-1 : ℂ) ^ (h * d) :=
      phase_factor hn omega root zLow h d
    _ = omega ^ (zLow * d) * (-1 : ℂ) ^ (h * lastBit d) := by
      rw [negOnePow_mul_eq_lastBit]

/--
The same result for a named value `z`, given an explicit high-bit split.
-/
theorem phase_factor_of_split
    {n z zLow h d : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (hz : z = zLow + h * 2 ^ (n - 1)) :
    omega ^ (z * d) =
      omega ^ (zLow * d) * (-1 : ℂ) ^ (h * lastBit d) := by
  subst z
  exact phase_factor_lastBit hn omega root zLow h d

/--
Boolean specialization of the Step 2 phase formula.  Here `h.toNat` is
definitionally either zero or one, so it genuinely represents one high bit.
-/
theorem phase_factor_bit
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (zLow d : ℕ) (h : Bool) :
    omega ^ ((zLow + h.toNat * 2 ^ (n - 1)) * d) =
      omega ^ (zLow * d) * (-1 : ℂ) ^ (h.toNat * lastBit d) :=
  phase_factor_lastBit hn omega root zLow h.toNat d

/-- With high bit zero, only the low-part phase remains. -/
theorem phase_factor_bit_false
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (zLow d : ℕ) :
    omega ^ ((zLow + false.toNat * 2 ^ (n - 1)) * d) =
      omega ^ (zLow * d) := by
  simpa using phase_factor_bit hn omega root zLow d false

/-- With high bit one, the relative sign is exactly the last bit of `d`. -/
theorem phase_factor_bit_true
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (zLow d : ℕ) :
    omega ^ ((zLow + 2 ^ (n - 1)) * d) =
      omega ^ (zLow * d) * (-1 : ℂ) ^ lastBit d := by
  simpa using phase_factor_bit hn omega root zLow d true

/-- The relative high-bit phase, stated independently of the low part. -/
theorem relativeHighBitPhase
    {n : ℕ} (_hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    (d : ℕ) :
    omega ^ (2 ^ (n - 1) * d) = (-1 : ℂ) ^ lastBit d := by
  calc
    omega ^ (2 ^ (n - 1) * d) = (omega ^ (2 ^ (n - 1))) ^ d := by
      rw [pow_mul]
    _ = (-1 : ℂ) ^ d := by
      rw [root]
    _ = (-1 : ℂ) ^ lastBit d := negOnePow_eq_lastBit d

/-- An even secret exponent gives relative high-bit phase `1`. -/
theorem relativeHighBitPhase_of_lastBit_zero
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    {d : ℕ} (hd : lastBit d = 0) :
    omega ^ (2 ^ (n - 1) * d) = 1 := by
  rw [relativeHighBitPhase hn omega root d, hd, pow_zero]

/-- An odd secret exponent gives relative high-bit phase `-1`. -/
theorem relativeHighBitPhase_of_lastBit_one
    {n : ℕ} (hn : 0 < n) (omega : ℂ)
    (root : omega ^ (2 ^ (n - 1)) = (-1 : ℂ))
    {d : ℕ} (hd : lastBit d = 1) :
    omega ^ (2 ^ (n - 1) * d) = -1 := by
  rw [relativeHighBitPhase hn omega root d, hd, pow_one]

end SimonDCP.Quantum.Step2Phase
