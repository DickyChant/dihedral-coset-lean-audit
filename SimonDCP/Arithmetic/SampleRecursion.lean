import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Arithmetic for the recursive reduction of dihedral-coset samples

The preprint says that, after recovering the least significant bit of the
hidden shift, one can "erase" that bit from every sample and recurse.  It
does not specify the reversible quantum operation or prove that the faulty
sample distribution is preserved.  This file therefore formalizes only the
arithmetic kernel of that sentence.

For an integer `x`, subtracting `x % 2` leaves an even integer, and division
by two recovers `x / 2`.  Applying this observation to both branches of

`|0, x> + |1, x + secret>`

shows that subtracting the known low bit from the second branch, removing
the common low bit of `x`, and dividing by two leaves a sample whose shift
is `secret / 2`.  The last part of the file gives the same calculation for
finite dot products and modular congruences.
-/

namespace SimonDCP.Arithmetic.SampleRecursion

open scoped BigOperators

/-- The canonical low bit of an integer, represented by `0` or `1`. -/
def lowBit (x : ℤ) : ℤ :=
  x % 2

/-- The integer obtained after deleting the canonical low bit. -/
def removeLowBit (x : ℤ) : ℤ :=
  x - lowBit x

/-- The integer represented by the remaining bits. -/
def reducedAfterLowBit (x : ℤ) : ℤ :=
  x / 2

/-- Euclidean division by two decomposes an integer into its low bit and tail. -/
theorem lowBit_add_two_mul_reduced (x : ℤ) :
    lowBit x + 2 * reducedAfterLowBit x = x := by
  exact Int.emod_add_mul_ediv x 2

/-- Removing the low bit produces exactly twice the reduced integer. -/
theorem removeLowBit_eq_two_mul_reduced (x : ℤ) :
    removeLowBit x = 2 * reducedAfterLowBit x := by
  calc
    removeLowBit x = x - lowBit x := rfl
    _ = (lowBit x + 2 * reducedAfterLowBit x) - lowBit x := by
      rw [lowBit_add_two_mul_reduced]
    _ = 2 * reducedAfterLowBit x := by ring

/-- In particular, the result of removing the low bit is even. -/
theorem two_dvd_removeLowBit (x : ℤ) :
    2 ∣ removeLowBit x := by
  rw [removeLowBit_eq_two_mul_reduced]
  exact ⟨reducedAfterLowBit x, rfl⟩

/-- Division by two after low-bit removal gives the reduced integer. -/
theorem removeLowBit_ediv_two (x : ℤ) :
    removeLowBit x / 2 = reducedAfterLowBit x := by
  rw [removeLowBit_eq_two_mul_reduced]
  exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)

/-- An explicitly supplied correct low bit can be used in place of `x % 2`. -/
theorem sub_knownLowBit_eq_two_mul_reduced {x bit : ℤ}
    (hbit : lowBit x = bit) :
    x - bit = 2 * reducedAfterLowBit x := by
  rw [← hbit]
  exact removeLowBit_eq_two_mul_reduced x

/-- Subtracting a correct, explicitly supplied low bit leaves an even value. -/
theorem two_dvd_sub_knownLowBit {x bit : ℤ} (hbit : lowBit x = bit) :
    2 ∣ x - bit := by
  rw [sub_knownLowBit_eq_two_mul_reduced hbit]
  exact ⟨reducedAfterLowBit x, rfl⟩

/-- Division by two is exact after subtracting a correct known low bit. -/
theorem sub_knownLowBit_ediv_two {x bit : ℤ} (hbit : lowBit x = bit) :
    (x - bit) / 2 = reducedAfterLowBit x := by
  rw [sub_knownLowBit_eq_two_mul_reduced hbit]
  exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)

/-- Interpret the branch qubit as the integer zero or one. -/
def branchValue : Bool → ℤ
  | false => 0
  | true => 1

/-- An integer lift of one DCP branch, before reduction modulo the group order. -/
def samplePosition (base secret : ℤ) (branch : Bool) : ℤ :=
  base + branchValue branch * secret

/-- Remove the known low-bit contribution of the hidden shift. -/
def correctedPosition (base secret knownBit : ℤ) (branch : Bool) : ℤ :=
  samplePosition base secret branch - branchValue branch * knownBit

/-- Remove the common base low bit and divide the corrected position by two. -/
def reducedSamplePosition (base secret knownBit : ℤ) (branch : Bool) : ℤ :=
  (correctedPosition base secret knownBit branch - lowBit base) / 2

/--
After correction, the numerator in either branch is twice the corresponding
position of the reduced DCP sample.
-/
theorem correctedPosition_sub_lowBit_eq_two_mul
    {base secret knownBit : ℤ} (branch : Bool)
    (hbit : lowBit secret = knownBit) :
    correctedPosition base secret knownBit branch - lowBit base =
      2 * (reducedAfterLowBit base +
        branchValue branch * reducedAfterLowBit secret) := by
  calc
    correctedPosition base secret knownBit branch - lowBit base =
        (base - lowBit base) + branchValue branch * (secret - knownBit) := by
      simp only [correctedPosition, samplePosition]
      ring
    _ = (base - lowBit base) +
        branchValue branch * (secret - lowBit secret) := by
      rw [hbit]
    _ = 2 * reducedAfterLowBit base +
        branchValue branch * (2 * reducedAfterLowBit secret) := by
      change removeLowBit base + branchValue branch * removeLowBit secret = _
      rw [removeLowBit_eq_two_mul_reduced, removeLowBit_eq_two_mul_reduced]
    _ = 2 * (reducedAfterLowBit base +
        branchValue branch * reducedAfterLowBit secret) := by ring

/-- The quantity divided by two in `reducedSamplePosition` is always even. -/
theorem two_dvd_correctedPosition_sub_lowBit
    {base secret knownBit : ℤ} (branch : Bool)
    (hbit : lowBit secret = knownBit) :
    2 ∣ correctedPosition base secret knownBit branch - lowBit base := by
  rw [correctedPosition_sub_lowBit_eq_two_mul branch hbit]
  exact ⟨reducedAfterLowBit base +
    branchValue branch * reducedAfterLowBit secret, rfl⟩

/-- The corrected-and-halved branch is an exact reduced DCP branch. -/
theorem reducedSamplePosition_eq
    {base secret knownBit : ℤ} (branch : Bool)
    (hbit : lowBit secret = knownBit) :
    reducedSamplePosition base secret knownBit branch =
      reducedAfterLowBit base +
        branchValue branch * reducedAfterLowBit secret := by
  rw [reducedSamplePosition,
    correctedPosition_sub_lowBit_eq_two_mul branch hbit]
  exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)

/-- The two reduced branches differ by exactly the reduced hidden shift. -/
theorem reducedSamplePosition_true_sub_false
    {base secret knownBit : ℤ} (hbit : lowBit secret = knownBit) :
    reducedSamplePosition base secret knownBit true -
        reducedSamplePosition base secret knownBit false =
      reducedAfterLowBit secret := by
  rw [reducedSamplePosition_eq true hbit,
    reducedSamplePosition_eq false hbit]
  simp [branchValue]

/-- The integer dot product on a finite coordinate type. -/
def dot {Index : Type*} [Fintype Index]
    (frequency secret : Index → ℤ) : ℤ :=
  ∑ i, frequency i * secret i

/-- Removing each secret low bit pulls a factor of two out of a dot product. -/
theorem dot_sub_lowBits_eq_two_mul {Index : Type*} [Fintype Index]
    (frequency secret : Index → ℤ) :
    dot frequency secret - dot frequency (fun i => lowBit (secret i)) =
      2 * dot frequency (fun i => reducedAfterLowBit (secret i)) := by
  calc
    dot frequency secret - dot frequency (fun i => lowBit (secret i)) =
        ∑ i, (frequency i * secret i -
          frequency i * lowBit (secret i)) := by
      simp only [dot, Finset.sum_sub_distrib]
    _ = ∑ i, 2 * (frequency i * reducedAfterLowBit (secret i)) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        frequency i * secret i - frequency i * lowBit (secret i) =
            frequency i * (secret i - lowBit (secret i)) := by ring
        _ = frequency i * (2 * reducedAfterLowBit (secret i)) := by
          change frequency i * removeLowBit (secret i) = _
          rw [removeLowBit_eq_two_mul_reduced]
        _ = 2 * (frequency i * reducedAfterLowBit (secret i)) := by ring
    _ = 2 * dot frequency (fun i => reducedAfterLowBit (secret i)) := by
      simp only [dot, Finset.mul_sum]

/-- The removed part of a dot product is even. -/
theorem two_dvd_dot_sub_lowBits {Index : Type*} [Fintype Index]
    (frequency secret : Index → ℤ) :
    2 ∣ dot frequency secret - dot frequency (fun i => lowBit (secret i)) := by
  rw [dot_sub_lowBits_eq_two_mul]
  exact ⟨dot frequency (fun i => reducedAfterLowBit (secret i)), rfl⟩

/-- Dividing the corrected dot product by two gives the reduced dot product. -/
theorem dot_sub_lowBits_ediv_two {Index : Type*} [Fintype Index]
    (frequency secret : Index → ℤ) :
    (dot frequency secret - dot frequency (fun i => lowBit (secret i))) / 2 =
      dot frequency (fun i => reducedAfterLowBit (secret i)) := by
  rw [dot_sub_lowBits_eq_two_mul]
  exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)

/-- Replace the canonical low-bit vector by any extensionally equal known vector. -/
theorem dot_sub_knownLowBits_ediv_two {Index : Type*} [Fintype Index]
    (frequency secret knownBits : Index → ℤ)
    (hbits : ∀ i, lowBit (secret i) = knownBits i) :
    (dot frequency secret - dot frequency knownBits) / 2 =
      dot frequency (fun i => reducedAfterLowBit (secret i)) := by
  have hknown : knownBits = fun i => lowBit (secret i) := by
    funext i
    exact (hbits i).symm
  rw [hknown]
  exact dot_sub_lowBits_ediv_two frequency secret

/-- Cancel a common factor two from both values and the modulus. -/
theorem halve_modEq {left right modulus : ℤ}
    (hleft : 2 ∣ left) (hright : 2 ∣ right)
    (hcong : left ≡ right [ZMOD 2 * modulus]) :
    left / 2 ≡ right / 2 [ZMOD modulus] := by
  rcases hleft with ⟨left', rfl⟩
  rcases hright with ⟨right', rfl⟩
  have hcancelled : left' ≡ right' [ZMOD modulus] :=
    Int.ModEq.mul_left_cancel' (by norm_num : (2 : ℤ) ≠ 0) hcong
  simpa only [Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    using hcancelled

/--
Halve a dot-product congruence after subtracting the known low-bit
contribution.  The right-hand numerator is even as a consequence of the
original congruence; it is not assumed independently.
-/
theorem reducedDot_modEq {Index : Type*} [Fintype Index]
    (frequency secret knownBits : Index → ℤ) (target modulus : ℤ)
    (hbits : ∀ i, lowBit (secret i) = knownBits i)
    (hcong : dot frequency secret ≡ target [ZMOD 2 * modulus]) :
    dot frequency (fun i => reducedAfterLowBit (secret i)) ≡
      (target - dot frequency knownBits) / 2 [ZMOD modulus] := by
  have hknown : knownBits = fun i => lowBit (secret i) := by
    funext i
    exact (hbits i).symm
  have hleftEven : 2 ∣ dot frequency secret - dot frequency knownBits := by
    rw [hknown]
    exact two_dvd_dot_sub_lowBits frequency secret
  have hremoved :
      dot frequency secret - dot frequency knownBits ≡
        target - dot frequency knownBits [ZMOD 2 * modulus] :=
    hcong.sub (Int.ModEq.refl (dot frequency knownBits))
  have hparity :
      dot frequency secret - dot frequency knownBits ≡
        target - dot frequency knownBits [ZMOD 2] :=
    hremoved.of_mul_right modulus
  have hrightEven : 2 ∣ target - dot frequency knownBits :=
    (hparity.dvd_iff).mp hleftEven
  have hhalved := halve_modEq hleftEven hrightEven hremoved
  rw [dot_sub_knownLowBits_ediv_two frequency secret knownBits hbits] at hhalved
  exact hhalved

/--
If a measured dot product has even parity, then its known low-bit
contribution has the same parity.  This is the `j · s = 0 (mod 2)` special
case often used when describing the recursion.
-/
theorem knownLowBits_modEq_zero_of_dot_modEq_zero
    {Index : Type*} [Fintype Index]
    (frequency secret knownBits : Index → ℤ)
    (hbits : ∀ i, lowBit (secret i) = knownBits i)
    (hparity : dot frequency secret ≡ 0 [ZMOD 2]) :
    dot frequency knownBits ≡ 0 [ZMOD 2] := by
  have hknown : knownBits = fun i => lowBit (secret i) := by
    funext i
    exact (hbits i).symm
  have heven : 2 ∣ dot frequency secret - dot frequency knownBits := by
    rw [hknown]
    exact two_dvd_dot_sub_lowBits frequency secret
  have hsame : dot frequency secret ≡ dot frequency knownBits [ZMOD 2] := by
    rw [Int.modEq_iff_dvd]
    have hneg :
        dot frequency knownBits - dot frequency secret =
          -(dot frequency secret - dot frequency knownBits) := by ring
    rw [hneg, Int.dvd_neg]
    exact heven
  exact hsame.symm.trans hparity

end SimonDCP.Arithmetic.SampleRecursion
