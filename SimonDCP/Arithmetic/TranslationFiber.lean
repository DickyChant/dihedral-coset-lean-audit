import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Translation by the high bit in a binary cyclic group

This file isolates the algebraic content of Lemma 2 in Simon's preprint.  In
`ZMod (2 ^ n)`, adding `2 ^ (n - 1)` toggles the high bit.  The translation is
an involution, and an equation of the form

`z + contribution = target + highBit`

is unchanged when both `z` and `highBit` are toggled.  Consequently, any
restricted fibre and any weighted sum over that fibre are unchanged as well.

The paper's sets also encode measured classical data and quantum-state
bookkeeping.  Those details are deliberately represented here by arbitrary
candidate finite sets, contribution functions, and weights.  Thus the results
below prove the reusable algebraic kernel without silently postulating the
paper-specific state construction.
-/

namespace SimonDCP.Arithmetic.TranslationFiber

open scoped BigOperators

/-- The additive group of `n`-bit words. -/
abbrev Word (n : ℕ) := ZMod (2 ^ n)

/-- The element represented by a one in the high bit and zeroes below it. -/
def halfTurn (n : ℕ) : Word n := (2 ^ (n - 1) : ℕ)

/-- In a nonempty binary word, the high-bit element added to itself is zero. -/
theorem halfTurn_add_self {n : ℕ} (hn : 0 < n) :
    halfTurn n + halfTurn n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [halfTurn, Nat.succ_sub_one]
  rw [← Nat.cast_add]
  convert ZMod.natCast_self (2 ^ (k + 1)) using 1
  simp [pow_succ, mul_two]

/-- In a nonempty binary word, the high-bit element is not zero. -/
theorem halfTurn_ne_zero {n : ℕ} (hn : 0 < n) : halfTurn n ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [halfTurn, Nat.succ_sub_one]
  intro hzero
  have hdvd : 2 ^ (k + 1) ∣ 2 ^ k :=
    (ZMod.natCast_eq_zero_iff (2 ^ k) (2 ^ (k + 1))).mp hzero
  have hle : 2 ^ (k + 1) ≤ 2 ^ k :=
    Nat.le_of_dvd (by positivity : 0 < 2 ^ k) hdvd
  have hpos : 0 < 2 ^ k := by positivity
  rw [pow_succ] at hle
  omega

/-- The high-bit element has additive order exactly two. -/
theorem addOrderOf_halfTurn {n : ℕ} (hn : 0 < n) :
    addOrderOf (halfTurn n) = 2 := by
  apply addOrderOf_eq_prime
  · simpa only [two_nsmul] using halfTurn_add_self hn
  · exact halfTurn_ne_zero hn

/-- Translate an `n`-bit word by its high-bit element. -/
def translate (n : ℕ) (z : Word n) : Word n := z + halfTurn n

/-- High-bit translation is an involution. -/
theorem translate_involutive {n : ℕ} (hn : 0 < n) :
    Function.Involutive (translate n) := by
  intro z
  simp [translate, add_assoc, halfTurn_add_self hn]

/-- High-bit translation is a bijection. -/
theorem translate_bijective {n : ℕ} (hn : 0 < n) :
    Function.Bijective (translate n) :=
  (translate_involutive hn).bijective

/-- High-bit translation, packaged as a self-equivalence. -/
def translateEquiv (n : ℕ) (hn : 0 < n) : Word n ≃ Word n where
  toFun := translate n
  invFun := translate n
  left_inv := translate_involutive hn
  right_inv := translate_involutive hn

/-- Interpret a Boolean as either zero or the high-bit element. -/
def bitValue (n : ℕ) (h : Bool) : Word n :=
  if h then halfTurn n else 0

/-- Complementing a bit is the same as adding the high-bit element. -/
theorem bitValue_not {n : ℕ} (hn : 0 < n) (h : Bool) :
    bitValue n (!h) = bitValue n h + halfTurn n := by
  cases h <;> simp [bitValue, halfTurn_add_self hn]

/-- Encode a low `(n - 1)`-bit value together with a Boolean high bit. -/
def ofLowHigh (n : ℕ) (low : Fin (2 ^ (n - 1))) (h : Bool) : Word n :=
  (low.val : Word n) + bitValue n h

/-- Translation complements the high bit while leaving the low part fixed. -/
theorem translate_ofLowHigh {n : ℕ} (hn : 0 < n)
    (low : Fin (2 ^ (n - 1))) (h : Bool) :
    translate n (ofLowHigh n low h) = ofLowHigh n low (!h) := by
  simp only [ofLowHigh, translate]
  rw [bitValue_not hn]
  ac_rfl

/--
The fibre equation used by the algebraic part of the paper's Lemma 2.

`contribution` stands for the subset sum attached to a state portion, while
`target` stands for the previously measured total.
-/
def FiberEquation (n : ℕ) (z contribution target : Word n) (h : Bool) : Prop :=
  z + contribution = target + bitValue n h

/--
Translating `z` and complementing `h` preserves the fibre equation.
-/
theorem fiberEquation_translate_not_iff {n : ℕ} (hn : 0 < n)
    (z contribution target : Word n) (h : Bool) :
    FiberEquation n (translate n z) contribution target (!h) ↔
      FiberEquation n z contribution target h := by
  simp only [FiberEquation, translate]
  rw [bitValue_not hn]
  constructor
  · intro hEq
    apply add_right_cancel (b := halfTurn n)
    calc
      (z + contribution) + halfTurn n = (z + halfTurn n) + contribution := by
        ac_rfl
      _ = target + (bitValue n h + halfTurn n) := hEq
      _ = (target + bitValue n h) + halfTurn n := by
        ac_rfl
  · intro hEq
    calc
      (z + halfTurn n) + contribution = (z + contribution) + halfTurn n := by
        ac_rfl
      _ = (target + bitValue n h) + halfTurn n :=
        congrArg (fun x : Word n ↦ x + halfTurn n) hEq
      _ = target + (bitValue n h + halfTurn n) := by
        ac_rfl

/-- Toggling the first input of XOR toggles its output. -/
theorem xor_not_left (high measured : Bool) :
    (!high).xor measured = !(high.xor measured) := by
  cases high <;> cases measured <;> rfl

/--
The invariant in the form used after the paper measures `h' = high XOR h`.
The measured bit stays fixed while `high`, and hence `h`, is complemented.
-/
theorem fiberEquation_translate_fixedXor_iff {n : ℕ} (hn : 0 < n)
    (z contribution target : Word n) (high measured : Bool) :
    FiberEquation n (translate n z) contribution target ((!high).xor measured) ↔
      FiberEquation n z contribution target (high.xor measured) := by
  rw [xor_not_left]
  exact fiberEquation_translate_not_iff hn z contribution target (high.xor measured)

/-- The fibre invariant stated directly for two words with the same low bits. -/
theorem fiberEquation_ofLowHigh_fixedXor_iff {n : ℕ} (hn : 0 < n)
    (low : Fin (2 ^ (n - 1))) (contribution target : Word n)
    (high measured : Bool) :
    FiberEquation n (ofLowHigh n low (!high)) contribution target
        ((!high).xor measured) ↔
      FiberEquation n (ofLowHigh n low high) contribution target
        (high.xor measured) := by
  rw [← translate_ofLowHigh hn low high]
  exact fiberEquation_translate_fixedXor_iff hn
    (ofLowHigh n low high) contribution target high measured

/-- Elements whose contribution satisfies a given fibre equation. -/
def fiber {Index : Type*} (n : ℕ) (contribution : Index → Word n)
    (z target : Word n) (h : Bool) : Set Index :=
  {i | FiberEquation n z (contribution i) target h}

/-- High-bit translation leaves the corresponding fibre set unchanged. -/
theorem fiber_translate_not {Index : Type*} {n : ℕ} (hn : 0 < n)
    (contribution : Index → Word n) (z target : Word n) (h : Bool) :
    fiber n contribution (translate n z) target (!h) =
      fiber n contribution z target h := by
  ext i
  exact fiberEquation_translate_not_iff hn z (contribution i) target h

/-- The same fibre equality with a fixed measured XOR bit. -/
theorem fiber_translate_fixedXor {Index : Type*} {n : ℕ} (hn : 0 < n)
    (contribution : Index → Word n) (z target : Word n)
    (high measured : Bool) :
    fiber n contribution (translate n z) target ((!high).xor measured) =
      fiber n contribution z target (high.xor measured) := by
  ext i
  exact fiberEquation_translate_fixedXor_iff hn z (contribution i) target high measured

/-- Restrict a fibre to candidates compatible with all other measurements. -/
noncomputable def fiberFinset {Index : Type*} (n : ℕ) (candidates : Finset Index)
    (contribution : Index → Word n) (z target : Word n) (h : Bool) : Finset Index := by
  classical
  exact candidates.filter fun i ↦ FiberEquation n z (contribution i) target h

/-- Restricting to other measured data does not affect the translation argument. -/
theorem fiberFinset_translate_not {Index : Type*} {n : ℕ} (hn : 0 < n)
    (candidates : Finset Index) (contribution : Index → Word n)
    (z target : Word n) (h : Bool) :
    fiberFinset n candidates contribution (translate n z) target (!h) =
      fiberFinset n candidates contribution z target h := by
  classical
  ext i
  simp only [fiberFinset, Finset.mem_filter]
  rw [fiberEquation_translate_not_iff hn]

/-- The finite fibre equality with a fixed measured XOR bit. -/
theorem fiberFinset_translate_fixedXor {Index : Type*} {n : ℕ} (hn : 0 < n)
    (candidates : Finset Index) (contribution : Index → Word n)
    (z target : Word n) (high measured : Bool) :
    fiberFinset n candidates contribution (translate n z) target ((!high).xor measured) =
      fiberFinset n candidates contribution z target (high.xor measured) := by
  classical
  ext i
  simp only [fiberFinset, Finset.mem_filter]
  rw [fiberEquation_translate_fixedXor_iff hn]

/-- An arbitrary weighted sum over a fibre, abstracting the paper's coefficient `C`. -/
noncomputable def fiberCoefficient {Index Coeff : Type*} [AddCommMonoid Coeff]
    (n : ℕ) (candidates : Finset Index) (contribution : Index → Word n)
    (weight : Index → Coeff) (z target : Word n) (h : Bool) : Coeff :=
  ∑ i ∈ fiberFinset n candidates contribution z target h, weight i

/-- Any weighted fibre sum is unchanged by the paired translation. -/
theorem fiberCoefficient_translate_not {Index Coeff : Type*} [AddCommMonoid Coeff]
    {n : ℕ} (hn : 0 < n) (candidates : Finset Index)
    (contribution : Index → Word n) (weight : Index → Coeff)
    (z target : Word n) (h : Bool) :
    fiberCoefficient n candidates contribution weight (translate n z) target (!h) =
      fiberCoefficient n candidates contribution weight z target h := by
  simp only [fiberCoefficient]
  rw [fiberFinset_translate_not hn candidates contribution z target h]

/--
Weighted fibre sums agree for the two high-bit choices at a fixed measured XOR
bit.  This is the direct algebraic analogue of the equality claimed for `C` in
the paper's Lemma 2.
-/
theorem fiberCoefficient_translate_fixedXor {Index Coeff : Type*} [AddCommMonoid Coeff]
    {n : ℕ} (hn : 0 < n) (candidates : Finset Index)
    (contribution : Index → Word n) (weight : Index → Coeff)
    (z target : Word n) (high measured : Bool) :
    fiberCoefficient n candidates contribution weight (translate n z) target
        ((!high).xor measured) =
      fiberCoefficient n candidates contribution weight z target (high.xor measured) := by
  simp only [fiberCoefficient]
  rw [fiberFinset_translate_fixedXor hn candidates contribution z target high measured]

/--
The coefficient equality stated directly for two words which differ only in
their Boolean high bit.
-/
theorem fiberCoefficient_ofLowHigh_fixedXor
    {Index Coeff : Type*} [AddCommMonoid Coeff] {n : ℕ} (hn : 0 < n)
    (candidates : Finset Index) (contribution : Index → Word n)
    (weight : Index → Coeff) (low : Fin (2 ^ (n - 1)))
    (target : Word n) (high measured : Bool) :
    fiberCoefficient n candidates contribution weight (ofLowHigh n low (!high)) target
        ((!high).xor measured) =
      fiberCoefficient n candidates contribution weight (ofLowHigh n low high) target
        (high.xor measured) := by
  rw [← translate_ofLowHigh hn low high]
  exact fiberCoefficient_translate_fixedXor hn candidates contribution weight
    (ofLowHigh n low high) target high measured

end SimonDCP.Arithmetic.TranslationFiber
