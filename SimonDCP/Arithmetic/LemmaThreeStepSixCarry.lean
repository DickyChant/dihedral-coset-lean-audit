import Mathlib.Tactic

/-!
# The Step-6 high-bit/carry calculation

This file isolates the deterministic arithmetic behind Step 6 of the paper.
Write the word width as `n = 2 ^ ell`.  If an `n`-bit group sum is split into
its top `ell` bits and its remaining bits, then its low-block base is

`B = 2 ^ (n - ell)`.

For `a` selected groups, the sum of the omitted low parts contributes the
carry

`q = floor ((sum_j low_j) / B)`.

The bound `low_j < B` gives `q < a`.  The paper takes `a = n / ell`; below we
allow an explicit `a` and record the sufficient scheduling condition
`a * ell <= n`.

Adding `q` to the sum of the retained high blocks can change its top bit only
in one of two intervals: immediately below `n / 2`, or immediately below
`n`.  `carryVulnerable n a s` is the exact half-open, integer version of these
two width-`a` boundary windows.  Thus it is a precise interval replacement for
the paper's bit predicate `l_(s*) = 1`.  Connecting that interval predicate to
the paper's particular choice and rounding convention for `log log n` remains
a separate encoding equivalence; the carry theorem itself does not need it.
-/

namespace SimonDCP.Arithmetic.LemmaThreeStepSixCarry

open scoped BigOperators

/-- The paper's word width `n`, represented as an exact power of two. -/
def paperWidth (ell : Nat) : Nat := 2 ^ ell

/-- The base below the retained top `ell` bits of an `n = 2 ^ ell` bit word. -/
def lowBlockBase (ell : Nat) : Nat := 2 ^ (paperWidth ell - ell)

/-- The modulus of an `n = 2 ^ ell` bit word. -/
def wordModulus (ell : Nat) : Nat := 2 ^ paperWidth ell

/-- The top bit of a natural number after reduction modulo `modulus`. -/
def modularTopBit (modulus value : Nat) : Bool :=
  decide (modulus / 2 <= value % modulus)

/-- The high-block sum retained by Step 6. -/
def retainedHighSum {a : Nat} (high : Fin a -> Nat) : Nat :=
  ∑ j, high j

/-- The residue `s*` computed in Step 6. -/
def stepSixResidue {a : Nat} (ell : Nat) (high : Fin a -> Nat) : Nat :=
  retainedHighSum high % paperWidth ell

/-- The carry produced by all omitted low blocks. -/
def lowCarry {a : Nat} (base : Nat) (low : Fin a -> Nat) : Nat :=
  (∑ j, low j) / base

/--
The two vulnerable boundary windows for a carry known to be strictly smaller
than `a`.  For a canonical residue `s < n`, this says

* `s < n / 2` and the largest possible carry can reach `n / 2`, or
* `n / 2 <= s` and the largest possible carry can wrap at `n`.

The strict inequalities on the right make the definition exact for carries
`q < a`, whose largest possible value is `a - 1`.
-/
def carryVulnerable (n a s : Nat) : Prop :=
  (s < n / 2 ∧ n / 2 < s + a) ∨
    (n / 2 <= s ∧ n < s + a)

/-- Every natural exponent is at least its index when the base is two. -/
theorem index_le_two_pow (ell : Nat) : ell <= 2 ^ ell := by
  induction ell with
  | zero => simp
  | succ ell ih =>
      simp only [pow_succ]
      have hone : 1 <= 2 ^ ell := Nat.one_le_two_pow
      omega

/-- The retained and omitted block sizes multiply to the full word modulus. -/
theorem paperWidth_mul_lowBlockBase (ell : Nat) :
    paperWidth ell * lowBlockBase ell = wordModulus ell := by
  change 2 ^ ell * 2 ^ (2 ^ ell - ell) = 2 ^ (2 ^ ell)
  rw [← pow_add]
  rw [Nat.add_comm, Nat.sub_add_cancel (index_le_two_pow ell)]

/-- The low-block base is positive. -/
theorem lowBlockBase_pos (ell : Nat) : 0 < lowBlockBase ell := by
  simp [lowBlockBase]

/-- The paper width is positive. -/
theorem paperWidth_pos (ell : Nat) : 0 < paperWidth ell := by
  simp [paperWidth]

/-! ## The low carry -/

/-- Summing `a` values strictly below `base` produces a quotient below `a`. -/
theorem lowCarry_lt_groupCount {a base : Nat} (ha : 0 < a) (hbase : 0 < base)
    (low : Fin a -> Nat) (hlow : ∀ j, low j < base) :
    lowCarry base low < a := by
  have hsum : (∑ j, low j) < ∑ _j : Fin a, base := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨⟨0, ha⟩, Finset.mem_univ _⟩
    · intro j _hj
      exact hlow j
  have hsum' : (∑ j, low j) < a * base := by
    simpa [Nat.mul_comm] using hsum
  exact (Nat.div_lt_iff_lt_mul hbase).2 hsum'

/--
Under the rounded scheduling condition `a * ell <= n`, the low carry is below
the paper's scale `n / ell`.
-/
theorem lowCarry_lt_width_div_log {ell a base : Nat} (hell : 0 < ell)
    (ha : 0 < a) (hgroups : a * ell <= paperWidth ell)
    (low : Fin a -> Nat) (hlow : ∀ j, low j < base) (hbase : 0 < base) :
    lowCarry base low < paperWidth ell / ell := by
  have hcarry : lowCarry base low < a :=
    lowCarry_lt_groupCount ha hbase low hlow
  have ha_le : a <= paperWidth ell / ell :=
    (Nat.le_div_iff_mul_le hell).2 hgroups
  exact lt_of_lt_of_le hcarry ha_le

/-! ## Boundary windows and top-bit stability -/

/-- Outside the vulnerable windows is equivalently a pair of safe margins. -/
theorem not_carryVulnerable_iff_safeMargins {n a s : Nat} :
    ¬ carryVulnerable n a s ↔
      (s < n / 2 -> s + a <= n / 2) ∧
      (n / 2 <= s -> s + a <= n) := by
  unfold carryVulnerable
  omega

/--
Adding any `q < a` to a canonical residue outside the two vulnerable windows
preserves its top bit, including reduction modulo `n`.
-/
theorem modularTopBit_add_smallCarry {n a s q : Nat}
    (hs : s < n) (hq : q < a) (houtside : ¬ carryVulnerable n a s) :
    modularTopBit n (s + q) = modularTopBit n s := by
  have hmargins := not_carryVulnerable_iff_safeMargins.mp houtside
  by_cases hlow : s < n / 2
  · have hsafeA : s + a <= n / 2 := hmargins.1 hlow
    have hsq_lt : s + q < n / 2 := by omega
    have hsq_n : s + q < n :=
      lt_of_lt_of_le hsq_lt (Nat.div_le_self n 2)
    simp [modularTopBit, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hsq_n,
      Nat.not_le_of_gt hlow, Nat.not_le_of_gt hsq_lt]
  · have hhigh : n / 2 <= s := Nat.le_of_not_gt hlow
    have hsafeA : s + a <= n := hmargins.2 hhigh
    have hsq_n : s + q < n := by omega
    have hsq_high : n / 2 <= s + q := by omega
    simp [modularTopBit, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hsq_n,
      hhigh, hsq_high]

/-! ## Exact block arithmetic -/

/--
Dividing the residue of `k * base + remainder` by `base` recovers `k mod n`,
provided `remainder` really is a low block.
-/
theorem quotient_mod_blockProduct (n base k remainder : Nat)
    (hn : 0 < n) (hbase : 0 < base) (hremainder : remainder < base) :
    ((k * base + remainder) % (n * base)) / base = k % n := by
  have hkmod : k % n < n := Nat.mod_lt k hn
  have hsmall : (k % n) * base + remainder < n * base := by
    calc
      (k % n) * base + remainder < (k % n) * base + base :=
        Nat.add_lt_add_left hremainder _
      _ = (k % n + 1) * base := by ring
      _ <= n * base := Nat.mul_le_mul_right base (Nat.succ_le_iff.mpr hkmod)
  have hexpand :
      k * base + remainder =
        ((k % n) * base + remainder) + (n * base) * (k / n) := by
    nth_rewrite 1 [← Nat.mod_add_div k n]
    ring
  rw [hexpand, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
  calc
    ((k % n) * base + remainder) / base =
        (remainder + base * (k % n)) / base := by ring_nf
    _ = remainder / base + k % n := Nat.add_mul_div_left _ _ hbase
    _ = k % n := by rw [Nat.div_eq_of_lt hremainder, zero_add]

/-- The sum of group decompositions has the expected total block form. -/
theorem sum_groupDecomposition {a base : Nat}
    (high low : Fin a -> Nat) :
    (∑ j, (high j * base + low j)) =
      (retainedHighSum high + lowCarry base low) * base +
        (∑ j, low j) % base := by
  unfold retainedHighSum lowCarry
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  nth_rewrite 1 [← Nat.mod_add_div (∑ j, low j) base]
  ring

/--
The high-block index of the complete sum modulo the full word modulus is the
retained high sum plus the omitted-low carry, modulo `2 ^ ell`.
-/
theorem fullSum_highBlock_eq {ell a : Nat} (r high low : Fin a -> Nat)
    (hdecomp : ∀ j, r j = high j * lowBlockBase ell + low j) :
    ((∑ j, r j) % wordModulus ell) / lowBlockBase ell =
      (retainedHighSum high + lowCarry (lowBlockBase ell) low) %
        paperWidth ell := by
  have hsum :
      (∑ j, r j) = ∑ j, (high j * lowBlockBase ell + low j) := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact hdecomp j
  rw [hsum, sum_groupDecomposition]
  rw [← paperWidth_mul_lowBlockBase ell]
  exact quotient_mod_blockProduct
    (paperWidth ell) (lowBlockBase ell)
    (retainedHighSum high + lowCarry (lowBlockBase ell) low)
    ((∑ j, low j) % lowBlockBase ell)
    (paperWidth_pos ell) (lowBlockBase_pos ell)
    (Nat.mod_lt _ (lowBlockBase_pos ell))

/-- The full-word top bit exposed through its top-`ell`-bit quotient. -/
def highBlockTopBit (ell total : Nat) : Bool :=
  modularTopBit (paperWidth ell)
    ((total % wordModulus ell) / lowBlockBase ell)

/-- The literal top-bit threshold of the complete sum modulo `2 ^ n`. -/
def fullWordTopBit (ell total : Nat) : Bool :=
  decide (2 ^ (paperWidth ell - 1) <= total % wordModulus ell)

/-- The top-bit threshold factors as half the high-block range times `B`. -/
theorem halfPaperWidth_mul_lowBlockBase {ell : Nat} (hell : 0 < ell) :
    paperWidth ell / 2 * lowBlockBase ell = 2 ^ (paperWidth ell - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  change
    (2 ^ (k + 1) / 2) * 2 ^ (2 ^ (k + 1) - (k + 1)) =
      2 ^ (2 ^ (k + 1) - 1)
  rw [pow_succ, Nat.mul_div_cancel _ Nat.zero_lt_two]
  rw [← pow_add]
  congr 1
  have hindex := index_le_two_pow (k + 1)
  omega

/-- Taking the top bit after the high-block quotient is the literal word bit. -/
theorem highBlockTopBit_eq_fullWordTopBit {ell : Nat} (hell : 0 < ell)
    (total : Nat) : highBlockTopBit ell total = fullWordTopBit ell total := by
  have hresidue :
      total % wordModulus ell < paperWidth ell * lowBlockBase ell := by
    rw [paperWidth_mul_lowBlockBase]
    exact Nat.mod_lt _ (by simp [wordModulus])
  have hquotient :
      (total % wordModulus ell) / lowBlockBase ell < paperWidth ell :=
    (Nat.div_lt_iff_lt_mul (lowBlockBase_pos ell)).2 hresidue
  unfold highBlockTopBit modularTopBit fullWordTopBit
  rw [Nat.mod_eq_of_lt hquotient]
  apply Bool.decide_congr
  rw [Nat.le_div_iff_mul_le (lowBlockBase_pos ell),
    halfPaperWidth_mul_lowBlockBase hell]

/--
Main repaired Step-6 carry theorem.  If every selected group has the displayed
high/low decomposition, and `s*` is outside the two carry-vulnerable windows,
then the bit computed from `s*` is exactly the top bit of the complete group
sum modulo `2 ^ n`.
-/
theorem stepSix_topBit_eq_fullSum {ell a : Nat} (hell : 0 < ell) (ha : 0 < a)
    (hgroups : a * ell <= paperWidth ell)
    (r high low : Fin a -> Nat)
    (hdecomp : ∀ j, r j = high j * lowBlockBase ell + low j)
    (hlow : ∀ j, low j < lowBlockBase ell)
    (houtside :
      ¬ carryVulnerable (paperWidth ell) a (stepSixResidue ell high)) :
    modularTopBit (paperWidth ell) (stepSixResidue ell high) =
      fullWordTopBit ell (∑ j, r j) := by
  have hsStar : stepSixResidue ell high < paperWidth ell :=
    Nat.mod_lt _ (paperWidth_pos ell)
  have hcarry : lowCarry (lowBlockBase ell) low < a :=
    lowCarry_lt_groupCount ha (lowBlockBase_pos ell) low hlow
  have _hcarryScale :
      lowCarry (lowBlockBase ell) low < paperWidth ell / ell :=
    lowCarry_lt_width_div_log hell ha hgroups low hlow (lowBlockBase_pos ell)
  have hstable := modularTopBit_add_smallCarry hsStar hcarry houtside
  have hblock := fullSum_highBlock_eq r high low hdecomp
  have hmod :
      (retainedHighSum high + lowCarry (lowBlockBase ell) low) % paperWidth ell =
        (stepSixResidue ell high + lowCarry (lowBlockBase ell) low) %
          paperWidth ell := by
    unfold stepSixResidue
    simp only [Nat.add_mod, Nat.mod_mod]
  have htop :
      modularTopBit (paperWidth ell)
          ((retainedHighSum high + lowCarry (lowBlockBase ell) low) %
            paperWidth ell) =
        modularTopBit (paperWidth ell)
          (stepSixResidue ell high + lowCarry (lowBlockBase ell) low) := by
    unfold modularTopBit
    rw [Nat.mod_mod, hmod]
  have hquotientTop :
      modularTopBit (paperWidth ell) (stepSixResidue ell high) =
        highBlockTopBit ell (∑ j, r j) := by
    unfold highBlockTopBit
    rw [hblock]
    exact hstable.symm.trans htop.symm
  exact hquotientTop.trans (highBlockTopBit_eq_fullWordTopBit hell _)

/--
The carry bound used in the main theorem also has the paper's advertised
`n / ell` form.  It is kept as a separate conclusion because top-bit stability
uses the sharper bound `q < a` directly.
-/
theorem stepSix_lowCarry_lt_width_div_log {ell a : Nat} (hell : 0 < ell)
    (ha : 0 < a) (hgroups : a * ell <= paperWidth ell)
    (low : Fin a -> Nat) (hlow : ∀ j, low j < lowBlockBase ell) :
    lowCarry (lowBlockBase ell) low < paperWidth ell / ell :=
  lowCarry_lt_width_div_log hell ha hgroups low hlow (lowBlockBase_pos ell)

end SimonDCP.Arithmetic.LemmaThreeStepSixCarry
