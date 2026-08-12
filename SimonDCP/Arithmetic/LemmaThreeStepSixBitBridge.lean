import SimonDCP.Arithmetic.LemmaThreeStepSixCarry

/-!
# The Step-6 paper-bit bridge

This file connects the bit tested in Step 6 of the paper to the exact carry
windows in `LemmaThreeStepSixCarry`.

Write the paper's word width as `n = 2 ^ ell`, so `ell = log_2 n`.  If
`tau = floor (log_2 ell)`, the paper tests the bits ranked second through
`tau` from the most significant end of the `ell`-bit residue `s*`.  Removing
the most significant bit is reduction modulo `n / 2`; removing the lowest
`ell - tau` bits is division by `2 ^ (ell - tau)`.  Thus those tested bits are
all one exactly when the resulting integer is `2 ^ (tau - 1) - 1`.

The important rounding direction is downward.  Since

`2 ^ floor(log_2 ell) <= ell`,

the rejected boundary block has width at least `n / ell`, hence at least the
number of selected groups.  A zero test result therefore excludes both carry
windows and makes the retained top bit correct.  The final finite example
shows that replacing the floor by a ceiling is not sound in general.
-/

namespace SimonDCP.Arithmetic.LemmaThreeStepSixBitBridge

open SimonDCP.Arithmetic.LemmaThreeStepSixCarry

/-- Number of lower bits discarded before reading the tested high prefix. -/
def carryGuardBlock (ell tau : Nat) : Nat :=
  2 ^ (ell - tau)

/-- The range of the tested bits (the leading bit itself is not tested). -/
def checkedInteriorPrefixModulus (tau : Nat) : Nat :=
  2 ^ (tau - 1)

/--
Arithmetic extraction of the paper's bits ranked second through `tau` from
the most significant end of an `ell`-bit residue.  Reduction modulo `n / 2`
drops the leading bit, and division drops all bits below the tested prefix.
-/
def paperInteriorBitsAllOne (ell tau s : Nat) : Prop :=
  (s % (paperWidth ell / 2)) / carryGuardBlock ell tau =
    checkedInteriorPrefixModulus tau - 1

/-- The literal Step-6 flag: one means that every tested interior bit is one. -/
def paperStepSixFlag (ell tau s : Nat) : Bool :=
  (s % (paperWidth ell / 2)) / carryGuardBlock ell tau ==
    checkedInteriorPrefixModulus tau - 1

/-- The paper width is twice its half-width whenever it has at least two bits. -/
theorem paperWidth_eq_two_mul_half {ell : Nat} (hell : 0 < ell) :
    paperWidth ell = 2 * (paperWidth ell / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  simp [paperWidth, pow_succ, Nat.mul_comm]

/-- The tested-prefix scale times its low block is exactly half the word. -/
theorem halfPaperWidth_eq_prefix_mul_guard {ell tau : Nat}
    (htau : 0 < tau) (htauEll : tau ≤ ell) :
    paperWidth ell / 2 =
      checkedInteriorPrefixModulus tau * carryGuardBlock ell tau := by
  have hell : 0 < ell := lt_of_lt_of_le htau htauEll
  have hhalf : paperWidth ell / 2 = 2 ^ (ell - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
    simp [paperWidth, pow_succ]
  rw [hhalf]
  unfold checkedInteriorPrefixModulus carryGuardBlock
  rw [← pow_add]
  congr 1
  omega

/--
Any carry-vulnerable residue has every bit tested by the paper equal to one,
provided the tested boundary block is at least as wide as the group count.
-/
theorem carryVulnerable_implies_paperInteriorBitsAllOne
    {ell tau a s : Nat} (htau : 0 < tau) (htauEll : tau ≤ ell)
    (hs : s < paperWidth ell) (ha : a ≤ carryGuardBlock ell tau) :
    carryVulnerable (paperWidth ell) a s →
      paperInteriorBitsAllOne ell tau s := by
  intro hvulnerable
  have hell : 0 < ell := lt_of_lt_of_le htau htauEll
  have hprefixPos : 0 < checkedInteriorPrefixModulus tau := by
    simp [checkedInteriorPrefixModulus]
  have hprefixOne : 1 ≤ checkedInteriorPrefixModulus tau := hprefixPos
  have hguardPos : 0 < carryGuardBlock ell tau := by
    simp [carryGuardBlock]
  have hhalf := halfPaperWidth_eq_prefix_mul_guard htau htauEll
  have hfull := paperWidth_eq_two_mul_half hell
  have hguardHalf : carryGuardBlock ell tau ≤ paperWidth ell / 2 := by
    rw [hhalf]
    simpa using Nat.mul_le_mul_right (carryGuardBlock ell tau) hprefixOne
  unfold carryVulnerable at hvulnerable
  unfold paperInteriorBitsAllOne
  rcases hvulnerable with hlow | hhigh
  · rcases hlow with ⟨hsHalf, hreach⟩
    rw [Nat.mod_eq_of_lt hsHalf]
    apply Nat.div_eq_of_lt_le
    · calc
        (checkedInteriorPrefixModulus tau - 1) * carryGuardBlock ell tau =
            paperWidth ell / 2 - carryGuardBlock ell tau := by
              rw [hhalf, Nat.sub_mul]
              simp
        _ ≤ s := by
          apply (Nat.sub_le_iff_le_add).2
          omega
    · calc
        s < paperWidth ell / 2 := hsHalf
        _ = ((checkedInteriorPrefixModulus tau - 1) + 1) *
            carryGuardBlock ell tau := by
              rw [hhalf, Nat.sub_add_cancel hprefixOne]
  · rcases hhigh with ⟨hsHalf, hreach⟩
    have hresidue : s % (paperWidth ell / 2) = s - paperWidth ell / 2 := by
      rw [Nat.mod_eq_sub_mod hsHalf, Nat.mod_eq_of_lt]
      omega
    rw [hresidue]
    apply Nat.div_eq_of_lt_le
    · calc
        (checkedInteriorPrefixModulus tau - 1) * carryGuardBlock ell tau =
            paperWidth ell / 2 - carryGuardBlock ell tau := by
              rw [hhalf, Nat.sub_mul]
              simp
        _ ≤ s - paperWidth ell / 2 := by
          omega
    · calc
        s - paperWidth ell / 2 < paperWidth ell / 2 := by omega
        _ = ((checkedInteriorPrefixModulus tau - 1) + 1) *
            carryGuardBlock ell tau := by
              rw [hhalf, Nat.sub_add_cancel hprefixOne]

/-- A zero paper flag excludes both exact carry-vulnerable intervals. -/
theorem paperStepSixFlag_false_not_carryVulnerable
    {ell tau a s : Nat} (htau : 0 < tau) (htauEll : tau ≤ ell)
    (hs : s < paperWidth ell) (ha : a ≤ carryGuardBlock ell tau)
    (hflag : paperStepSixFlag ell tau s = false) :
    ¬ carryVulnerable (paperWidth ell) a s := by
  have hnot : ¬ paperInteriorBitsAllOne ell tau s := by
    simpa [paperStepSixFlag, paperInteriorBitsAllOne] using hflag
  exact fun hvulnerable =>
    hnot (carryVulnerable_implies_paperInteriorBitsAllOne
      htau htauEll hs ha hvulnerable)

/-! ## The floor-rounded `log log n` specialization -/

/-- The exact natural-number interpretation of `floor (log_2 log_2 n)`. -/
def floorLogLogBits (ell : Nat) : Nat :=
  Nat.log 2 ell

/-- For `ell >= 2`, the floor-rounded number of tested high bits is positive. -/
theorem floorLogLogBits_pos {ell : Nat} (hell : 2 ≤ ell) :
    0 < floorLogLogBits ell := by
  exact Nat.log_pos (by omega) hell

/-- The floor-rounded `log log` index never exceeds the `ell`-bit width. -/
theorem floorLogLogBits_le (ell : Nat) : floorLogLogBits ell ≤ ell := by
  exact Nat.log_le_self 2 ell

/--
The scheduling inequality `a * ell <= 2 ^ ell` places the selected-group count
inside the block rejected by the floor-rounded paper test.
-/
theorem groupCount_le_floorLog_guard {ell a : Nat} (hell : 2 ≤ ell)
    (hgroups : a * ell ≤ paperWidth ell) :
    a ≤ carryGuardBlock ell (floorLogLogBits ell) := by
  have hellNe : ell ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by omega) hell)
  have hpow : 2 ^ floorLogLogBits ell ≤ ell := by
    exact Nat.pow_log_le_self 2 hellNe
  have htauEll : floorLogLogBits ell ≤ ell := floorLogLogBits_le ell
  have hmul : a * 2 ^ floorLogLogBits ell ≤ paperWidth ell :=
    (Nat.mul_le_mul_left a hpow).trans hgroups
  have hfactor :
      paperWidth ell =
        carryGuardBlock ell (floorLogLogBits ell) *
          2 ^ floorLogLogBits ell := by
    unfold paperWidth carryGuardBlock
    rw [← pow_add, Nat.sub_add_cancel htauEll]
  rw [hfactor] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (by simp)

/-- The paper's concrete group count automatically satisfies the schedule. -/
theorem paperGroupCount_mul_log_le_width (ell : Nat) :
    (paperWidth ell / ell) * ell ≤ paperWidth ell := by
  exact Nat.div_mul_le_self _ _

/-- The paper's concrete group count is positive for every positive `ell`. -/
theorem paperGroupCount_pos {ell : Nat} (hell : 0 < ell) :
    0 < paperWidth ell / ell := by
  exact Nat.div_pos (index_le_two_pow ell) hell

/--
The floor-rounded paper test is a sufficient check for the exact safe-margin
predicate used by the carry theorem.
-/
theorem floorLogPaperFlag_false_not_carryVulnerable
    {ell a s : Nat} (hell : 2 ≤ ell) (hs : s < paperWidth ell)
    (hgroups : a * ell ≤ paperWidth ell)
    (hflag : paperStepSixFlag ell (floorLogLogBits ell) s = false) :
    ¬ carryVulnerable (paperWidth ell) a s := by
  exact paperStepSixFlag_false_not_carryVulnerable
    (floorLogLogBits_pos hell) (floorLogLogBits_le ell) hs
    (groupCount_le_floorLog_guard hell hgroups) hflag

/--
End-to-end Step-6 bridge: the paper's floor-rounded zero bit test makes the
retained top bit equal the literal top bit of the complete group sum.
-/
theorem stepSix_floorLogPaperFlag_false_topBit_eq_fullSum
    {ell a : Nat} (hell : 2 ≤ ell) (ha : 0 < a)
    (hgroups : a * ell ≤ paperWidth ell)
    (r high low : Fin a → Nat)
    (hdecomp : ∀ j, r j = high j * lowBlockBase ell + low j)
    (hlow : ∀ j, low j < lowBlockBase ell)
    (hflag :
      paperStepSixFlag ell (floorLogLogBits ell)
        (stepSixResidue ell high) = false) :
    modularTopBit (paperWidth ell) (stepSixResidue ell high) =
      fullWordTopBit ell (∑ j, r j) := by
  apply stepSix_topBit_eq_fullSum (by omega) ha hgroups r high low hdecomp hlow
  exact floorLogPaperFlag_false_not_carryVulnerable hell
    (Nat.mod_lt _ (paperWidth_pos ell)) hgroups hflag

/--
Paper-parameter specialization of the end-to-end bridge.  Here the number of
selected groups is exactly `floor ((2 ^ ell) / ell)`, so the scheduling and
positivity premises are discharged automatically.
-/
theorem stepSix_paperGroupCount_floorLogPaperFlag_false_topBit_eq_fullSum
    {ell : Nat} (hell : 2 ≤ ell)
    (r high low : Fin (paperWidth ell / ell) → Nat)
    (hdecomp : ∀ j, r j = high j * lowBlockBase ell + low j)
    (hlow : ∀ j, low j < lowBlockBase ell)
    (hflag :
      paperStepSixFlag ell (floorLogLogBits ell)
        (stepSixResidue ell high) = false) :
    modularTopBit (paperWidth ell) (stepSixResidue ell high) =
      fullWordTopBit ell (∑ j, r j) := by
  exact stepSix_floorLogPaperFlag_false_topBit_eq_fullSum hell
    (paperGroupCount_pos (by omega))
    (paperGroupCount_mul_log_le_width ell)
    r high low hdecomp hlow hflag

/-! ## Why upward rounding is not a sound replacement -/

/--
For `ell = 5`, upward rounding gives `tau = 3`.  With the paper group count
`a = floor(32 / 5) = 6`, residue `s = 11` passes that narrower zero test even
though a legal carry `q = 5 < a` crosses the half-word boundary.  Thus the
rounding convention is mathematically material.
-/
theorem ceilRoundedLogLog_counterexample :
    paperStepSixFlag 5 3 11 = false ∧
      5 < paperWidth 5 / 5 ∧
      carryVulnerable (paperWidth 5) (paperWidth 5 / 5) 11 ∧
      modularTopBit (paperWidth 5) (11 + 5) ≠
        modularTopBit (paperWidth 5) 11 := by
  constructor
  · native_decide
  constructor
  · norm_num [paperWidth]
  constructor
  · norm_num [carryVulnerable, paperWidth]
  · native_decide

end SimonDCP.Arithmetic.LemmaThreeStepSixBitBridge
