import Mathlib.Tactic

/-!
# Exact-divisibility parameters for the Lemma 1 repair

The paper uses groups of width `c * log₂ n` and takes `k * n^(c+1)`
samples, while suppressing rounding conventions.  This file treats the
explicit special case in which the security parameter itself satisfies
`n = 2^logN` and the sample count is exactly divisible by the group width.
These are stronger bookkeeping assumptions than the paper states; under them,
the rational identity for the expected number of all-zero groups is exact.

Floor and ceiling conventions are intentionally not hidden here.  The general
security-parameter case still requires a separate rounded theorem.
-/

namespace SimonDCP.Probability.LemmaOneExactParameters

/--
Exact group-count arithmetic for the repaired Lemma 1 bound.

If `n = 2^logN`, `groupWidth = c * logN`, and
`groupCount * groupWidth = k * n^(c+1)`, then the uniform all-zero mean is
exactly

`groupCount * 2^(-groupWidth) = (k / c) * (n / logN)`.
-/
theorem exactMean_of_powerOfTwo_and_exactPartition
    (groupCount groupWidth k c n logN : Nat)
    (hc : 0 < c) (hlogN : 0 < logN)
    (hn : n = 2 ^ logN)
    (hWidth : groupWidth = c * logN)
    (hPartition : groupCount * groupWidth = k * n ^ (c + 1)) :
    (groupCount : Rat) * (1 / 2 : Rat) ^ groupWidth =
      ((k : Rat) / (c : Rat)) * ((n : Rat) / (logN : Rat)) := by
  have hnPos : 0 < n := by
    rw [hn]
    exact pow_pos (by norm_num) logN
  have hcRat : (c : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hc)
  have hlogNRat : (logN : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hlogN)
  have hnRat : (n : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnPos)
  have hnCast : (n : Rat) = (2 : Rat) ^ logN := by
    exact_mod_cast hn
  have hPower : (2 : Rat) ^ groupWidth = (n : Rat) ^ c := by
    rw [hWidth, Nat.mul_comm c logN,
      pow_mul (2 : Rat) logN c, ← hnCast]
  have hWidthCast : (groupWidth : Rat) = (c : Rat) * (logN : Rat) := by
    exact_mod_cast hWidth
  have hPartitionCast :
      (groupCount : Rat) * (groupWidth : Rat) =
        (k : Rat) * (n : Rat) ^ (c + 1) := by
    exact_mod_cast hPartition
  rw [one_div_pow, hPower]
  rw [hWidthCast, pow_succ] at hPartitionCast
  field_simp [hcRat, hlogNRat, hnRat]
  nlinarith [hPartitionCast]

end SimonDCP.Probability.LemmaOneExactParameters
