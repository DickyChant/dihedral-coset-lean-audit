import SimonDCP.Probability.LemmaOneChebyshevParameters

/-!
# Rounded parameters for the Lemma 1 repair

This file removes the power-of-two and exact-divisibility assumptions from
the parameter arithmetic used by the finite Lemma 1 model.  For a security
parameter `n`, set

* `ell = floor(log_2 n)`,
* `groupWidth = c * ell`,
* `nominalSampleCount = k * n^(c+1)`, and
* `groupCount = ceil(nominalSampleCount / groupWidth)`.

The algorithm may then collect exactly `groupCount * groupWidth` samples.
This is at least the nominal count and differs from it by less than one
group.  Choosing the floor logarithm is important: it gives
`2^groupWidth <= n^c`, and therefore preserves the paper's condition `k > c`.

The main probability lemma below also removes an artificial exact-mean
hypothesis.  A lower bound on the actual mean is enough because
`x / (x - target)^2` is decreasing for `x > target >= 0`.
-/

namespace SimonDCP.Probability.LemmaOneRoundedParameters

open SimonDCP.Probability.PairwiseBernoulliTail
open SimonDCP.Probability.LemmaOneChebyshevParameters

/-- Above a nonnegative target, the Chebyshev ratio is antitone in the mean. -/
theorem mean_div_gap_sq_antitone
    (target referenceMean actualMean : Rat)
    (hTarget : 0 <= target)
    (hReference : target < referenceMean)
    (hMean : referenceMean <= actualMean) :
    actualMean / (actualMean - target) ^ 2 <=
      referenceMean / (referenceMean - target) ^ 2 := by
  have hActual : target < actualMean := hReference.trans_le hMean
  have hReferenceNonneg : 0 <= referenceMean :=
    hTarget.trans hReference.le
  have hActualNonneg : 0 <= actualMean := hReferenceNonneg.trans hMean
  have hProduct : target ^ 2 <= actualMean * referenceMean := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMean) hReferenceNonneg,
      sq_nonneg (referenceMean - target)]
  rw [div_le_div_iff₀
    (sq_pos_of_pos (sub_pos.mpr hActual))
    (sq_pos_of_pos (sub_pos.mpr hReference))]
  have hFactor :
      0 <= (actualMean - referenceMean) *
        (actualMean * referenceMean - target ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hMean) (sub_nonneg.mpr hProduct)
  nlinarith

/-- Pairwise Bernoulli Chebyshev with only a lower bound on the actual mean.

This is the rounded replacement for an exact identity between the number of
groups and the paper's reference mean.
-/
theorem lowerTailMass_le_reference_mean_ratio
    {Omega : Type*} [Fintype Omega] (G : Nat)
    (weight : Omega -> Rat) (indicator : Fin G -> Omega -> Rat)
    (p target referenceMean : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hNormalized : Finset.univ.sum weight = 1)
    (hIdempotent : forall i omega,
      indicator i omega * indicator i omega = indicator i omega)
    (hIndicatorMean : forall i, weightedMean weight (indicator i) = p)
    (hPair : forall i j, Ne i j ->
      weightedMean weight (fun omega => indicator i omega * indicator j omega) =
        p ^ 2)
    (hp : 0 <= p)
    (hTarget : 0 <= target)
    (hReference : target < referenceMean)
    (hMean : referenceMean <= (G : Rat) * p) :
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
      referenceMean / (referenceMean - target) ^ 2 := by
  calc
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
        ((G : Rat) * p) / ((G : Rat) * p - target) ^ 2 :=
      lowerTailMass_le_mean_div_gap_sq G weight indicator p target hWeight
        hNormalized hIdempotent hIndicatorMean hPair hp
        (hReference.trans_le hMean)
    _ <= referenceMean / (referenceMean - target) ^ 2 :=
      mean_div_gap_sq_antitone target referenceMean ((G : Rat) * p)
        hTarget hReference hMean

/-- The paper-shaped lower-tail bound when the actual mean is at least, but
need not equal, `(k / c) * (n / L)`. -/
theorem lowerTailMass_le_paper_bound_of_mean_ge
    {Omega : Type*} [Fintype Omega] (G : Nat)
    (weight : Omega -> Rat) (indicator : Fin G -> Omega -> Rat)
    (p target k c n L : Rat)
    (hWeight : forall omega, 0 <= weight omega)
    (hNormalized : Finset.univ.sum weight = 1)
    (hIdempotent : forall i omega,
      indicator i omega * indicator i omega = indicator i omega)
    (hIndicatorMean : forall i, weightedMean weight (indicator i) = p)
    (hPair : forall i j, Ne i j ->
      weightedMean weight (fun omega => indicator i omega * indicator j omega) =
        p ^ 2)
    (hp : 0 <= p)
    (hTargetParameters : target = n / L)
    (hMeanLower : (k / c) * (n / L) <= (G : Rat) * p)
    (hc : 0 < c) (hn : 0 < n) (hL : 0 < L) (hkc : c < k) :
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
      (k * c / (k - c) ^ 2) * (L / n) := by
  let referenceMean : Rat := (k / c) * (n / L)
  have hTargetNonneg : 0 <= target := by
    rw [hTargetParameters]
    exact (div_pos hn hL).le
  have hTargetBelow : target < referenceMean := by
    dsimp [referenceMean]
    rw [hTargetParameters]
    have hncL : 0 < n / (c * L) := div_pos hn (mul_pos hc hL)
    calc
      n / L = c * (n / (c * L)) := by field_simp
      _ < k * (n / (c * L)) := mul_lt_mul_of_pos_right hkc hncL
      _ = (k / c) * (n / L) := by field_simp
  calc
    eventMass weight (fun omega => indicatorSum G indicator omega < target) <=
        referenceMean / (referenceMean - target) ^ 2 :=
      lowerTailMass_le_reference_mean_ratio G weight indicator p target
        referenceMean hWeight hNormalized hIdempotent hIndicatorMean hPair hp
        hTargetNonneg hTargetBelow hMeanLower
    _ = (k * c / (k - c) ^ 2) * (L / n) :=
      paper_chebyshev_ratio referenceMean target k c n L rfl
        hTargetParameters hc hn hL hkc

/-- `floor(log_2 n)`, the integer logarithm used for rounding group widths. -/
def roundedLog (n : Nat) : Nat := Nat.log 2 n

/-- The integer width of one group. -/
def roundedGroupWidth (c n : Nat) : Nat := c * roundedLog n

/-- The paper's nominal polynomial sample count. -/
def nominalSampleCount (k c n : Nat) : Nat := k * n ^ (c + 1)

/-- The least number of complete groups covering the nominal sample count. -/
def roundedGroupCount (k c n : Nat) : Nat :=
  nominalSampleCount k c n ⌈/⌉ roundedGroupWidth c n

/-- The actual sample count after rounding up to a complete group. -/
def roundedSampleCount (k c n : Nat) : Nat :=
  roundedGroupCount k c n * roundedGroupWidth c n

/-- The rounded group width is positive for `n >= 2` and `c > 0`. -/
theorem roundedGroupWidth_pos (c n : Nat) (hc : 0 < c) (hn : 2 <= n) :
    0 < roundedGroupWidth c n := by
  exact Nat.mul_pos hc (Nat.log_pos (by norm_num) hn)

/-- Ceiling division makes the rounded sample count cover the nominal one. -/
theorem nominalSampleCount_le_roundedSampleCount
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n) :
    nominalSampleCount k c n <= roundedSampleCount k c n := by
  have hm : 0 < roundedGroupWidth c n :=
    roundedGroupWidth_pos c n hc hn
  have hCover :
      nominalSampleCount k c n <=
        roundedGroupWidth c n * roundedGroupCount k c n := by
    exact (ceilDiv_le_iff_le_mul hm).1 le_rfl
  simpa [roundedSampleCount, Nat.mul_comm] using hCover

/-- Rounding up adds strictly less than one complete group of samples. -/
theorem roundedSampleCount_lt_nominal_add_width
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n) :
    roundedSampleCount k c n <
      nominalSampleCount k c n + roundedGroupWidth c n := by
  have hm : 0 < roundedGroupWidth c n :=
    roundedGroupWidth_pos c n hc hn
  rw [roundedSampleCount, roundedGroupCount, Nat.ceilDiv_eq_add_pred_div]
  calc
    ((nominalSampleCount k c n + roundedGroupWidth c n - 1) /
          roundedGroupWidth c n) * roundedGroupWidth c n <=
        nominalSampleCount k c n + roundedGroupWidth c n - 1 :=
      Nat.div_mul_le_self _ _
    _ < nominalSampleCount k c n + roundedGroupWidth c n := by omega

/-- The number of rounded groups is no larger than the nominal sample count. -/
theorem roundedGroupCount_le_nominalSampleCount
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n) :
    roundedGroupCount k c n <= nominalSampleCount k c n := by
  have hm : 0 < roundedGroupWidth c n :=
    roundedGroupWidth_pos c n hc hn
  apply (ceilDiv_le_iff_le_mul hm).2
  have hmOne : 1 <= roundedGroupWidth c n := by omega
  calc
    nominalSampleCount k c n = 1 * nominalSampleCount k c n := by simp
    _ <= roundedGroupWidth c n * nominalSampleCount k c n :=
      Nat.mul_le_mul_right _ hmOne

/-- The floor-logarithmic group width satisfies the key power bound
`2^groupWidth <= n^c`. -/
theorem pow_roundedGroupWidth_le (c n : Nat) (hn : 2 <= n) :
    2 ^ roundedGroupWidth c n <= n ^ c := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 2 ^ roundedLog n <= n := by
    exact Nat.pow_log_le_self 2 hn0
  rw [roundedGroupWidth, roundedLog, Nat.mul_comm c (Nat.log 2 n), pow_mul]
  exact Nat.pow_le_pow_left hlog c

/-- A reusable arithmetic lemma: ceiling-division coverage and
`2^m <= n^c` imply the desired lower bound on the all-zero-group mean. -/
theorem mean_ge_reference_of_cover
    (K Q m k c n L : Nat)
    (hc : 0 < c) (hL : 0 < L)
    (hWidth : m = c * L)
    (hSamples : Q = k * n ^ (c + 1))
    (hCover : Q <= m * K)
    (hPower : 2 ^ m <= n ^ c) :
    ((k : Rat) / (c : Rat)) * ((n : Rat) / (L : Rat)) <=
      (K : Rat) * (1 / 2 : Rat) ^ m := by
  have hCrossNat : k * n * 2 ^ m <= K * c * L := by
    calc
      k * n * 2 ^ m <= k * n * n ^ c :=
        Nat.mul_le_mul_left (k * n) hPower
      _ = k * n ^ (c + 1) := by
        rw [pow_succ]
        ring
      _ = Q := hSamples.symm
      _ <= m * K := hCover
      _ = K * c * L := by rw [hWidth]; ring
  have hCrossRat :
      (k : Rat) * (n : Rat) * (2 : Rat) ^ m <=
        (K : Rat) * (c : Rat) * (L : Rat) := by
    exact_mod_cast hCrossNat
  have hcRat : (0 : Rat) < (c : Rat) := by exact_mod_cast hc
  have hLRat : (0 : Rat) < (L : Rat) := by exact_mod_cast hL
  rw [one_div_pow]
  rw [show
      ((k : Rat) / (c : Rat)) * ((n : Rat) / (L : Rat)) =
        ((k : Rat) * (n : Rat)) / ((c : Rat) * (L : Rat)) by ring]
  rw [show
      (K : Rat) * (1 / (2 : Rat) ^ m) =
        (K : Rat) / (2 : Rat) ^ m by ring]
  rw [div_le_div_iff₀ (mul_pos hcRat hLRat) (pow_pos (by norm_num) m)]
  nlinarith

/-- The rounded group count has mean at least the paper's reference mean. -/
theorem roundedMean_ge_reference
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n) :
    ((k : Rat) / (c : Rat)) *
        ((n : Rat) / (roundedLog n : Rat)) <=
      (roundedGroupCount k c n : Rat) *
        (1 / 2 : Rat) ^ roundedGroupWidth c n := by
  have hL : 0 < roundedLog n := Nat.log_pos (by norm_num) hn
  apply mean_ge_reference_of_cover
    (roundedGroupCount k c n) (nominalSampleCount k c n)
    (roundedGroupWidth c n) k c n (roundedLog n) hc hL
  · rfl
  · rfl
  · have hm : 0 < roundedGroupWidth c n :=
      roundedGroupWidth_pos c n hc hn
    exact (ceilDiv_le_iff_le_mul hm).1 le_rfl
  · exact pow_roundedGroupWidth_le c n hn

/-- In particular, `k > c` puts the rounded expected number of all-zero
groups strictly above the target `n / floor(log_2 n)`. -/
theorem target_lt_roundedMean
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n) (hkc : c < k) :
    (n : Rat) / (roundedLog n : Rat) <
      (roundedGroupCount k c n : Rat) *
        (1 / 2 : Rat) ^ roundedGroupWidth c n := by
  have hcRat : (0 : Rat) < (c : Rat) := by exact_mod_cast hc
  have hnRat : (0 : Rat) < (n : Rat) := by positivity
  have hLRat : (0 : Rat) < (roundedLog n : Rat) := by
    exact_mod_cast Nat.log_pos (by norm_num) hn
  have hkcRat : (c : Rat) < (k : Rat) := by exact_mod_cast hkc
  apply lt_of_lt_of_le _ (roundedMean_ge_reference k c n hc hn)
  have hRatio : 1 < (k : Rat) / (c : Rat) :=
    (lt_div_iff₀ hcRat).2 (by simpa using hkcRat)
  have hTargetPos : 0 < (n : Rat) / (roundedLog n : Rat) :=
    div_pos hnRat hLRat
  nlinarith

/-- A coarse polynomial budget implies the exact rounded collision budget.

The exponent `6*c+2` comes from two group-count factors of degree `c+1`
and the elementary estimate `3^(2m) <= 2^(4m) <= n^(4c)`.
-/
theorem roundedCollisionBudget_of_polynomialBudget
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n)
    (hBudget :
      4 * k ^ 2 * n ^ (6 * c + 2) <= 2 ^ (n - 1)) :
    4 * roundedGroupCount k c n ^ 2 *
        (3 ^ (2 * roundedGroupWidth c n) - 1) <=
      2 ^ (n - 1) := by
  have hK : roundedGroupCount k c n <= nominalSampleCount k c n :=
    roundedGroupCount_le_nominalSampleCount k c n hc hn
  have hTernary :
      3 ^ (2 * roundedGroupWidth c n) - 1 <= n ^ (4 * c) := by
    have hThree :
        3 ^ (2 * roundedGroupWidth c n) <=
          2 ^ (4 * roundedGroupWidth c n) := by
      calc
        3 ^ (2 * roundedGroupWidth c n) <=
            4 ^ (2 * roundedGroupWidth c n) :=
          Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ (4 * roundedGroupWidth c n) := by
          rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]
          congr 1
          omega
    have hTwo : 2 ^ (4 * roundedGroupWidth c n) <= n ^ (4 * c) := by
      calc
        2 ^ (4 * roundedGroupWidth c n) =
            (2 ^ roundedLog n) ^ (4 * c) := by
          rw [← pow_mul]
          congr 1
          simp [roundedGroupWidth]
          ring
        _ <= n ^ (4 * c) :=
          Nat.pow_le_pow_left
            (Nat.pow_log_le_self 2 (by omega : n ≠ 0)) _
    exact (Nat.sub_le _ _).trans (hThree.trans hTwo)
  have hPolynomial :
      4 * roundedGroupCount k c n ^ 2 *
          (3 ^ (2 * roundedGroupWidth c n) - 1) <=
        4 * nominalSampleCount k c n ^ 2 * n ^ (4 * c) := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hK 2)) hTernary
  calc
    4 * roundedGroupCount k c n ^ 2 *
        (3 ^ (2 * roundedGroupWidth c n) - 1) <=
        4 * nominalSampleCount k c n ^ 2 * n ^ (4 * c) := hPolynomial
    _ = 4 * k ^ 2 * n ^ (6 * c + 2) := by
      simp only [nominalSampleCount, mul_pow]
      rw [show (n ^ (c + 1)) ^ 2 = n ^ ((c + 1) * 2) by
        rw [pow_mul]]
      rw [show
        4 * (k ^ 2 * n ^ ((c + 1) * 2)) * n ^ (4 * c) =
          4 * k ^ 2 * (n ^ ((c + 1) * 2) * n ^ (4 * c)) by ring]
      rw [← pow_add]
      rw [show (c + 1) * 2 + 4 * c = 6 * c + 2 by omega]
    _ <= 2 ^ (n - 1) := hBudget

/-- A directly checkable logarithmic condition implies the coarse polynomial
collision budget.  This exposes one explicit `sufficiently large n`
condition without any power-of-two assumption on `n`. -/
theorem polynomialCollisionBudget_of_clogBudget
    (k c n : Nat)
    (hBudget :
      3 + 2 * Nat.clog 2 k + (6 * c + 2) * Nat.clog 2 n <= n) :
    4 * k ^ 2 * n ^ (6 * c + 2) <= 2 ^ (n - 1) := by
  let vk := Nat.clog 2 k
  let vn := Nat.clog 2 n
  let degree := 6 * c + 2
  have hk : k <= 2 ^ vk := Nat.le_pow_clog (by norm_num) k
  have hn : n <= 2 ^ vn := Nat.le_pow_clog (by norm_num) n
  have hExponent : 2 + 2 * vk + degree * vn <= n - 1 := by
    dsimp [vk, vn, degree] at hBudget ⊢
    omega
  calc
    4 * k ^ 2 * n ^ (6 * c + 2) <=
        4 * (2 ^ vk) ^ 2 * (2 ^ vn) ^ degree :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hk 2))
        (Nat.pow_le_pow_left hn degree)
    _ = 2 ^ (2 + 2 * vk + degree * vn) := by
      rw [show (4 : Nat) = 2 ^ 2 by norm_num]
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      rw [show
        2 + vk * 2 + vn * degree = 2 + 2 * vk + degree * vn by
          simp [Nat.mul_comm]]
    _ <= 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hExponent

/-- The logarithmic collision condition directly supplies the exact rounded
budget used by the finite model. -/
theorem roundedCollisionBudget_of_clogBudget
    (k c n : Nat) (hc : 0 < c) (hn : 2 <= n)
    (hBudget :
      3 + 2 * Nat.clog 2 k + (6 * c + 2) * Nat.clog 2 n <= n) :
    4 * roundedGroupCount k c n ^ 2 *
        (3 ^ (2 * roundedGroupWidth c n) - 1) <=
      2 ^ (n - 1) :=
  roundedCollisionBudget_of_polynomialBudget k c n hc hn
    (polynomialCollisionBudget_of_clogBudget k c n hBudget)

section ExplicitConstants

/-- The elementary exponential estimate used for the concrete constants
`c = 12` and `k = 24`. -/
theorem thirteen_add_seventyFour_mul_le_pow_pred
    (t : Nat) (ht : 11 <= t) :
    13 + 74 * t <= 2 ^ (t - 1) + 1 := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      have hSeventyFour : 74 <= 2 ^ (t - 1) := by
        calc
          74 <= 2 ^ 10 := by norm_num
          _ <= 2 ^ (t - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      have hPower : 2 ^ t = 2 * 2 ^ (t - 1) := by
        calc
          2 ^ t = 2 ^ ((t - 1) + 1) :=
            congrArg (2 ^ ·) (by omega)
          _ = 2 ^ (t - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (t - 1) := Nat.mul_comm _ _
      calc
        13 + 74 * (t + 1) = (13 + 74 * t) + 74 := by ring
        _ <= (2 ^ (t - 1) + 1) + 2 ^ (t - 1) :=
          Nat.add_le_add ih hSeventyFour
        _ = 2 ^ t + 1 := by rw [hPower]; ring

/-- For the concrete paper-compatible choice `c = 12`, `k = 24`, every
`n >= 1024` satisfies the logarithmic collision condition. -/
theorem paperConstants_clogBudget (n : Nat) (hn : 1024 <= n) :
    3 + 2 * Nat.clog 2 24 + (6 * 12 + 2) * Nat.clog 2 n <= n := by
  let t := Nat.clog 2 n
  have ht : 10 <= t := by
    dsimp [t]
    calc
      10 = Nat.clog 2 1024 := by norm_num
      _ <= Nat.clog 2 n := Nat.clog_mono_right 2 hn
  have hConcrete : 13 + 74 * t <= n := by
    by_cases htTen : t = 10
    · subst t
      omega
    · have htEleven : 11 <= t := by omega
      have hExponential :=
        thirteen_add_seventyFour_mul_le_pow_pred t htEleven
      have hnOne : 1 < n := by omega
      have hPower : 2 ^ (t - 1) + 1 <= n := by
        have hStrict : 2 ^ (t - 1) < n := by
          dsimp [t]
          simpa [Nat.pred_eq_sub_one] using
            (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hnOne)
        omega
      exact hExponential.trans hPower
  norm_num
  exact hConcrete

/-- The same concrete constants satisfy the natural-number form of the
Chebyshev `1/4` budget for every `n >= 1024`. -/
theorem paperConstants_tailBudget (n : Nat) (hn : 1024 <= n) :
    4 * 24 * 12 * roundedLog n <= (24 - 12) ^ 2 * n := by
  have hCollision := paperConstants_clogBudget n hn
  have hLogClog : roundedLog n <= Nat.clog 2 n := by
    exact Nat.log_le_clog 2 n
  have hEight : 8 * roundedLog n <= n := by
    calc
      8 * roundedLog n <= 8 * Nat.clog 2 n :=
        Nat.mul_le_mul_left 8 hLogClog
      _ <= 13 + 74 * Nat.clog 2 n := by omega
      _ <= n := by norm_num at hCollision ⊢; exact hCollision
  norm_num at ⊢
  omega

/-- The two explicit arithmetic hypotheses needed by the rounded finite
model, packaged for `c = 12`, `k = 24`, and `n >= 1024`. -/
theorem paperConstants_parameterBudgets (n : Nat) (hn : 1024 <= n) :
    (3 + 2 * Nat.clog 2 24 + (6 * 12 + 2) * Nat.clog 2 n <= n) ∧
      (4 * 24 * 12 * roundedLog n <= (24 - 12) ^ 2 * n) :=
  ⟨paperConstants_clogBudget n hn, paperConstants_tailBudget n hn⟩

/-- In the exact form consumed by the finite model, the concrete constants
give both the rounded ternary-collision budget and the Chebyshev budget. -/
theorem paperConstants_roundedBudgets (n : Nat) (hn : 1024 <= n) :
    (4 * roundedGroupCount 24 12 n ^ 2 *
        (3 ^ (2 * roundedGroupWidth 12 n) - 1) <= 2 ^ (n - 1)) ∧
      (4 * 24 * 12 * roundedLog n <= (24 - 12) ^ 2 * n) := by
  constructor
  · exact roundedCollisionBudget_of_clogBudget 24 12 n
      (by norm_num) (by omega) (paperConstants_clogBudget n hn)
  · exact paperConstants_tailBudget n hn

end ExplicitConstants

end SimonDCP.Probability.LemmaOneRoundedParameters
