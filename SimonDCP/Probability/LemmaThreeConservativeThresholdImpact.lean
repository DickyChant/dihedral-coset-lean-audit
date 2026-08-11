import SimonDCP.Probability.Lemma4Parameters

/-!
# Effect of the conservative Lemma 3 threshold on Lemma 4

`LemmaThreeAdaptiveFibreUpperBound` gives an adaptive-sector tail conditional
on explicit fine-energy normalization when a `2^(c*n)` fine space is tested at squared threshold
`2^((c+1)*n)`.  The corresponding amplitude exponent is `(c+1)*n/2`.

This module substitutes a general amplitude exponent into the corrected
deterministic calculation from `Lemma4Parameters`.  At the conservative
exponent, every `c*n` term cancels and the aggregate error exponent becomes

```text
7*n/2 + faultLoss/2 + c*logN/2.
```

It is nonnegative for the intended parameter range.  Therefore the generic
maximum-fibre repair is logically sound but cannot replace the paper's much
smaller pointwise amplitude bound in the existing Lemma 4 argument.
-/

namespace SimonDCP.Probability.LemmaThreeConservativeThresholdImpact

open SimonDCP.Probability.Lemma4Parameters

noncomputable section

/-- Corrected aggregate exponent with an arbitrary per-component amplitude
exponent replacing the paper's `3*n/2`. -/
def totalDeviationExponentWithAmplitude
    (c n logN faultLoss amplitudeExponent : Real) : Real :=
  correctedBinDeviationExponent c n logN faultLoss -
    meanExponent c n logN faultLoss + n + amplitudeExponent

theorem totalDeviationExponentWithAmplitude_eq
    (c n logN faultLoss amplitudeExponent : Real) :
    totalDeviationExponentWithAmplitude
        c n logN faultLoss amplitudeExponent =
      (c * n) / 2 + faultLoss / 2 + c * logN / 2 +
        3 * n - c * n + amplitudeExponent := by
  simp only [totalDeviationExponentWithAmplitude,
    correctedBinDeviationExponent, standardDeviationExponent, meanExponent]
  ring

/-- The amplitude exponent forced by the generic `2^(c*n)` fibre bound. -/
def conservativeAmplitudeExponent (c n : Real) : Real :=
  (c + 1) * n / 2

/-- Substitution of the conservative Lemma 3 threshold into Lemma 4. -/
theorem conservativeTotalDeviationExponent_eq
    (c n logN faultLoss : Real) :
    totalDeviationExponentWithAmplitude c n logN faultLoss
        (conservativeAmplitudeExponent c n) =
      7 * n / 2 + faultLoss / 2 + c * logN / 2 := by
  rw [totalDeviationExponentWithAmplitude_eq]
  simp only [conservativeAmplitudeExponent]
  ring

/-- In the intended nonnegative parameter range, this conservative exponent
cannot yield an exponentially decaying error term. -/
theorem conservativeTotalDeviationExponent_nonneg
    {c n logN faultLoss : Real}
    (hn : 0 <= n) (hc : 0 <= c)
    (hlogN : 0 <= logN) (hfaultLoss : 0 <= faultLoss) :
    0 <= totalDeviationExponentWithAmplitude c n logN faultLoss
      (conservativeAmplitudeExponent c n) := by
  rw [conservativeTotalDeviationExponent_eq]
  positivity

end

end SimonDCP.Probability.LemmaThreeConservativeThresholdImpact
