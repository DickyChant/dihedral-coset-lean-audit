import SimonDCP.Probability.LemmaThreePostselection

/-!
# Exponent slack for Lemma 3 postselection

Conditioning on an event of inverse-polynomial mass does not preserve the
literal exponent in a dyadic joint bound.  It does preserve exponential
negligibility when the joint bound reserves enough exponent slack.

Concretely, a joint bad mass at most `2^(-(kept + slack))`, an acceptance
mass at least `n^(-degree)`, and the explicit arithmetic premise
`n^degree <= 2^slack` imply conditional bad mass at most `2^(-kept)`.
The last theorem instantiates this bookkeeping with `kept = n / 2` and
`slack = n - n / 2`: an inverse-polynomial postselection therefore turns a
joint `2^(-n)` bound into a conditional `2^(-floor(n / 2))` bound whenever
the displayed polynomial-versus-exponential premise holds.
-/

namespace SimonDCP.Probability.LemmaThreePostselectionSlack

open SimonDCP.Probability.LemmaThreePostselection

/-- Exact arithmetic for absorbing an inverse-polynomial conditioning loss
into an explicitly reserved dyadic exponent slack. -/
theorem dyadicExponentSlack_div_inversePolynomial_le
    (n degree kept slack : Nat) (hn : 0 < n)
    (hPolynomial : (n : Real) ^ degree <= (2 : Real) ^ slack) :
    (1 / (2 : Real) ^ (kept + slack)) /
        (1 / (n : Real) ^ degree) <=
      1 / (2 : Real) ^ kept := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hnPow : 0 < (n : Real) ^ degree := pow_pos hnReal degree
  have hTwo : (0 : Real) < 2 := by norm_num
  have hTwoTotal : 0 < (2 : Real) ^ (kept + slack) := pow_pos hTwo _
  calc
    (1 / (2 : Real) ^ (kept + slack)) /
          (1 / (n : Real) ^ degree) =
        (n : Real) ^ degree / (2 : Real) ^ (kept + slack) := by
      field_simp [ne_of_gt hnPow, ne_of_gt hTwoTotal]
    _ <= (2 : Real) ^ slack / (2 : Real) ^ (kept + slack) :=
      (div_le_div_iff_of_pos_right hTwoTotal).2 hPolynomial
    _ = 1 / (2 : Real) ^ kept := by
      rw [pow_add]
      field_simp

/-- A joint dyadic bound with `slack` reserved exponent bits remains a
`kept`-bit dyadic bound after inverse-polynomial postselection. -/
theorem finiteConditionalBadMass_le_of_exponentSlack
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (n degree kept slack : Nat) (hn : 0 < n)
    (hWeight : forall omega, 0 <= weight omega)
    (hAccept : 1 / (n : Real) ^ degree <=
      finiteAcceptanceMass weight accept)
    (hJoint : finiteJointBadMass weight accept bad <=
      1 / (2 : Real) ^ (kept + slack))
    (hPolynomial : (n : Real) ^ degree <= (2 : Real) ^ slack) :
    finiteConditionalBadMass weight accept bad <=
      1 / (2 : Real) ^ kept := by
  have hRho : 0 < 1 / (n : Real) ^ degree := by
    have hnReal : (0 : Real) < n := by exact_mod_cast hn
    positivity
  exact (finiteConditionalBadMass_le_bound_div_rho
    weight accept bad (1 / (2 : Real) ^ (kept + slack))
      (1 / (n : Real) ^ degree) hWeight hJoint hRho hAccept).trans
    (dyadicExponentSlack_div_inversePolynomial_le
      n degree kept slack hn hPolynomial)

/-- A version whose joint premise is stated with a single total exponent.
The equality `kept + slack = total` records how much of that exponent is
retained after conditioning and how much is spent on postselection. -/
theorem finiteConditionalBadMass_le_of_splitExponent
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (n degree total kept slack : Nat) (hn : 0 < n)
    (hSplit : kept + slack = total)
    (hWeight : forall omega, 0 <= weight omega)
    (hAccept : 1 / (n : Real) ^ degree <=
      finiteAcceptanceMass weight accept)
    (hJoint : finiteJointBadMass weight accept bad <=
      1 / (2 : Real) ^ total)
    (hPolynomial : (n : Real) ^ degree <= (2 : Real) ^ slack) :
    finiteConditionalBadMass weight accept bad <=
      1 / (2 : Real) ^ kept := by
  apply finiteConditionalBadMass_le_of_exponentSlack
    weight accept bad n degree kept slack hn hWeight hAccept
  · simpa only [hSplit] using hJoint
  · exact hPolynomial

/-- Half-exponent specialization of a joint `2^(-n)` estimate.  The retained
exponent is `floor (n / 2)`; the complementary exponent pays exactly for the
inverse-polynomial postselection loss. -/
theorem finiteConditionalBadMass_le_halfExponent
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (n degree : Nat) (hn : 0 < n)
    (hWeight : forall omega, 0 <= weight omega)
    (hAccept : 1 / (n : Real) ^ degree <=
      finiteAcceptanceMass weight accept)
    (hJoint : finiteJointBadMass weight accept bad <=
      1 / (2 : Real) ^ n)
    (hPolynomial : (n : Real) ^ degree <=
      (2 : Real) ^ (n - n / 2)) :
    finiteConditionalBadMass weight accept bad <=
      1 / (2 : Real) ^ (n / 2) := by
  have hSplit : n / 2 + (n - n / 2) = n :=
    Nat.add_sub_of_le (Nat.div_le_self n 2)
  exact finiteConditionalBadMass_le_of_splitExponent
    weight accept bad n degree n (n / 2) (n - n / 2) hn hSplit
      hWeight hAccept hJoint hPolynomial

end SimonDCP.Probability.LemmaThreePostselectionSlack
