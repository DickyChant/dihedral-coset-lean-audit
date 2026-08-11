import SimonDCP.Probability.LemmaThreeBornBounds

/-!
# Postselection bounds for a repaired Lemma 3

Postselection divides the joint mass of acceptance and failure by the
acceptance mass.  Consequently, a small joint bad mass remains small only when
the acceptance probability has a quantitative positive lower bound.

This file records that bookkeeping exactly for finite real-weighted spaces.
It also gives two parameter specializations used by the Lemma 3 repair:

* a `2^(-3n)` exact-residue joint bound remains at most `2^(-n)` after an
  inverse-polynomial postselection, under an explicit polynomial-versus-
  exponential inequality;
* an `n^(-3)` joint bound and acceptance at least `n^(-1)` give a conditional
  bound of `n^(-2)`.

No independence assumption is used.
-/

namespace SimonDCP.Probability.LemmaThreePostselection

open scoped BigOperators
open SimonDCP.Probability.LemmaThreeBornBounds

/-- The mass of the postselection event in a finite real-weighted space. -/
noncomputable def finiteAcceptanceMass
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept : Omega -> Prop) : Real :=
  realFiniteMass weight accept

/-- The joint mass of postselection and the bad event. -/
noncomputable def finiteJointBadMass
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop) : Real :=
  realFiniteMass weight fun omega => accept omega ∧ bad omega

/-- The bad mass conditioned on acceptance, defined by the exact finite-mass
ratio.  Applications should supply a positive lower bound on the denominator. -/
noncomputable def finiteConditionalBadMass
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop) : Real :=
  finiteJointBadMass weight accept bad / finiteAcceptanceMass weight accept

/-- Unfolding conditional bad mass gives joint bad mass divided by acceptance
mass exactly. -/
theorem finiteConditionalBadMass_eq_joint_div_accept
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop) :
    finiteConditionalBadMass weight accept bad =
      finiteJointBadMass weight accept bad /
        finiteAcceptanceMass weight accept :=
  rfl

/-- A finite event has nonnegative real mass when every point weight is
nonnegative. -/
theorem realFiniteMass_nonneg
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (event : Omega -> Prop)
    (hWeight : ∀ omega, 0 <= weight omega) :
    0 <= realFiniteMass weight event := by
  classical
  unfold realFiniteMass
  apply Finset.sum_nonneg
  intro omega _
  by_cases hEvent : event omega
  · simpa [hEvent] using hWeight omega
  · simp [hEvent]

/-- Abstract joint-to-conditional estimate.  If the acceptance mass is at
least `rho > 0` and the joint bad mass is at most `bound`, division loses at
most the factor `1 / rho`. -/
theorem jointBadMass_div_acceptMass_le
    (jointBadMass acceptMass bound rho : Real)
    (hJointNonneg : 0 <= jointBadMass)
    (hJoint : jointBadMass <= bound)
    (hRho : 0 < rho)
    (hAccept : rho <= acceptMass) :
    jointBadMass / acceptMass <= bound / rho := by
  have hAcceptPos : 0 < acceptMass := lt_of_lt_of_le hRho hAccept
  have hBoundNonneg : 0 <= bound := le_trans hJointNonneg hJoint
  calc
    jointBadMass / acceptMass <= bound / acceptMass :=
      (div_le_div_iff_of_pos_right hAcceptPos).2 hJoint
    _ <= bound / rho :=
      div_le_div_of_nonneg_left hBoundNonneg hRho hAccept

/-- Finite-space joint-to-conditional bound.  Normalization of `weight` is not
needed for this algebraic implication; applications may provide it separately
when interpreting the masses as probabilities. -/
theorem finiteConditionalBadMass_le_bound_div_rho
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (bound rho : Real)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hJoint : finiteJointBadMass weight accept bad <= bound)
    (hRho : 0 < rho)
    (hAccept : rho <= finiteAcceptanceMass weight accept) :
    finiteConditionalBadMass weight accept bad <= bound / rho := by
  rw [finiteConditionalBadMass_eq_joint_div_accept]
  apply jointBadMass_div_acceptMass_le
  · exact realFiniteMass_nonneg weight (fun omega => accept omega ∧ bad omega)
      hWeight
  · exact hJoint
  · exact hRho
  · exact hAccept

/-- Exact arithmetic behind the dyadic specialization.  The explicit premise
`n^degree <= 2^(2n)` is precisely what is needed to absorb an inverse-
polynomial acceptance loss into the gap between `2^(-3n)` and `2^(-n)`. -/
theorem dyadicJoint_div_inversePolynomial_le
    (n degree : Nat) (hn : 0 < n)
    (hPolynomial : (n : Real) ^ degree <= (2 : Real) ^ (2 * n)) :
    (1 / (2 : Real) ^ (3 * n)) / (1 / (n : Real) ^ degree) <=
      1 / (2 : Real) ^ n := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hnPow : 0 < (n : Real) ^ degree := pow_pos hnReal degree
  have hTwo : (0 : Real) < 2 := by norm_num
  have hTwoThree : 0 < (2 : Real) ^ (3 * n) := pow_pos hTwo _
  calc
    (1 / (2 : Real) ^ (3 * n)) / (1 / (n : Real) ^ degree) =
        (n : Real) ^ degree / (2 : Real) ^ (3 * n) := by
      field_simp [ne_of_gt hnPow, ne_of_gt hTwoThree]
    _ <= (2 : Real) ^ (2 * n) / (2 : Real) ^ (3 * n) :=
      (div_le_div_iff_of_pos_right hTwoThree).2 hPolynomial
    _ = 1 / (2 : Real) ^ n := by
      rw [show 3 * n = 2 * n + n by omega, pow_add]
      field_simp

/-- An exact-residue joint bad mass of at most `2^(-3n)` remains at most
`2^(-n)` after conditioning on an event of mass at least `n^(-degree)`, under
the displayed explicit arithmetic premise. -/
theorem finiteConditionalBadMass_le_dyadic
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (n degree : Nat) (hn : 0 < n)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hAccept : 1 / (n : Real) ^ degree <=
      finiteAcceptanceMass weight accept)
    (hJoint : finiteJointBadMass weight accept bad <=
      1 / (2 : Real) ^ (3 * n))
    (hPolynomial : (n : Real) ^ degree <= (2 : Real) ^ (2 * n)) :
    finiteConditionalBadMass weight accept bad <=
      1 / (2 : Real) ^ n := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hRho : 0 < 1 / (n : Real) ^ degree := by positivity
  exact (finiteConditionalBadMass_le_bound_div_rho
    weight accept bad (1 / (2 : Real) ^ (3 * n))
      (1 / (n : Real) ^ degree) hWeight hJoint hRho hAccept).trans
    (dyadicJoint_div_inversePolynomial_le n degree hn hPolynomial)

/-- Exact arithmetic for the bucket specialization:
`n^(-3) / n^(-1) = n^(-2)` for positive `n`. -/
theorem inverseCube_div_inverse_eq_inverseSquare
    (n : Nat) (hn : 0 < n) :
    (1 / (n : Real) ^ 3) / (1 / (n : Real)) =
      1 / (n : Real) ^ 2 := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  field_simp [ne_of_gt hnReal]

/-- A joint bad mass of at most `n^(-3)` and acceptance mass at least
`n^(-1)` give conditional bad mass at most `n^(-2)` exactly. -/
theorem finiteConditionalBadMass_le_inverseSquare
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Real) (accept bad : Omega -> Prop)
    (n : Nat) (hn : 0 < n)
    (hWeight : ∀ omega, 0 <= weight omega)
    (hAccept : 1 / (n : Real) <= finiteAcceptanceMass weight accept)
    (hJoint : finiteJointBadMass weight accept bad <=
      1 / (n : Real) ^ 3) :
    finiteConditionalBadMass weight accept bad <=
      1 / (n : Real) ^ 2 := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hRho : 0 < 1 / (n : Real) := by positivity
  calc
    finiteConditionalBadMass weight accept bad <=
        (1 / (n : Real) ^ 3) / (1 / (n : Real)) :=
      finiteConditionalBadMass_le_bound_div_rho
        weight accept bad (1 / (n : Real) ^ 3) (1 / (n : Real))
          hWeight hJoint hRho hAccept
    _ = 1 / (n : Real) ^ 2 :=
      inverseCube_div_inverse_eq_inverseSquare n hn

end SimonDCP.Probability.LemmaThreePostselection
