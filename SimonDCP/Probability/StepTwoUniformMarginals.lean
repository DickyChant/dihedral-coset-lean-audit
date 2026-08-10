import SimonDCP.Probability.SimultaneousLocalInjectivity
import SimonDCP.Probability.StepTwoMeasurementBridge

/-!
# Uniform local marginals after the Step-2 quotient

The Fourier labels before Step 2 are sampled uniformly from the full function
space `I -> ZMod (2 ^ n)`.  Step 2 keeps only their images under `lowBitsHom`.
This file proves that every finite restriction of the reduced label vector is
still exactly uniform.

The proof is finite counting.  A surjective additive homomorphism between
finite additive groups has equicardinal fibres, so the pushforward of the
uniform law is uniform.  The local map used here first applies `lowBitsHom`
coordinatewise and then restricts to a prescribed coordinate set.
-/

namespace SimonDCP.Probability.StepTwoUniformMarginals

open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Probability.ProjectionInjectivity
open SimonDCP.Probability.SimultaneousLocalInjectivity
open SimonDCP.Probability.StepTwoMeasurementBridge
open SimonDCP.Probability.TernaryProjectionBridge
open SimonDCP.Probability.TernarySubsetSumBound

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The uniform rational weight on the full `n`-bit Fourier-label space. -/
noncomputable def uniformFullFourierWeight
    (n : Nat) (_sample : I -> ZMod (2 ^ n)) : Rat :=
  1 / (Fintype.card (I -> ZMod (2 ^ n)) : Rat)

/-- The denominator of the full Fourier-label law is `(2 ^ n) ^ |I|`. -/
theorem uniformFullFourierWeight_eq
    (n : Nat) (sample : I -> ZMod (2 ^ n)) :
    uniformFullFourierWeight n sample =
      (1 : Rat) / (((2 ^ n : Nat) : Rat) ^ Fintype.card I) := by
  simp [uniformFullFourierWeight]

/-- Real-valued form of the same normalization, matching the Born-weight
normalization used by the quantum model. -/
theorem uniformFullFourierWeight_cast_real
    (n : Nat) (sample : I -> ZMod (2 ^ n)) :
    (uniformFullFourierWeight n sample : Real) =
      ((((2 ^ n : Nat) : Real)⁻¹) ^ Fintype.card I) := by
  rw [uniformFullFourierWeight_eq]
  push_cast
  simp [one_div, inv_pow]

/-- Apply the Step-2 low-bit quotient coordinatewise and restrict to `fixed`. -/
def restrictedLowBitsHom (n : Nat) (fixed : Finset I) :
    (I -> ZMod (2 ^ n)) →+ (fixed -> ZMod (2 ^ (n - 1))) where
  toFun sample i := lowBitsHom n (sample i)
  map_zero' := by
    funext i
    simp
  map_add' left right := by
    funext i
    exact map_add (lowBitsHom n) (left i) (right i)

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem restrictedLowBitsHom_apply
    (n : Nat) (fixed : Finset I) (sample : I -> ZMod (2 ^ n)) :
    restrictedLowBitsHom n fixed sample =
      restrictedSample fixed (fun i => lowBitsHom n (sample i)) :=
  rfl

omit [Fintype I] in
/-- Every prescribed local low-bit vector has a full `n`-bit lift. -/
theorem restrictedLowBitsHom_surjective (n : Nat) (fixed : Finset I) :
    Function.Surjective (restrictedLowBitsHom n fixed) := by
  classical
  have hLow : Function.Surjective (lowBitsHom n) :=
    ZMod.castHom_surjective (pow_dvd_pow 2 (Nat.sub_le n 1))
  intro target
  choose lift hLift using fun i : fixed => hLow (target i)
  let sample : I -> ZMod (2 ^ n) := fun i =>
    if hi : i ∈ fixed then lift ⟨i, hi⟩ else 0
  refine ⟨sample, ?_⟩
  funext i
  change lowBitsHom n (sample i) = target i
  rw [show sample i = lift i from by simp [sample, i.2]]
  exact hLift i

section UniformPushforward

variable {Omega H : Type*}
  [Fintype Omega] [DecidableEq Omega] [AddCommGroup Omega]
  [Fintype H] [DecidableEq H] [AddCommGroup H]

/-- A surjective additive homomorphism sends the uniform law on a finite
additive group to the uniform law on its codomain. -/
theorem finiteMass_uniform_preimage_eq
    (hom : Omega →+ H) (hSurjective : Function.Surjective hom)
    (event : Finset H) :
    finiteMass
        (fun _ : Omega => 1 / (Fintype.card Omega : Rat))
        (fun omega => hom omega ∈ event) =
      (event.card : Rat) / (Fintype.card H : Rat) := by
  classical
  let occurs : Omega -> Prop := fun omega => hom omega ∈ event
  let fibreCard : Nat :=
    (Finset.univ.filter fun omega : Omega => hom omega = 0).card
  have hFibreCard (value : H) :
      (Finset.univ.filter fun omega : Omega => hom omega = value).card =
        fibreCard := by
    exact hom_fiber_card_eq_of_surjective hom hSurjective value 0
  have hEventCard :
      (Finset.univ.filter occurs).card =
        event.card * fibreCard := by
    dsimp only [occurs]
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ event hom]
    simp_rw [hFibreCard]
    simp
  have hTotalCard : Fintype.card Omega = Fintype.card H * fibreCard := by
    have hMaps :
        (↑(Finset.univ : Finset Omega) : Set Omega).MapsTo hom
          (↑(Finset.univ : Finset H) : Set H) := by
      simp
    rw [Fintype.card, Finset.card_eq_sum_card_fiberwise hMaps]
    simp_rw [hFibreCard]
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ]
  have hFibrePositive : 0 < fibreCard := by
    obtain ⟨omega, homega⟩ := hSurjective 0
    have : omega ∈ Finset.univ.filter fun x : Omega => hom x = 0 := by
      simp [homega]
    exact Finset.card_pos.mpr ⟨omega, this⟩
  change finiteMass
      (fun _ : Omega => 1 / (Fintype.card Omega : Rat)) occurs = _
  unfold finiteMass
  change (∑ omega,
      @ite Rat (occurs omega) (Classical.propDecidable _)
        (1 / (Fintype.card Omega : Rat)) 0) = _
  have hFilterSum :
      (∑ omega ∈ (Finset.univ.filter occurs),
        1 / (Fintype.card Omega : Rat)) =
      ∑ omega,
        @ite Rat (occurs omega) (Classical.propDecidable _)
          (1 / (Fintype.card Omega : Rat)) 0 := by
    convert Finset.sum_filter occurs
      (fun _ : Omega => 1 / (Fintype.card Omega : Rat)) using 1
    apply Finset.sum_congr rfl
    intro omega _homega
    by_cases homega : occurs omega <;> simp [homega]
  rw [← hFilterSum]
  simp only [Finset.sum_const, nsmul_eq_mul, hEventCard, hTotalCard]
  push_cast
  field_simp

end UniformPushforward

section MarginalLift

variable {Omega Auxiliary G : Type*}
  [Fintype Omega] [Fintype Auxiliary]
  [Fintype G] [DecidableEq G]

/-- Adding finite auxiliary randomness preserves uniform local marginals when
the joint weight has the original sample weight as its first marginal.

This is the interface needed when the outer outcome records both the full
Fourier vector and a subsequently measured Step-2 residue. -/
theorem hasUniformLocalMarginals_prod_of_first_marginal
    (family : Finset (Finset I))
    (baseWeight : Omega -> Rat) (sample : Omega -> I -> G)
    (jointWeight : Omega × Auxiliary -> Rat)
    (hMarginal : forall omega,
      (∑ auxiliary, jointWeight (omega, auxiliary)) = baseWeight omega)
    (hUniform : HasUniformLocalMarginals family baseWeight sample) :
    HasUniformLocalMarginals family jointWeight
      (fun outcome => sample outcome.1) := by
  intro fixed hfixed event
  rw [← hUniform fixed hfixed event]
  unfold finiteMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro omega _homega
  by_cases hEvent : restrictedSample fixed (sample omega) ∈ event
  · simp only [hEvent, if_true]
    exact hMarginal omega
  · simp only [hEvent, if_false]
    simp

end MarginalLift

/-- Every local restriction of a uniformly sampled full Fourier vector remains
uniform after Step 2 forgets the highest bit of each coordinate. -/
theorem hasUniformLocalMarginals_lowBits
    (n : Nat) (_hn : 0 < n) (family : Finset (Finset I)) :
    HasUniformLocalMarginals family
      (uniformFullFourierWeight (I := I) n)
      (fun sample i => lowBitsHom n (sample i)) := by
  intro fixed _hfixed event
  change finiteMass
      (fun _ : I -> ZMod (2 ^ n) =>
        1 / (Fintype.card (I -> ZMod (2 ^ n)) : Rat))
      (fun sample => restrictedLowBitsHom n fixed sample ∈ event) = _
  exact finiteMass_uniform_preimage_eq
    (restrictedLowBitsHom n fixed)
    (restrictedLowBitsHom_surjective n fixed) event

end SimonDCP.Probability.StepTwoUniformMarginals
