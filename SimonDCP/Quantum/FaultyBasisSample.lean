import SimonDCP.Quantum.FourierShift
import QuantumAlg.Core.Base.Measurement
import QuantumAlg.Core.Components.Gates

/-!
# Local Fourier behavior of a faulty basis sample

A faulty sample in Step 1 of the preprint is a computational-basis state
`|b, x⟩`, rather than a coherent coset state.  This file records its exact
local behavior under the two transforms used later in the algorithm.

After the normalized `ZMod N` DFT on the position coordinate, the branch bit
remains fixed and every Fourier outcome `y` has probability `1 / N`.  The
input position `x` appears only through the unit-modulus character
`stdAddChar (-(x * y))`.

Independently, applying a Hadamard gate to the fixed branch bit gives each
output bit probability `1 / 2`.  The fixed input bit contributes only the
unit-modulus sign `(-1)^(b d)` to the amplitude.  Once `d` is fixed by a
measurement, this sign is common to every other coherent coordinate.
-/

namespace SimonDCP.Quantum.FaultyBasisSample

open QuantumAlg

noncomputable section

variable {N : ℕ} [NeZero N]

/-- A local faulty-sample label consists of its fixed bit and cyclic position. -/
abbrev Label (N : ℕ) := Bool × ZMod N

/-- The finite register carrying one faulty sample. -/
abbrev faultyRegister (N : ℕ) [NeZero N] : Register where
  Index := Label N
  fintype := inferInstance
  decEq := inferInstance

/-- The computational-basis state `|b, x⟩` supplied by a faulty sampler. -/
def faultyBasisState (b : Bool) (x : ZMod N) : PureState (faultyRegister N) :=
  PureState.ket (b, x)

/-- Inverse square root of the cyclic-register dimension. -/
def invSqrtModulus (N : ℕ) : ℂ :=
  (Real.sqrt (N : ℝ) : ℂ)⁻¹

@[simp]
theorem norm_invSqrtModulus (N : ℕ) :
    ‖invSqrtModulus N‖ = (Real.sqrt (N : ℝ))⁻¹ := by
  rw [invSqrtModulus, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_sq_invSqrtModulus (N : ℕ) [NeZero N] :
    ‖invSqrtModulus N‖ ^ 2 = ((N : ℝ)⁻¹) := by
  rw [norm_invSqrtModulus, inv_pow, Real.sq_sqrt]
  positivity

/-- The unit-modulus position phase produced by the DFT of `|x⟩`. -/
def positionPhase (x y : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(x * y))

@[simp]
theorem norm_positionPhase (x y : ZMod N) : ‖positionPhase x y‖ = 1 := by
  rw [positionPhase, ZMod.stdAddChar_apply]
  exact Circle.norm_coe (ZMod.toCircle (-(x * y)))

/--
The normalized vector obtained by applying the `ZMod N` DFT only to the
position coordinate of `|b, x⟩`.
-/
def afterPositionDftVec (b : Bool) (x : ZMod N) :
    StateVector (faultyRegister N) :=
  WithLp.toLp 2 fun z ↦
    if z.1 = b then invSqrtModulus N * positionPhase x z.2 else 0

/-- The normalized position DFT of a faulty basis sample has unit norm. -/
theorem norm_afterPositionDftVec (b : Bool) (x : ZMod N) :
    ‖afterPositionDftVec b x‖ = 1 := by
  rw [afterPositionDftVec, EuclideanSpace.norm_eq]
  have hsum :
      ∑ z : Label N,
          ‖if z.1 = b then invSqrtModulus N * positionPhase x z.2 else 0‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    cases b <;>
      simp [norm_positionPhase, ZMod.card, NeZero.ne N]
  rw [hsum, Real.sqrt_one]

/-- The normalized pure state after the position-register DFT. -/
def afterPositionDftState (b : Bool) (x : ZMod N) :
    PureState (faultyRegister N) :=
  PureState.ofVec (afterPositionDftVec b x) (norm_afterPositionDftVec b x)

@[simp]
theorem afterPositionDftState_apply (b : Bool) (x : ZMod N)
    (z : Label N) :
    afterPositionDftState b x z =
      if z.1 = b then invSqrtModulus N * positionPhase x z.2 else 0 :=
  rfl

/-- The explicit phase is exactly the normalized Mathlib DFT of a point mass. -/
theorem afterPositionDftState_apply_eq_normalizedDft
    (b b' : Bool) (x y : ZMod N) :
    afterPositionDftState b x (b', y) =
      if b' = b then
        invSqrtModulus N *
          ZMod.dft (FourierShift.pointMass x) y
      else 0 := by
  rw [afterPositionDftState_apply, FourierShift.dft_pointMass]
  rfl

/-- The branch bit is unchanged, and each position frequency is uniform. -/
theorem probOutcome_afterPositionDft (b b' : Bool) (x y : ZMod N) :
    PureState.probOutcome (afterPositionDftState b x) (b', y) =
      if b' = b then (N : ℝ)⁻¹ else 0 := by
  change ‖afterPositionDftState b x (b', y)‖ ^ 2 = _
  rw [afterPositionDftState_apply]
  by_cases h : b' = b
  · rw [if_pos h, if_pos h, norm_mul, norm_positionPhase, mul_one,
      norm_sq_invSqrtModulus]
  · simp [h]

/-- In particular, every Fourier outcome `y` has probability exactly `1 / N`. -/
theorem probPositionOutcome_afterPositionDft (b : Bool) (x y : ZMod N) :
    PureState.probOutcome (afterPositionDftState b x) (b, y) = (N : ℝ)⁻¹ := by
  rw [probOutcome_afterPositionDft, if_pos rfl]

/-- Convert a Boolean label to the corresponding one-qubit basis index. -/
def bitIndex (b : Bool) : Fin (2 ^ 1) :=
  if b then 1 else 0

/-- The one-qubit computational state representing a fixed faulty branch bit. -/
def fixedBitState (b : Bool) : PureState (Qubits 1) :=
  PureState.ket (bitIndex b)

/-- The phase contributed by a fixed input bit to Hadamard outcome `d`. -/
def fixedBitPhase (b d : Bool) : ℂ :=
  (-1 : ℂ) ^ (b.toNat * d.toNat)

@[simp]
theorem norm_fixedBitPhase (b d : Bool) : ‖fixedBitPhase b d‖ = 1 := by
  cases b <;> cases d <;> norm_num [fixedBitPhase]

/-- A fixed bit contributes only its sign to the normalized Hadamard amplitude. -/
theorem hadamard_fixedBitState_apply (b d : Bool) :
    Gate.H.apply (fixedBitState b) (bitIndex d) =
      PureState.invSqrt2 * fixedBitPhase b d := by
  cases b with
  | false =>
      have hstate : fixedBitState false = PureState.ket0 := rfl
      rw [hstate, Gate.H_apply_ket0]
      cases d <;> simp [bitIndex, fixedBitPhase]
  | true =>
      have hstate : fixedBitState true = PureState.ket1 := rfl
      rw [hstate, Gate.H_apply_ket1]
      cases d <;> simp [bitIndex, fixedBitPhase]

/-- The Hadamard readout of a fixed faulty branch bit is uniform. -/
theorem probOutcome_afterHadamard (b d : Bool) :
    PureState.probOutcome (Gate.H.apply (fixedBitState b)) (bitIndex d) =
      (1 / 2 : ℝ) := by
  change ‖Gate.H.apply (fixedBitState b) (bitIndex d)‖ ^ 2 = _
  rw [hadamard_fixedBitState_apply, norm_mul, norm_fixedBitPhase, mul_one,
    PureState.norm_sq_invSqrt2]
  norm_num

end

end SimonDCP.Quantum.FaultyBasisSample
