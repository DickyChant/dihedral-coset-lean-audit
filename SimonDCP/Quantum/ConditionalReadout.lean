import SimonDCP.Quantum.BitReadout
import SimonDCP.Quantum.PhaseTransfer

/-!
# Conditional one-qubit phase readout

The Boolean phase-transfer identity leaves a factor depending only on measured
classical data.  That factor has complex norm one, so it is a global phase and
cannot change computational-basis Born probabilities.  Combining this fact
with the one-qubit Hadamard calculation shows that an *exactly balanced*
relative-phase state still reveals the encoded bit with certainty.

The exact balanced-state equation is an explicit premise below.  Nothing in
this file claims that the preprint's preceding conditioning argument produces
that state; establishing equal magnitudes for its two residual amplitudes is a
separate, currently unsupported obligation.
-/

namespace SimonDCP.Quantum.ConditionalReadout

open QuantumAlg

noncomputable section

/-- Multiply a pure state by a unit-modulus complex global phase. -/
def multiplyByGlobalPhase {R : Register}
    (phase : ℂ) (phaseUnit : ‖phase‖ = 1) (state : PureState R) : PureState R :=
  PureState.ofVec (phase • (state : StateVector R)) (by
    rw [norm_smul, phaseUnit, state.norm_eq_one, one_mul])

/-- The underlying vector is scalar multiplication by the global phase. -/
@[simp]
theorem multiplyByGlobalPhase_coe {R : Register}
    (phase : ℂ) (phaseUnit : ‖phase‖ = 1) (state : PureState R) :
    (multiplyByGlobalPhase phase phaseUnit state : StateVector R) =
      phase • (state : StateVector R) := rfl

/-- Pointwise amplitudes are multiplied by the same global phase. -/
@[simp]
theorem multiplyByGlobalPhase_apply {R : Register}
    (phase : ℂ) (phaseUnit : ‖phase‖ = 1) (state : PureState R)
    (x : R.Index) :
    multiplyByGlobalPhase phase phaseUnit state x = phase * state x := by
  simp [multiplyByGlobalPhase, PiLp.smul_apply, smul_eq_mul]

/-- A unit-modulus global phase does not change any computational-basis probability. -/
theorem probOutcome_multiplyByGlobalPhase {R : Register}
    (phase : ℂ) (phaseUnit : ‖phase‖ = 1) (state : PureState R)
    (x : R.Index) :
    PureState.probOutcome (multiplyByGlobalPhase phase phaseUnit state) x =
      PureState.probOutcome state x := by
  change ‖multiplyByGlobalPhase phase phaseUnit state x‖ ^ 2 = ‖state x‖ ^ 2
  rw [multiplyByGlobalPhase_apply, norm_mul, phaseUnit, one_mul]

/-- Unitary evolution commutes with multiplication by a global phase. -/
theorem gate_apply_multiplyByGlobalPhase {R : Register}
    (gate : Gate R) (phase : ℂ) (phaseUnit : ‖phase‖ = 1)
    (state : PureState R) :
    gate.apply (multiplyByGlobalPhase phase phaseUnit state) =
      multiplyByGlobalPhase phase phaseUnit (gate.apply state) := by
  apply PureState.ext
  intro x
  change (gate.applyVec (phase • (state : StateVector R))) x =
    (phase • gate.applyVec (state : StateVector R)) x
  rw [Gate.applyVec_smul]

/--
The canonical balanced state after fixing the measured XOR.  Its only
measurement-dependent factor is the unit-modulus global phase proved in
`PhaseTransfer`.
-/
def conditionalRelativePhaseState (measured dBit : Bool) :
    PureState (Qubits 1) :=
  multiplyByGlobalPhase
    (PhaseTransfer.measurementGlobalPhase measured dBit)
    (PhaseTransfer.norm_measurementGlobalPhase measured dBit)
    (BitReadout.relativePhaseState dBit)

/-- The exact balanced signed-superposition form of the conditional state. -/
theorem conditionalRelativePhaseState_vector (measured dBit : Bool) :
    (conditionalRelativePhaseState measured dBit : StateVector (Qubits 1)) =
      PhaseTransfer.measurementGlobalPhase measured dBit •
        (PureState.invSqrt2 •
          ((PureState.ket0 : StateVector (Qubits 1)) +
            ((-1 : ℂ) ^ dBit.toNat) •
              (PureState.ket1 : StateVector (Qubits 1)))) := by
  rw [conditionalRelativePhaseState, multiplyByGlobalPhase_coe,
    BitReadout.relativePhaseState_vector]

/-- The measurement-dependent global phase does not change pre-Hadamard probabilities. -/
theorem probOutcome_conditionalRelativePhaseState
    (measured dBit : Bool) (outcome : Fin (2 ^ 1)) :
    PureState.probOutcome (conditionalRelativePhaseState measured dBit) outcome =
      PureState.probOutcome (BitReadout.relativePhaseState dBit) outcome := by
  exact probOutcome_multiplyByGlobalPhase
    (PhaseTransfer.measurementGlobalPhase measured dBit)
    (PhaseTransfer.norm_measurementGlobalPhase measured dBit)
    (BitReadout.relativePhaseState dBit) outcome

/-- After Hadamard, the conditional state is a globally phased `|dBit>`. -/
theorem hadamard_conditionalRelativePhaseState (measured dBit : Bool) :
    Gate.H.apply (conditionalRelativePhaseState measured dBit) =
      multiplyByGlobalPhase
        (PhaseTransfer.measurementGlobalPhase measured dBit)
        (PhaseTransfer.norm_measurementGlobalPhase measured dBit)
        (BitReadout.computationalBitState dBit) := by
  rw [conditionalRelativePhaseState, gate_apply_multiplyByGlobalPhase,
    BitReadout.hadamard_relativePhaseState]

/-- The complete post-Hadamard distribution remains the point mass at `dBit`. -/
theorem probOutcome_afterHadamard
    (measured dBit : Bool) (outcome : Fin (2 ^ 1)) :
    PureState.probOutcome
        (Gate.H.apply (conditionalRelativePhaseState measured dBit)) outcome =
      if outcome = BitReadout.bitIndex dBit then 1 else 0 := by
  rw [hadamard_conditionalRelativePhaseState,
    probOutcome_multiplyByGlobalPhase]
  simpa using BitReadout.probOutcome_afterHadamard dBit outcome

/-- The encoded bit is read with probability one in the canonical balanced state. -/
theorem probOutcome_encodedBit (measured dBit : Bool) :
    PureState.probOutcome
        (Gate.H.apply (conditionalRelativePhaseState measured dBit))
        (BitReadout.bitIndex dBit) = 1 := by
  rw [probOutcome_afterHadamard, if_pos rfl]

/--
Conditional readout theorem with the missing balanced-relative-phase premise
exposed explicitly.  The hypothesis `balanced` is exactly what the preprint's
earlier counting and conditioning argument would have to establish.
-/
theorem readout_of_exact_balancedRelativePhase
    (observedState : PureState (Qubits 1)) (measured dBit : Bool)
    (balanced : observedState = conditionalRelativePhaseState measured dBit) :
    PureState.probOutcome (Gate.H.apply observedState)
        (BitReadout.bitIndex dBit) = 1 := by
  rw [balanced]
  exact probOutcome_encodedBit measured dBit

end

end SimonDCP.Quantum.ConditionalReadout
