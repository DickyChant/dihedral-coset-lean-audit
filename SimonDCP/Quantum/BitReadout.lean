import QuantumAlg.Core.Base.Measurement
import QuantumAlg.Core.Components.Gates

/-!
# Reading a relative phase with one Hadamard gate

This file formalizes the last, sound one-qubit implication used by the
preprint.  For `b : Bool`, the normalized state

`(|0> + (-1) ^ b |1>) / sqrt 2`

is `|+>` when `b = false` and `|->` when `b = true`.  A Hadamard gate maps it
to the computational-basis state `|b>`, so a terminal computational-basis
measurement returns `b` with probability one.

This result deliberately starts from the exact relative-phase state.  It does
not assert the paper's earlier, unjustified premise that the two amplitudes
remaining after its conditioned measurements have equal magnitude.
-/

namespace SimonDCP.Quantum.BitReadout

open QuantumAlg
open QuantumAlg.PureState

noncomputable section

/-- The computational-basis index represented by a Boolean bit. -/
def bitIndex (b : Bool) : Fin (2 ^ 1) :=
  if b then 1 else 0

/-- The named one-qubit computational-basis state `|b>`. -/
def computationalBitState (b : Bool) : PureState (Qubits 1) :=
  if b then ket1 else ket0

/--
The normalized one-qubit state whose relative phase encodes `b`:
`|+>` for `false` and `|->` for `true`.
-/
def relativePhaseState (b : Bool) : PureState (Qubits 1) :=
  if b then ketMinus else ketPlus

/-- The named computational state is the generic basis ket at `bitIndex b`. -/
theorem computationalBitState_eq_ket (b : Bool) :
    computationalBitState b = PureState.ket (bitIndex b) := by
  cases b <;> rfl

/--
The raw-vector form of `relativePhaseState` is exactly
`(|0> + (-1) ^ b |1>) / sqrt 2`.
-/
theorem relativePhaseState_vector (b : Bool) :
    (relativePhaseState b : StateVector (Qubits 1)) =
      invSqrt2 •
        ((ket0 : StateVector (Qubits 1)) +
          ((-1 : ℂ) ^ b.toNat) • (ket1 : StateVector (Qubits 1))) := by
  cases b <;>
    simp [relativePhaseState, ketPlus, ketPlusVec, ketMinus, ketMinusVec,
      sub_eq_add_neg]

/-- The explicit signed superposition has unit norm. -/
theorem norm_relativePhaseSuperposition (b : Bool) :
    ‖invSqrt2 •
        ((ket0 : StateVector (Qubits 1)) +
          ((-1 : ℂ) ^ b.toNat) • (ket1 : StateVector (Qubits 1)))‖ = 1 := by
  rw [← relativePhaseState_vector b]
  exact (relativePhaseState b).norm_eq_one

/-- A Hadamard gate converts the encoded relative phase into `|b>`. -/
@[simp]
theorem hadamard_relativePhaseState (b : Bool) :
    Gate.H.apply (relativePhaseState b) = computationalBitState b := by
  cases b <;> simp [relativePhaseState, computationalBitState]

/--
The complete Born distribution after the Hadamard gate is the point mass at
`bitIndex b`.
-/
theorem probOutcome_afterHadamard (b : Bool) (outcome : Fin (2 ^ 1)) :
    PureState.probOutcome (Gate.H.apply (relativePhaseState b)) outcome =
      if outcome = bitIndex b then 1 else 0 := by
  rw [hadamard_relativePhaseState, computationalBitState_eq_ket]
  exact PureState.probOutcome_ket (R := Qubits 1) (bitIndex b) outcome

/-- Measuring after the Hadamard gate returns the encoded bit with probability one. -/
theorem probOutcome_encodedBit (b : Bool) :
    PureState.probOutcome
        (Gate.H.apply (relativePhaseState b)) (bitIndex b) = 1 := by
  rw [probOutcome_afterHadamard, if_pos rfl]

/-- The Boolean complement has a different one-qubit basis index. -/
theorem bitIndex_not_ne (b : Bool) : bitIndex (!b) ≠ bitIndex b := by
  cases b <;> simp [bitIndex]

/-- Measuring after the Hadamard gate returns the other bit with probability zero. -/
theorem probOutcome_otherBit (b : Bool) :
    PureState.probOutcome
        (Gate.H.apply (relativePhaseState b)) (bitIndex (!b)) = 0 := by
  rw [probOutcome_afterHadamard, if_neg (bitIndex_not_ne b)]

end

end SimonDCP.Quantum.BitReadout
