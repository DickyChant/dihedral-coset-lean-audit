import SimonDCP.Quantum.BitReadout
import SimonDCP.Quantum.PhaseTransfer

/-!
# Approximate one-qubit phase readout

The exact readout theorem in `BitReadout` starts from perfectly balanced
amplitudes.  Lemma 4 only needs a robust version: after the target phase has
been transferred to the surviving bit, an additive mismatch between its two
branch amplitudes should give a quantitative bound on the wrong Hadamard
outcome.

For a normalized state with amplitudes `a` and `b`, let

```text
mismatch = b - (-1)^d * a.
```

The wrong-bit Born probability after a Hadamard gate is exactly
`normSq mismatch / 2`.  Consequently an additive amplitude error `epsilon`
gives success probability at least `1 - epsilon^2 / 2`.  No division by either
branch amplitude, and hence no anti-cancellation premise, is needed.
-/

namespace SimonDCP.Quantum.ApproximateReadout

open QuantumAlg

noncomputable section

/-- The sign that should relate the two branches when they encode `dBit`. -/
def targetSign (dBit : Bool) : ℂ :=
  (-1 : ℂ) ^ dBit.toNat

/-- Additive deviation from the ideal relative-phase relation. -/
def branchMismatch (state : PureState (Qubits 1)) (dBit : Bool) : ℂ :=
  state 1 - targetSign dBit * state 0

/--
Exact robust Hadamard identity: wrong-outcome probability is one half of the
squared additive branch mismatch.
-/
theorem wrong_probability_eq_mismatch
    (state : PureState (Qubits 1)) (dBit : Bool) :
    PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex (!dBit)) =
      Complex.normSq (branchMismatch state dBit) / 2 := by
  have hInvSqrt2 : Complex.normSq PureState.invSqrt2 = (1 : ℝ) / 2 := by
    rw [Complex.normSq_eq_norm_sq, PureState.norm_sq_invSqrt2]
    norm_num
  cases dBit
  · simp only [PureState.probOutcome, StateVector.probOutcome, branchMismatch,
      targetSign, BitReadout.bitIndex, Bool.not_false, Bool.toNat_false,
      pow_zero, one_mul]
    simp [Gate.H, Gate.HOp, Complex.sq_norm]
    rw [show PureState.invSqrt2 * state 0 +
          -(PureState.invSqrt2 * state 1) =
        PureState.invSqrt2 * (state 0 - state 1) by ring,
      Complex.normSq_mul, hInvSqrt2]
    rw [show state 1 - state 0 = -(state 0 - state 1) by ring,
      Complex.normSq_neg]
    ring
  · simp only [PureState.probOutcome, StateVector.probOutcome, branchMismatch,
      targetSign, BitReadout.bitIndex, Bool.not_true, Bool.toNat_true,
      pow_one, neg_one_mul, sub_neg_eq_add]
    simp [Gate.H, Gate.HOp, Complex.sq_norm]
    rw [← mul_add, Complex.normSq_mul, hInvSqrt2]
    rw [add_comm (state 1) (state 0)]
    ring

/-- The two one-qubit outcome probabilities are complementary. -/
theorem correct_probability_eq_one_sub_wrong
    (state : PureState (Qubits 1)) (dBit : Bool) :
    PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex dBit) =
      1 - PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex (!dBit)) := by
  have hTotal := PureState.sum_probOutcome (Gate.H.apply state)
  change (∑ x : Fin 2, PureState.probOutcome (Gate.H.apply state) x) = 1 at hTotal
  rw [Fin.sum_univ_two] at hTotal
  cases dBit <;> simp [BitReadout.bitIndex] <;> linarith

/-- Correct-outcome probability written directly in terms of branch mismatch. -/
theorem correct_probability_eq_one_sub_mismatch
    (state : PureState (Qubits 1)) (dBit : Bool) :
    PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex dBit) =
      1 - Complex.normSq (branchMismatch state dBit) / 2 := by
  rw [correct_probability_eq_one_sub_wrong,
    wrong_probability_eq_mismatch]

/-- A squared mismatch-energy budget gives a direct readout guarantee. -/
theorem correct_probability_ge_of_mismatch_normSq_le
    (state : PureState (Qubits 1)) (dBit : Bool) (errorEnergy : ℝ)
    (hMismatch : Complex.normSq (branchMismatch state dBit) ≤ errorEnergy) :
    1 - errorEnergy / 2 ≤
      PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex dBit) := by
  rw [correct_probability_eq_one_sub_mismatch]
  linarith

/-- An additive norm error `error` gives failure probability at most `error^2 / 2`. -/
theorem correct_probability_ge_of_mismatch_norm_le
    (state : PureState (Qubits 1)) (dBit : Bool) (error : ℝ)
    (hError : 0 ≤ error)
    (hMismatch : ‖branchMismatch state dBit‖ ≤ error) :
    1 - error ^ 2 / 2 ≤
      PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex dBit) := by
  apply correct_probability_ge_of_mismatch_normSq_le
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (branchMismatch state dBit)]

/-- Exact branch balance recovers the existing probability-one readout. -/
theorem correct_probability_eq_one_of_mismatch_eq_zero
    (state : PureState (Qubits 1)) (dBit : Bool)
    (hMismatch : branchMismatch state dBit = 0) :
    PureState.probOutcome (Gate.H.apply state)
        (BitReadout.bitIndex dBit) = 1 := by
  rw [correct_probability_eq_one_sub_mismatch, hMismatch,
    Complex.normSq_zero]
  norm_num

end


end SimonDCP.Quantum.ApproximateReadout
