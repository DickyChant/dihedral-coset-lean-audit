import SimonDCP.Arithmetic.SampleRecursion
import SimonDCP.Arithmetic.SwapFiber
import SimonDCP.Arithmetic.TranslationFiber
import SimonDCP.Probability.Conditioning
import SimonDCP.Probability.LinearPhaseIndependence
import SimonDCP.Quantum.AmplitudeCancellation
import SimonDCP.Quantum.BitReadout
import SimonDCP.Quantum.ConditionalReadout
import SimonDCP.Quantum.FourierShift
import SimonDCP.Quantum.IdealCosetSample
import SimonDCP.Quantum.PhaseCorrelation
import SimonDCP.Quantum.PhaseTransfer
import SimonDCP.Quantum.Step2Phase

/-!
# Kernel trust audit

The declarations below are the principal machine-checked outputs of the current
formalization. These commands make their axiom dependencies visible during a
build. In particular, none may depend on `sorryAx` or a project-specific axiom.
-/

open SimonDCP.Arithmetic.SampleRecursion
open SimonDCP.Arithmetic.SwapFiber
open SimonDCP.Arithmetic.TranslationFiber
open SimonDCP.Probability.Conditioning
open SimonDCP.Probability.LinearPhaseIndependence
open SimonDCP.Quantum.AmplitudeCancellation
open SimonDCP.Quantum.BitReadout
open SimonDCP.Quantum.ConditionalReadout
open SimonDCP.Quantum.FourierShift
open SimonDCP.Quantum.IdealCosetSample
open SimonDCP.Quantum.PhaseCorrelation
open SimonDCP.Quantum.PhaseTransfer
open SimonDCP.Quantum.Step2Phase

#print axioms lowPartBitSwap_delta
#print axioms reducedSamplePosition_true_sub_false
#print axioms reducedDot_modEq
#print axioms lemmaOneMap_does_not_preserve_measured_fiber
#print axioms counterexample_preserves_phase_but_not_fiber
#print axioms lemmaOneMap_not_fiberPreserving
#print axioms lemmaOneMap_not_fiberPreserving_on_locallyWellFormed_inputs
#print axioms fiberCoefficient_translate_fixedXor
#print axioms walshPhase_eq_of_eq_off_zero_set
#print axioms coordinate_independence_destroyed_by_conditioning
#print axioms correlated_overflow_can_destroy_balance
#print axioms nonzero_dot_balanced
#print axioms distinct_nonzero_joint_fiber_card_eq
#print axioms one_term_change_can_escape_any_multiplicative_zero_bound
#print axioms SimonDCP.Quantum.BitReadout.probOutcome_encodedBit
#print axioms readout_of_exact_balancedRelativePhase
#print axioms dft_twoPoint
#print axioms probOutcome_idealCosetState
#print axioms encodeThroughMeasuredXor_eq_globalPhase
#print axioms phase_factor_lastBit
#print axioms relativeHighBitPhase_of_lastBit_one
