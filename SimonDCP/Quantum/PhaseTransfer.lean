import SimonDCP.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# Transferring a Boolean phase through a measured XOR

The final step of the paper measures `h' = h XOR hStar`.  Once the measured
value is fixed, `h` is uniquely determined by `hStar`.  The Boolean character
encoding the target bit then factors as

`(-1)^(h * dBit) = (-1)^(h' * dBit) * (-1)^(hStar * dBit)`.

The first factor depends only on measured classical data and is therefore a
global phase.  This file proves that Boolean, natural-number, and complex
algebraic kernel, including its pointwise action on a two-amplitude state.

These results are conditional identities.  They do not establish the paper's
separate claim that the unmodelled `B` registers contribute the same
amplitudes and phases for both values of `hStar`.
-/

namespace SimonDCP.Quantum.PhaseTransfer

/-- Recover `h` from the measured XOR and the remaining bit `hStar`. -/
def hiddenFromMeasured (measured hStar : Bool) : Bool :=
  measured.xor hStar

/-- XORing twice on the right cancels. -/
theorem xor_cancel_right (left right : Bool) :
    (left.xor right).xor right = left := by
  cases left <;> cases right <;> rfl

/-- The recovered bit has the prescribed measured XOR. -/
theorem hiddenFromMeasured_xor (measured hStar : Bool) :
    (hiddenFromMeasured measured hStar).xor hStar = measured := by
  cases measured <;> cases hStar <;> rfl

/-- Any bit with the prescribed measured XOR is the recovered bit. -/
theorem hiddenFromMeasured_unique (h hStar measured : Bool)
    (hMeasured : h.xor hStar = measured) :
    h = hiddenFromMeasured measured hStar := by
  calc
    h = (h.xor hStar).xor hStar := (xor_cancel_right h hStar).symm
    _ = measured.xor hStar :=
      congrArg (fun bit : Bool => bit.xor hStar) hMeasured
    _ = hiddenFromMeasured measured hStar := rfl

/-- Solving a fixed-XOR equation is equivalent to substituting the recovered bit. -/
theorem xor_eq_measured_iff (h hStar measured : Bool) :
    h.xor hStar = measured ↔ h = hiddenFromMeasured measured hStar := by
  constructor
  · exact hiddenFromMeasured_unique h hStar measured
  · intro hRecovered
    rw [hRecovered]
    exact hiddenFromMeasured_xor measured hStar

/-- For fixed `measured` and `hStar`, there is exactly one compatible `h`. -/
theorem existsUnique_hiddenFromMeasured (measured hStar : Bool) :
    ∃! h : Bool, h.xor hStar = measured := by
  refine ⟨hiddenFromMeasured measured hStar,
    hiddenFromMeasured_xor measured hStar, ?_⟩
  intro h hMeasured
  exact hiddenFromMeasured_unique h hStar measured hMeasured

/-- The natural exponent representing the product of two Boolean bits. -/
def bitExponent (bit dBit : Bool) : ℕ :=
  bit.toNat * dBit.toNat

/-- XOR is addition modulo two after coercing Boolean bits to naturals. -/
theorem xor_toNat_eq_add_mod_two (left right : Bool) :
    (left.xor right).toNat = (left.toNat + right.toNat) % 2 := by
  cases left <;> cases right <;> decide

/-- Multiplication by `dBit` preserves the XOR/addition parity identity. -/
theorem bitExponent_xor_mod_two (left right dBit : Bool) :
    bitExponent (left.xor right) dBit % 2 =
      (bitExponent left dBit + bitExponent right dBit) % 2 := by
  cases left <;> cases right <;> cases dBit <;> decide

/-- The exponent of the recovered bit splits modulo two. -/
theorem bitExponent_hiddenFromMeasured_mod_two
    (measured hStar dBit : Bool) :
    bitExponent (hiddenFromMeasured measured hStar) dBit % 2 =
      (bitExponent measured dBit + bitExponent hStar dBit) % 2 := by
  simpa only [hiddenFromMeasured] using
    bitExponent_xor_mod_two measured hStar dBit

/-- The complex sign that encodes `dBit` in the phase of a Boolean label. -/
def encodingPhase (bit dBit : Bool) : ℂ :=
  (-1 : ℂ) ^ bitExponent bit dBit

/-- A Boolean phase character turns XOR into multiplication. -/
theorem encodingPhase_xor (left right dBit : Bool) :
    encodingPhase (left.xor right) dBit =
      encodingPhase left dBit * encodingPhase right dBit := by
  cases left <;> cases right <;> cases dBit <;>
    norm_num [encodingPhase, bitExponent]

/-- The phase of the recovered `h` splits into measured and `hStar` phases. -/
theorem encodingPhase_hiddenFromMeasured (measured hStar dBit : Bool) :
    encodingPhase (hiddenFromMeasured measured hStar) dBit =
      encodingPhase measured dBit * encodingPhase hStar dBit := by
  simpa only [hiddenFromMeasured] using
    encodingPhase_xor measured hStar dBit

/-- The phase-transfer identity stated from the measured-XOR hypothesis. -/
theorem encodingPhase_transfer (h hStar measured dBit : Bool)
    (hMeasured : h.xor hStar = measured) :
    encodingPhase h dBit =
      encodingPhase measured dBit * encodingPhase hStar dBit := by
  rw [hiddenFromMeasured_unique h hStar measured hMeasured]
  exact encodingPhase_hiddenFromMeasured measured hStar dBit

/-- The factor depending only on the measured XOR and the encoded target bit. -/
def measurementGlobalPhase (measured dBit : Bool) : ℂ :=
  encodingPhase measured dBit

/-- The measurement-dependent factor is a unit-modulus complex phase. -/
theorem norm_measurementGlobalPhase (measured dBit : Bool) :
    ‖measurementGlobalPhase measured dBit‖ = 1 := by
  cases measured <;> cases dBit <;>
    norm_num [measurementGlobalPhase, encodingPhase, bitExponent]

/-- A two-amplitude state, indexed by the remaining Boolean basis label. -/
abbrev TwoAmplitudeState := Bool → ℂ

/-- Multiply both amplitudes of a Boolean state by the same scalar. -/
def scaleState (scalar : ℂ) (state : TwoAmplitudeState) : TwoAmplitudeState :=
  fun bit => scalar * state bit

/-- Encode `dBit` directly in the phase indexed by `hStar`. -/
def encodeInHStar (state : TwoAmplitudeState) (dBit : Bool) : TwoAmplitudeState :=
  fun hStar => encodingPhase hStar dBit * state hStar

/-- Encode through the compatible value of `h` after the XOR measurement. -/
def encodeThroughMeasuredXor (state : TwoAmplitudeState)
    (measured dBit : Bool) : TwoAmplitudeState :=
  fun hStar =>
    encodingPhase (hiddenFromMeasured measured hStar) dBit * state hStar

/--
On both amplitudes, encoding through `h` is encoding through `hStar` up to the
same measurement-dependent global phase.
-/
theorem encodeThroughMeasuredXor_eq_globalPhase
    (state : TwoAmplitudeState) (measured dBit : Bool) :
    encodeThroughMeasuredXor state measured dBit =
      scaleState (measurementGlobalPhase measured dBit)
        (encodeInHStar state dBit) := by
  funext hStar
  simp only [encodeThroughMeasuredXor, scaleState, measurementGlobalPhase,
    encodeInHStar]
  rw [encodingPhase_hiddenFromMeasured, mul_assoc]

end SimonDCP.Quantum.PhaseTransfer
