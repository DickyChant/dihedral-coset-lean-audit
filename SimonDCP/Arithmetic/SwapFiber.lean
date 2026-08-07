import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The low-part swap in Lemma 1 does not preserve the measured fibre

This file audits the two-coordinate operation used in the sketch proof of
Lemma 1 of IACR ePrint 2026/1591.  Write a Fourier sample as
`low + B * high`.  The proposed map simultaneously swaps two subset bits and
the low parts of their Fourier samples, while leaving the high parts in their
original coordinates.

The Hadamard phase exponent is preserved when the corresponding output bits
are swapped as well.  The subset sum, however, changes by

`B * (phiJ - phiI) * (highI - highJ)`.

For the paper's `n = 8` split, `B = 2^(8 - 2 * log2 8) = 4`, while measuring
the low `n - 1` bits means reducing modulo `128`.  The explicit data below
have subset sum `1` before the map and `5` afterwards, so the map leaves the
selected measured fibre.
-/

namespace SimonDCP.Arithmetic.SwapFiber

/-- The data in two coordinates affected by the proposed map. -/
structure SwapInput where
  phiI : ℤ
  phiJ : ℤ
  lowI : ℤ
  lowJ : ℤ
  highI : ℤ
  highJ : ℤ
deriving DecidableEq, Repr

/-- Recombine the low and high parts of a Fourier sample. -/
def recombine (B low high : ℤ) : ℤ :=
  low + B * high

/-- Contribution of the two coordinates before the simultaneous swap. -/
def beforeContribution (B : ℤ) (x : SwapInput) : ℤ :=
  x.phiI * recombine B x.lowI x.highI +
    x.phiJ * recombine B x.lowJ x.highJ

/--
Contribution after swapping `phiI` with `phiJ` and swapping `lowI` with
`lowJ`, but retaining each high part at its original coordinate.
-/
def afterContribution (B : ℤ) (x : SwapInput) : ℤ :=
  x.phiJ * recombine B x.lowJ x.highI +
    x.phiI * recombine B x.lowI x.highJ

/-- The exact subset-sum error introduced by the two-coordinate map. -/
theorem lowPartBitSwap_delta (B : ℤ) (x : SwapInput) :
    afterContribution B x - beforeContribution B x =
      B * (x.phiJ - x.phiI) * (x.highI - x.highJ) := by
  simp only [afterContribution, beforeContribution, recombine]
  ring

/-- Dot-product exponent used for a Hadamard phase on two coordinates. -/
def phaseExponent (phiI phiJ outputI outputJ : ℤ) : ℤ :=
  phiI * outputI + phiJ * outputJ

/-- Swapping both the subset bits and output bits preserves the phase exponent. -/
theorem simultaneousSwap_preserves_phase
    (phiI phiJ outputI outputJ : ℤ) :
    phaseExponent phiJ phiI outputJ outputI =
      phaseExponent phiI phiJ outputI outputJ := by
  simp only [phaseExponent]
  ring

/-- Membership in the fibre selected by measuring a modular residue. -/
def InMeasuredFiber (modulus residue value : ℤ) : Prop :=
  value % modulus = residue % modulus

/-- The universal fibre-preservation property asserted for the swap map. -/
def FiberPreserving (modulus B : ℤ) : Prop :=
  ∀ x : SwapInput,
    InMeasuredFiber modulus (beforeContribution B x) (afterContribution B x)

/-- An integer is a valid subset-selection bit. -/
def IsSelectionBit (value : ℤ) : Prop :=
  value = 0 ∨ value = 1

/--
Local domain constraints for the two coordinates used by the swap argument.

The low parts lie in `[0, B)`, while the recombined samples lie in `[0, N)`.
This deliberately does not encode the paper's global group layout, its
`D_bad`-to-`D_good` requirement, or pairwise distinctness of all `Q` low parts.
-/
def LocallyWellFormedSwapInput (B N : ℤ) (x : SwapInput) : Prop :=
  IsSelectionBit x.phiI ∧
  IsSelectionBit x.phiJ ∧
  0 ≤ x.lowI ∧ x.lowI < B ∧
  0 ≤ x.lowJ ∧ x.lowJ < B ∧
  0 ≤ recombine B x.lowI x.highI ∧
    recombine B x.lowI x.highI < N ∧
  0 ≤ recombine B x.lowJ x.highJ ∧
    recombine B x.lowJ x.highJ < N

/-- Fibre preservation restricted to pairs satisfying the local range constraints. -/
def FiberPreservingOnLocallyWellFormedInputs (modulus B N : ℤ) : Prop :=
  ∀ x : SwapInput,
    LocallyWellFormedSwapInput B N x →
      InMeasuredFiber modulus (beforeContribution B x) (afterContribution B x)

def counterexampleN : ℕ := 8

def counterexampleLogN : ℕ := 3

/-- Number of possibilities for the `n - 2 * log2 n` low bits. -/
def counterexampleLowBase : ℤ :=
  2 ^ (counterexampleN - 2 * counterexampleLogN)

/-- Modulus seen when the low `n - 1` bits of an `n`-bit sum are measured. -/
def counterexampleMeasuredModulus : ℤ :=
  2 ^ (counterexampleN - 1)

/--
Here the original samples are `yI = 4` and `yJ = 1`, with distinct low parts
`0` and `1`.  The selected bit is initially at coordinate `J`.
-/
def counterexampleInput : SwapInput where
  phiI := 0
  phiJ := 1
  lowI := 0
  lowJ := 1
  highI := 1
  highJ := 0

theorem counterexample_parameters :
    counterexampleLowBase = 4 ∧ counterexampleMeasuredModulus = 128 := by
  norm_num [counterexampleLowBase, counterexampleMeasuredModulus,
    counterexampleN, counterexampleLogN]

theorem counterexample_low_parts_distinct :
    counterexampleInput.lowI ≠ counterexampleInput.lowJ := by
  norm_num [counterexampleInput]

/-- The explicit witness obeys all local bit, low-part, and sample-range constraints. -/
theorem counterexample_locallyWellFormed :
    LocallyWellFormedSwapInput counterexampleLowBase
      (2 * counterexampleMeasuredModulus) counterexampleInput := by
  norm_num [LocallyWellFormedSwapInput, IsSelectionBit, recombine,
    counterexampleMeasuredModulus, counterexampleLowBase, counterexampleN,
    counterexampleLogN, counterexampleInput]

theorem counterexample_before :
    beforeContribution counterexampleLowBase counterexampleInput = 1 := by
  norm_num [beforeContribution, recombine, counterexampleLowBase,
    counterexampleN, counterexampleLogN, counterexampleInput]

theorem counterexample_after :
    afterContribution counterexampleLowBase counterexampleInput = 5 := by
  norm_num [afterContribution, recombine, counterexampleLowBase,
    counterexampleN, counterexampleLogN, counterexampleInput]

theorem counterexample_delta :
    afterContribution counterexampleLowBase counterexampleInput -
        beforeContribution counterexampleLowBase counterexampleInput = 4 := by
  norm_num [afterContribution, beforeContribution, recombine,
    counterexampleLowBase, counterexampleN, counterexampleLogN,
    counterexampleInput]

/-- The original subset sum lies in the fibre selected by residue `1`. -/
theorem counterexample_before_mem_fiber :
    InMeasuredFiber counterexampleMeasuredModulus 1
      (beforeContribution counterexampleLowBase counterexampleInput) := by
  norm_num [InMeasuredFiber, beforeContribution, recombine,
    counterexampleMeasuredModulus, counterexampleLowBase, counterexampleN,
    counterexampleLogN, counterexampleInput]

/-- The image under the paper's map does not lie in that measured fibre. -/
theorem counterexample_after_not_mem_fiber :
    ¬ InMeasuredFiber counterexampleMeasuredModulus 1
      (afterContribution counterexampleLowBase counterexampleInput) := by
  norm_num [InMeasuredFiber, afterContribution, recombine,
    counterexampleMeasuredModulus, counterexampleLowBase, counterexampleN,
    counterexampleLogN, counterexampleInput]

/--
Machine-checked counterexample to the fibre-preservation property required by
the map in the proof sketch of Lemma 1.
-/
theorem lemmaOneMap_does_not_preserve_measured_fiber :
    ¬ InMeasuredFiber counterexampleMeasuredModulus
        (beforeContribution counterexampleLowBase counterexampleInput)
        (afterContribution counterexampleLowBase counterexampleInput) := by
  norm_num [InMeasuredFiber, beforeContribution, afterContribution, recombine,
    counterexampleMeasuredModulus, counterexampleLowBase, counterexampleN,
    counterexampleLogN, counterexampleInput]

/--
For the same witness, swapping an output pair `(1, 0)` together with the
selection bits does preserve the Hadamard exponent.  Thus the obstruction is
specifically the measured subset-sum fibre, not the phase permutation.
-/
theorem counterexample_preserves_phase_but_not_fiber :
    phaseExponent counterexampleInput.phiJ counterexampleInput.phiI 0 1 =
        phaseExponent counterexampleInput.phiI counterexampleInput.phiJ 1 0 ∧
      ¬ InMeasuredFiber counterexampleMeasuredModulus
        (beforeContribution counterexampleLowBase counterexampleInput)
        (afterContribution counterexampleLowBase counterexampleInput) := by
  constructor
  · exact simultaneousSwap_preserves_phase
      counterexampleInput.phiI counterexampleInput.phiJ 1 0
  · exact lemmaOneMap_does_not_preserve_measured_fiber

/-- The swap operation is not fibre-preserving, witnessed by `counterexampleInput`. -/
theorem lemmaOneMap_not_fiberPreserving :
    ¬ FiberPreserving counterexampleMeasuredModulus counterexampleLowBase := by
  intro h
  exact lemmaOneMap_does_not_preserve_measured_fiber (h counterexampleInput)

/--
The failure persists after imposing all two-coordinate range constraints; it
is not an artefact of allowing arbitrary integers. This theorem is a local
obstruction, not a claim that the `n = 8` witness satisfies the paper's global
all-`Q` distinctness event.
-/
theorem lemmaOneMap_not_fiberPreserving_on_locallyWellFormed_inputs :
    ¬ FiberPreservingOnLocallyWellFormedInputs counterexampleMeasuredModulus
      counterexampleLowBase (2 * counterexampleMeasuredModulus) := by
  intro h
  exact lemmaOneMap_does_not_preserve_measured_fiber
    (h counterexampleInput counterexample_locallyWellFormed)

end SimonDCP.Arithmetic.SwapFiber
