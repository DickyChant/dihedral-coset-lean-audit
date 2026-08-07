# Lean library survey

Survey date: 2026-08-07. Only upstream repositories and source files were
used. The project currently pins Lean, Mathlib, and CSLib 4.31.0 together with
QuantumAlg commit `7e80846034b9e76fdeded711775a513a7d5ba917`.

## Reused now

### QuantumAlg

Upstream: <https://github.com/QudeLeap/Lean-QuantumAlg>, pinned at
[commit `7e80846`](https://github.com/QudeLeap/Lean-QuantumAlg/commit/7e80846034b9e76fdeded711775a513a7d5ba917).

- `Core/Base/State.lean` and `Core/Base/Measurement.lean` provide finite
  registers, normalized pure states, and terminal Born probabilities.
- `Core/Components/Gates.lean` provides the Hadamard identities used by the
  one-bit readout proof.
- `Primitives/QFT.lean` and `Primitives/WalshHadamard.lean` provide reusable
  qubit QFT and Walsh-character results.
- `Algorithms/Simon.lean` provides useful `F_2` dot-product conventions and a
  post-sampling recovery interface.

QuantumAlg does not currently model intermediate measurement, post-measurement
states, or classical control depending on a measured outcome. Its Simon module
also assumes completeness of the sampled equations rather than proving the
quantum sampling theorem. The adaptive middle of the preprint therefore needs
a new instrument/branch semantics.

### Mathlib

Upstream commit:
<https://github.com/leanprover-community/mathlib4/commit/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f>

- `Mathlib.Analysis.Fourier.ZMod` supplies `ZMod.dft`, inverse DFT, and standard
  additive characters.
- finite-Abelian Fourier orthogonality supplies character expectation and
  linear-independence lemmas.
- `PMF.uniformOfFinset`, `PMF.uniformOfFintype`, `IndepFun`, `iIndepFun`, and
  variance/Chebyshev results can support a repaired finite probability proof.

Mathlib's `ZMod.dft` is an unnormalized classical linear transform, so a bridge
to normalized quantum states and measurement distributions is still required.
No ready-made theorem was found for joint uniformity of distinct binary linear
forms; this project proves the required finite-fibre theorem directly.

## Optional later dependency

[VCVio](https://github.com/Verified-zkEVM/VCVio) at its Lean 4.31-compatible
[commit `cbd4144`](https://github.com/Verified-zkEVM/VCVio/commit/cbd4144b51d92da00dd50f05e068b2348fa6e529)
can model probabilistic oracle computations, transcripts, query
bounds, and cryptographic games. It includes executable LWE experiment
definitions, but not the Regev or BKSW worst-case reductions. Adding it now
would not close a proof obligation and would require a bridge between its
probabilistic computation model and QuantumAlg, so it is intentionally not a
current dependency.

## Not reused

- `duckki/quantum-computing-lean` has projective-measurement and partial-trace
  material but targets Lean/Mathlib 4.29.1 and lacks adaptive classical control.
- `Physlib/QuantumInfo` focuses on density operators, channels, and entropy,
  currently on a different toolchain, and does not provide a DCP algorithm
  layer.

## Missing upstream formalizations

No current Lean 4 implementation was found for any of the following:

- the dihedral coset problem or dihedral hidden-subgroup algorithm;
- Regev's DCP-to-lattice reduction;
- the BKSW LWE reduction;
- adaptive measurement-controlled quantum circuits suitable for this paper;
- a complete worst-case LWE reduction proof.

The development therefore uses Mathlib for finite algebra/Fourier/probability,
QuantumAlg for states and unitary gates, and keeps every unavailable external
reduction or adaptive-measurement argument as an explicit future obligation.
