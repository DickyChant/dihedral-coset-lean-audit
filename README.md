# Simon DCP Formalization and Audit

This Lean 4 project formalizes and audits Daniel R. Simon's preliminary draft
[*A Polynomial-Time Quantum Algorithm for the Dihedral Coset Problem*](https://eprint.iacr.org/2026/1591)
(IACR ePrint 2026/1591).

The draft's headline theorem is not currently represented as a proved Lean
theorem. Its proof relies on several false or unproved intermediate claims. The
development therefore starts with the sound algebraic kernel and kernel-checkable
obstructions to the invalid proof steps. It does not use `sorry` or hide gaps as
axioms.

## Formalization map

- `Quantum/IdealCosetSample.lean` defines the normalized ideal DCP sample in
  QuantumAlg and proves its exact two-point Born distribution.
- `Quantum/FourierShift.lean` proves the corresponding `ZMod` DFT translation
  and relative-phase identities using Mathlib's exact sign convention.
- `Quantum/Step2Phase.lean` proves the root-of-unity factorization that exposes
  the least significant bit of the hidden shift.
- `Arithmetic/TranslationFiber.lean` proves the valid high-bit translation
  argument underlying Lemma 2.
- `Quantum/PhaseTransfer.lean` proves the measured-XOR phase transfer used at
  the end of the proposed algorithm.
- `Quantum/BitReadout.lean` proves that one Hadamard gate reads an exact
  `(-1)^bit` relative phase with probability one.
- `Quantum/ConditionalReadout.lean` packages the final result under the exact
  balanced-amplitude premise that the paper would still need to prove.
- `Quantum/PhaseCorrelation.lean`, `Probability/Conditioning.lean`, and
  `Quantum/AmplitudeCancellation.lean` isolate the failures in Lemmas 3 and 4.
- `Probability/LinearPhaseIndependence.lean` proves the correct unconditioned
  joint-uniformity theorem for distinct nonzero binary linear forms.
- `Arithmetic/SampleRecursion.lean` proves the arithmetic of deleting a known
  low bit and halving an ideal DCP sample.
- `Arithmetic/SwapFiber.lean` gives an `n = 8` locally valid two-coordinate
  counterexample to the fibre-preserving algebra used in Lemma 1, together
  with the general error formula.

The project deliberately separates these formalized local facts from the missing
adaptive-measurement, probability, postselection, amplification, and lattice-
reduction arguments needed for the headline result.

## Toolchain

- Lean 4.31.0
- Mathlib 4.31.0
- CSLib 4.31.0
- `QudeLeap/Lean-QuantumAlg` at commit
  `7e80846034b9e76fdeded711775a513a7d5ba917`

The project is intended to be built in Arch Linux under WSL:

```bash
cd /mnt/c/Users/yanyx/Documents/Simon
bash scripts/setup-wsl-arch.sh
bash scripts/build-wsl.sh
```

The same build can be launched from PowerShell with:

```powershell
wsl.exe -d archlinux -- bash -lc 'cd /mnt/c/Users/yanyx/Documents/Simon && bash scripts/build-wsl.sh'
```

The checked environment uses Elan 4.2.3 and Lean 4.31.0.  For faster builds on
Windows-mounted drives, copy the repository to a WSL-native directory before
running `scripts/build-wsl.sh`; the source tree remains authoritative.

The full project was verified in Arch Linux under WSL on August 7, 2026.  The
command `lake build` completed all 3278 jobs successfully.

## Verification policy

Every theorem in the project must compile without `sorry`. Missing arguments
from the paper are recorded as named obligations or refuted by explicit
counterexamples; they are never silently promoted to assumptions. Final claims
are checked with `#print axioms`.  The audit reports only the standard Lean
dependencies `propext`, `Classical.choice`, and `Quot.sound`; it reports no
`sorryAx` or project-local axiom.

See [AUDIT.md](AUDIT.md) for the proof-status map and
[LIBRARIES.md](LIBRARIES.md) for the TCS/quantum-library survey.
