# Simon DCP Formalization and Audit

## Table of contents

- [Status of Lemmas 1, 3, and 4](#status-of-lemmas-1-3-and-4)
  - [Lemma 1](#lemma-1)
  - [Lemma 3](#lemma-3)
  - [Lemma 4](#lemma-4)
- [Project scope](#project-scope)
- [Formalization map](#formalization-map)
- [Toolchain](#toolchain)
- [Verification policy](#verification-policy)

## Status of Lemmas 1, 3, and 4

**Bottom line:** this development does not refute the final statement of any of
Lemmas 1, 3, or 4.  All three conclusions remain unproved.  What it does refute
are specific intermediate claims and inference rules on which the paper's proof
sketches rely.  Those refutations show that the published sketches do not prove
the lemmas, even though a different proof might conceivably establish some of
their conclusions.

| Lemma | Status of the final statement | What has been refuted |
| --- | --- | --- |
| Lemma 1 | Unproved, not refuted | The proposed swap is not fibre-preserving, so the claimed injection is invalid. |
| Lemma 3 | Unproved, not refuted | The phases are not pairwise independent after the adaptive choice of `A`. |
| Lemma 4 | Unproved, not refuted | Correlated overflow need not improve uniformity; count closeness does not imply multiplicative amplitude closeness; and a displayed exponent estimate is false for the stated parameter range. |

### Lemma 1

The Lean development proves that the change caused by the paper's simultaneous
swap of selection bits and low sample parts is

```text
B * (phi_j - phi_i) * (H_i - H_j).
```

This expression need not vanish modulo the measured subset-sum modulus.  A
locally valid `n = 8` instance changes the relevant contribution from `1` to
`5` modulo `128`.  Thus the proposed map does not preserve a measured fibre;
see [`SwapFiber.lean`](SimonDCP/Arithmetic/SwapFiber.lean).

The concrete `n = 8` witness is not a full member of the paper's event `D_Y`,
because that event imposes additional global distinctness conditions.  More
importantly, failure of this particular injection does not logically imply
that Lemma 1's constant-probability conclusion is false.  The injection argument
is refuted; the lemma statement remains unproved.

### Lemma 3

Step 4 selects `A` from blocks on which the measured mask `D` is zero.  Hence
`D_A = 0`, and

```text
(-1)^(phi dot D) = (-1)^(phi_B dot D_B).
```

States with the same `B` component and different `A` components therefore have
identical phases.  They are perfectly correlated rather than pairwise
independent, contrary to the variance argument in the proof sketch; see
[`PhaseCorrelation.lean`](SimonDCP/Quantum/PhaseCorrelation.lean).

This directly refutes the claimed phase-independence step.  It does not yet give
a complete instance of the paper's conditioned experiment that violates the
final "well-behaved" probability statement, so Lemma 3 itself remains unproved
rather than refuted.

### Lemma 4

The development gives finite counterexamples to three inference patterns used
in or around the proof:

- independent Boolean coordinates can become perfectly correlated after
  conditioning;
- adding a correlated overflow bit can turn a balanced bit into a constant;
- nearly equal counts of signed terms give no multiplicative control of an
  amplitude when cancellation is possible.

See [`Conditioning.lean`](SimonDCP/Probability/Conditioning.lean) and
[`AmplitudeCancellation.lean`](SimonDCP/Quantum/AmplitudeCancellation.lean).
In addition, substituting `c = 12` into the displayed page-14 exponent yields

```text
-n/2 + 6n/(c' log n) + 6 log n,
```

which is not below `-n`; therefore the claimed `delta < 2^(-n)` bound does not
follow for the stated range.

These results refute general assertions and arithmetic steps used in the proof,
but they do not constitute a full counterexample drawn from the paper's exact
conditioned distribution.  The final multiplicative-amplitude conclusion of
Lemma 4 therefore also remains unproved, not refuted.  The detailed audit is in
[`AUDIT.md`](AUDIT.md).

## Project scope

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
