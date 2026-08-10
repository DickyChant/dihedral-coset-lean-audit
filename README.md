# Simon DCP Formalization and Audit

**Reference:** Daniel R. Simon,
[*A Polynomial-Time Quantum Algorithm for the Dihedral Coset Problem*](https://eprint.iacr.org/2026/1591),
IACR Cryptology ePrint Archive, Report 2026/1591 (2026).

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

| Lemma | Status of the final statement | Refutation and repair status |
| --- | --- | --- |
| Lemma 1 | Unproved, not refuted | The proposed low-part swap is invalid. Restricted Parseval gives an unconditional inverse-polynomial replacement, and two-group subset-sum injectivity is a candidate route back to high probability; the latter route is not yet fully formalized. |
| Lemma 3 | Unproved, not refuted | The phases are not pairwise independent after the adaptive choice of `A`. |
| Lemma 4 | Unproved, not refuted | The exponent, `mu`, and `n^(3/2)` bookkeeping errors are repaired. Conditional independence, correlated overflow, and multiplicative amplitude control remain unresolved. |

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

[`SwapFiberRepair.lean`](SimonDCP/Arithmetic/SwapFiberRepair.lean) proves the
exact repair criterion: for a zero/one swap with measured modulus
`B * stride`, the original low-part operation is valid exactly when
`stride` divides `H_i - H_j`.  It also proves that permuting each complete
Fourier sample together with its selection and Hadamard-output coordinates is
a bijection preserving the subset sum, every measured residue fibre, the phase
exponent, and sample distinctness.

This repairs the algebraic map, but not yet the whole Lemma 1 injection.  After
Step 4, terms with equal `(h, s_1, ..., s_g)` labels interfere.  A termwise
weight-preserving permutation proof must choose its map only from the measured
outcome and carry every such interference class through one fixed label
equivalence.  A weaker class map can still be useful if its target coherent
weight is proved directly to be at least the source weight.  The Lean module
formalizes the resulting group-level
tension: a complete-record permutation that stays within every Step-3 group
preserves the full group subset sums (and hence their high-bit `s_j` labels),
but provably leaves the number of all-zero Hadamard-output groups unchanged.
It therefore cannot implement the required `D_Y^bad`-to-`D_Y^good` step, which
must move outputs across groups.  Moving whole groups does not escape the
obstruction: Lean proves that it coherently relabels the group-sum vector but
only bijects the all-zero groups, leaving their cardinality fixed.  A successful
map must therefore mix coordinates between groups and prove a nontrivial fixed
relabeling theorem for the resulting `s_j` values.  The module packages the
remaining requirements as an explicit
`LemmaOneRepairCertificate`; this is only a structural interface.  Lean now
proves that every such certificate descends through the erased hidden selection
string to an injective map on measured outcomes.  It does not prove that their
probability weights do not decrease.  The separate
`MeasuredOutcomeWeightInjectionCertificate` states exactly that remaining
finite weighted-injection obligation, and Lean proves that any such certificate
implies total bad-event weight at most total good-event weight; no instance of
either certificate is assumed.

For the stronger label containing each *full* group subset sum, Lean proves a
rigidity theorem: outcome coherence permits one-coordinate hidden-selection
probes, and when every Fourier sample is nonzero these force any fixed
group-relabeling certificate to move whole groups.  Its all-zero-group count is
therefore unchanged.  This does not yet settle the paper's weaker label, which
stores only the most significant `log n` bits `s_j`; truncation can erase the
one-coordinate distinctions used by the rigidity proof.

The truncation escape is not automatic.  A concrete two-group, six-coordinate
witness uses samples `17, 34, 51, 68, 85, 153`, whose residues modulo `16` are
pairwise distinct.  On the measured fibre `z = 76 (mod 128)`, however, there
are four supported selections rather than only the two originally displayed.
All four have the complete local label `(h, s_a, s_b) = (1, 3, 9)`, and their
Hadamard signs are `+1, -1, -1, +1`.  The source outcome therefore has zero
coherent weight.  Swapping one coordinate across the groups splits this class
four ways and changes the normalized local weight from `0` to `1/64`.

[`LemmaOneFiniteSupportPrototype.lean`](SimonDCP/Arithmetic/LemmaOneFiniteSupportPrototype.lean)
checks the whole finite experiment.  Of all `720` coordinate permutations,
`288` create an all-zero group and `72` let the target full label factor through
the occupied source label; these are exactly the `72 = 2(3!)^2` permutations
that move the two groups as whole blocks.  None creates an all-zero group.  The
remaining `648` permutations all change the raw coherent weight from `0` to
`4`.  Moreover, all `27` six-bit outputs with at most three ones and no
all-zero group have raw source weight zero.  Thus the witness rules out an exact
interference-class repair by a useful coordinate permutation, but it does not
rule out a direct weight-nondecreasing repair: every local bad output is null.
The `/16` summary is a local truncation surrogate, not a complete instantiation
of the paper's relations among `n`, group size, and truncation width.

A different route avoids the swap entirely.  Restricted Parseval on the
Boolean cube gives, for every coordinate set `A`,

```text
Pr[D_A = 0 | Y, z'] >= 2^(-|A|).
```

Consequently the expected number of all-zero groups is at least
`(k/c) * n/log n`.  Boundedness alone yields probability
`(k-c)/(k*n^c-c) = Omega(n^(-c))` of reaching `n/log n` groups, which is already
amplifiable in polynomial time.  Requiring Boolean subset sums to be injective
on every union of two groups makes the group-zero indicators pairwise
independent; Chebyshev then gives failure probability
`O(log n/n)`.  The natural-language derivation and the remaining conditioning
and faulty-sample obligations are recorded in
[`LEMMA1_REPAIR.md`](LEMMA1_REPAIR.md).

Lean now proves the restricted character identity, the collision-count form
of Parseval, and the diagonal lower bound after summing every occupied complete
Step-4 label.  It normalizes that bound to the exact rational baseline
`2^(-|A|)`, proves the finite weighted tail inequality, and simplifies the
paper's parameter ratio to `(k-c)/(k*n^c-c)`.  The high-probability route still
needs its size-biased conditioning and fault-model estimates.

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

The page-14 exponent does admit a local repair.  The standard-deviation
exponent already contains `-n`, so multiplication by `kappa' = 2^n` must cancel
that term.  The printed calculation instead retains an extra `+n`.  Correcting
it changes the total exponent at `c = 12` from

```text
-n/2 + 6n/(c' log n) + 6 log n,
```

to

```text
-3n/2 + 6n/(c' log n) + 6 log n.
```

Consequently the desired exponent is at most `-n` under the explicit budget
`12n/(c' log n) + 12 log n <= n`.  The same module proves that the amplitude
sum factors out the mean bin multiplicity `mu`, not the total `|A_(g_a)|`, and
that retaining the actual `n^(3/2)` bound gives polynomial exponent `-2` at
`c = 12`.  These repairs are in
[`Lemma4Parameters.lean`](SimonDCP/Probability/Lemma4Parameters.lean).

Even without correcting the extra `+n`, the printed exponent at `c = 12` is
`-n/2 + o(n)`.  If this were first established as a simultaneous absolute
error bound on normalized amplitudes, it would absorb every downstream
polynomial factor.  Thus the exponent typo is repairable and is not the
decisive obstruction to Lemma 4.

The repaired arithmetic does not establish the conditional balls-in-bins
premises or overcome signed-amplitude cancellation.  The final
multiplicative-amplitude conclusion of Lemma 4 therefore remains unproved, not
refuted.  The detailed audit is in [`AUDIT.md`](AUDIT.md).

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
- `Arithmetic/SwapFiberRepair.lean` proves the exact matching condition, the
  complete-coordinate permutation identity, and partial certificate interfaces
  for the still-missing Step-4 interference and measured-weight arguments.
- `Arithmetic/LemmaOneFiniteSupportPrototype.lean` models the complete local
  `(h, s_a, s_b)` label, exhausts the six-coordinate support and all `720`
  coordinate permutations, and computes exact coherent weights for all `64`
  measured output masks.
- `Probability/RestrictedParseval.lean` proves restricted Walsh orthogonality
  and the finite signed-amplitude Parseval identity used by the swap-free
  repair.
- `Probability/LabelledParseval.lean` sums that identity across arbitrary
  occupied coherent labels and proves the exact `2^(Q-|A|) * |Z_Y|` diagonal
  lower bound.
- `Probability/LabelledBornProbability.lean` divides by the exact
  `2^Q * |Z_Y|` denominator and proves the normalized lower bound
  `2^(-|A|)` for every nonempty finite support.
- `Probability/BoundedTail.lean` proves the finite weighted first-moment bound
  that turns a lower expectation bound into an explicit upper-tail mass.
- `Probability/ResidueConditioningBound.lean` proves the exact rational Bayes
  loss and its dyadic affine-dimension specialization, conditional on the
  finite experiment's joint- and marginal-mass premises.
- `Probability/OneTimePadCounting.lean` constructs the translation equivalence
  showing that one selected free coordinate outside a local event makes all
  residue fibres equicardinal after the local samples are fixed.
- `Probability/ProjectionInjectivity.lean` proves that local Boolean
  subset-sum injectivity removes every off-diagonal residue-fibre collision,
  giving exact one- and two-group Parseval masses.
- `Probability/PairwiseBernoulliTail.lean` proves the corresponding finite
  pairwise-Bernoulli mean, second moment, variance, and Chebyshev bound.
- `LEMMA1_REPAIR.md` derives the restricted-Parseval replacement for Lemma 1
  and separates its unconditional inverse-polynomial conclusion from the
  stronger two-group-injectivity route.
- `Probability/Lemma4Parameters.lean` repairs the page-14 exponent arithmetic,
  distinguishes `mu` from total cardinality, and propagates the stated
  `n^(3/2)` amplitude bound.

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

The full project, including the Lemma 1 repair modules, was verified in Arch
Linux under WSL on August 10, 2026.  The command `lake build` completed all
8600 jobs successfully.

## Verification policy

Every theorem in the project must compile without `sorry`. Missing arguments
from the paper are recorded as named obligations or refuted by explicit
counterexamples; they are never silently promoted to assumptions. Final claims
are checked with `#print axioms`.  The analytic repair theorems report only the
standard Lean dependencies `propext`, `Classical.choice`, and `Quot.sound`.
The explicitly executable six-coordinate searches additionally report the
generated certificates named `*.native_decide.ax_*`, which record reliance on
Lean's native evaluator.  The audit reports no `sorryAx` and the source declares
no project-specific mathematical axiom.

See [AUDIT.md](AUDIT.md) for the proof-status map and
[LIBRARIES.md](LIBRARIES.md) for the TCS/quantum-library survey.
