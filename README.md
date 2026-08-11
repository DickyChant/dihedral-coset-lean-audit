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

**Bottom line:** the published proof of Lemma 1 is invalid, but its core
constant-probability claim now has a corrected proof formalized in Lean.  The
repair follows the draft's textual faulty-sample definition where its Step-1
display is inconsistent, and supplies an explicit rounding convention where
the schedule is underspecified; the goal is to prove the core mathematical
claim, not to reproduce the draft line by line.
The final claims of Lemmas 3 and 4 remain unproved and not refuted, and the
paper's overall headline algorithm theorem remains open.

| Lemma | Status of the core claim | Published proof and repair status |
| --- | --- | --- |
| Lemma 1 | **Repaired and formalized** | The proposed low-part swap is invalid, so the repair replaces it rather than completing that argument. Restricted Parseval gives an unconditional inverse-polynomial bound, while the stronger route connects the corrected mixed correct/fault amplitudes, Step-2 joint law, complete Step-4 label, exact Born moments, collision-plus-Chebyshev bound, classical fault-environment averaging, and rounded parameters. For the padded repaired schedule with `k = 24`, `c = 12`, and every `n >= 1024`, the explicitly summed success event has mass at least `1/2`. This is the formalized constant-probability core needed from Lemma 1. |
| Lemma 3 | Unproved, not refuted | The phases are not pairwise independent after the adaptive choice of `A`. |
| Lemma 4 | Unproved, not refuted | The exponent, `mu`, and `n^(3/2)` bookkeeping errors are repaired. A finite corrected theorem now gives high-probability additive control from explicit per-bin tails, and relative control with an explicit anti-cancellation lower bound. Establishing those hypotheses for the paper's conditioned experiment remains open. |

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
that Lemma 1's constant-probability conclusion is false.  The injection
argument is refuted; the independent restricted-Parseval and
collision-plus-Chebyshev route below proves a repaired version of the core
conclusion.

[`SwapFiberRepair.lean`](SimonDCP/Arithmetic/SwapFiberRepair.lean) proves the
exact repair criterion: for a zero/one swap with measured modulus
`B * stride`, the original low-part operation is valid exactly when
`stride` divides `H_i - H_j`.  It also proves that permuting each complete
Fourier sample together with its selection and Hadamard-output coordinates is
a bijection preserving the subset sum, every measured residue fibre, the phase
exponent, and sample distinctness.

This repairs the algebraic map, but not the original Lemma 1 injection route;
that route is not needed by the completed replacement proof.  After Step 4,
terms with equal `(h, s_1, ..., s_g)` labels interfere.  A termwise
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
`O(log n/n)`.  The natural-language derivation, the fixed-environment theorem,
the rounded-parameter repair, optional circuit-level refinements, and the later
algorithmic obligations are recorded in
[`LEMMA1_REPAIR.md`](LEMMA1_REPAIR.md).

Lean now proves the restricted character identity, the collision-count form
of Parseval, and the diagonal lower bound after summing every occupied complete
Step-4 label.  It normalizes that bound to the exact rational baseline
`2^(-|A|)`, proves the finite weighted tail inequality, and simplifies the
paper's parameter ratio to `(k-c)/(k*n^c-c)`.  For the high-probability route,
Lean now also proves the uniform ternary collision bound `(3^a-1)/M`, transports
it to local Boolean subset-sum injectivity, and unions it over the complete
family of one- and two-group sets.  It aggregates the one-time-pad residue
fibres over an arbitrary finite selection support, derives the exact joint and
marginal count formulas with distinct `delta` and `epsilon` exceptional sets,
and specializes the normalized Bayes bound to an actual coordinate subcube.
The faulty fixed bits contribute only a selection-independent phase, and the
Boolean coordinate-subcube residue fibre is identified exactly with the mask
support used by restricted Parseval.  On that support Lean constructs the full
normalized Born weight, proves the exact one- and two-group moments under the
corresponding local subset-sum injectivity hypotheses, and derives the displayed
`O(log n/n)` Chebyshev bound after charging failures of those hypotheses to the
ternary-collision event.  It also bounds excessive faults by Markov from
per-coordinate fault marginals, without assuming fault independence.

The analytic fixed-environment composition is now also formalized.  The paper
describes a faulty sample as `|b,x>`, but its displayed Step-1 product formula
uses `x_i + b_i d` at every coordinate, including faulty ones.  The development
follows the stated faulty sampler: a correct coordinate uses `x_i + b_i d`,
whereas a faulty coordinate uses `x_i` and has no secret shift.
`MixedFaultPatternFourierProduct.lean` proves that this mixed analytic product
amplitude is the earlier coordinate-subcube amplitude times an explicit unit
secret phase.  `StepTwoMeasurementBridge.lean` identifies measurement of the
low `n-1` bits with the canonical quotient map, and
`StepTwoJointKernel.lean` proves the normalized joint law of the full Fourier
vector and that residue, pointwise equal after casting to the mixed-amplitude
Born mass summed over the measured fibre.  `FaultyHighBitCarry.lean` proves
that the fixed faulty offset contributes only a residue- and
environment-dependent unit phase; the remaining selection-dependent factor is
captured by the paper-style high bit `h`.  `ActualStepFourBorn.lean` then
factors the raw projected Hadamard amplitudes, computes their total mass, proves
that raw output mass divided by total mass is the normalized conditional
Step-4 Born weight, and identifies that weight pointwise with the labelled
Walsh law on every reachable Step-2 fibre.  Under the corresponding local
subset-sum injectivity hypotheses, it also obtains the exact one- and two-group
masses.

`LemmaOneFiniteModel.lean` combines the ternary collision bound, local
injectivity, Chebyshev, and outer averaging.  `LemmaOneFixedEnvironment.lean`
instantiates it with the Step-2 joint kernel and the analytic Step-4 Born law,
giving the collision-plus-tail bound, and a failure bound of `1/2` when each
summand is budgeted by `1/4`.  This closes the fixed-fault-environment analytic
model.  `LemmaOneFaultEnvironmentAveraging.lean` then proves that the same bound
survives every nonnegative normalized finite classical mixture of such
environments, even when positions, free coordinates, fixed bits, and group
summaries vary with the environment.  This is probability-level averaging,
not a QuantumAlg gate/tensor-circuit equality or a quantum density-mixture
construction.  The older exact arithmetic theorem
`LemmaOneExactParameters.lean` assumes a power-of-two security parameter and
exact divisibility.  For a padded repaired sample schedule,
`LemmaOneRoundedParameters.lean` removes both restrictions by taking
`ell = floor(log_2 n)`, rounding the number of complete groups upward, and
collecting fewer than one extra group of samples.  It proves the required
mean lower bound and explicit collision/tail budgets.  The end-to-end module
`LemmaOneRoundedFixedEnvironment.lean` gives failure mass at most `1/2` for
`k = 24`, `c = 12`, and every `n >= 1024`, including arbitrary normalized
finite classical fault-environment mixtures.  `LemmaOneRepaired.lean` defines
the complementary success event explicitly, proves that success and failure
masses sum to one, and exposes the direct success-mass-at-least-`1/2` theorem.
A density-matrix/channel
realization of the random fault process is an optional semantic refinement, not
an obligation for the analytic Lemma 1 repair.  The later algorithmic steps
remain open.

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

[`Lemma4Repair.lean`](SimonDCP/Probability/Lemma4Repair.lean) now packages the
valid deterministic conclusion of the proposed balls-in-bins step. If the two
high-bit branches have bin counts within `error` of one common mean and every
signed coefficient has magnitude at most `coefficientBound`, their amplitudes
differ additively by at most

```text
2 * numberOfBins * error * coefficientBound.
```

The same file proves that this becomes a relative, multiplicative estimate
only after assuming an explicit positive lower bound on one reference
amplitude. That anti-cancellation lower bound, or a replacement such as phase
alignment, is the precise additional obligation missing from the sketch.

The repair is also lifted to a normalized finite probability space. If every
bin in each of the two branches has deviation-event mass at most `tail`, Lean
proves additive success mass at least

```text
1 - 2 * numberOfBins * tail.
```

With a uniform positive reference-amplitude lower bound, the relative success
event has the same mass. The existing finite pairwise-Bernoulli Chebyshev
theorem can supply each per-bin tail when the required conditional moment
identities are available; the repair deliberately does not infer them from the
paper's unconditioned distribution.

Even without correcting the extra `+n`, the printed exponent at `c = 12` is
`-n/2 + o(n)`.  If this were first established as a simultaneous absolute
error bound on normalized amplitudes, it would absorb every downstream
polynomial factor.  Thus the exponent typo is repairable and is not the
decisive obstruction to Lemma 4.

The repaired finite theorem does not establish its conditional concentration
or anti-cancellation hypotheses for the paper's actual experiment. The
original multiplicative-amplitude claim of Lemma 4 therefore remains unproved,
not refuted. The detailed audit is in [`AUDIT.md`](AUDIT.md).

## Project scope

This Lean 4 project formalizes and audits Daniel R. Simon's preliminary draft
[*A Polynomial-Time Quantum Algorithm for the Dihedral Coset Problem*](https://eprint.iacr.org/2026/1591)
(IACR ePrint 2026/1591).

The draft's headline theorem is not currently represented as a proved Lean
theorem. Its proof relies on several false or unproved intermediate claims. The
development therefore starts with the sound algebraic kernel and kernel-checkable
obstructions to the invalid proof steps. It does not use `sorry` or hide gaps as
axioms.  Within that larger open program, the repaired core claim of Lemma 1 is
now a proved Lean result; the remaining headline-theorem gaps occur later.

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
- `Probability/AffineResidueCounting.lean` aggregates those fibres over an
  arbitrary finite selection support, proves the bad-inside joint-count bound,
  and separately computes the full-sample marginal with only the zero mask as
  an exceptional selection.
- `Probability/FiniteConditioningMass.lean` normalizes the natural-number joint
  bound and marginal identity into exact rational masses.
- `Probability/ResidueConditioningAssembly.lean` identifies the inside/outside
  sample split and assembles the count lemmas with the rational Bayes theorem.
- `Probability/TernarySubsetSumBound.lean` proves the exact `3^a-1` relation
  count, the one-relation `|G|^(a-1)` bound, and the normalized collision bound
  `(3^a-1)/|G|` under uniform sampling.
- `Probability/TernaryProjectionBridge.lean` transports ternary collision
  freeness to Boolean subset-sum injectivity on a prescribed local coordinate
  set, with exponent equal to the local cardinality rather than the ambient one.
- `Probability/SimultaneousLocalInjectivity.lean` and
  `Probability/GroupUnionFamily.lean` union these local failures over every
  one- and two-group set, giving the explicit `N^2` family-size bound without
  assuming independence between local events.
  `Probability/RectangularGroupPartition.lean` supplies exact-size,
  pairwise-disjoint groups and their Born/union-bound interfaces when the
  coordinate count is exactly `N*m`.
- `Probability/CoordinateSubcubeSupport.lean` proves the exact cardinality and
  the two branches of the exceptional `delta` count for fixed faulty bits;
  `Probability/CoordinateSubcubeParameters.lean` turns these counts into the
  dyadic conditional Bayes estimate, and
  `Probability/CoordinateSubcubeConditionalInjectivity.lean` supplies its
  explicit local ternary prior factor after integrating out irrelevant inside
  coordinates.  `Probability/CoordinateSubcubeConditionalFamily.lean` places
  all local events on one residue-conditioned space and proves sum and uniform
  family-cardinality bounds.
- `Probability/FaultySamplePhase.lean` and
  `Probability/BooleanMaskBridge.lean` show that fixed faulty selections add
  only a common group-character factor and identify the Boolean residue fibre
  exactly with the mask support used by Parseval.
- `Quantum/FaultyBasisSample.lean` proves the missing one-coordinate quantum
  facts: a faulty basis sample has a uniform Fourier-position outcome, its
  fixed branch bit has uniform Hadamard readout, and that bit contributes only
  the expected unit phase.  `Quantum/FaultPatternProductAmplitude.lean`
  constructs the normalized product selection state for an arbitrary fault
  pattern and proves that its Born support is exactly the coordinate subcube.
  `Quantum/FaultPatternFourierProduct.lean` extends an explicit phase-free
  product amplitude through every position DFT and proves that its joint
  Fourier sample `Y` is exactly uniform, independently of the fault pattern
  and fixed bits.  `Quantum/MixedFaultPatternFourierProduct.lean` replaces the
  phase-free formula by the analytic mixed correct/fault amplitude for one
  fixed environment and proves exact equality up to an explicit unit secret
  phase, preserving pointwise support and squared norms.  The paper's Step-1
  display shifts faulty coordinates despite describing the faulty sampler as
  `|b,x>`; this module follows the latter and applies no secret shift at a
  faulty coordinate.  It remains an analytic amplitude identity, not a
  gate/tensor-circuit construction.
- `Probability/StepTwoMeasurementBridge.lean` models the measured low
  `n-1` bits by the canonical quotient from `ZMod (2^n)` to
  `ZMod (2^(n-1))` and identifies its Boolean fibre exactly with the
  coordinate-subcube mask fibre.  `Probability/StepTwoJointKernel.lean`
  normalizes the joint Fourier-vector/residue counting law, proves its exact
  total mass and local uniformity, and identifies its real cast pointwise with
  the analytic mixed Born mass on the measured fibre.
- `Probability/FaultyHighBitCarry.lean` computes the affine borrow/carry from
  the fixed faulty offset.  After conditioning on the Step-2 residue, that
  contribution is a common unit phase and no extra carry label is needed beyond
  the paper-style high bit `h`.  Together with
  `Probability/StepFourLabelPhaseBridge.lean`,
  `Probability/ActualStepFourBorn.lean` identifies the analytic conditional
  Step-4 output law pointwise with the labelled Walsh law on each nonempty
  measured fibre, derives its normalization directly from the raw projected
  amplitudes, and proves exact one- and two-group zero-event masses under local
  injectivity.
- `Probability/CoordinateSubcubeProjection.lean` and
  `Probability/CoordinateSubcubeBorn.lean` prove exact diagonal Parseval and
  exact one- and two-group zero-event masses using injectivity only on the free
  local coordinates.
- `Probability/LabelledBornPairwiseTail.lean` constructs the complete normalized
  output weight, supplies the Bernoulli mean and pair-moment hypotheses, and
  derives the paper-facing `O(log n/n)` lower-tail estimate together with
  `Probability/LemmaOneChebyshevParameters.lean`.
- `Probability/FaultCountMarkov.lean` and
  `Probability/FaultPatternSupportBridge.lean` identify the actual free-set
  cardinality and control the loss of half the free coordinates;
  `Probability/RandomFixedBitsMixture.lean` proves that uniformly random free
  bits together with uniformly random fixed-fault bits push forward to the
  uniform full Boolean mask, independently of the fault partition;
  `Probability/LemmaOneGoodEnvironment.lean` combines excessive faults with
  local-collision failure on the prior environment space.  None of these steps
  assumes independence of the fault coordinates or exceptional events; this
  theorem is not itself a posterior bound after fixing a measured residue.
- `Probability/LemmaOneOuterAveraging.lean` proves injectivity monotonicity and
  the shorter total-probability assembly: prior bad-environment mass `p` plus a
  uniform good-environment conditional tail `q` gives total failure at most
  `p+q`.
- `Probability/LemmaOneFiniteModel.lean` assembles the rectangular-group
  collision and conditional Chebyshev terms and supplies explicit `1/4 + 1/4`
  budgets.  `Probability/LemmaOneFixedEnvironment.lean` instantiates that
  theorem with the analytic Step-2 joint kernel and Step-4 Born law for any one
  fixed classical fault environment.
  `Probability/LemmaOneFaultEnvironmentAveraging.lean` preserves the resulting
  bound under arbitrary normalized finite classical mixtures of environments;
  it deliberately does not claim a density-matrix construction.
  `Probability/LemmaOneExactParameters.lean` records the stronger exact
  power-of-two/divisibility special case.
  `Probability/LemmaOneRoundedParameters.lean` instead proves floor-logarithmic
  group widths, ceiling group division, a mean lower bound, and checkable
  collision/tail budgets without either restriction.  It verifies those
  budgets uniformly for `k = 24`, `c = 12`, and `n >= 1024`.
  `Probability/LemmaOneRoundedFixedEnvironment.lean` plugs these facts into the
  actual analytic and classical-environment chains and proves the resulting
  failure mass is at most `1/2`.
- `Probability/LemmaOneRepaired.lean` is the public repaired Lemma 1 interface.
  It explicitly sums the event with at least `n / floor(log_2 n)` all-zero
  groups, proves its mass plus the strict lower-tail mass is exactly one, and
  concludes success mass at least `1/2` for both fixed and arbitrary normalized
  finite classical fault-environment mixtures.
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
- `Probability/Lemma4Repair.lean` derives the valid pairwise additive-amplitude
  estimate from two near-uniform bin-count bounds, lifts it through a finite
  union bound to success mass `1 - 2 * numberOfBins * tail`, and proves the
  relative form under an explicit positive anti-cancellation lower bound.

The project deliberately separates the formalized and classically averaged
analytic experiment from a gate/tensor-circuit implementation, a quantum
density-mixture construction over random fault environments and the later adaptive-measurement,
postselection, amplification, and lattice-reduction arguments needed for the
headline result.

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

The full project, including the Lemma 1 and conditional Lemma 4 repair modules,
was verified on August 11, 2026. The command `lake build` completed all 8641
jobs successfully.

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
