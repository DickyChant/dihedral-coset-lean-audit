# Lemma 1 repair program

Reference: Daniel R. Simon,
[*A Polynomial-Time Quantum Algorithm for the Dihedral Coset Problem*](https://eprint.iacr.org/2026/1591),
IACR ePrint 2026/1591, Lemma 1 and Steps 2--4.

This note completes a repaired proof of the core constant-probability statement
of Lemma 1.  It does not use the paper's invalid low-part swap.  The first
conclusion below is an unconditional inverse-polynomial repair.  The stronger
constant-probability conclusion uses a sparse subset-sum event.  The complete
analytic experiment for one fixed classical fault environment is formalized
from the mixed correct/fault amplitudes through the Step-2 joint measurement
law and the Step-4 Born distribution to the collision-plus-Chebyshev bound.
Classical averaging over arbitrary finite fault-environment distributions is
also proved.  General rounded parameters and their budgets are formalized for
a padded complete-group sample schedule.  The corrected faulty sampler and
this padding are deliberate repairs, not outstanding obligations: the project
targets the paper's core mathematical claims rather than a verbatim rendering
of every displayed formula and convention.

The development does not claim a gate/tensor-circuit equality or a
density-matrix construction.  Those would strengthen the semantic connection
to a particular implementation or physical noise model, but they are not
needed for the repaired Lemma 1 probability theorem.  Lemmas 3 and 4, the later
algorithmic steps, and therefore the paper's overall polynomial-time theorem
remain open.

## 1. Exact Step-4 weight

Fix a measured Step-2 residue `z'` and a measured Fourier-sample vector `Y`.
Let `Z_Y` be the supported hidden selection strings:

```text
Z_Y = {phi in Omega | sum_i phi_i * y_i = z' (mod 2^(n-1))}.
```

Here `Omega` is the affine subcube obtained by fixing the selection bits of any
faulty samples.  Let

```text
label_Y(phi) = (h_Y(phi), s_1,Y(phi), ..., s_G,Y(phi))
```

be the complete orthogonal label retained after Step 4.  For an occupied label
`lambda`, define

```text
F_lambda = {phi in Z_Y | label_Y(phi) = lambda},
A_lambda(D) = sum_{phi in F_lambda} (-1)^(phi dot D).
```

The conditional Born probability of `D` is exactly

```text
p_Y(D) = 1 / (2^Q * |Z_Y|) * sum_lambda |A_lambda(D)|^2.       (1)
```

The secret phase requires one correction before this formula applies to faulty
samples.  The paper describes a correct sample as
`2^(-1/2) sum_b |b,x+bd>` and a faulty sample as `|b,x>`, but its displayed
Step-1 product formula writes `x_i+b_i d` at every coordinate, including the
faulty coordinates.  Those statements are inconsistent.  The formal model
follows the stated faulty sampler: only correct coordinates carry the secret
shift, while a faulty coordinate remains at `x_i` with a fixed selection bit.

If `F` is the set of correct/free coordinates, every supported selection then
satisfies the exact decomposition

```text
fullSubsetSum = freeSelectedSum + fixedFaultyContribution.
```

Consequently the residue equation is equivalently a translated equation for
the free sum.  `FaultySamplePhase.lean` proves the support-level decomposition,
and `BooleanMaskBridge.lean` identifies the Boolean coordinate subcube and
residue fibre with the mask support used below.

The analytic amplitude chain is now explicit.  `FaultyBasisSample.lean` proves
the one-coordinate Fourier and Hadamard laws of `|b,x>`, and
`FaultPatternProductAmplitude.lean` constructs the normalized product
selection amplitude on a fixed coordinate subcube.
`FaultPatternFourierProduct.lean` first supplies a phase-free product formula.
`MixedFaultPatternFourierProduct.lean` then proves that the corrected mixed
amplitude--using `x_i+b_i d` on correct coordinates and `x_i` on faulty
coordinates--is exactly that formula times an explicit unit secret phase.
Its pointwise support and squared norms are therefore unchanged, and the full
Fourier vector `Y` is uniform for every fixed environment.

`StepTwoMeasurementBridge.lean` represents measurement of the low `n-1` bits
as the canonical quotient `ZMod (2^n) -> ZMod (2^(n-1))` and proves that the
resulting Boolean selection fibre is exactly the mask fibre in (1).
`StepTwoJointKernel.lean` normalizes the joint law of `(Y,z')`, proves total
mass one and the required local uniformity, and identifies its real cast
pointwise with the sum of the mixed-amplitude Born masses over that measured
fibre.

The actual secret exponent is the free-coordinate subset sum, whereas the
classical Step-2 sum also contains the fixed faulty contribution.
`FaultyHighBitCarry.lean` performs the affine high-bit borrow/carry calculation.
After `z'` is fixed, the offset contributes a common unit phase depending only
on `z'` and the fixed environment; the only selection-dependent high-bit factor
is `(-1)^(h_Y(phi) * d_n)`.  Thus no extra carry bit is needed in the complete
Step-4 label.  `StepFourLabelPhaseBridge.lean` removes this common unit phase
from each label fibre.  `ActualStepFourBorn.lean` factors the raw projected
Hadamard amplitudes, computes their total mass, proves that their normalized
ratio is the conditional Step-4 Born law in (1), and identifies it pointwise on
every reachable Step-2 fibre.  Under the corresponding local subset-sum
injectivity hypotheses, it also gives the exact one- and two-group zero-event
masses.

These are analytic product-amplitude and finite measurement-law theorems
conditioned on one classical fault environment.  They are not a QuantumAlg
gate/tensor-circuit equality, and `RandomFixedBitsMixture.lean` is only a
classical uniform-mask pushforward theorem, not an unconditional quantum
density-mixture construction over random fault environments.

## 2. Restricted Parseval identity

For a coordinate set `A`, write `D_A = 0` for the event that every coordinate
of `D` in `A` is zero.  Expanding the squares in (1) and summing over the free
coordinates of `D` gives

```text
Pr_Y[D_A = 0]
  = 2^(-|A|) / |Z_Y|
      * sum_lambda #{(phi, psi) in F_lambda^2 |
          phi restricted to A^c = psi restricted to A^c}.     (2)
```

This is ordinary character orthogonality on the Boolean cube.  Every diagonal
pair survives, hence

```text
Pr_Y[D_A = 0] >= 2^(-|A|).                                   (3)
```

Unlike the paper's sign-symmetry claim, (2) is a deterministic identity for
every supported `Y` and every measured residue `z'`.

## 3. Unconditional inverse-polynomial repair

Let every group have size

```text
m = c * log_2(n),
```

and use the paper's sample count `Q = k * n^(c+1)`.  Ignoring routine floor,
ceiling, and divisibility adjustments, the number of groups is

```text
G = Q / m = (k/c) * n^(c+1) / log_2(n).
```

Let `X_g` indicate that group `g` is all zero in `D`.  With
`Z = sum_g X_g`, (3) gives

```text
E[Z] >= G * 2^(-m)
     = (k / c) * n / log_2(n).
```

Set `a = n / log_2(n)`.  Since `0 <= Z <= G`,

```text
Pr[Z >= a]
  >= (E[Z] - a) / (G - a)
  >= (k - c) / (k * n^c - c)
  = Omega(n^(-c)).                                            (4)
```

Therefore the following corrected lemma has a short unconditional proof:

> If `k > c`, Step 4 produces at least `n / log_2(n)` all-zero groups with
> inverse-polynomial probability.

Independent repetition `O(n^c)` times amplifies (4) to constant success while
remaining polynomial time because `c` is constant.  A complete algorithmic
repair must propagate this changed repetition count through the later steps.

Restricted Parseval alone cannot generally improve (4) to a constant.  In an
abstract one-label example whose hidden support is the annihilator of the
subspace on which all group masks are equal, every all-zero-group event is the
same event and has probability `2^(-m)`.  Additional collision control is
therefore genuinely necessary for a constant bound.

The Lean development proves restricted Walsh orthogonality, the Parseval
identity over arbitrary finite Boolean supports, its extension across all
occupied full-label fibres, and the exact `2^(Q-|A|) * |Z_Y|` diagonal lower
bound.  It normalizes this finite mass by `2^Q * |Z_Y|` and proves the rational
`2^(-|A|)` statement, then proves the generic finite weighted tail inequality
and the simplification of its Lemma-1 parameter ratio.  For one fixed fault
environment, `ActualStepFourBorn.lean` now identifies this labelled law with
the normalized analytic mixed-amplitude Step-4 Born law.  A gate/tensor-circuit
or density-matrix realization is outside the scope of this probability proof;
the later algorithmic steps remain separate obligations for the overall paper
theorem.

## 4. Constant-probability repair

A clean sufficient condition on `Y` is **two-group subset-sum injectivity**:
for every two distinct groups `g` and `h`, the map

```text
u |-> sum_{i in group(g) union group(h)} u_i * y_i (mod 2^(n-1))
```

is injective on Boolean selections `u`.

Suppose two supported selections agree outside those two groups.  Subtracting
their two Step-2 fibre equations leaves equal subset sums on the union.  The
condition forces the selections to be equal.  Thus the collision count in (2)
contains only diagonal pairs for one- and two-group coordinate sets.  It
follows that

```text
Pr[X_g = 1] = 2^(-m),
Pr[X_g = 1 and X_h = 1] = 2^(-2m).
```

The indicators are pairwise independent.  Writing

```text
mu = E[Z] = (k / c) * n / log_2(n),
```

we have `Var(Z) <= mu`, and Chebyshev gives

```text
Pr[Z < n / log_2(n)]
  <= (k * c / (k - c)^2) * log_2(n) / n.                      (5)
```

This is high probability, stronger than the published constant-probability
claim.

Lean now formalizes the complete finite-model version of this implication.  It
defines Boolean subset-sum injectivity on masks supported inside a chosen union
of groups, transports the local problem to the restricted index type, and
proves the `3^|A|-1` ternary collision bound with the local rather than ambient
exponent.  A common complementary contribution cancels, yielding projection
injectivity of every coordinate-subcube residue fibre.  Restricted Parseval
then becomes an exact diagonal equality for one group and for a union of two
groups.  Lean constructs the full normalized output Born weight, proves its
total mass is one, obtains exact single-group means and disjoint two-group
moments, and feeds them to the finite pairwise-Bernoulli Chebyshev theorem.  The
result is the closed form (5), conditional only on the explicitly stated group
sizes, injectivity hypotheses, and rational parameter equalities.

Before conditioning, failure on one union `A` of `a <= 2m` independent uniform
coordinates has probability at most

```text
(3^a - 1) / M,                 M = 2^(n-1).                  (6)
```

A union bound over all pairs of groups remains exponentially small because
`c` and `k` are constants.  Lean packages every single group and every pair
union as one family, proves that the family has at most `N^2` members and that
each member has at most `2m` coordinates, and derives the corresponding
simultaneous local-failure bound.  The subtlety is that Step 2 measures `z'` before
`Y`, so the conditional law of `Y` is size-biased by `|Z_Y|`.

The conditioning loss can nevertheless be stated exactly.  Let the hidden
selection `Phi` be uniform on an affine Boolean space `Omega` of dimension
`R`, independently of uniform sample coordinates `Y_i`, and put
`Z = sum_i Phi_i Y_i`.  For an event `Bad_A` determined by `Y_A`, write

```text
p_A     = Pr[Bad_A],
epsilon = Pr[Phi = 0],
delta_A = Pr[Phi restricted to A^c is zero].
```

Then, for every residue `z'` having positive probability,

```text
Pr[Bad_A | Z = z']
  <= p_A * (1 + (M - 1) * delta_A)
       / (1 - epsilon + M * epsilon * 1[z' = 0]).             (7)
```

Here `epsilon` is either `0` or `2^(-R)`, while
`delta_A <= min(1, 2^(a-R))`.  Thus, if `R >= r >= a`, a uniform bound is

```text
Pr[Bad_A | Z = z']
  <= p_A * (1 + (M - 1) * 2^(-(R-r))) / (1 - 2^(-R)).        (8)
```

In the fault-free case `R = Q`.  In the paper's coordinate-subcube fault model,
let `F` be the free selection coordinates.  If every fixed coordinate outside
`A` is fixed to zero, then the exact exceptional factor is
`delta_A = 2^(-|F \ A|)`.  If any coordinate outside `A` is fixed to one, then
`delta_A = 0`.  Thus the unconditional statement is
`delta_A <= 2^(-|F \ A|)`.  Supported selections cannot differ at fixed fault
coordinates, so the necessary injectivity event concerns only
`S = A intersection F`, with prior failure probability at most
`(3^|S| - 1) / M`.  This stronger form retains the small factor `p_A` on the
exceptional branch and avoids demanding randomness from faulty `Y_i` values.

Lean proves the exact rational implication (7), its dyadic consequence (8),
and the finite counting premises from which (7) follows.  After fixing `Y_A`,
any selected coordinate outside `A` gives an explicit translation equivalence
between residue fibres.  Summing those fibres over an arbitrary finite
selection support gives the joint-count bound with exceptional numerator
`delta_A`; a separate full-sample count proves that only the globally zero
selection contributes the marginal numerator `epsilon`.  Lean normalizes both
counts and assembles the complete finite Bayes estimate for every nonempty
support and every residue of positive marginal mass.  It also proves the
uniform ternary-relation bound (6), the exact coordinate-subcube counts, and
the dimension implications

```text
R <= |F|, |A| <= r
  ==> epsilon <= 2^(-R), delta_A <= 2^(-(R-r)).
```

These facts are assembled into a coordinate-subcube specialization of (8).
For the concrete local bad event, Lean further splits the inside sample space
as `(F intersection A)` times `(A \ F)`, cancels the irrelevant complement
cardinality exactly, and proves the one-set conditioned estimate with explicit
prior factor

```text
(3^(|F intersection A|) - 1) / M.
```

Separately, a finite Markov theorem shows that per-coordinate fault marginal
at most `1/(c' L)` implies

```text
Pr[number of faults >= Q/2] <= 2/(c' L),
```

without assuming independence among faults.  The same weighted-space API adds
this exceptional event to the simultaneous local-collision event without an
independence assumption.  `FaultPatternSupportBridge.lean` identifies the
fault-set cardinality with that random variable, proves that its complement has
cardinality `Q - numberOfFaults`, and turns the good half-fault event into the
required lower bound on the coordinate-subcube dimension.
This combined environment theorem is a prior bound, not a claim that the same
fault marginals survive conditioning on a prescribed residue.  The intended
outer argument instead needs a uniform conditional success theorem for every
good realized environment and every reachable residue, followed by total-
probability averaging over the original environment law.

`LemmaOneOuterAveraging.lean` now proves exactly this finite two-level theorem:
an outer bad-event mass `p` plus a uniform good-environment conditional failure
bound `q` gives total failure at most `p+q`, without independence.  It also
proves that subset-sum injectivity is monotone under shrinking the coordinate
set, so injectivity on every full group or pair union automatically supplies
the `F intersection A` hypothesis for every realized fault pattern.  This gives
a shorter Lemma-1 route: bound bad full-coordinate `Y` in the prior, use the
same conditional Chebyshev bound for every good `Y` and reachable residue, and
average.  The half-free Markov bound is therefore useful for refined posterior
estimates and later algorithmic steps, but is not needed for the Step-4
all-zero-group conclusion itself.

For completeness, the more refined posterior route is also closed in the
finite model.  `CoordinateSubcubeConditionalFamily.lean` defines the common
selection/full-sample conditional weight, proves that each family event is
exactly noninjectivity on `F intersection A`, bridges it to the existing joint
counts, and derives both sum and `family.card` dyadic bounds.

`LemmaOneFiniteModel.lean` now performs the complete finite probability
assembly.  Its main bound adds the at-most-`N^2` ternary-collision term to the
conditional Chebyshev term, without assuming independence between the two
layers; explicit hypotheses budgeting each term by `1/4` give total failure at
most `1/2`.  `LemmaOneFixedEnvironment.lean` instantiates this theorem with
`StepTwoJointKernel` and the analytic Step-4 Born law.  Its outer outcome is
exactly `(Y,z')`, its inner law is pointwise the mixed-amplitude analytic
conditional Born law, and its conclusion holds for an arbitrary fixed free set
and arbitrary fixed faulty bits.  This closes the end-to-end analytic fixed-environment
estimate.  `LemmaOneFaultEnvironmentAveraging.lean` then preserves the same
bound under every nonnegative normalized finite classical distribution of
fault environments, without any independence assumption.  This is classical
probability averaging, not a density-matrix construction.

`RectangularGroupPartition.lean` constructs exactly `N` disjoint groups of
exactly `m` coordinates covering `N*m` coordinates.  The earlier
`LemmaOneExactParameters.lean` proves the expected-mean identity under the
stronger assumptions that the security parameter is exactly `2^logN` and the
sample count is exactly divisible by the group width.

The rounded repair removes those assumptions.  `LemmaOneRoundedParameters.lean`
sets `ell = floor(log_2 n)`, `m = c*ell`, and
`K = ceil(k*n^(c+1)/m)`.  Thus `K*m` covers the nominal sample count while
adding strictly fewer than one group.  Lean proves

```text
K * 2^(-m) >= (k/c) * (n/ell) > n/ell
```

when `0 < c < k` and `n >= 2`.  Since the Chebyshev ratio decreases as the
actual mean grows above the target, no exact-mean identity is needed.  The same
module proves a logarithmic sufficient collision condition and verifies both
`1/4` budgets for every `n >= 1024` with `c = 12` and `k = 24`.
`LemmaOneRoundedFixedEnvironment.lean` inserts these facts into the fixed and
classically averaged analytic experiments, giving failure mass at most `1/2`
with no remaining arithmetic budget hypothesis.  This completes the repaired
core constant-probability theorem.  `LemmaOneRepaired.lean` additionally
defines the complementary success event as an explicit event sum, proves that
its mass plus the strict lower-tail failure mass is one, and states the final
success-mass-at-least-`1/2` theorem directly.  The padded schedule collects
fewer than one extra complete group and is part of the repair, rather than a
blocker.  A
quantum density/channel realization would be an optional stronger semantics
result; later algorithmic steps remain open for the paper's overall theorem.

## 5. Why bit complementation is insufficient

For the complemented mask `D_bar = D xor 1^Q`, split one label amplitude into
even- and odd-weight selections:

```text
A_lambda(D)     = E_lambda(D) + O_lambda(D),
A_lambda(D_bar) = E_lambda(D) - O_lambda(D).
```

Consequently,

```text
p_Y(D) - p_Y(D_bar)
  = 2^(2-Q) / |Z_Y| * sum_lambda E_lambda(D) * O_lambda(D).
```

The right-hand side has no fixed sign.  Complementation supplies an identity,
not the zero-majority inequality asserted in the paper's first paragraph.

## 6. Formalization order and current status

1. **Proved:** Boolean character orthogonality, restricted Parseval on an
   arbitrary finite support, the full-label diagonal bound, its exact rational
   normalization, and the inverse-polynomial tail estimate (3)--(4).
2. **Proved for one fixed classical fault environment:** the corrected analytic
   mixed correct/fault product amplitude has the exact coordinate-subcube
   support and differs from the phase-free amplitude by a unit secret phase.
   This follows the stated faulty sampler `|b,x>`, not the inconsistent Step-1
   display that shifts faulty coordinates by `b d`.
3. **Proved for the analytic measurement law:** the Step-2 low-bit quotient
   fibre, normalized joint `(Y,z')` kernel, total mass, local uniformity, and
   pointwise Born-mass identification.
4. **Proved for the analytic Step-4 law:** the fixed faulty offset/high-bit
   carry is a common phase after fixing `z'`; the complete `(h,s_1,...,s_g)`
   label therefore gives exactly the labelled Walsh Born law.  Under the
   corresponding local subset-sum injectivity hypotheses, it also gives the
   exact one- and two-group masses.
5. **Proved:** local subset-sum injectivity implies coordinate-subcube
   residue-fibre projection injectivity, and the sparse ternary bound controls
   simultaneous failure over the at-most-`N^2` one- and two-group family.
6. **Proved in the finite model:** the normalized labelled Born law has the
   required Bernoulli means and pair moments, and Chebyshev gives (5).
7. **Proved for the coordinate-subcube conditioning model:** the one-time-pad
   fibre counts, distinct `delta_A` and `epsilon` branches, dyadic estimates,
   and the direct family bounds (7)--(8).
8. **Proved abstractly:** fault-count Markov control and prior-event unioning do
   not require fault independence; uniform free and fixed-fault bits push
   forward to a uniform full mask.
9. **Proved:** outer averaging combines the prior local-collision loss with a
   uniform conditional tail, and full-coordinate injectivity descends to every
   free-coordinate intersection.
10. **Proved end to end for the analytic fixed-environment experiment:**
    `LemmaOneFiniteModel.lean` assembles the collision and Chebyshev terms, and
    `LemmaOneFixedEnvironment.lean` instantiates it with the actual analytic
    Step-2 and Step-4 laws, including an explicit failure-at-most-`1/2` theorem
    under two `1/4` budgets.
11. **Proved at the classical mixture level:** every normalized finite mixture
    of the fixed-environment analytic experiments inherits the same bound, even
    when positions and fault data vary with the environment.
12. **Proved in a stronger arithmetic special case:** the exact mean when
    the security parameter is a power of two and the sample count is exactly
    divisible by the group width.
13. **Proved for general integer security parameters:** floor-log group width,
    ceiling-rounded complete groups, the mean lower bound, and explicit
    collision/tail budgets.  For `c = 12`, `k = 24`, and `n >= 1024`, the
    classically averaged analytic failure mass is at most `1/2` without extra
    arithmetic hypotheses.
14. **Completed:** `LemmaOneRepaired.lean` exposes the repaired core Lemma 1
    statement directly: the explicitly summed success event has mass at least
    `1/2` for general integer security parameters and arbitrary normalized
    finite classical fault-environment mixtures.  The
    published swap argument remains invalid, but is no longer used.  A
    gate/tensor-circuit equality and quantum density-mixture construction are
    optional semantic strengthening, not blockers for this result.  Lemmas 3
    and 4 and the later algorithmic steps remain open, so the paper's overall
    polynomial-time theorem is not yet established.
