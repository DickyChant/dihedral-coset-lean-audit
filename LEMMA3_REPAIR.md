# Repairing Lemma 3 by Born energy

Reference: [ePrint 2026/1591](https://eprint.iacr.org/2026/1591)

## Scope

The objective is to prove and formalize the mathematical core of Lemma 3, not
to preserve its proof sketch word for word.  In particular, the repaired proof
does not try to recover pairwise independence after the adaptive choice of
`A`.  It replaces that invalid step with finite Born-energy estimates that are
stable under arbitrary classical dependence of `A` on the measured mask `D`.

This document describes the repair and separates the proved finite
inequalities from the remaining circuit-to-finite-model bridge.

## The original obstruction

After Step 4, `A` is the first prescribed number of blocks on which the
measured Hadamard string `D` is zero.  Consequently `A = A(D)` and `D_A = 0`.
The proof of Lemma 3 nevertheless fixes the other entries of the transcript
and varies `D` as though:

1. the `A/B` partition and the compatible path sets did not change; and
2. the signs of all distinct paths were pairwise independent.

Neither assertion follows.  Paths with the same `B` part and different `A`
parts have exactly the same sign because

```text
(-1)^(phi dot D) = (-1)^(phi_B dot D_B).
```

Moreover, `D` is sampled with its Born weight, not uniformly.  A Chebyshev
bound under a hypothetical uniform mask distribution therefore cannot be
read directly as a probability over measured transcripts.

These points invalidate the proof sketch, but they do not refute the final
probability bounds.

## Exact finite repair of the well-behaved bound

Let `M` be a complete accepted transcript and let `h` range over the two final
branches.  Write

```text
Delta(M,h) = tPlus(M,h) - tMinus(M,h),
t(M,h)     = tPlus(M,h) + tMinus(M,h).
```

Suppose the paths in one `(M,h)` fibre have a common squared magnitude
`scale(M,h)`.  The coherent Born contribution and the corresponding
incoherent path energy are then

```text
coherent(M,h)   = scale(M,h) * Delta(M,h)^2,
incoherent(M,h) = scale(M,h) * t(M,h).
```

If both branches fail the explicit squared well-behaved threshold

```text
Delta(M,h)^2 >= 2^(-n) * t(M,h),
```

then, pointwise in `M`,

```text
BornMass(M) <= 2^(-n) * sum_h incoherent(M,h).
```

Now refine the experiment by retaining the original path as an orthogonal
label.  Completeness of this refined measurement gives

```text
sum_(M,h) incoherent(M,h) <= 1.
```

Summing the pointwise inequality proves that the joint Born mass of accepted
transcripts for which both branches are below threshold is at most `2^(-n)`.
No independence or uniformity of `D` is used, and `A` may be an arbitrary
function of the already measured part of the transcript.

The finite inequality and its exact `2^(-n)` specialization are formalized in
`SimonDCP/Probability/LemmaThreeBornBounds.lean`.

## Exact finite repair of the implicit-component tail

For a transcript `M`, let `p(M)` be its unnormalized Born mass.  After `(Y,D)`
has been measured, `A(D)` is fixed.  Reversibly compute an additional sector
label `z` before the operation that erases or merges that label.  Let
`u(M,z)` be the resulting unnormalized component and define the paper's
normalized implicit component by

```text
alpha(M,z) = u(M,z) / sqrt(p(M)).
```

The reversible sector refinement gives the energy identity or inequality

```text
sum_(M,z) |u(M,z)|^2 <= 1.
```

For any positive squared threshold `R2`, if some component satisfies

```text
R2 * p(M) < |u(M,z)|^2,
```

then the mass of that transcript is at most the sum of its labelled component
energies divided by `R2`.  Summing over transcripts gives

```text
Pr[exists z, |alpha(M,z)|^2 > R2] <= 1 / R2.
```

Taking `R2 = 2^(3*n)` yields `2^(-3*n)`, stronger than the exponential scale
requested by Lemma 3.  The argument does not require the transcript to be
well-behaved.

For the corollary, compute the high `log n` bits as the sector label directly.
Taking `R2 = n^3` gives an `n^(-3)` joint tail, avoiding a lossy union bound
over exact residues.

Both finite bounds are formalized in
`SimonDCP/Probability/LemmaThreeBornBounds.lean`.

## Conditioning convention

The bounds above are joint masses in the experiment in which the displayed
transcripts are retained.  If the statement is instead interpreted as a
conditional probability given an earlier acceptance event of mass `rho`, the
right-hand side must be divided by `rho` unless the refined experiment is
normalized directly inside that accepted branch.

This distinction is harmless for the `2^(-3*n)` and `n^(-3)` component tails
when `rho` is inverse-polynomial, but it must be stated explicitly for the
first `2^(-n)` bound.  The paper's phrase "over choices of M" does not specify
this convention precisely.

## Fixed affine conditioning criterion

`SimonDCP/Probability/ConditionalLinearForms.lean` records a separate exact
criterion.  On a reachable fixed affine fibre `condition x = c`, a pair of
binary linear observations is jointly uniform if and only if its restriction
to `ker condition` is surjective.  Equivalently, two condition-preserving dual
masks realize the outputs `(1,0)` and `(0,1)`.

This criterion is useful for auditing conditional-independence claims, but it
is not the main repair route for Lemma 3.  The actual selection rule `A(D)` is
adaptive and need not define one fixed affine fibre.

## Remaining formal bridge

The abstract probability inequalities are complete.  To close the repaired
core Lemma 3 theorem for the paper's analytic experiment, the following
identifications remain:

1. define the complete finite transcript for Steps 3--7;
2. identify the paper's `tPlus`, `tMinus`, and common path magnitude with the
   coherent and incoherent energies used by the first theorem;
3. prove that retaining the original path is a normalized refined experiment;
4. after measuring `(Y,D)`, compute exact `z` and its high-bit bucket as
   reversible orthogonal labels;
5. identify the paper's implicit `alpha_z` with the normalized refined-sector
   component;
6. state explicitly whether the final probability is joint or conditioned on
   reaching Step 7, and normalize accordingly.

Until these bridges are machine-checked, the correct status is: the original
proof is invalid, the replacement finite bounds are proved, and the repaired
Lemma 3 experiment-level theorem is in progress.
