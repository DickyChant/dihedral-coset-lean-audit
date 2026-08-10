# Lemma 1 repair program

Reference: Daniel R. Simon,
[*A Polynomial-Time Quantum Algorithm for the Dihedral Coset Problem*](https://eprint.iacr.org/2026/1591),
IACR ePrint 2026/1591, Lemma 1 and Steps 2--4.

This note gives a replacement route for Lemma 1.  It does not use the paper's
invalid low-part swap.  The first conclusion below is an unconditional
inverse-polynomial repair.  The stronger constant-probability conclusion uses
an additional sparse subset-sum event whose interaction with Step-2
conditioning and faulty samples is listed explicitly among the remaining proof
obligations.

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

The factor `(-1)^(h_Y(phi) * d_n)` is constant inside one full label
fibre, so it disappears after taking the squared magnitude.  The remaining
Fourier phase is global after fixing `Y` and `z'`.

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
and the simplification of its Lemma-1 parameter ratio.  What remains on this
route is identifying the paper's post-measurement QuantumAlg state with this
finite labelled model and instantiating the integer-rounded parameter
conventions.

## 4. Candidate constant-probability repair

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

Lean now formalizes the deterministic core of this implication.  It defines
Boolean subset-sum injectivity on masks supported inside a chosen union of
groups, proves that a common complementary contribution cancels, and derives
projection injectivity of every measured residue fibre.  Restricted Parseval
then becomes an exact diagonal equality for one group and for a union of two
groups.  The separate finite Bernoulli module proves the exact mean, second
moment, variance `G*p*(1-p)`, and a finite weighted Chebyshev bound.

Before conditioning, failure on one union `A` of `a <= 2m` independent uniform
coordinates has probability at most

```text
(3^a - 1) / M,                 M = 2^(n-1).                  (6)
```

A union bound over all pairs of groups remains exponentially small because
`c` and `k` are constants.  The subtlety is that Step 2 measures `z'` before
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
let `F` be the free selection coordinates.  Then the exact exceptional factor
is `delta_A = 2^(-|F \ A|)`.  Supported selections cannot differ at fixed fault
coordinates, so the necessary injectivity event concerns only
`S = A intersection F`, with prior failure probability at most
`(3^|S| - 1) / M`.  This stronger form retains the small factor `p_A` on the
exceptional branch and avoids demanding randomness from faulty `Y_i` values.

Lean now proves the exact rational implication (7) and its dyadic consequence
(8), assuming the displayed joint-mass and marginal-mass premises.  The main
one-time-pad kernel is also proved: after fixing `Y_A`, any selected free
coordinate outside `A` gives an explicit translation equivalence between the
outside-sample fibres of any two residues.  The remaining conditioning tasks
are to aggregate these equicardinal fibres over the affine selection support,
derive the joint and marginal premises of (7), instantiate the
coordinate-subcube fault support, and prove the required high-probability lower
bound on `|F|`.

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

1. **Proved:** Boolean character orthogonality and the restricted Parseval
   identity for one arbitrary finite support.
2. **Proved:** package arbitrary occupied full-label fibres, derive the exact
   `2^(Q-|A|) * |Z_Y|` diagonal lower bound behind (3), and prove the
   bounded-variable tail theorem, the algebraic ratio in (4), and the exact
   rational normalization giving (3).  Connecting the paper's concrete
   QuantumAlg state to this finite model remains bookkeeping rather than a new
   probabilistic claim.
3. **Proved:** local subset-sum injectivity implies residue-fibre projection
   injectivity and exact one- and two-group Parseval masses.
4. **Proved:** finite pairwise-Bernoulli second moments, variance, and
   Chebyshev; instantiate their parameters to obtain the displayed closed form
   (5) after the paper's rounding conventions are fixed.
5. Formalize the sparse subset-sum union bound under uniform `Y`.
6. **Bayes algebra and one-pad fibre equivalence proved; aggregation open:**
   derive the joint and marginal premises of (7) by summing the equicardinal
   outside-sample fibres over the affine selection support, then incorporate
   faulty coordinates.
7. Revisit the algorithm's total repetition count under both the unconditional
   and constant-probability repairs.
