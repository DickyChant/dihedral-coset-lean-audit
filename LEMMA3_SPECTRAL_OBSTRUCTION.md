# Spectral obstruction to the Lemma 3 decoder

Reference: [IACR ePrint 2026/1591](https://eprint.iacr.org/2026/1591)

## Status and scope

This note records a natural-language two-copy Fourier analysis of the decoder
used after Step 2.  It is not yet a Lean theorem.  Its purpose is to distinguish
three logically different questions:

1. whether the published pairwise-independence proof of Lemma 3 is valid;
2. whether the two standalone probability inequalities in Lemma 3 can be
   replaced by sound finite-energy inequalities; and
3. whether Steps 2--7 actually recover the secret top bit with
   inverse-polynomial bias.

The first answer is no, and the repository already formalizes the correlation
obstruction.  Sound abstract replacements for parts of the second question are
also formalized.  The new conclusion concerns the third question: in the clean,
fault-free instance below, the two-copy kernel of the proposed decoder is
asymptotically balanced between the correct and wrong outputs.  The previously
considered modification that retains the low summary `u` does not repair this.

The exact no-guard calculation is complete at the natural-language level.  For
the paper's concrete safe-residue guard and zero-low-Hadamard postselection, the
same conclusion follows from a remaining explicit Parseval perturbation bound.
That bound is described below but has not yet been written line by line or
formalized in Lean.  Accordingly, this document records a strong mathematical
obstruction and the current proof route, not a machine-checked countertheorem.

## Clean divisible parameter regime

It is enough to analyze the fault-free sampler.  The paper assumes a lower
bound on the probability of a correct sample, so the oracle that always returns
a correct sample is within the claimed input model.

Work along a divisible subsequence on which

```text
N = 2^n,
H = N/2,
B = N/n,
m = c * log_2(n),
q = 2^m = n^c,
a = n / log_2(n),
G = lambda * a * q,
lambda = k/c > 1.
```

Here `B` is the width of one high-summary interval, `q` is the number of
Boolean masks in one group, `a` groups are selected, and `G` candidate groups
are generated.  Rounding changes only lower-order terms and is irrelevant to
the spectral mechanism.

For a group mask `x : {0,1}^m` and independent uniform samples
`y_i : ZMod N`, define

```text
T_x = sum_i x_i * y_i mod N,
s_x = floor(T_x / B) in ZMod n.
```

The two-copy calculation is performed before conditioning on a single
classical transcript.  This is essential: measured transcripts are Born-size
biased, so an unweighted variance calculation after fixing them is not valid.

## Exact one-group Fourier kernel

Let `omega` be a primitive `N`-th root of unity.  For each frequency
`xi : ZMod N`, put

```text
D_xi = sum_(0 <= e < B) omega^(xi * e),
a_xi = n * |D_xi|^2 / N^2,
b_xi = D_xi / N.
```

When the complete high summary of a nonterminal group is recorded and its
Walsh outcome is zero, the exact averaged two-copy eigenvalue is

```text
p_xi = q^(-2) *
  (q + (q - 1) * (q - 2) * a_xi
     + 2 * (q - 1) * Re(b_xi)).
```

The three terms are respectively the equal-mask, distinct-nonzero-mask, and
zero/nonzero-mask contributions.  Two distinct nonzero Boolean masks give a
surjective two-coordinate linear map, so their subset sums are exactly uniform
on `ZMod N x ZMod N`; no heuristic independence is used here.

Summing all Walsh outcomes forces the two masks to be equal.  Hence the kernel
for a nonzero Walsh outcome is exactly `1 - p_xi`.

Interval Parseval gives

```text
sum_xi a_xi = 1,
|b_xi|^2 = a_xi / n.
```

These identities expose the basic spectral budget: only polynomially many
frequencies can receive a non-diagonal coherent enhancement.

## Almost every frequency is diagonal

Fix a large polynomial `P(n)`, for example `n^20`, and define

```text
Typical = {xi | a_xi <= 1 / (P * q)}.
```

Since `sum_xi a_xi = 1`, at most `P*q` of the `N = 2^n` frequencies are
exceptional.  On every typical frequency,

```text
p_xi = q^(-1) * (1 + o(1)).
```

Thus almost every mode sees a zero group through the equal-mask diagonal
contribution `1/q`, rather than through the larger coherent contribution that
the proof sketch implicitly needs.

## Exact transfer of the first-`a`-zero rule

In a fixed Fourier mode, every zero group contributes `p_xi`, every preceding
nonzero group contributes `1-p_xi`, and every group after the terminal selected
group contributes `1` after all its outcomes are summed.  Consequently the
whole first-`a`-zero selection rule has the exact transfer function

```text
A_xi = Pr[Binomial(G, p_xi) >= a].
```

This is an identity of the signed two-copy kernel, not an approximation by an
independent classical process.

For a typical frequency,

```text
G * p_xi = (lambda + o(1)) * a,
```

and `lambda > 1`.  A Chernoff estimate therefore yields

```text
A_xi = 1 - exp(-Omega(a)).
```

The paper's large candidate pool does not filter the diagonal modes.  It was
chosen large enough that modes with only the baseline success rate `1/q` also
obtain `a` zero groups with overwhelming probability.

## Correct and wrong terminal kernels

The safest exact bookkeeping retains the two `h*` sectors.  If two paths have
total-sum difference `DeltaT` and selected high bits `h*` and `h*'`, then,
after imposing the same measured `h'`, the correct and wrong pair coefficients
are

```text
K_wrong = (1/2) *
  (1[DeltaT = 0 and h* = h*']
   - 1[DeltaT = H and h* != h*']),

K_correct = (1/2) *
  (1[DeltaT = 0 and h* = h*']
   + 1[DeltaT = H and h* != h*']).
```

Equivalently, after the DSP secret phase and the target Hadamard outcome have
been combined in this two-copy coefficient,

```text
K_correct = (1/(2*N)) * sum_xi chi_xi(DeltaT) *
  (1[h* = h*'] + (-1)^xi * 1[h* != h*']),

K_wrong = (1/(2*N)) * sum_xi chi_xi(DeltaT) *
  (1[h* = h*'] - (-1)^xi * 1[h* != h*']).
```

It is tempting to call the two outcomes simply the even and odd Fourier
sectors.  That shorthand drops the `h*` equality indicators and is not an
exact identity unless a separate vanishing or reindexing theorem is supplied.
All conclusions below use the all-frequency formula above.

### Retaining the low summary

Consider the proposed repair that keeps the computational low summary `u`
instead of postselecting its all-zero Hadamard outcome.  Before the safe-residue
guard, the exact terminal eigenvalues are

```text
w_wrong(xi)   = 1 / (2*q),
w_correct(xi) = p_xi - 1 / (2*q),
w_wrong(xi) + w_correct(xi) = p_xi.
```

Distinct-mask and zero/nonzero-mask terms cancel between the two half-turn
sectors in the wrong kernel; the equal-mask diagonal remains.  Replacing the
terminal ordinary success by this kernel gives

```text
P_wrong   = (1/N) * sum_xi (w_wrong(xi) / p_xi) * A_xi,
P_correct = (1/N) * sum_xi (w_correct(xi) / p_xi) * A_xi.
```

At a mode where `p_xi=0`, this notation means the original terminal-position
sum, equivalently its continuous zero extension; the ratio is only used
literally on the typical modes where `p_xi` is positive.

On all but polynomially many frequencies, `p_xi = (1+o(1))/q` and
`A_xi = 1-o(1)`.  Hence

```text
P_wrong   = 1/2 + o(1),
P_correct = 1/2 + o(1),
P_accept  = 1 - o(1).
```

The retained-`u` decoder therefore has conditional error `1/2+o(1)`.  It
removes the Step-6 acceptance problem, but it also preserves the diagonal
modes that carry no information about the secret bit.

### Zero-low-Hadamard postselection before the guard

Let `L = n/2` be the number of low-summary values.  Postselecting the zero
Walsh outcome multiplies the terminal diagonal wrong kernel by `1/L`:

```text
w_wrong,0(xi) = 1 / (2*q*L).
```

The correct kernel has the same typical diagonal baseline plus coherent terms
supported by the Fourier transform of the safe-summary indicator.  Parseval
shows that the total additional Fourier energy is bounded, while the set on
which `p_xi` is not approximately `1/q` is only polynomially large.  This gives
the working asymptotics

```text
P_wrong   = 1/(2*L) + o(1/n),
P_correct = 1/(2*L) + o(1/n),
P_accept  = 1/L + o(1/n),
Pr[wrong | accept] = 1/2 + o(1).
```

Thus the zero postselection supplies the expected acceptance scale `2/n`, but
not a useful output bias.

## Effect of the safe-residue guard

In the diagonal two-copy contribution averaged over `Y`, the selected
high-summary sum is uniform on `ZMod n` whenever at least one selected local
mask is nonzero.  The all-zero exception has relative weight `q^(-a)`.  This is
an averaged kernel statement, not pointwise uniformity after fixing a
transcript.  The paper's safe set has density

```text
g = 1 - O(1/log n).
```

The guard therefore multiplies the correct and wrong diagonal baselines by the
same factor `g`.  A two-shift version only translates the safe set and leaves
its Fourier magnitudes unchanged.

For off-diagonal terms, choose the typical threshold
`a_xi <= 1/(P*a*q)`.  Parseval bounds the exceptional set by `O(P*a*q)`.
Completing the estimate must simultaneously control all
`G=Theta(a*q)` preterminal failure factors, the sensitivity of the binomial
tail to `p_xi`, the `L`-dimensional terminal coarsening, a uniform polynomial
bound on exceptional-mode transfer, and the zero/nonzero-mask cross terms.
The intended bound outside the exceptional set is `O(1/P)`.  Once all these
pieces are supplied, the calculation should give

```text
keep-u:
  P_wrong = g/2 + o(1),
  P_accept = g + o(1),

zero-low-Hadamard:
  P_wrong = g/(2*L) + o(1/n),
  P_accept = g/L + o(1/n).
```

This final guard estimate is the one part of the present counteranalysis that
still needs a complete written proof and Lean formalization.  It is an
explicit Fourier-error estimate, not a missing probabilistic independence
principle.

## What the calculation does and does not refute

The calculation does not directly refute the weak first clause of Lemma 3,
which only says that at least one signed branch count exceeds a very small
threshold.  Nor does it by itself disprove the isolated pointwise upper bound
on every normalized `alpha_z` component.  The repository's sound finite-energy
replacements for those statements remain useful as abstract results.

It does refute the unguarded retained-`u` repair and, once the stated guard
estimate is completed, the decoder-level conclusion needed downstream:

- the hoped-for small global `L2` decoding error;
- the branch-amplitude closeness used by Lemma 4; and
- the claim that Steps 2--7 recover `d_n` with inverse-polynomial bias.

This is already a fault-free obstruction.  Fault bookkeeping cannot restore a
guarantee that fails on an oracle returning only correct samples.

The proper repository status is therefore not “Lemma 3 only lacks another
conditional collision estimate.”  Its first finite analytic inequality may
still be repaired, and its second has a correct energy-budgeted form, but the
present decoder architecture has a separate spectral obstruction to the core
algorithmic conclusion.

## Why local repairs do not remove the obstruction

For any polynomial-range group summary `f`, define its collision spectrum by

```text
A_f(xi) = N^(-2) * sum_s
  |sum_(t : f(t)=s) omega^(xi*t)|^2.
```

Parseval gives

```text
A_f(xi) >= 0,
sum_xi A_f(xi) = 1.
```

Consequently only polynomially many modes can receive an inverse-polynomial
coherent enhancement over the diagonal baseline.  Exact Step 2 spreads its
outer Fourier weight over all `N=2^n` modes.  This produces a basic tradeoff:

- a fixed or tightly capped selection rule can filter the typical modes, but
  then its total acceptance is at most `poly(n)/N + q^(-a)`, which is
  exponentially small;
- a candidate pool of size `Theta(a*q)` gives inverse-polynomial or constant
  acceptance, but it also accepts almost every diagonal mode, making the final
  bit asymptotically unbiased.

Random shifts and twirls only permute the polynomial exceptional set.  A
coarse Step-2 window can concentrate Fourier mass, but the unmeasured low
residue contributes an unknown secret-dependent modulation that shifts the
spectral peak.  Measuring that residue removes the unknown phase precisely by
flattening the spectrum again.  Accepting more Walsh outcomes requires keeping
enough which-path information to correct their phases, trading acceptance rank
for coherent-fibre size without a net gain.

These are heuristic structural consequences for the polynomial-range local
summary plus first-`a`-zero architecture analyzed here.  Turning them into a
general no-go theorem would require an explicit definition of the permitted
filters and a uniform hybrid bound.  They are not a no-go statement for all
possible quantum algorithms for DCP.

## Structural repair that would suffice

A genuinely different decoder could be based on a global `HalfTurnEraser`
primitive.  Such a primitive would have to

1. operate on the full selected-mask superposition rather than independent
   polynomial-size groups;
2. succeed with inverse-polynomial probability;
3. pair total sums `z` and `z+N/2` into the same residual garbage label;
4. preserve the faulty-sample and `B`-side phases; and
5. produce residual states `R_0,R_1` satisfying

```text
||R_0 - R_1|| <= epsilon * sqrt(||R_0||^2 + ||R_1||^2).
```

Then a final Hadamard would have error at most

```text
epsilon^2 / 2.
```

Constructing this primitive amounts to coherent balanced matching or index
erasure on exponentially large subset-sum fibres.  The paper's independent
groups and first-zero schedule do not implement it, and no polynomial-time
construction is identified or supplied in this project.  It is therefore a
possible new algorithmic research direction, not a completed repair of the
proof.

## Next formalization target

Before adding more positive Lemma 3 repair lemmas, the next useful formal task
is to encode the clean one-group two-copy kernel and prove:

1. the exact formula for `p_xi` and `sum_xi a_xi = 1`;
2. the first-`a`-zero binomial transfer identity;
3. the exact all-frequency terminal identities
   `w_wrong = 1/(2*q)` and `w_correct = p_xi-w_wrong`;
4. the typical-mode asymptotics; and
5. the safe-guard Parseval perturbation estimate.

Only after those checks should the repository promote the guarded conclusion
from a natural-language spectral obstruction to a machine-checked
countertheorem.
