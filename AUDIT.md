# Proof audit for IACR ePrint 2026/1591

Source reviewed: the 16-page preliminary draft dated July 31, 2026, received by
IACR on August 3 and approved on August 6, 2026.

## Result

The paper's polynomial-time DCP theorem is not established by the published
proof. Three central arguments fail before the claimed lattice and LWE
corollaries can be reached.

## Lean formalization targets

The source contains no `sorry`, `admit`, or project-local axioms.  A clean Arch
WSL build, including both repair modules, completed all 3280 jobs successfully
on August 7, 2026.
`SimonDCP/AxiomAudit.lean` prints the axiom dependencies of the principal
results; the output contains only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or project-local axiom.

### Ideal sample and Step 2 phase extraction

The ideal input is represented as the normalized QuantumAlg pure state

```text
(|false, x> + |true, x + d>) / sqrt(2).
```

Its only nonzero Born probabilities are the two displayed labels, each with
probability `1/2`. The phase factorization in Step 2 is proved from the explicit
root condition `omega^(2^(n-1)) = -1`; the relative high-bit phase is
`(-1)^(d mod 2)`.

At the classical Fourier layer, Mathlib's unnormalized `ZMod.dft` is used with
its negative-kernel convention to prove the exact point-mass translation law
and the two-label factorization into a global phase and the relative DCP phase.

### Lemma 1 swap obstruction

The proof swaps two subset-selection bits and the low parts of the corresponding
sample values. Write

```text
y_i = B * H_i + L_i
y_j = B * H_j + L_j.
```

The new pair contribution minus the old contribution is

```text
B * (phi_j - phi_i) * (H_i - H_j),
```

which need not vanish modulo the measured modulus. For locally valid values
using the paper's `n = 8` bit split,

```text
n = 8, B = 4, H_i = 1, H_j = 0,
L_i = 0, L_j = 1, phi_i = 0, phi_j = 1,
```

the contribution changes from `1` to `5` modulo `128`. Thus the proposed local
swap does not preserve a measured subset-sum fibre.

This concrete `n = 8` witness checks the two-coordinate bit and range
constraints, but it is not itself a member of the paper's full event `D_Y`:
at `n = 8` there are only four possible low parts, while `D_Y` demands that
all `Q` low parts be distinct. The parameterized Lean identity for the error
term is the reusable obstruction. Embedding it into a complete `D_Y` instance
requires a separate sufficiently-large-`n` construction and is not claimed as
machine-checked here.

Accordingly, the current result invalidates the proposed injection argument;
it does not by itself prove that Lemma 1's probability conclusion is false.

The repair module proves two valid algebraic alternatives.  First, the low-part-only
swap is fibre-preserving exactly when the measured modulus divides
`B * (phi_j - phi_i) * (H_i - H_j)`; for a zero/one swap with modulus
`B * stride`, this reduces to `stride | (H_i - H_j)`.  Second, permuting the
complete samples together with the selection and Hadamard-output coordinates
preserves the subset sum and phase exactly and is bijective.

This is not yet a complete Lemma 1 proof.  Since `phi` is summed out after the
Hadamard transform, a state-dependent permutation must be chosen only from the
measured outcome and must map the `(h, s_1, ..., s_g)` interference classes by
one fixed label equivalence.  `SwapFiberRepair.lean` exposes these requirements
as a `LemmaOneRepairCertificate`; no such certificate is currently constructed.
This is only a structural interface on complete states containing the hidden
selection string.  Even constructing an instance would not by itself prove a
weighted injection on projected `(Y, D)` outcomes.  A full repair must also
preserve term amplitudes up to an outcome-global unit scalar, cover the faulty
sample support, and prove that the target outcome's probability weight is at
least the source weight.  The separate
`MeasuredOutcomeWeightInjectionCertificate` formalizes the last step and proves
that an injective, pointwise weight-nondecreasing outcome map bounds total bad
weight by total good weight.  No instance is currently constructed.

### Lemma 3 phase-correlation obstruction

Step 4 chooses the set `A` only from groups whose measured Hadamard string is
zero. Consequently `D_A = 0`, and the phase

```text
(-1)^(phi dot D)
```

depends only on `phi_B`. States with the same `B` part and different `A` parts
therefore have identical phases. They are perfectly correlated, not pairwise
independent as required by the variance argument in Lemma 3.

### Lemma 2 algebraic kernel

Translation by `2^(n-1)` modulo `2^n` is an involution. This is the sound
order-two translation underlying the paper's Lemma 2 and is formalized
separately from the invalid probabilistic arguments.

### Measured-XOR transfer and recursion

For fixed `h' = h XOR hStar`, the compatible value of `h` is unique and

```text
(-1)^(h * dBit) = (-1)^(h' * dBit) * (-1)^(hStar * dBit).
```

The first factor is a global phase. Separately, subtracting a known low bit
from the branch-one position and removing the common base parity makes both
branches exactly divisible by two, with reduced hidden shift `(d - dBit) / 2`.
Neither result supplies the missing reversible implementation or distribution-
preservation proof.

If the remaining qubit really is the exact normalized state
`(|0> + (-1)^dBit |1>) / sqrt(2)`, the QuantumAlg model proves that a Hadamard
gate followed by a computational-basis measurement returns `dBit` with
probability one. The disputed lemmas are precisely what fail to establish that
premise for the paper's conditioned state.

### Conditioning, overflow, and cancellation obstructions

Finite-count examples prove all three of the following:

- independent Boolean coordinates can become perfectly correlated after
  conditioning;
- adding a correlated overflow bit can collapse a balanced bit to a constant;
- equal numbers of signed contributions do not control amplitudes when terms
  cancel.

These are direct obstructions to the inference pattern used in Lemmas 3 and 4,
unless the paper supplies stronger conditional-independence and anti-
cancellation hypotheses.

For comparison, the development also proves the valid unconditioned theorem:
under a uniform mask in the full space `F_2^n`, a nonzero linear form is
balanced, and two distinct nonzero forms have four equal-cardinality joint
fibres. The proof constructs dual masks explicitly. Its hypotheses fail after
the paper selects `A` from the zero coordinates of that same mask and
conditions on the resulting measurement record.

### Lemma 4 quantitative repairs

The page-14 calculation retains an extra `+n`.  Its standard-deviation exponent
already includes `-n`, which is cancelled when multiplying by
`kappa' = 2^n`.  Removing the extra term changes the total exponent from

```text
E_print(c) = ((11 - c)/2) * n + faultLoss/2 + (c/2) * log n
```

to

```text
E_corrected(c) = ((9 - c)/2) * n + faultLoss/2 + (c/2) * log n.
```

At `c = 12`, the corrected exponent is at most `-n` whenever
`faultLoss + 12 * log n <= n`.  If the printed expression is retained instead,
the same type of bound is recovered at `c = 14` under
`faultLoss + 14 * log n <= n`.  `Lemma4Parameters.lean` proves both statements
and the corresponding base-two real-power inequality.

If the extra `+n` is left in place, the `c = 12` expression is still
`-n/2 + o(n)`.  Conditional on it being a simultaneous absolute error bound for
normalized amplitudes, it is exponentially smaller than every downstream
polynomial loss and would suffice for the final inverse-polynomial error goal.
It does not prove the literal `< 2^(-n)` line or any multiplicative ratio near a
zero amplitude.

The same module proves that uniform bin multiplicity factors out as `mu`, while
the total cardinality is the number of bins times `mu`; substituting
`|A_(g_a)|` therefore inserts an extra bin-count factor.  It also propagates the
corollary's stated `n^(3/2)` amplitude bound: at `c = 12` the resulting aggregate
polynomial exponent is `-2`, so replacing it by the unsupported bound `n` is
unnecessary.  Only additive signed-sum error control follows without a
non-cancellation hypothesis.

## Remaining invalid or missing obligations

- Lemma 1 still assumes an unproved sign symmetry and lacks a concrete
  reversible bad-to-good plan preserving all Step-4 interference classes.
- Lemma 3 varies `D` as if it changed only signs, although changing `D` can
  change the adaptive `A/B` partition and later measurement records.
- Lemma 4 reuses pairwise independence after conditioning on
  `z'`, `D`, `A`, `W'`, `S`, and `h'`; no preservation theorem is supplied.
- The claim that the sets indexed by `q_(g_a)` have equal size ignores that
  `W'`, including the postselected `l_(s*)`, depends on `s_a` and hence on
  `q_(g_a)`.
- Correlated overflow terms do not necessarily increase uniformity.
- The all-zero `q_(g_a)` makes `s_a = 0`, contradicting literal pairwise
  independence over all `q_(g_a)` values (although this isolated exception may
  be asymptotically removable).
- The repaired Lemma 4 parameter arithmetic still relies on unproved
  conditional balls-in-bins, variance, and union-bound premises, and additive
  count control still does not imply a multiplicative amplitude ratio under
  cancellation.
- Step 6 postselection probabilities, recursive recovery of all bits, fault-rate
  preservation, amplification, and uniform circuit cost are not proved.
- The lattice corollary relies on external Regev/BKSW reductions that are not
  formalized here. Its transitions among unique-SVP, approximate search-SVP,
  and LWE parameter conventions therefore remain source-qualified obligations;
  the exact conventions in the cited references have not yet been independently
  verified in this development.

## Formalization boundary

The current development proves algebraic identities and counterexamples that
can be checked by Lean's kernel. A future repaired main theorem would require
new, explicit proofs of conditional phase balance, conditional fibre
uniformity, adaptive measurement semantics, error amplification, and the
external lattice reductions. Until those obligations exist, the headline
theorem and its SVP/LWE corollaries must remain unproved.
