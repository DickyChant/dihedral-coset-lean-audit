# Proof audit for IACR ePrint 2026/1591

Source reviewed: the 16-page preliminary draft dated July 31, 2026, received by
IACR on August 3 and approved on August 6, 2026.

## Result

The paper's polynomial-time DCP theorem is not established by the published
proof. Three central arguments fail before the claimed lattice and LWE
corollaries can be reached.

## Lean formalization targets

The source contains no `sorry`, `admit`, or project-local axioms.  A clean Arch
WSL build completed all 3278 jobs successfully on August 7, 2026.
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

## Remaining invalid or missing obligations

- Lemma 1 also assumes an unproved sign symmetry and does not construct an
  injection preserving all measured registers.
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
- Substituting `c = 12` into the displayed page-14 exponent gives
  `-n/2 + 6n/(c' log n) + 6 log n`, not a value below `-n`; the asserted
  `delta < 2^(-n)` does not follow for the stated parameter range.
- The page-14 prose requires a multiplicative factor `mu`, while the displayed
  amplitude formula substitutes `|A_(g_a)|`; these differ by the number of
  bins.
- The corollary to Lemma 3 states an `n^(3/2)` amplitude bound, while the final
  derivation uses `n`.
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
