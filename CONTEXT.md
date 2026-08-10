# Lemma 1 Repair Audit

This context distinguishes the physical records, hidden summation terms, and
coherent labels used when auditing or repairing Lemma 1 of IACR ePrint
2026/1591.

## Language

**Measured outcome**:
The complete classical record that fixes a probability outcome and determines
which hidden terms contribute to it.
_Avoid_: Using only the visible sample and Hadamard mask when other measured or
postselected records affect the support.

**Supported selection**:
A hidden selection string satisfying every fibre, range, and postselection
condition imposed by one measured outcome.
_Avoid_: Arbitrary selection, probe state.

**Full Step-4 label**:
The subset-sum high bit and all stored group summaries that jointly determine which
supported selections aggregate coherently after Step 4.
For Lemma 1 this is `(h, s_1, ..., s_G)`; the Hadamard exponent `phi dot D`
is a signed coefficient, not part of the orthogonal label.
_Avoid_: Group label, truncated label, Hadamard phase label.

**Support-compatible repair**:
A bad-to-good outcome map whose induced map on supported selections respects
the occupied fibres of the full Step-4 label.
_Avoid_: Global repair, label-preserving permutation.

**Local witness**:
A finite configuration satisfying an explicitly listed subset of the paper's
conditions and used to test one proposed proof mechanism.
_Avoid_: Counterexample, unless every hypothesis of the target statement is met.

**Coherent weight**:
The sum, over occupied full Step-4 labels, of the squared magnitude of the
signed sum of supported hidden terms in that label.
_Avoid_: Number of hidden terms, termwise weight.

**Projected collision ratio**:
The normalized number of same-label pairs of supported selections that agree
outside a chosen coordinate set.  Restricted Parseval identifies it as the
multiplicative correction to the uniform probability that the chosen output
coordinates are all zero.
_Avoid_: Collision probability, unless a probability distribution has been specified.

**Two-group subset-sum injectivity**:
Injectivity modulo the measured Step-2 modulus of the Boolean subset-sum map on
the union of any two Step-3 groups.  It eliminates every off-diagonal pair in
the one- and two-group restricted Parseval identities.
_Avoid_: Pairwise-distinct samples, which is strictly weaker.

**Free selection dimension**:
The dimension `R` of the affine Boolean support remaining after faulty samples
fix some hidden selection coordinates.  Conditioning losses depend on `R` and
on the number of free coordinates outside a local event, not on the nominal
sample count `Q` alone.
_Avoid_: Number of nonfaulty measured values, unless its equality with `R` has
been proved for the fault model.

**Prior local-sample event**:
An event `Bad_A` determined by sample coordinates in `A` before conditioning on
the Step-2 residue.  Its prior mass `p_A` remains as a multiplicative factor on
the exceptional branch where no free outside coordinate one-time-pads the
residue.
_Avoid_: Treating `Y` as still uniform after measuring `z'`.
