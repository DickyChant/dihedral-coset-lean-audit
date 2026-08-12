import Mathlib

/-!
# First-zero refinement count for Lemma 3

This module isolates the finite combinatorial core of the adaptive
"first `a` zero blocks" rule used in the energy-budget audit for Lemma 3.
Blocks are ordered by `Fin G`.  An accepted outcome has at least `a` zero
blocks, and its selected set consists of the first `a` such blocks.

For a fixed complete string `x`, refining by both the selected block set `A`
and the complete restricted string `x |_ A` creates exactly one label for
each `a`-element subset of the `G` blocks.  Consequently, the labels reachable
through the adaptive first-zero rule have incidence at most `Nat.choose G a`.
If every such restriction carries diagonal weight `q ^ (-a)`, the resulting
diagonal frame weight is at most

```text
Nat.choose G a / q ^ a.
```

The final theorem is stated with the denominator cleared.  It can therefore
be used without importing an operator library: a circuit-level bridge only
has to identify its diagonal frame eigenvalue with (or bound it by) the
finite incidence sum defined here.
-/

namespace SimonDCP.Probability.LemmaThreeFirstZeroFrame

open scoped BigOperators

/-- A `G`-block string over an arbitrary finite alphabet. -/
abbrev BlockString (G : Nat) (Alphabet : Type*) := Fin G -> Alphabet

/-- Zero blocks, listed in the natural order on `Fin G`. -/
noncomputable def zeroBlocksList {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (d : BlockString G Alphabet) : List (Fin G) := by
  classical
  exact (List.finRange G).filter fun i => d i = zero

/-- Number of zero blocks in an outcome. -/
noncomputable def zeroBlockCount {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (d : BlockString G Alphabet) : Nat :=
  (zeroBlocksList zero d).length

/-- The first `a` zero blocks of an outcome, in the order inherited from `Fin G`. -/
noncomputable def firstZeroBlocks {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (a : Nat) (d : BlockString G Alphabet) : Finset (Fin G) :=
  ((zeroBlocksList zero d).take a).toFinset

/-- The ordered list of zero blocks has no repetitions. -/
theorem zeroBlocksList_nodup {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (d : BlockString G Alphabet) :
    (zeroBlocksList zero d).Nodup := by
  classical
  unfold zeroBlocksList
  exact (List.nodup_finRange G).filter _

/-- Exact size of the first-zero selection, including nonaccepted outcomes. -/
theorem card_firstZeroBlocks {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (a : Nat) (d : BlockString G Alphabet) :
    (firstZeroBlocks zero a d).card = min a (zeroBlockCount zero d) := by
  classical
  unfold firstZeroBlocks zeroBlockCount
  rw [List.toFinset_card_of_nodup]
  · exact List.length_take
  · exact (zeroBlocksList_nodup zero d).take

/-- On an accepted outcome, exactly `a` zero blocks are selected. -/
theorem card_firstZeroBlocks_of_accepted
    {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (a : Nat) (d : BlockString G Alphabet)
    (hAccepted : a <= zeroBlockCount zero d) :
    (firstZeroBlocks zero a d).card = a := by
  classical
  rw [card_firstZeroBlocks, min_eq_left hAccepted]

/-- Every selected block is a zero block. -/
theorem value_eq_zero_of_mem_firstZeroBlocks
    {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (a : Nat) (d : BlockString G Alphabet) {i : Fin G}
    (hi : i ∈ firstZeroBlocks zero a d) :
    d i = zero := by
  classical
  have hiTake : i ∈ (zeroBlocksList zero d).take a := by
    simpa [firstZeroBlocks] using hi
  have hiZeroList : i ∈ zeroBlocksList zero d :=
    (List.take_sublist a (zeroBlocksList zero d)).subset hiTake
  simpa [zeroBlocksList] using hiZeroList

/-- Outcomes on which the first-zero rule can select `a` blocks. -/
abbrev AcceptedOutcome (G : Nat) (Alphabet : Type*)
    (zero : Alphabet) (a : Nat) :=
  {d : BlockString G Alphabet // a <= zeroBlockCount zero d}

/-- The type of `a`-element block sets. -/
abbrev SizedBlockSet (G a : Nat) :=
  {blocks : Finset (Fin G) // blocks.card = a}

/-- The first-zero block set of an accepted outcome. -/
noncomputable def firstZeroSelection {G : Nat} {Alphabet : Type*}
    (zero : Alphabet) (a : Nat) (d : AcceptedOutcome G Alphabet zero a) :
    SizedBlockSet G a :=
  ⟨firstZeroBlocks zero a d.1,
    card_firstZeroBlocks_of_accepted zero a d.1 d.2⟩

/-- There are exactly `G choose a` possible selected block sets. -/
theorem card_sizedBlockSet (G a : Nat) :
    Fintype.card (SizedBlockSet G a) = Nat.choose G a := by
  simp

/-- A complete selected-string label records both `A` and every value on `A`. -/
abbrev SelectedString (G a : Nat) (Alphabet : Type*) :=
  Sigma fun blocks : SizedBlockSet G a => (i : blocks.1) -> Alphabet

/-- Restrict a complete string to a selected block set. -/
def restrictString {G a : Nat} {Alphabet : Type*}
    (x : BlockString G Alphabet) (blocks : SizedBlockSet G a) :
    SelectedString G a Alphabet :=
  ⟨blocks, fun i => x i.1⟩

/-- For fixed `x`, the complete restricted label remembers its block set. -/
theorem restrictString_injective {G a : Nat} {Alphabet : Type*}
    (x : BlockString G Alphabet) :
    Function.Injective (restrictString (a := a) x) := by
  intro blocks blocks' h
  simpa [restrictString] using congrArg Sigma.fst h

/-- All complete selected-string labels compatible with a fixed full string. -/
noncomputable def fullStringRefinements
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (x : BlockString G Alphabet) : Finset (SelectedString G a Alphabet) := by
  classical
  exact Finset.univ.image (restrictString (a := a) x)

/-- The full selected-string refinement has exactly `G choose a` labels. -/
theorem card_fullStringRefinements
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (x : BlockString G Alphabet) :
    (fullStringRefinements (a := a) x).card = Nat.choose G a := by
  classical
  rw [fullStringRefinements, Finset.card_image_of_injective _
    (restrictString_injective (a := a) x)]
  exact card_sizedBlockSet G a

/--
Complete selected-string labels reachable by varying the accepted outcome
`d`, while keeping the underlying full string `x` fixed.
-/
noncomputable def adaptiveFirstZeroRefinements
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) :
    Finset (SelectedString G a Alphabet) := by
  classical
  exact Finset.univ.image fun d : AcceptedOutcome G Alphabet zero a =>
    restrictString x (firstZeroSelection zero a d)

/-- Adaptive first-zero labels are a subset of the complete refinement. -/
theorem adaptiveFirstZeroRefinements_subset
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) :
    adaptiveFirstZeroRefinements zero (a := a) x ⊆
      fullStringRefinements (a := a) x := by
  classical
  intro label hLabel
  rw [adaptiveFirstZeroRefinements] at hLabel
  rw [fullStringRefinements]
  rcases Finset.mem_image.mp hLabel with ⟨d, _hd, rfl⟩
  exact Finset.mem_image.mpr
    ⟨firstZeroSelection zero a d, Finset.mem_univ _, rfl⟩

/-- The adaptive incidence count is at most `G choose a`. -/
theorem card_adaptiveFirstZeroRefinements_le_choose
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) :
    (adaptiveFirstZeroRefinements zero (a := a) x).card <= Nat.choose G a := by
  calc
    (adaptiveFirstZeroRefinements zero (a := a) x).card
        <= (fullStringRefinements (a := a) x).card :=
      Finset.card_le_card (adaptiveFirstZeroRefinements_subset zero x)
    _ = Nat.choose G a := card_fullStringRefinements x

/--
The diagonal frame weight when every reachable complete restriction has
weight `1 / q^a`.
-/
noncomputable def adaptiveFirstZeroFrameWeight
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) (q : Nat) : Real :=
  ∑ _label ∈ adaptiveFirstZeroRefinements zero (a := a) x,
    1 / (q : Real) ^ a

/-- Division-form frame bound. -/
theorem adaptiveFirstZeroFrameWeight_le_choose_div
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) (q : Nat) :
    adaptiveFirstZeroFrameWeight zero (a := a) x q <=
      (Nat.choose G a : Real) / (q : Real) ^ a := by
  classical
  simp only [adaptiveFirstZeroFrameWeight, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast card_adaptiveFirstZeroRefinements_le_choose zero x
  · positivity

/--
Cleared-denominator frame/eigenvalue interface.  This is the form convenient
for a later circuit-level proof that identifies its diagonal frame weight
with `adaptiveFirstZeroFrameWeight`.
-/
theorem qPow_mul_adaptiveFirstZeroFrameWeight_le_choose
    {G a : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) (q : Nat) (hq : 0 < q) :
    (q : Real) ^ a * adaptiveFirstZeroFrameWeight zero (a := a) x q <=
      Nat.choose G a := by
  have hqPow : (q : Real) ^ a ≠ 0 := by
    positivity
  calc
    (q : Real) ^ a * adaptiveFirstZeroFrameWeight zero (a := a) x q
        <= (q : Real) ^ a * ((Nat.choose G a : Real) / (q : Real) ^ a) := by
      exact mul_le_mul_of_nonneg_left
        (adaptiveFirstZeroFrameWeight_le_choose_div zero x q) (by positivity)
    _ = Nat.choose G a := by field_simp

/-- Power-of-two block specialization (`q = 2^m`) in cleared form. -/
theorem twoPowBlock_mul_adaptiveFirstZeroFrameWeight_le_choose
    {G a m : Nat} {Alphabet : Type*} [Fintype Alphabet]
    (zero : Alphabet) (x : BlockString G Alphabet) :
    (2 : Real) ^ (m * a) *
        adaptiveFirstZeroFrameWeight zero (a := a) x (2 ^ m) <=
      Nat.choose G a := by
  simpa [Nat.cast_pow, pow_mul] using
    qPow_mul_adaptiveFirstZeroFrameWeight_le_choose
      zero x (2 ^ m) (pow_pos (by decide) _)

end SimonDCP.Probability.LemmaThreeFirstZeroFrame
