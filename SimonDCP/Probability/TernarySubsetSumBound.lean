import Mathlib

/-!
# Ternary subset-sum union bounds

This file isolates the finite counting argument behind the usual estimate
that a random sample has a nontrivial ternary relation with probability at
most `(3 ^ a - 1) / M`.

There are three layers.

* `card_biUnion_le_card_mul` and `finiteMass_iUnion_le` are the elementary
  finite union bounds.
* `card_nonzeroTernaryVectors` proves that there are exactly `3 ^ a - 1`
  nonzero coefficient vectors in `{-1, 0, 1}^a`.
* The final theorems apply those facts to the concrete relation
  `sum_i coefficient_i * sample_i = 0` in a finite additive commutative
  group.  The per-relation estimate is kept as an explicit hypothesis in the
  generic API and is also proved below by deleting one nonzero pivot.

No independence beyond uniform sampling of the whole sample vector is used.
-/

namespace SimonDCP.Probability.TernarySubsetSumBound

open scoped BigOperators

section FiniteUnion

variable {Index Omega : Type*}

/-- The mass of an event in a finite rationally weighted space. -/
noncomputable def finiteMass [Fintype Omega]
    (weight : Omega -> Rat) (event : Omega -> Prop) : Rat :=
  by
    classical
    exact ∑ omega, if event omega then weight omega else 0

/-- A finite union bound for arbitrary nonnegative rational weights. -/
theorem finiteMass_iUnion_le
    [Fintype Omega]
    (indices : Finset Index) (weight : Omega -> Rat)
    (event : Index -> Omega -> Prop)
    (hWeight : forall omega, 0 <= weight omega) :
    finiteMass weight (fun omega => exists i, i ∈ indices ∧ event i omega) <=
      ∑ i ∈ indices, finiteMass weight (event i) := by
  classical
  unfold finiteMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro omega _
  by_cases hUnion : exists i, i ∈ indices ∧ event i omega
  · simp only [hUnion, if_true]
    obtain ⟨i, hi, hEvent⟩ := hUnion
    calc
      weight omega = if event i omega then weight omega else 0 := by simp [hEvent]
      _ <= ∑ j ∈ indices, if event j omega then weight omega else 0 := by
        exact Finset.single_le_sum (s := indices)
          (f := fun j => if event j omega then weight omega else 0)
          (by
            intro j hj
            split_ifs
            · exact hWeight omega
            · exact le_rfl)
          hi
  · simp only [hUnion, if_false]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hWeight omega
    · exact le_rfl

/-- Cardinal form of the finite union bound with a uniform bound on every
member of the family. -/
theorem card_biUnion_le_uniform
    [DecidableEq Omega] (indices : Finset Index) (event : Index -> Finset Omega)
    (bound : Nat) (hEvent : ∀ i ∈ indices, (event i).card <= bound) :
    (indices.biUnion event).card <= indices.card * bound :=
  Finset.card_biUnion_le_card_mul indices event bound hEvent

end FiniteUnion

section Coefficients

variable {I : Type*} [Fintype I]

/-- `none`, `some false`, and `some true` represent `0`, `+1`, and `-1`. -/
abbrev TernaryCoefficient := Option Bool

/-- A ternary coefficient vector. -/
abbrev TernaryVector (I : Type*) := I -> TernaryCoefficient

/-- The all-zero ternary vector. -/
def zeroTernaryVector : TernaryVector I := fun _ => none

/-- All nonzero ternary coefficient vectors. -/
noncomputable def nonzeroTernaryVectors : Finset (TernaryVector I) := by
  classical
  exact Finset.univ.erase zeroTernaryVector

@[simp]
theorem mem_nonzeroTernaryVectors (coefficient : TernaryVector I) :
    coefficient ∈ nonzeroTernaryVectors ↔ coefficient ≠ zeroTernaryVector := by
  classical
  simp [nonzeroTernaryVectors]

/-- There are exactly `3^a - 1` nonzero vectors in `{-1,0,1}^a`. -/
theorem card_nonzeroTernaryVectors :
    (nonzeroTernaryVectors (I := I)).card = 3 ^ Fintype.card I - 1 := by
  classical
  rw [nonzeroTernaryVectors, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- The generic counting core: if each nonzero ternary relation holds on at
most `bound` samples, their union holds on at most
`(3^a - 1) * bound` samples. -/
theorem card_ternaryUnion_le
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (event : TernaryVector I -> Finset Omega) (bound : Nat)
    (hEvent : ∀ coefficient ∈ nonzeroTernaryVectors (I := I),
      (event coefficient).card <= bound) :
    ((nonzeroTernaryVectors (I := I)).biUnion event).card <=
      (3 ^ Fintype.card I - 1) * bound := by
  rw [← card_nonzeroTernaryVectors (I := I)]
  exact card_biUnion_le_uniform (nonzeroTernaryVectors (I := I)) event bound hEvent

/-- Weighted form of the same union bound.  This is the exact interface
needed when each nonzero relation has mass at most `singleMass`. -/
theorem mass_ternaryUnion_le
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Rat) (event : TernaryVector I -> Omega -> Prop)
    (singleMass : Rat) (hWeight : forall omega, 0 <= weight omega)
    (hEvent : ∀ coefficient ∈ nonzeroTernaryVectors (I := I),
      finiteMass weight (event coefficient) <= singleMass) :
    finiteMass weight (fun omega => exists coefficient,
        coefficient ∈ nonzeroTernaryVectors (I := I) ∧ event coefficient omega) <=
      (3 ^ Fintype.card I - 1 : Nat) * singleMass := by
  calc
    finiteMass weight (fun omega => exists coefficient,
        coefficient ∈ nonzeroTernaryVectors (I := I) ∧ event coefficient omega) <=
        ∑ coefficient ∈ nonzeroTernaryVectors (I := I),
          finiteMass weight (event coefficient) :=
      finiteMass_iUnion_le (nonzeroTernaryVectors (I := I)) weight event hWeight
    _ <= ∑ _coefficient ∈ nonzeroTernaryVectors (I := I), singleMass :=
      Finset.sum_le_sum hEvent
    _ = (3 ^ Fintype.card I - 1 : Nat) * singleMass := by
      rw [Finset.sum_const, nsmul_eq_mul, card_nonzeroTernaryVectors]

/-- In particular, per-relation mass at most `1/M` gives the advertised
`(3^a - 1)/M` union bound. -/
theorem mass_ternaryUnion_le_div
    {Omega : Type*} [Fintype Omega]
    (weight : Omega -> Rat) (event : TernaryVector I -> Omega -> Prop)
    (M : Nat) (hWeight : forall omega, 0 <= weight omega)
    (hEvent : ∀ coefficient ∈ nonzeroTernaryVectors (I := I),
      finiteMass weight (event coefficient) <= 1 / (M : Rat)) :
    finiteMass weight (fun omega => exists coefficient,
        coefficient ∈ nonzeroTernaryVectors (I := I) ∧ event coefficient omega) <=
      (3 ^ Fintype.card I - 1 : Nat) / (M : Rat) := by
  calc
    finiteMass weight (fun omega => exists coefficient,
        coefficient ∈ nonzeroTernaryVectors (I := I) ∧ event coefficient omega) <=
        (3 ^ Fintype.card I - 1 : Nat) * (1 / (M : Rat)) :=
      mass_ternaryUnion_le weight event (1 / (M : Rat)) hWeight hEvent
    _ = (3 ^ Fintype.card I - 1 : Nat) / (M : Rat) := by ring

end Coefficients

section GroupRelation

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Interpret a ternary coefficient as multiplication by `0`, `+1`, or
`-1` in an additive group. -/
def ternaryTerm : TernaryCoefficient -> G -> G
  | none, _ => 0
  | some false, value => value
  | some true, value => -value

omit [Fintype G] [DecidableEq G] in
/-- A nonzero ternary coefficient acts injectively on an additive group. -/
theorem ternaryTerm_injective
    {coefficient : TernaryCoefficient} (hCoefficient : coefficient ≠ none) :
    Function.Injective (ternaryTerm coefficient : G -> G) := by
  cases coefficient with
  | none => exact (hCoefficient rfl).elim
  | some sign =>
      cases sign <;> simp [ternaryTerm, Function.Injective]

/-- The ternary linear combination of a finite sample. -/
def ternarySum (coefficient : TernaryVector I) (sample : I -> G) : G :=
  ∑ i, ternaryTerm (coefficient i) (sample i)

omit [DecidableEq I] in
/-- Every nonzero ternary vector has a nonzero coordinate. -/
theorem exists_nonzero_ternary_coordinate
    {coefficient : TernaryVector I}
    (hCoefficient : coefficient ≠ zeroTernaryVector) :
    exists pivot, coefficient pivot ≠ none := by
  by_contra hPivot
  push Not at hPivot
  apply hCoefficient
  funext i
  exact hPivot i

/-- Delete one coordinate from a sample. -/
def sampleWithout (pivot : I) (sample : I -> G) : {i : I // i ≠ pivot} -> G :=
  fun i => sample i.1

/-- Samples satisfying one prescribed ternary relation. -/
noncomputable def ternaryRelationSamples
    (coefficient : TernaryVector I) : Finset (I -> G) := by
  classical
  exact Finset.univ.filter fun sample => ternarySum coefficient sample = 0

/-- Samples satisfying at least one nonzero ternary relation. -/
noncomputable def ternaryCollisionSamples : Finset (I -> G) := by
  classical
  exact (nonzeroTernaryVectors (I := I)).biUnion ternaryRelationSamples

@[simp]
theorem mem_ternaryRelationSamples
    (coefficient : TernaryVector I) (sample : I -> G) :
    sample ∈ ternaryRelationSamples coefficient ↔ ternarySum coefficient sample = 0 := by
  classical
  simp [ternaryRelationSamples]

/-- On the solutions of a relation with a nonzero pivot coefficient,
deleting that pivot is injective: the relation uniquely reconstructs it. -/
theorem sampleWithout_injOn_ternaryRelationSamples
    (coefficient : TernaryVector I) (pivot : I)
    (hPivot : coefficient pivot ≠ none) :
    Set.InjOn (sampleWithout (G := G) pivot)
      (ternaryRelationSamples (G := G) coefficient : Set (I -> G)) := by
  classical
  intro left hLeft right hRight hWithout
  have hLeftRelation : ternarySum coefficient left = 0 :=
    mem_ternaryRelationSamples coefficient left |>.mp hLeft
  have hRightRelation : ternarySum coefficient right = 0 :=
    mem_ternaryRelationSamples coefficient right |>.mp hRight
  have hRestTerms :
      ∀ i ∈ (Finset.univ.erase pivot),
        ternaryTerm (coefficient i) (left i) =
          ternaryTerm (coefficient i) (right i) := by
    intro i hi
    have hne : i ≠ pivot := (Finset.mem_erase.mp hi).1
    have hValue := congrFun hWithout (⟨i, hne⟩ : {j : I // j ≠ pivot})
    rw [sampleWithout, sampleWithout] at hValue
    rw [hValue]
  have hRestSum :
      (∑ i ∈ (Finset.univ.erase pivot),
          ternaryTerm (coefficient i) (left i)) =
        ∑ i ∈ (Finset.univ.erase pivot),
          ternaryTerm (coefficient i) (right i) :=
    Finset.sum_congr rfl hRestTerms
  have hLeftSplit :
      ternaryTerm (coefficient pivot) (left pivot) +
          (∑ i ∈ (Finset.univ.erase pivot),
            ternaryTerm (coefficient i) (left i)) = 0 := by
    calc
      ternaryTerm (coefficient pivot) (left pivot) +
          (∑ i ∈ (Finset.univ.erase pivot),
            ternaryTerm (coefficient i) (left i)) =
          ternarySum coefficient left := by
        exact
          Finset.add_sum_erase Finset.univ
            (fun i => ternaryTerm (coefficient i) (left i))
            (Finset.mem_univ pivot)
      _ = 0 := hLeftRelation
  have hRightSplit :
      ternaryTerm (coefficient pivot) (right pivot) +
          (∑ i ∈ (Finset.univ.erase pivot),
            ternaryTerm (coefficient i) (right i)) = 0 := by
    calc
      ternaryTerm (coefficient pivot) (right pivot) +
          (∑ i ∈ (Finset.univ.erase pivot),
            ternaryTerm (coefficient i) (right i)) =
          ternarySum coefficient right := by
        exact
          Finset.add_sum_erase Finset.univ
            (fun i => ternaryTerm (coefficient i) (right i))
            (Finset.mem_univ pivot)
      _ = 0 := hRightRelation
  funext i
  by_cases hi : i = pivot
  · subst i
    apply ternaryTerm_injective hPivot
    rw [hRestSum] at hLeftSplit
    exact add_right_cancel (hLeftSplit.trans hRightSplit.symm)
  · exact congrFun hWithout (⟨i, hi⟩ : {j : I // j ≠ pivot})

/-- A single nonzero ternary relation holds on at most `|G|^(a-1)` samples.
The proof is a direct finite injection, with no probabilistic assumption. -/
theorem card_ternaryRelationSamples_le
    (coefficient : TernaryVector I)
    (hCoefficient : coefficient ≠ zeroTernaryVector) :
    (ternaryRelationSamples (G := G) coefficient).card <=
      Fintype.card G ^ (Fintype.card I - 1) := by
  classical
  obtain ⟨pivot, hPivot⟩ := exists_nonzero_ternary_coordinate hCoefficient
  calc
    (ternaryRelationSamples (G := G) coefficient).card <=
        (Finset.univ : Finset ({i : I // i ≠ pivot} -> G)).card := by
      apply Finset.card_le_card_of_injOn (sampleWithout (G := G) pivot)
      · intro sample hSample
        exact Finset.mem_univ _
      · exact sampleWithout_injOn_ternaryRelationSamples coefficient pivot hPivot
    _ = Fintype.card G ^ (Fintype.card I - 1) := by
      simp [Fintype.card_subtype_compl]

@[simp]
theorem mem_ternaryCollisionSamples (sample : I -> G) :
    sample ∈ ternaryCollisionSamples (I := I) (G := G) ↔
      exists coefficient, coefficient ≠ zeroTernaryVector ∧
        ternarySum coefficient sample = 0 := by
  classical
  simp [ternaryCollisionSamples]

/-- Concrete union bound for ternary subset-sum collisions.  The remaining
hypothesis is exactly the single-relation count, not an independence claim. -/
theorem card_ternaryCollisionSamples_le_of_single
    (bound : Nat)
    (hSingle : ∀ coefficient ∈ nonzeroTernaryVectors (I := I),
      (ternaryRelationSamples (G := G) coefficient).card <= bound) :
    (ternaryCollisionSamples (I := I) (G := G)).card <=
      (3 ^ Fintype.card I - 1) * bound := by
  exact card_ternaryUnion_le (I := I) ternaryRelationSamples bound hSingle

/-- The unconditional finite counting theorem: among all `G^a` samples, at
most `(3^a - 1) * |G|^(a-1)` have a nontrivial ternary relation. -/
theorem card_ternaryCollisionSamples_le :
    (ternaryCollisionSamples (I := I) (G := G)).card <=
      (3 ^ Fintype.card I - 1) *
        Fintype.card G ^ (Fintype.card I - 1) := by
  apply card_ternaryCollisionSamples_le_of_single
  intro coefficient hCoefficient
  exact card_ternaryRelationSamples_le coefficient
    (mem_nonzeroTernaryVectors coefficient |>.mp hCoefficient)

/-- Paper-facing uniform-probability form of the counting theorem.  The
sample index set is assumed nonempty only to rewrite
`|G|^(a-1) / |G|^a` as `1 / |G|`. -/
theorem uniform_ternaryCollisionSamples_le [Nonempty I] :
    ((ternaryCollisionSamples (I := I) (G := G)).card : Rat) /
        (Fintype.card (I -> G) : Rat) <=
      ((3 ^ Fintype.card I - 1 : Nat) : Rat) /
        (Fintype.card G : Rat) := by
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
  have hG : 0 < Fintype.card G := Fintype.card_pos_iff.mpr inferInstance
  have hGRat : 0 < (Fintype.card G : Rat) := by exact_mod_cast hG
  have hSampleRat :
      0 < (Fintype.card G ^ Fintype.card I : Nat) := pow_pos hG _
  have hSampleRat' :
      0 < ((Fintype.card G ^ Fintype.card I : Nat) : Rat) := by
    exact_mod_cast hSampleRat
  have hCount :
      ((ternaryCollisionSamples (I := I) (G := G)).card : Rat) <=
        (((3 ^ Fintype.card I - 1) *
          Fintype.card G ^ (Fintype.card I - 1) : Nat) : Rat) := by
    exact_mod_cast card_ternaryCollisionSamples_le (I := I) (G := G)
  have hExponent : Fintype.card I - 1 + 1 = Fintype.card I := by omega
  have hScale :
      ((3 ^ Fintype.card I - 1) *
          Fintype.card G ^ (Fintype.card I - 1)) * Fintype.card G =
        (3 ^ Fintype.card I - 1) * Fintype.card G ^ Fintype.card I := by
    rw [mul_assoc, ← pow_succ, hExponent]
  rw [Fintype.card_fun]
  apply (div_le_div_iff₀ hSampleRat' hGRat).2
  calc
    ((ternaryCollisionSamples (I := I) (G := G)).card : Rat) *
        (Fintype.card G : Rat) <=
        (((3 ^ Fintype.card I - 1) *
          Fintype.card G ^ (Fintype.card I - 1) : Nat) : Rat) *
            (Fintype.card G : Rat) :=
      mul_le_mul_of_nonneg_right hCount hGRat.le
    _ = ((3 ^ Fintype.card I - 1 : Nat) : Rat) *
          ((Fintype.card G ^ Fintype.card I : Nat) : Rat) := by
      exact_mod_cast hScale

end GroupRelation

end SimonDCP.Probability.TernarySubsetSumBound
