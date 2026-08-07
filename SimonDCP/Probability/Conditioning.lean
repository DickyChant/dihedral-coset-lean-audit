import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum

/-!
# Conditioning can destroy pairwise independence

Lemma 4 of the preprint reuses an unconditioned pairwise-independence claim
after conditioning on several measurement outcomes.  Such a step requires a
new proof: independence is not preserved by arbitrary conditioning.

This file records the smallest exact counterexample.  The two coordinates of
a uniform element of `Bool × Bool` are independent.  After conditioning on the
event that the coordinates are equal, they are perfectly correlated.

Everything is expressed by finite counts, so no measure-theoretic convention
is hidden in the statement.
-/

namespace SimonDCP.Probability.Conditioning

/-- Number of points in `space` on which two observations take prescribed values. -/
def jointCount {Ω α β : Type*} [DecidableEq α] [DecidableEq β]
    (space : Finset Ω) (X : Ω → α) (Y : Ω → β) (x : α) (y : β) : ℕ :=
  (space.filter fun ω => X ω = x ∧ Y ω = y).card

/-- Number of points in `space` on which an observation takes a prescribed value. -/
def marginalCount {Ω α : Type*} [DecidableEq α]
    (space : Finset Ω) (X : Ω → α) (x : α) : ℕ :=
  (space.filter fun ω => X ω = x).card

/-- Independence for the uniform distribution on a finite, possibly restricted, space. -/
def CountIndependent {Ω α β : Type*} [DecidableEq α] [DecidableEq β]
    (space : Finset Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ∀ x y,
    space.card * jointCount space X Y x y =
      marginalCount space X x * marginalCount space Y y

abbrev BitPair := Bool × Bool

/-- The unconditioned four-point sample space. -/
def bitPairSpace : Finset BitPair := Finset.univ

/-- The event on which the two coordinates agree. -/
def equalCoordinateEvent : Finset BitPair :=
  bitPairSpace.filter fun ω => ω.1 = ω.2

/-- Before conditioning, the two coordinate projections are independent. -/
theorem coordinate_independence_unconditioned :
    CountIndependent bitPairSpace Prod.fst Prod.snd := by
  intro x y
  cases x <;> cases y <;> decide

/-- The conditioning event consists exactly of `(false, false)` and `(true, true)`. -/
theorem equalCoordinateEvent_card : equalCoordinateEvent.card = 2 := by
  decide

/-- An off-diagonal outcome is impossible after conditioning. -/
theorem conditioned_off_diagonal_count :
    jointCount equalCoordinateEvent Prod.fst Prod.snd false true = 0 := by
  decide

/-- Each individual coordinate is still balanced on the conditioning event. -/
theorem conditioned_marginals_balanced :
    marginalCount equalCoordinateEvent Prod.fst false = 1 ∧
      marginalCount equalCoordinateEvent Prod.snd true = 1 := by
  decide

/-- After conditioning, the two coordinate projections are not independent. -/
theorem coordinate_independence_destroyed_by_conditioning :
    ¬ CountIndependent equalCoordinateEvent Prod.fst Prod.snd := by
  intro independent
  have offDiagonal := independent false true
  rw [equalCoordinateEvent_card, conditioned_off_diagonal_count,
    conditioned_marginals_balanced.1, conditioned_marginals_balanced.2] at offDiagonal
  norm_num at offDiagonal

/-- A single uniformly counted bit, used to audit the paper's overflow claim. -/
def singleBitSpace : Finset Bool := Finset.univ

/-- Adding a perfectly correlated bit modulo two. -/
def correlatedXor (b : Bool) : Bool := b.xor b

/-- The input bit is balanced. -/
theorem single_bit_balanced :
    marginalCount singleBitSpace id false = 1 ∧
      marginalCount singleBitSpace id true = 1 := by
  decide

/-- Adding a correlated copy can collapse a balanced bit to a constant. -/
theorem correlated_overflow_can_destroy_balance :
    marginalCount singleBitSpace correlatedXor false = 2 ∧
      marginalCount singleBitSpace correlatedXor true = 0 := by
  decide

end SimonDCP.Probability.Conditioning
