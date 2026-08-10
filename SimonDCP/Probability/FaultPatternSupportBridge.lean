import SimonDCP.Probability.CoordinateSubcubeSupport
import SimonDCP.Probability.FaultCountMarkov

/-!
# From Boolean fault patterns to coordinate-subcube supports

This file turns the Boolean fault pattern used by the first-moment argument
into the finite sets used by the coordinate-subcube counting argument.  For
each environment `omega`, `faultSet` contains exactly the coordinates marked
faulty, while `freeCoordinates` is its complement in `Fin Q`.

The cardinality identities below are deterministic.  In particular, the
rational half-fault good event from `FaultCountMarkov` gives both the exact
rational lower bound `Q / 2 <= |freeCoordinates|` and its natural-number
consequence `Q / 2 <= |freeCoordinates|`.
-/

namespace SimonDCP.Probability.FaultPatternSupportBridge

open SimonDCP.Probability.CoordinateSubcubeSupport
open SimonDCP.Probability.FaultCountMarkov

section FaultPattern

variable {Omega : Type*}

/-- Coordinates marked faulty in a fixed environment. -/
def faultSet (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega) :
    Finset (Fin Q) :=
  Finset.univ.filter fun i => faulted i omega = true

@[simp]
theorem mem_faultSet_iff
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega) (i : Fin Q) :
    i ∈ faultSet Q faulted omega ↔ faulted i omega = true := by
  simp [faultSet]

/-- Coordinates that remain coherent in a fixed environment. -/
def freeCoordinates (Q : Nat) (faulted : Fin Q -> Omega -> Bool)
    (omega : Omega) : Finset (Fin Q) :=
  Finset.univ \ faultSet Q faulted omega

@[simp]
theorem mem_freeCoordinates_iff
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega) (i : Fin Q) :
    i ∈ freeCoordinates Q faulted omega ↔ faulted i omega = false := by
  cases hbit : faulted i omega <;> simp [freeCoordinates, faultSet, hbit]

/-- The set-theoretic fault count agrees with the indicator-sum count. -/
@[simp]
theorem card_faultSet
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega) :
    (faultSet Q faulted omega).card =
      coordinateFaultCount Q faulted omega := by
  classical
  have hCard := Finset.card_eq_sum_ite
    (s := Finset.univ.filter fun i : Fin Q => faulted i omega = true)
    (t := Finset.univ)
    (Finset.filter_subset (fun i : Fin Q => faulted i omega = true) Finset.univ)
  simpa only [faultSet, coordinateFaultCount, Finset.mem_filter,
    Finset.mem_univ, true_and] using hCard

/-- The complement of the fault set has the abstract `freeCount` size. -/
@[simp]
theorem card_freeCoordinates
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega) :
    (freeCoordinates Q faulted omega).card =
      freeCount Q (coordinateFaultCount Q faulted) omega := by
  classical
  rw [freeCoordinates,
    Finset.card_sdiff_of_subset (Finset.subset_univ (faultSet Q faulted omega))]
  simp [freeCount, card_faultSet]

/-- The rational half-fault good event leaves at least half the coordinates
free, with the threshold interpreted in `Rat`. -/
theorem rational_half_le_card_freeCoordinates_of_faultCount_le_half
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega)
    (hGood :
      (coordinateFaultCount Q faulted omega : Rat) <= (Q : Rat) / 2) :
    (Q : Rat) / 2 <= ((freeCoordinates Q faulted omega).card : Rat) := by
  rw [card_freeCoordinates]
  exact rational_half_le_freeCount_of_faultCount_le_half
    Q (coordinateFaultCount Q faulted) omega hGood

/-- Natural-number floor consequence of the rational half-fault good event. -/
theorem half_le_card_freeCoordinates_of_faultCount_le_half
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega)
    (hGood :
      (coordinateFaultCount Q faulted omega : Rat) <= (Q : Rat) / 2) :
    Q / 2 <= (freeCoordinates Q faulted omega).card := by
  have hTwiceRat :
      (2 : Rat) * coordinateFaultCount Q faulted omega <= (Q : Rat) := by
    linarith
  have hTwiceNat :
      2 * coordinateFaultCount Q faulted omega <= Q := by
    exact_mod_cast hTwiceRat
  have hFaultNat : coordinateFaultCount Q faulted omega <= Q / 2 := by
    omega
  rw [card_freeCoordinates]
  exact half_le_freeCount_of_faultCount_le_half
    Q (coordinateFaultCount Q faulted) omega hFaultNat

/-- Boolean selection masks compatible with the free coordinates in one
environment and with a prescribed mask on every faulty coordinate. -/
noncomputable def selectionSupport
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega)
    (fixed : Fin Q -> Bool) : Finset (Fin Q -> Bool) :=
  coordinateSubcube (freeCoordinates Q faulted omega) fixed

/-- A fault-pattern support has one Boolean degree of freedom for every
nonfaulty coordinate. -/
@[simp]
theorem card_selectionSupport
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega)
    (fixed : Fin Q -> Bool) :
    (selectionSupport Q faulted omega fixed).card =
      2 ^ (freeCoordinates Q faulted omega).card := by
  simp [selectionSupport]

/-- The same support-size identity expressed through `freeCount`. -/
theorem card_selectionSupport_eq_pow_freeCount
    (Q : Nat) (faulted : Fin Q -> Omega -> Bool) (omega : Omega)
    (fixed : Fin Q -> Bool) :
    (selectionSupport Q faulted omega fixed).card =
      2 ^ freeCount Q (coordinateFaultCount Q faulted) omega := by
  rw [card_selectionSupport, card_freeCoordinates]

end FaultPattern

end SimonDCP.Probability.FaultPatternSupportBridge
