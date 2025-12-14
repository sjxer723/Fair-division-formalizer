import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic


open Finset
open Function
open scoped BigOperators Finset

/-
Basic setup:
- We fix a finite type `Item` of indivisible goods.
- There are exactly three agents: 0, 1, 2.
- Each agent has an additive valuation over items (nonnegative reals per item).
-/

abbrev Agent := Fin 3
variable {Item : Type} [DecidableEq Item] [Fintype Item]
def agents : Finset Agent := Finset.univ

namespace FairDivision

structure FDValuation (Item : Type) where
  items : Finset Item
  val : Agent → Item → ℝ
  nonneg : ∀ a i, 0 ≤ val a i

def all_zero {Item : Type} (v : FDValuation Item) : Prop :=
  ∀ a i, v.val a i = 0

/-- Additive extension of a valuation to finite bundles. -/
def val_on {Item : Type} (v : FDValuation Item) (a : Agent) (s : Finset Item) : ℝ :=
  s.sum (fun i => v.val a i)

/-- An allocation partitions the `items` set into three disjoint bundles, one per agent.-/
structure Allocation (V : FDValuation Item)where
  alloc : Agent → Finset Item
  pairwise_disjoint : ∀ (x y : Agent), x ≠ y → (alloc x ∩ alloc y) = ∅
  cover : (alloc 0 ∪ alloc 1 ∪ alloc 2) = V.items

/-- An allocation that gives all items to some agent. -/
def all_items_to_agent0 (V : FDValuation Item) (i : Agent) : Allocation V :=
{ alloc := fun a =>
    match a with
    | j => if j = i then V.items else ∅,
  pairwise_disjoint := by
    intros x y hxy
    by_cases hx : x = i
    · by_cases hy : y = i
      · rw [hx, hy] at hxy; contradiction
      · rw [hx]; simp;
        have h : (if y = i then V.items else ∅) = (∅ : Finset Item) := by simp [hy];
        rw [h]; simp
    · by_cases hy : y = i
      · rw [hy]; simp;
        have h : (if x = i then V.items else ∅) = (∅ : Finset Item) := by simp [hx];
        rw [h]; simp
      · have h1 : (if x = i then V.items else ∅) = (∅ : Finset Item) := by simp [hx];
        have h2 : (if y = i then V.items else ∅) = (∅ : Finset Item) := by simp [hy];
        rw [h1, h2]; simp,
  cover := by
    by_cases hi : i = 0
    · rw [hi]; simp
    · by_cases hi1 : i = 1
      · rw [hi1]; simp
      · fin_cases i <;> simp at *
}

end FairDivision
