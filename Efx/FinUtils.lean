import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

variable {α : Type _} [DecidableEq α]
lemma findIdx_get (l : List α) (hnodup : l.Nodup) (i : Fin l.length) :
    l.findIdx (fun x => x = l[i.val]) = i := by
  rw [List.findIdx_eq i.isLt]

  constructor
  · -- prove p l[i]
    simp
  · -- prove ∀ j < i, p l[j] = false
    intro j hj
    simp
    -- use l.Nodup: if l[j] = l[i], then j = i
    intro h_eq
    unfold List.Nodup at hnodup
    simp at hnodup
    have h_ne := List.pairwise_iff_getElem.1 hnodup j i.val (Nat.lt_trans hj i.isLt) i.isLt hj
    --  l[j] ≠ l[i]
    exact h_ne h_eq

lemma fin_add_one_sub_one
  {n : Nat} (idx : Fin n) (h : 1 < n) :
  idx = idx + ⟨1, h⟩ + ⟨n - 1, (by omega)⟩ := by
  -- reduce equality of `Fin` to equality of the `.val` (nat) components
  ext
  simp only [Fin.val_add]
  simp
  rw [add_assoc]
  have h_fold: 1 + (n - 1) = n := by omega
  rw [h_fold]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt idx.is_lt]

lemma fin_sub_one_add_one
  {n : Nat} (idx : Fin n) (h : 1 < n) :
  idx = idx + ⟨n - 1, (by omega)⟩ + ⟨1, h⟩ := by
  -- reduce equality of `Fin` to equality of the `.val` (nat) components
  ext
  simp only [Fin.val_add]
  simp
  rw [add_assoc]
  have h_fold: (n - 1 + 1) = n := by omega
  rw [h_fold]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt idx.is_lt]


lemma fin_i_lt_n_add_one
  {n : Nat} (h : 1 < n) (hi : i < n - 1) :
  (⟨i, by omega⟩ : Fin n) + ⟨1, h⟩ = (⟨i + 1, by omega⟩ : Fin n) := by
  ext
  simp only [Fin.val_add]
  have h_fold: (i + 1) = i + 1 := by omega
  rw [h_fold]
  have hi' : i + 1 < n := by
    omega
  rw [Nat.mod_eq_of_lt hi']


lemma fin_n_minus_one_add_one
  {n : Nat} (h : 1 < n) :
  (⟨n - 1, by omega⟩ : Fin n) + ⟨1, h⟩ = (⟨0, by omega⟩ : Fin n) := by
  ext
  simp only [Fin.val_add]
  have h_fold: (n - 1 + 1) = n := by omega
  rw [h_fold]
  have hn0 : n ≠ 0 := by
    omega
  simp [Nat.mod_self]
