import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.Cases
import Mathlib.Combinatorics.Additive.Convolution

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

namespace fairdivision

variable {Agent Item : Type}
variable [Fintype Agent] [Inhabited Agent] [DecidableEq Agent] [DecidableEq Item]
def Allocation (Agent Item : Type) := Agent → Finset Item
structure is_feasible (A : Allocation Agent Item) (U : Finset Item) (Items : Finset Item) where
  disjoint : Disjoint (Finset.univ.biUnion A) U
  cover : Finset.univ.biUnion A ∪ U = Items

def Envies
  (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (i j : Agent) : Prop :=
  u i (A i) < u i (A j)

def EF1ij (u : Agent → Finset Item → ℕ) (A : Allocation Agent Item) (i j : Agent) : Prop :=
  Envies u A i j →
   ∃ g ∈ A j, u i (A i) ≥ u i (A j \ {g})

def EF1
  (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item) : Prop :=
  ∀ i j : Agent,
    EF1ij u A i j

structure EnvyCycle (u : Agent → Finset Item → ℕ) (A : Allocation Agent Item) where
  agents : List Agent
  nodup  : agents.Nodup
  ne_nil : agents ≠ []
  gt_one : agents.length > 1
  chain  : ∀ i (hi : i < agents.length - 1),
    Envies u A (agents.get ⟨i, by omega⟩) (agents.get ⟨i + 1, by omega⟩)
  last   : Envies u A (agents[agents.length - 1]) (agents[0])

def EnvyCycle.next (u : Agent → Finset Item → ℕ) (C : EnvyCycle u A) (i : Agent) : Agent :=
  match C.agents.findIdx (· = i) with
  | idx =>
      if h : idx < C.agents.length then
        -- Get the next agent in the list (circularly)
        C.agents.get (⟨idx, h⟩ + ⟨1, C.gt_one⟩)
      else i

def EnvyCycle.prev (u : Agent → Finset Item → ℕ) (C : EnvyCycle u A) (i : Agent) : Agent :=
  match C.agents.findIdx (· = i) with
  | idx =>
      if h : idx < C.agents.length then
        -- Get the previous agent in the list (circularly)
        C.agents.get (⟨idx, h⟩ + ⟨C.agents.length - 1, by omega⟩)
      else i

lemma EnvyCycle.next_prev (u : Agent → Finset Item → ℕ)
  (C : EnvyCycle u A)
  (i : Agent) :
  i = C.prev u (C.next u i)  := by
  by_cases hmem : i ∈ C.agents
  · --- i ∈ C.agents
    rcases List.mem_iff_get.mp hmem with ⟨idx, hidx, hget⟩
    unfold next prev
    simp
    have h_inner : List.findIdx (· = C.agents[idx]) C.agents = idx := by
      apply findIdx_get _ C.nodup idx
    simp [h_inner] at *
    congr
    let next_idx : Fin C.agents.length := idx + ⟨1, C.gt_one⟩
    have h_find :
      List.findIdx (· = C.agents[next_idx.val]) C.agents = next_idx := by
        simp [findIdx_get _ C.nodup next_idx]
    unfold next_idx at h_find
    simp_all
    exact fin_add_one_sub_one idx C.gt_one
  · -- i ∉ C.agents
    unfold next prev
    simp [hmem]

-- set_option pp.all true in
lemma EnvyCycle.prev_next (u : Agent → Finset Item → ℕ)
  (C : EnvyCycle u A)
  (i : Agent) :
  i = C.next u (C.prev u i)  := by
  by_cases hmem : i ∈ C.agents
  · --- i ∈ C.agents
    rcases List.mem_iff_get.mp hmem with ⟨idx, hidx, hget⟩
    unfold next prev
    simp
    have h_inner : List.findIdx (· = C.agents[idx]) C.agents = idx := by
      apply findIdx_get _ C.nodup idx
    simp [h_inner] at *
    congr
    let prev_idx : Fin C.agents.length := idx + ⟨C.agents.length - 1, by omega⟩
    have h_find :
      List.findIdx (· = C.agents[prev_idx.val]) C.agents = prev_idx := by
        simp [findIdx_get _ C.nodup prev_idx]
    unfold prev_idx at h_find
    simp_all
    exact fin_sub_one_add_one idx C.gt_one
  · -- i ∉ C.agents
    unfold next prev
    simp [hmem]


lemma EnvyCycle.next_of_last (u : Agent → Finset Item → ℕ)
  (C : EnvyCycle u A) :
  have : C.agents.length > 1 := C.gt_one;
  C.next u (C.agents[C.agents.length - 1]) = C.agents[0] := by
  unfold EnvyCycle.next
  have h_C_pos_len : C.agents.length > 1 := C.gt_one
  let idx_of_last := List.findIdx (fun x ↦ decide (x = C.agents[C.agents.length - 1])) C.agents
  have idx_of_last_eq_len_minus_one : idx_of_last = C.agents.length - 1 := by
    unfold idx_of_last
    exact (findIdx_get _ C.nodup ⟨C.agents.length - 1, by omega⟩)
  have idx_of_last_lt_len : idx_of_last < C.agents.length := by
    rw [idx_of_last_eq_len_minus_one]
    omega
  have h_next_of_last : C.agents.get
           (⟨idx_of_last, idx_of_last_lt_len⟩ + ⟨1, h_C_pos_len⟩)
         = C.agents.get ⟨0, by omega⟩ := by
    simp [idx_of_last_eq_len_minus_one]
    congr
    have := fin_n_minus_one_add_one h_C_pos_len
    simp [this]
  simp
  exact h_next_of_last

lemma EnvyCycle.next_of_other ( u : Agent → Finset Item → ℕ)
  (C : EnvyCycle u A)
  (i : ℕ)
  (hmem : i < C.agents.length - 1) :
  C.next u (C.agents[i]) = C.agents[i + 1] := by
  unfold EnvyCycle.next
  let idx : Fin C.agents.length := ⟨i, by omega⟩
  have h_find_idx : List.findIdx (fun x ↦ decide (x = C.agents[i])) C.agents = i := by
    apply findIdx_get _ C.nodup idx
  have h_i_lt_len : i < C.agents.length := by
    omega
  have h_next_of_other : C.agents.get
           (⟨i, by omega⟩ + ⟨1, C.gt_one⟩)
         = C.agents.get ⟨i + 1, by omega⟩ := by
    congr
    have := fin_i_lt_n_add_one C.gt_one hmem
    simp [this]
  simp [h_find_idx]
  simp [h_i_lt_len]
  exact h_next_of_other

def rotate_allocation
  (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (C : EnvyCycle u A) : Allocation Agent Item :=
  fun i => A (C.next u i)


def potential (u : Agent → Finset Item → ℕ) (A : Allocation Agent Item) (U : Finset Item) : ℕ :=
   ∑ i, u i U  - ∑ i, u i (A i)
  -- (U.card, - ∑ i, u i (A i))


end fairdivision
