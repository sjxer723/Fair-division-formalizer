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
import Efx.FinUtils
import Mathlib.Algebra.Order.Group.Int.Sum

namespace fairdivision

variable {Agent Item : Type}
variable [Fintype Agent] [Inhabited Agent] [DecidableEq Agent] [DecidableEq Item]

def Allocation (Agent Item : Type) := Agent → Finset Item

def Monotone (u : Agent → Finset Item → ℕ) : Prop :=
  ∀ a s t, s ⊆ t → u a s ≤ u a t

structure Feasible (A : Allocation Agent Item) (U : Finset Item) (Items : Finset Item) where
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
  not_nil : agents ≠ []
  length_gt_one : agents.length > 1
  chain  : ∀ i (hi : i < agents.length - 1),
    Envies u A (agents.get ⟨i, by omega⟩) (agents.get ⟨i + 1, by omega⟩)
  last   : Envies u A (agents[agents.length - 1]) (agents[0])

def EnvyCycle.next (u : Agent → Finset Item → ℕ) (C : EnvyCycle u A) (i : Agent) : Agent :=
  match C.agents.findIdx (· = i) with
  | idx =>
      if h : idx < C.agents.length then
        -- Get the next agent in the list (circularly)
        C.agents.get (⟨idx, h⟩ + ⟨1, C.length_gt_one⟩)
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
    let next_idx : Fin C.agents.length := idx + ⟨1, C.length_gt_one⟩
    have h_find :
      List.findIdx (· = C.agents[next_idx.val]) C.agents = next_idx := by
        simp [findIdx_get _ C.nodup next_idx]
    unfold next_idx at h_find
    simp_all
    exact fin_add_one_sub_one idx C.length_gt_one
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
    exact fin_sub_one_add_one idx C.length_gt_one
  · -- i ∉ C.agents
    unfold next prev
    simp [hmem]


lemma EnvyCycle.next_of_last (u : Agent → Finset Item → ℕ)
  (C : EnvyCycle u A) :
  have : C.agents.length > 1 := C.length_gt_one;
  C.next u (C.agents[C.agents.length - 1]) = C.agents[0] := by
  unfold EnvyCycle.next
  have h_C_pos_len : C.agents.length > 1 := C.length_gt_one
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
           (⟨i, by omega⟩ + ⟨1, C.length_gt_one⟩)
         = C.agents.get ⟨i + 1, by omega⟩ := by
    congr
    have := fin_i_lt_n_add_one C.length_gt_one hmem
    simp [this]
  simp [h_find_idx]
  simp [h_i_lt_len]
  exact h_next_of_other

def rotate_allocation
  (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (C : EnvyCycle u A) : Allocation Agent Item :=
  fun i => A (C.next u i)


def social_welfare (u : Agent → Finset Item → ℕ) (A : Allocation Agent Item) : ℕ :=
  ∑ i, u i (A i)

lemma upper_bound_of_social_welfare
  (u : Agent → Finset Item → ℕ)
  (h_mono_u : Monotone u)
  (A : Allocation Agent Item)
  (U : Finset Item) -- unallocated items
  (M : Finset Item) -- ground set of items
  (h_fea : Feasible A U M) :
  social_welfare u A ≤ ∑ i, u i M := by
  unfold social_welfare
  -- have h_sum_le : ∑ i, u i (A i) ≤ ∑ i, u i M := by
  apply Finset.sum_le_sum
  intro i hi
  apply h_mono_u
  -- We need to show that A i ⊆ M for each agent i.
  -- This follows from the feasibility condition: A i is part of the allocation, and M is the set of
  -- items that are not allocated to any agent, so A i must be a subset of the items that are
  -- allocated to agents, which is a subset of M.
  have h_union_subset_M :
    Finset.univ.biUnion A ⊆ M := by
    intro x hx
    have : x ∈ Finset.univ.biUnion A ∪ U :=
      Finset.mem_union.mpr (Or.inl hx)
    simpa [h_fea.cover] using this
  have h_alloc_subset : A i ⊆ (Finset.univ.biUnion A) := by
    apply Finset.subset_biUnion_of_mem
    exact Finset.mem_univ i
  exact h_alloc_subset.trans h_union_subset_M

def potential (u : Agent → Finset Item → ℕ) (A : Allocation Agent Item) (M : Finset Item) : ℕ :=
   ∑ i, u i M  - ∑ i, u i (A i)

lemma potential_nonnegative
  (u : Agent → Finset Item → ℕ)
  (h_mono_u : Monotone u)
  (A : Allocation Agent Item)
  (U : Finset Item)
  (M : Finset Item)
  (h_fea : Feasible A U M) :
  potential u A M ≥ 0 := by
  unfold potential
  have h_sum_le : ∑ i, u i (A i) ≤ ∑ i, u i M := by
    apply upper_bound_of_social_welfare u h_mono_u A U M h_fea
  linarith

lemma potential_lt_equiv_social_welfare_gt
  (u : Agent → Finset Item → ℕ)
  (A1 A2 : Allocation Agent Item)
  (U1 U2 : Finset Item)
  (M : Finset Item)
  (h_mono_u : Monotone u)
  (h_feasible1 : Feasible A1 U1 M)
  (h_feasible2 : Feasible A2 U2 M) :
  potential u A1 M < potential u A2 M ↔ social_welfare u A1 > social_welfare u A2 := by
  unfold potential social_welfare
  have h_potential1_pos : ∑ i, u i M ≥ ∑ i, u i (A1 i) := by
    apply upper_bound_of_social_welfare u h_mono_u A1 U1 M h_feasible1
  have h_potential2_pos : ∑ i, u i M ≥ ∑ i, u i (A2 i) := by
    apply upper_bound_of_social_welfare u h_mono_u A2 U2 M h_feasible2
  omega

end fairdivision
