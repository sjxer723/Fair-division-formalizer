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

structure FDContext (Agent Item : Type) where
  (M : Finset Item)
  (u : Agent → Finset Item → ℕ)
  (mono_u : Monotone u)

structure FDState (Agent Item : Type) where
  (A : Allocation Agent Item)
  (U : Finset Item) -- unallocated items

structure Feasible (c : FDContext Agent Item) (st : FDState Agent Item) where
  disjoint : Disjoint (Finset.univ.biUnion st.A) st.U
  cover : Finset.univ.biUnion st.A ∪ st.U = c.M

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

structure EnvyCycle (c : FDContext Agent Item) (st : FDState Agent Item) where
  agents : List Agent
  nodup  : agents.Nodup
  not_nil : agents ≠ []
  length_gt_one : agents.length > 1
  chain  : ∀ i (hi : i < agents.length - 1),
    Envies c.u st.A (agents.get ⟨i, by omega⟩) (agents.get ⟨i + 1, by omega⟩)
  last   : Envies c.u st.A (agents[agents.length - 1]) (agents[0])

def EnvyCycle.next
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : Agent)
  : Agent :=
  match C.agents.findIdx (· = i) with
  | idx =>
      if h : idx < C.agents.length then
        -- Get the next agent in the list (circularly)
        C.agents.get (⟨idx, h⟩ + ⟨1, C.length_gt_one⟩)
      else i

def EnvyCycle.prev
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : Agent)
  : Agent :=
  match C.agents.findIdx (· = i) with
  | idx =>
      if h : idx < C.agents.length then
        -- Get the previous agent in the list (circularly)
        C.agents.get (⟨idx, h⟩ + ⟨C.agents.length - 1, by omega⟩)
      else i

lemma EnvyCycle.next_prev
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : Agent) :
  i = C.prev c st (C.next c st i)  := by
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
lemma EnvyCycle.prev_next
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : Agent) :
  i = C.next c st (C.prev c st i) := by
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


lemma EnvyCycle.next_of_last
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st) :
  have : C.agents.length > 1 := C.length_gt_one;
  C.next c st (C.agents[C.agents.length - 1]) = C.agents[0] := by
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

lemma EnvyCycle.next_of_other
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : ℕ)
  (hmem : i < C.agents.length - 1) :
  C.next c st (C.agents[i]) = C.agents[i + 1] := by
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

def social_welfare (c : FDContext Agent Item) (st : FDState Agent Item) : ℕ :=
  ∑ i, c.u i (st.A i)

lemma upper_bound_of_social_welfare
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_fea : Feasible c st) :
  social_welfare c st ≤ ∑ i, c.u i c.M := by
  unfold social_welfare
  -- have h_sum_le : ∑ i, u i (A i) ≤ ∑ i, u i M := by
  apply Finset.sum_le_sum
  intro i hi
  apply c.mono_u
  -- We need to show that A i ⊆ M for each agent i.
  -- This follows from the feasibility condition: A i is part of the allocation, and M is the set of
  -- items that are not allocated to any agent, so A i must be a subset of the items that are
  -- allocated to agents, which is a subset of M.
  have h_union_subset_M :
    Finset.univ.biUnion st.A ⊆ c.M := by
    intro x hx
    have : x ∈ Finset.univ.biUnion st.A ∪ st.U :=
      Finset.mem_union.mpr (Or.inl hx)
    simpa [h_fea.cover] using this
  have h_alloc_subset : st.A i ⊆ (Finset.univ.biUnion st.A) := by
    apply Finset.subset_biUnion_of_mem
    exact Finset.mem_univ i
  exact h_alloc_subset.trans h_union_subset_M

def potential (c : FDContext Agent Item) (st : FDState Agent Item) : ℕ :=
   ∑ i, c.u i c.M  - ∑ i, c.u i (st.A i) + st.U.card

lemma potential_nonnegative
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_fea : Feasible c st) :
  potential c st ≥ 0 := by
  unfold potential
  have h_sum_le : ∑ i, c.u i (st.A i) ≤ ∑ i, c.u i c.M := by
    apply upper_bound_of_social_welfare c st h_fea
  linarith

lemma potential_lt_equiv_social_welfare_gt
  (c : FDContext Agent Item)
  (st1 st2 : FDState Agent Item)
  (h_fea1 : Feasible c st1)
  (h_fea2 : Feasible c st2)
  (h_unallocated_unchanged : st1.U = st2.U) :
  potential c st1 < potential c st2 ↔ social_welfare c st1 > social_welfare c st2 := by
  unfold potential social_welfare
  have h_potential1_pos : ∑ i, c.u i c.M ≥ ∑ i, c.u i (st1.A i) := by
    apply upper_bound_of_social_welfare c st1 h_fea1
  have h_potential2_pos : ∑ i, c.u i c.M ≥ ∑ i, c.u i (st2.A i) := by
    apply upper_bound_of_social_welfare c st2 h_fea2
  have h_eq_card : st1.U.card = st2.U.card := by
    rw [h_unallocated_unchanged]
  omega

lemma potential_lt_implied_by_unallocated_size_lt
  (c : FDContext Agent Item)
  (st1 st2 : FDState Agent Item)
  (h_fea1 : Feasible c st1)
  (h_fea2 : Feasible c st2)
  (h_social_welfare_unchanged : social_welfare c st1 ≥ social_welfare c st2) :
  st1.U.card < st2.U.card ->
  potential c st1 < potential c st2 := by
  intro h_unallocated_size_lt
  unfold potential
  have h_potential1_pos : ∑ i, c.u i c.M ≥ ∑ i, c.u i (st1.A i) := by
    apply upper_bound_of_social_welfare c st1 h_fea1
  have h_potential2_pos : ∑ i, c.u i c.M ≥ ∑ i, c.u i (st2.A i) := by
    apply upper_bound_of_social_welfare c st2 h_fea2
  simp [social_welfare] at h_social_welfare_unchanged
  omega

end fairdivision
