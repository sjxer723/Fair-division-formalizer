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
import Efx.Basic

open fairdivision

variable {Agent Item : Type}
variable [Fintype Agent] [Inhabited Agent] [DecidableEq Agent] [DecidableEq Item]

lemma union_of_allocated_items_unchanged (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item) (C : EnvyCycle u A) :
  Finset.univ.biUnion (rotate_allocation u A C) = Finset.univ.biUnion A := by
  -- We need to show that the union of the items allocated to all agents is unchanged after
  -- rotation. This means we need to show that for each agent, the items allocated to them
  -- after rotation are the same as the items allocated to some agent before rotation.
  ext x
  simp [rotate_allocation]
  constructor
  · -- Show that if x is in the union of the new allocation,
    -- then it is in the union of the old allocation
    intro h
    rcases h with ⟨a, ha⟩
    use (EnvyCycle.next u C a)
  · -- Show that if x is in the union of the old allocation,
    -- then it is in the union of the new allocation
    intro h
    rcases h with ⟨a, ha⟩
    rw [EnvyCycle.prev_next u C a] at ha
    use (EnvyCycle.prev u C a)

lemma feasibility_preserved_under_rotation
  (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (Items : Finset Item)
  (C : EnvyCycle u A)
  (U : Finset Item) :
  Feasible A U Items →
  Feasible (rotate_allocation u A C) U Items :=
by
  intro h_fea
  -- We need to show that the new allocation after rotation is still feasible.
  -- This means we need to show that the union of the new allocation's items and U
  -- is still equal to Items, and that the new allocation's items are disjoint from U.
  constructor
  · -- Show that the new allocation's items are disjoint from U
    -- unfold rotate_allocation
    rw [union_of_allocated_items_unchanged]
    exact h_fea.disjoint
  · -- Show that the union of the new allocation's items and U is equal to Items
    -- unfold rotate_allocation
    rw [union_of_allocated_items_unchanged]
    exact h_fea.cover

lemma utility_increasing_for_cycle_agents (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (C : EnvyCycle u A)
  (i : Agent)
  (h_mem : i ∈ C.agents) :
  u i (rotate_allocation u A C i) > u i (A i) := by
  obtain ⟨idx, h_idx⟩ := List.mem_iff_get.1 h_mem
  by_cases h_last : idx.val = C.agents.length - 1
  · simp [rotate_allocation]
    have h_envy_last: Envies u A (C.agents[idx.val]) (C.agents[0]) := by
      simp [h_last]
      exact C.last
    have h_i_next_eq_head : EnvyCycle.next u C i = C.agents[0] := by
      rw [← h_idx]
      simp [h_last]
      exact (EnvyCycle.next_of_last u C)
    rw [h_i_next_eq_head]
    simp [Envies] at h_envy_last
    simp at h_idx
    rw [h_idx] at h_envy_last
    omega
  · simp [rotate_allocation]
    have h_envy_next : Envies u A (C.agents[idx.val]) (C.agents[idx.val + 1]) := by
      exact C.chain idx (by omega)
    have h_i_next_eq_next : EnvyCycle.next u C i = C.agents[idx.val + 1] := by
      rw [← h_idx]
      exact (EnvyCycle.next_of_other u C idx.val (by omega))
    rw [h_i_next_eq_next]
    simp [Envies] at h_envy_next
    simp at h_idx
    rw [h_idx] at h_envy_next
    omega

lemma utility_unchanged_for_non_cycle_agents (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (C : EnvyCycle u A)
  (i : Agent)
  (h_not_mem : i ∉ C.agents) : u i (rotate_allocation u A C i) = u i (A i) := by
  simp [rotate_allocation]
  unfold EnvyCycle.next
  simp [h_not_mem]

lemma utility_nondecreasing_under_rotation (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item)
  (C : EnvyCycle u A) :
  ∀ i, u i (rotate_allocation u A C i) ≥ u i (A i) := by
  intro i
  -- We need to show that the utility of each agent does not decrease after rotation.
  -- This means we need to show that for each agent, the items allocated to them after rotation
  -- give them at least as much utility as the items allocated to them before rotation.
  by_cases h_mem : i ∈ C.agents
  · have := utility_increasing_for_cycle_agents u A C i h_mem
    linarith
  · -- If i is not in the envy cycle, then rotate_allocation u A C i = A i, so utility is unchanged
    have := utility_unchanged_for_non_cycle_agents u A C i h_mem
    rw [this]

lemma ef1_preserved_under_rotation (u : Agent → Finset Item → ℕ)
  (A : Allocation Agent Item) (C : EnvyCycle u A) :
  EF1 u A → EF1 u (rotate_allocation u A C) := by
  intro h_ef1
  -- We need to show that the new allocation after rotation is still EF1.
  -- This means we need to show that for any two agents, if one envies the other in the new
  -- allocation, then there is some item in the envied agent's bundle that can be removed
  -- to eliminate the envy.
  intros i j h_envy
  -- By definition of envy, we have
  -- u i (rotate_allocation u A C i) < u i (rotate_allocation u A C j)
  -- We want to find an item in rotate_allocation u A C j that can be removed to eliminate the envy.
  -- Since rotate_allocation only changes the bundles of agents in the envy cycle,
  -- we can use the structure of the envy cycle to find such an item.
  -- Let k be the next agent in the envy cycle after j. Then we have:
  -- u i (rotate_allocation u A C i) < u i (rotate_allocation u A C j) = u i (A k)
  -- Since A is EF1, there exists an item x in A k such that:
  -- u i (A k \ {x}) ≤ u i (A j)
  -- We will show that this same item x can be removed from
  -- rotate_allocation u A C j to eliminate the envy.
  let i_next := EnvyCycle.next u C i
  let j_next := EnvyCycle.next u C j
  have h_envy_k : u i (A i_next) < u i (A j_next) := by
    exact h_envy
  have h_ef1_k : EF1ij u A i j_next := h_ef1 i j_next
  have h_envies_i_next_org : u i (A i_next) ≥ u i (A i) :=
    by apply utility_nondecreasing_under_rotation u A C i
  have h_envies_j_next_org: Envies u A i j_next := by
    simp [Envies]
    linarith
  simp [EF1ij] at h_ef1_k
  have h_ef1_i_j_next_org: ∃ g ∈ A j_next, u i (A i) ≥ u i (A j_next \ {g}) := by
    apply h_ef1_k
    exact h_envies_j_next_org
  simp [rotate_allocation]
  simp [j_next] at h_ef1_i_j_next_org
  rcases h_ef1_i_j_next_org with ⟨g, hg_in_j_next, h_ef1_i_j_next_org⟩
  use g
  constructor
  · exact hg_in_j_next
  · simp [i_next] at h_envies_i_next_org
    omega


lemma potential_decreases_after_rotation (u : Agent → Finset Item → ℕ)
  (h_mono_u : Monotone u)
  (A : Allocation Agent Item)
  (U : Finset Item)
  (M : Finset Item)
  (C : EnvyCycle u A)
  (h_feasible : Feasible A U M):
  potential u (rotate_allocation u A C) M < potential u A M := by
  have h_feasible_after_rotation : Feasible (rotate_allocation u A C) U M := by
    apply feasibility_preserved_under_rotation u A M C U
    exact h_feasible
  rw [
    potential_lt_equiv_social_welfare_gt u (rotate_allocation u A C) _ _ _ _
      h_mono_u h_feasible_after_rotation h_feasible
  ]
  unfold social_welfare
  apply Finset.sum_lt_sum
  · intro i hi
    have := utility_nondecreasing_under_rotation u A C i
    omega
  · use C.agents.head C.not_nil
    have h_C_head_mem : C.agents.head C.not_nil ∈ C.agents := by simp
    have := utility_increasing_for_cycle_agents u A C (C.agents.head C.not_nil) h_C_head_mem
    constructor
    · simp [Finset.mem_univ]
    · linarith
