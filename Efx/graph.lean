import Efx.Basic

open fairdivision

variable {Agent Item : Type}
variable [Fintype Agent] [Inhabited Agent] [DecidableEq Agent] [DecidableEq Item]

def rotate_allocation
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  : FDState Agent Item :=
  { A := fun i => st.A (C.next c st i),
    U := st.U }

-- Invariant 1: Feasibility is preserved under rotation
lemma union_of_allocated_items_unchanged
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st) :
  Finset.univ.biUnion (rotate_allocation c st C).A = Finset.univ.biUnion st.A := by
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
    use (EnvyCycle.next c st C a)
  · -- Show that if x is in the union of the old allocation,
    -- then it is in the union of the new allocation
    intro h
    rcases h with ⟨a, ha⟩
    rw [EnvyCycle.prev_next c st C a] at ha
    use (EnvyCycle.prev c st C a)

lemma feasibility_preserved_under_rotation
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st) :
  Feasible c st →
  Feasible c (rotate_allocation c st C) :=
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

-- Invariant 2: Potential decreases under rotation
lemma utility_increasing_for_cycle_agents
  (c : FDContext Agent Item)
  (st : FDState Agent Item )
  (C : EnvyCycle c st)
  (i : Agent)
  (h_mem : i ∈ C.agents) :
  let st1 := rotate_allocation c st C;
  c.u i (st1.A i) > c.u i (st.A i) := by
  obtain ⟨idx, h_idx⟩ := List.mem_iff_get.1 h_mem
  by_cases h_last : idx.val = C.agents.length - 1
  · simp [rotate_allocation]
    have h_envy_last: Envies c.u st.A (C.agents[idx.val]) (C.agents[0]) := by
      simp [h_last]
      exact C.last
    have h_i_next_eq_head : EnvyCycle.next c st C i = C.agents[0] := by
      rw [← h_idx]
      simp [h_last]
      exact (EnvyCycle.next_of_last c st C)
    rw [h_i_next_eq_head]
    simp [Envies] at h_envy_last
    simp at h_idx
    rw [h_idx] at h_envy_last
    omega
  · simp [rotate_allocation]
    have h_envy_next : Envies c.u st.A (C.agents[idx.val]) (C.agents[idx.val + 1]) := by
      exact C.chain idx (by omega)
    have h_i_next_eq_next : EnvyCycle.next c st C i = C.agents[idx.val + 1] := by
      rw [← h_idx]
      exact (EnvyCycle.next_of_other c st C idx.val (by omega))
    rw [h_i_next_eq_next]
    simp [Envies] at h_envy_next
    simp at h_idx
    rw [h_idx] at h_envy_next
    omega

lemma utility_unchanged_for_non_cycle_agents (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (i : Agent)
  (h_not_mem : i ∉ C.agents) :
  let st1 := rotate_allocation c st C;
  c.u i (st1.A i) = c.u i (st.A i) := by
  simp [rotate_allocation]
  unfold EnvyCycle.next
  simp [h_not_mem]

lemma utility_nondecreasing_under_rotation
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st) :
  let st1 := rotate_allocation c st C;
  ∀ i : Agent, c.u i (st1.A i) ≥ c.u i (st.A i) := by
  intro st1 i
  -- We need to show that the utility of each agent does not decrease after rotation.
  -- This means we need to show that for each agent, the items allocated to them after rotation
  -- give them at least as much utility as the items allocated to them before rotation.
  by_cases h_mem : i ∈ C.agents
  · have := utility_increasing_for_cycle_agents c st C i h_mem
    linarith
  · -- If i is not in the envy cycle, then rotate_allocation c st C i = st.A i,
    -- so utility is unchanged
    have := utility_unchanged_for_non_cycle_agents c st C i h_mem
    rw [this]

lemma potential_decreases_after_rotation
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st)
  (h_feasible : Feasible c st) :
  potential c (rotate_allocation c st C) < potential c st := by
  have h_feasible_after_rotation : Feasible c (rotate_allocation c st C) := by
    apply feasibility_preserved_under_rotation c st C
    exact h_feasible
  have h_unallocated_unchanged : (rotate_allocation c st C).U = st.U := by
    simp [rotate_allocation]
  rw [
    potential_lt_equiv_social_welfare_gt c (rotate_allocation c st C) st
     h_feasible_after_rotation h_feasible h_unallocated_unchanged
  ]
  unfold social_welfare
  apply Finset.sum_lt_sum
  · intro i hi
    have := utility_nondecreasing_under_rotation c st C i
    omega
  · use C.agents.head C.not_nil
    have h_C_head_mem : C.agents.head C.not_nil ∈ C.agents := by simp
    have := utility_increasing_for_cycle_agents c st C (C.agents.head C.not_nil) h_C_head_mem
    constructor
    · simp [Finset.mem_univ]
    · linarith


-- Invariant 3: Ef1 is preserved under rotation
lemma ef1_preserved_under_rotation
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (C : EnvyCycle c st) :
  EF1 c.u st.A → EF1 c.u (rotate_allocation c st C).A := by
  intro h_ef1
  -- We need to show that the new allocation after rotation is still EF1.
  -- This means we need to show that for any two agents, if one envies the other in the new
  -- allocation, then there is some item in the envied agent's bundle that can be removed
  -- to eliminate the envy.
  intros i j h_envy
  -- By definition of envy, we have
  -- u i (rotate_allocation c st C i) < u i (rotate_allocation c st C j)
  -- We want to find an item in rotate_allocation c st C j that can be removed to eliminate the envy.
  -- Since rotate_allocation only changes the bundles of agents in the envy cycle,
  -- we can use the structure of the envy cycle to find such an item.
  -- Let k be the next agent in the envy cycle after j. Then we have:
  -- u i (rotate_allocation c st C i) < u i (rotate_allocation c st C j) = u i (A k)
  -- Since A is EF1, there exists an item x in A k such that:
  -- u i (A k \ {x}) ≤ u i (A j)
  -- We will show that this same item x can be removed from
  -- rotate_allocation c st C j to eliminate the envy.
  let i_next := C.next c st i
  let j_next := C.next c st j
  have h_envy_k : c.u i (st.A i_next) < c.u i (st.A j_next) := by
    exact h_envy
  have h_ef1_k : EF1ij c.u st.A i j_next := h_ef1 i j_next
  have h_envies_i_next_org : c.u i (st.A i_next) ≥ c.u i (st.A i) :=
    by apply utility_nondecreasing_under_rotation c st C i
  have h_envies_j_next_org: Envies c.u st.A i j_next := by
    simp [Envies]
    linarith
  simp [EF1ij] at h_ef1_k
  have h_ef1_i_j_next_org: ∃ g ∈ st.A j_next, c.u i (st.A i) ≥ c.u i (st.A j_next \ {g}) := by
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
