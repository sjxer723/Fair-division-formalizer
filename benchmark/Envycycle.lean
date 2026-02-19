import Fairdivision.Basic
import Fairdivision.Envygraph

open fairdivision

section EnvycycleProc

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


def add_item_to_agent
  (st : FDState Agent Item)
  (source : Agent)
  (g : Item) : FDState Agent Item :=
{ A := fun i => if i = source then st.A i ∪ {g} else st.A i,
  U := st.U.erase g }

lemma feasibility_preserved_under_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (source : Agent)
  (g : Item)
  (h_g_in_U : g ∈ st.U)
  (h_feasible : Feasible c st) :
  Feasible c (add_item_to_agent st source g) := by
  have h_disjoint : Disjoint (Finset.univ.biUnion st.A) st.U := h_feasible.disjoint
  have h_cover : Finset.univ.biUnion st.A ∪ st.U = c.M := h_feasible.cover
  constructor
  · -- Show that the new allocation's items are disjoint from U
    simp [add_item_to_agent]
    simp_all
  · -- Show that the union of the new allocation's items and U is equal to Items
    simp [add_item_to_agent]
    simp_all

lemma utility_nondecreasing_after_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (source i : Agent)
  (g : Item) :
  c.u i (st.A i) ≤ c.u i ((add_item_to_agent st source g).A i) := by
  by_cases h_source : i = source
  -- source agent gets a new item, so utility should increase
  · rw [h_source]
    simp [add_item_to_agent]
    apply c.mono_u
    simp
  -- other agents' bundles are unchanged, so utility should be the same
  · apply c.mono_u
    simp [add_item_to_agent, h_source]

lemma potential_decreases_after_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_feasible : Feasible c st)
  (source : Agent)
  (g : Item)
  (h_g_in_U : g ∈ st.U) :
  potential c (add_item_to_agent st source g) < potential c st := by

  -- the number of unallocated items decreases by 1
  have h_unallocated_decreases : (add_item_to_agent st source g).U.card < st.U.card := by
    simp [add_item_to_agent]
    exact (Finset.card_erase_lt_of_mem h_g_in_U)

  -- the total social welfare does not decrease
  have h_social_welfare_nondecreasing :
    social_welfare c (add_item_to_agent st source g) ≥ social_welfare c st := by
    unfold social_welfare
    apply Finset.sum_le_sum
    intro i hi
    exact utility_nondecreasing_after_add_item_to_agent c st source i g

  -- the allocation remains feasible
  have h_feasible1 : Feasible c (add_item_to_agent st source g) := by
    exact feasibility_preserved_under_add_item_to_agent c st source g h_g_in_U h_feasible

  simp_all

lemma ef1_preserved_under_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (source : Agent)
  (h_source : ∀ j, ¬ Envies c.u st.A j source)
  (g : Item) :
  let st1 := add_item_to_agent st source g;
  EF1 c.u st.A → EF1 c.u st1.A := by
  intro st1 h_ef1
  unfold st1 EF1
  intro i j
  have h_envy_st1 : EF1ij c.u st.A i j := h_ef1 i j
  -- simp [EF1ij] at h_envy_st1
  by_cases h_source_i : i = source
  · simp [h_source_i] at *
    by_cases h_source_j : j = source
    · simp [h_source_j]
      simp [EF1ij]
      intro h_envy
      simp [Envies] at h_envy
    · simp [add_item_to_agent]
      have h_j_not_envy_source : ¬ Envies c.u st.A j source := h_source j
      exact (ef1ij_insert_i_of_ef1ij h_envy_st1)
  · have h_i_neq_source : i ≠ source := by omega
    by_cases h_source_j : j = source
    · simp [h_source_j] at *
      simp [add_item_to_agent]
      exact (ef1ij_maintained_after_adding_item_to_j c i source st.A g (h_source i))
    · have h_j_neq_source : j ≠ source := by omega
      simp [EF1ij]
      have h_i_bundle_unchanged : (add_item_to_agent st source g).A i = st.A i := by
        simp [add_item_to_agent, h_i_neq_source]
      have h_j_bundle_unchanged : (add_item_to_agent st source g).A j = st.A j := by
        simp [add_item_to_agent, h_j_neq_source]
      -- rw [h_i_bundle_unchanged, h_j_bundle_unchanged] at h_envy_
      simp [Envies]
      rw [h_i_bundle_unchanged, h_j_bundle_unchanged] at *
      exact h_envy_st1


end EnvycycleProc

abbrev Agent (n : ℕ) := Fin n
abbrev Item (m : ℕ) := Fin m

variable {n m : ℕ}

example {n : ℕ} : Fintype (Agent n) := inferInstance
example {n : ℕ} : DecidableEq (Agent n) := inferInstance
example {n : ℕ} [NeZero n] : Inhabited (Agent n) := inferInstance

example {m : ℕ} : Fintype (Item m) := inferInstance
example {m : ℕ} : DecidableEq (Item m) := inferInstance
example {m : ℕ} [NeZero m] : Inhabited (Item m) := inferInstance

noncomputable def envy_cycle_procedure
  (c : FDContext (Agent n) (Item m)) [NeZero n] :
  {st: FDState (Agent n) (Item m) // EF1 c.u st.A ∧ Feasible c st ∧ st.U = ∅ } :=
  -- let A0 : Allocation (Agent n) (Item m) := fun _ => ∅
  let st0 : FDState (Agent n) (Item m) := { A := fun _ => ∅, U := c.M }
  let U0 := c.M

  let rec loop
    (st : FDState (Agent n) (Item m))
    -- invariant: EF1 is preserved throughout the procedure
    (hEF1 : EF1 c.u st.A)
    -- invariant: feasibility is preserved throughout the procedure
    (HFeasible : Feasible c st)
    [NeZero n]
    : { st_final // EF1 c.u st_final.A ∧ Feasible c st_final ∧ st_final.U = ∅ } := by
    by_cases h_cycle : ∃ C : EnvyCycle c st, True
    -- case: there is an envy cycle, rotate along the cycle and continue
    · let C := h_cycle.choose
      let rotated_st := rotate_allocation c st C
      have hEF1_rotated : EF1 c.u rotated_st.A := by exact ef1_preserved_under_rotation c st C hEF1
      have hFeasible_rotated : Feasible c rotated_st :=
        by exact feasibility_preserved_under_rotation c st C HFeasible
      exact loop rotated_st hEF1_rotated hFeasible_rotated
    -- case: there is no envy cycle
    · have h_no_cycle : ∀ C : EnvyCycle c st, False := by
        intro C
        apply h_cycle
        exact ⟨C, trivial⟩
      by_cases h_nonempty : st.U.Nonempty
      · -- case: there is still item unallocated, find a source agent and
        -- give them an unallocated item, then continue
        let g := h_nonempty.choose
        let hg_in := h_nonempty.choose_spec
        -- find a source agent
        let source := (exists_source_of_no_cycle c st (by simpa using h_no_cycle)).choose
        have h_source_is_source :  ∀ j, ¬ Envies c.u st.A j source := by
          simpa using (exists_source_of_no_cycle c st (by simpa using h_no_cycle)).choose_spec
        have h_ef1_preserved_after_add :=
          ef1_preserved_under_add_item_to_agent c st source h_source_is_source g hEF1
        have h_feasibility_preserved_after_add := feasibility_preserved_under_add_item_to_agent c st source g hg_in HFeasible

        -- continue with the new allocation
        exact loop (add_item_to_agent st source g) h_ef1_preserved_after_add h_feasibility_preserved_after_add
      · -- case: U is empty, terminate
        have h_U_empty : st.U = ∅ := by
          exact Finset.not_nonempty_iff_eq_empty.mp h_nonempty
        exact ⟨st, ⟨hEF1, HFeasible, h_U_empty⟩⟩

  -- Termination of the envy cycle procedure
  termination_by potential c st
  decreasing_by
    · have hpot := potential_decreases_after_rotation c st C HFeasible
      exact hpot
    · have hpot := potential_decreases_after_add_item_to_agent c st HFeasible source g hg_in
      exact hpot

  -- the invariants hold for the initial state
  have h_EF1_initial : EF1 c.u st0.A := by
    -- EF1 for empty allocation
    unfold EF1 EF1ij Envies
    intros i j h_envy
    simp [st0] at h_envy

  have h_feasible_initial : Feasible c st0 := by
    constructor
    · simp [st0]
    · simp [st0]


  loop st0 h_EF1_initial h_feasible_initial

theorem envy_cycle_elimination
  (c : FDContext (Agent n) (Item m)) [NeZero n] :
   ∃ st : FDState (Agent n) (Item m),
   EF1 c.u st.A ∧ (Feasible c st) ∧ st.U = ∅ :=
by
  let result := envy_cycle_procedure c
  exact ⟨result.val, result.property⟩
