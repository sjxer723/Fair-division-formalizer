import Fairdivision.graph
import Fairdivision.source

open fairdivision

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
