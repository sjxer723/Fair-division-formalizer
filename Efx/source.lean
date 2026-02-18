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

lemma exists_cycle_of_finite {V : Type} [Fintype V] [Inhabited V] [DecidableEq V] (f : V → V) :
  ∃ v k, k > 0 ∧ (f^[k]) v = v :=
by
  let n := Fintype.card V
  let v0 := (Fintype.elems : Finset V).toList.headI
  -- 1. construct g : Fin (n + 1) → V, g(i) = f^i(v0)
  let g : Fin (n + 1) → V := fun i => (f^[i]) v0

  -- 2. use pigeonhole principle to find i < j with f^i(v0) = f^j(v0)
  have h_card : Fintype.card (Fin (n + 1)) > Fintype.card V := by simp [n]
  have h_mapsto: Set.MapsTo g (Finset.univ : Finset (Fin (n + 1))) (Finset.univ : Finset V) :=
    by
    intros x hx
    simp
  -- have h_mapsto : Finset
  obtain ⟨i, hiS, j, hjS, h_ne, h_eq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card h_mapsto
  -- 3. construct the cycle starting from f^i(v0) with length j - i
  by_cases hi : i ≤ j
  · use (f^[i]) v0, (j - i)
    constructor
    · omega
    · -- prove (f^[j-i]) (f^[i] v0) = f^[i] v0
      -- use f^a ∘ f^b = f^(a+b)
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi]
      simp [g] at h_eq
      rw [h_eq]
  · use (f^[j]) v0, (i - j)
    constructor
    · omega
    · -- prove (f^[i-j]) (f^[j] v0) = f^[j] v0
      -- use f^a ∘ f^b = f^(a+b)
      have h_ge: i ≥ j := Nat.le_of_not_le (by omega)
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h_ge]
      simp [g] at h_eq
      rw [h_eq]

lemma exist_min_cycle_of_finite {V : Type} [Fintype V] [Inhabited V] [DecidableEq V]
  (f : V → V) :
  ∃ v k, k > 0 ∧ (f^[k]) v = v ∧ (∀ m v', (m < k ∧ (f^[m]) v' = v') → m = 0):= by
classical

  -- Step 1: define the predicate on k
  let P : ℕ → Prop :=
    fun k => ∃ v, k > 0 ∧ (f^[k]) v = v

  -- Step 2: show it is nonempty
  have h_nonempty : ∃ k, P k := by
    rcases exists_cycle_of_finite f with ⟨v, k, hkpos, hfix⟩
    exact ⟨k, ⟨v, hkpos, hfix⟩⟩

  -- Step 3: take the minimal such k
  let k := Nat.find h_nonempty
  have hk : P k := Nat.find_spec h_nonempty

  -- extract the witness v
  rcases hk with ⟨v, hkpos, hfix⟩

  -- Step 4: prove minimality
  have hmin :
    ∀ m, m < k → ¬ P m :=
    fun m hm => Nat.find_min h_nonempty hm

  -- Step 5: conclude
  refine ⟨v, k, hkpos, hfix, ?_⟩
  intro m v' hm

  by_cases hm_zero : m = 0
  · exact hm_zero
  · have hm_pos : m > 0 := Nat.pos_of_ne_zero hm_zero
    have h_contra : P m := by
      exact ⟨v', hm_pos, hm.2⟩
    exact (hmin m hm.left h_contra).elim


omit [DecidableEq Item] in
lemma exists_source_of_no_cycle
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_no_cycle : ∀ C : EnvyCycle c st, False) :
  ∃ i : Agent, ∀ j : Agent, ¬ Envies c.u st.A j i := by
/-
    Step 1: If there is no source, then every agent is envied by someone.
    We will show this leads to an infinite chain, which implies a cycle in a finite set.
  -/
  by_contra h_exists
  push_neg at h_exists
  -- h_exists : ∀ i, ∃ j, Envies u A j i (Every agent has an in-neighbor)

  /-
    Step 2: Construct a sequence of agents where f (n+1) envies f n.
    In Mathlib, we use 'fintype' and 'relation' tools or 'exists_seq_strict_mono' logic.
  -/
  choose f hf using h_exists

  /-
    Step 3: In a finite type, a sequence defined by f(n+1) = next(f n)
    must eventually repeat an element.
  -/
  obtain ⟨x, h_repeat⟩ := exist_min_cycle_of_finite f
  let k := h_repeat.choose
  let h_k_pos := h_repeat.choose_spec.1
  let h_fkx_eq_x := h_repeat.choose_spec.2.1
  let h_minimal := h_repeat.choose_spec.2.2


  /-
    Step 4: Construct the list in the correct order.
    The sequence is x₀, x₁, ..., xₖ₋₁ where xᵢ₊₁ envies xᵢ.
    To satisfy (f i) envies (f i + 1), we must reverse the indices.
  -/
  let x_seq (i : ℕ) : Agent := f^[i] x
  let cycle_agents := (List.range k).reverse.map x_seq

  have h_ne : cycle_agents ≠ [] := by
    simp [cycle_agents]
    omega

  have h_len : cycle_agents.length = k := by
    simp [cycle_agents]

/-
    Step 5: Prove the Chain property.
    In the reversed list, the element at index i is f^{k-1-i}(x).
    The next element is f^{k-2-i}(x).
    By definition of f, f(f^{k-2-i} x) envies f^{k-2-i} x, which is exactly
    f^{k-1-i} x envies f^{k-2-i} x.
  -/
  have h_chain : ∀ i (hi : i < cycle_agents.length - 1),
    Envies c.u st.A (cycle_agents.get ⟨i, by omega⟩) (cycle_agents.get ⟨i + 1, by omega⟩) := by
    intro i hi
    simp [cycle_agents]
    unfold x_seq
    -- simp
    set n := k - 1 - (i + 1) with hn
    have h_succ : k - 1 - i = n + 1 := by
      omega -- Handles the Nat subtraction perfectly
    rw [h_succ]
    rw [Function.iterate_succ_apply']
    apply hf

  have h_head : cycle_agents.head h_ne = x_seq (k - 1) := by
    simp [cycle_agents, List.head_reverse]
    -- You may need to handle the k > 0 case explicitly if types differ


  have h_til : cycle_agents.getLast h_ne = x_seq 0 := by
    simp [cycle_agents, List.getLast_reverse]

  have h_last : Envies c.u st.A (cycle_agents[cycle_agents.length - 1]) (cycle_agents[0]) := by
    have h_fixed_point : x_seq k = x_seq 0 := by
      simp [x_seq]
      exact h_fkx_eq_x
    simp [cycle_agents]
    rw [← h_fixed_point]
    unfold x_seq
    have h_fold : k = 1 + (k - 1) := by omega
    rw [h_fold]
    rw [Function.iterate_add_apply]
    simp
    apply (hf (f^[k - 1] x))

  have h_length_gt_one: cycle_agents.length > 1 := by
    rw [h_len]
    by_contra h_le_one
    have h_eq : k = 1 := by omega
    rw [h_eq] at h_len
    have cycle_agents_eq : cycle_agents = [x_seq 0] := by
      simp [cycle_agents, h_eq]
    simp [cycle_agents_eq] at h_last
    unfold Envies at h_last
    omega


  have h_nodup : cycle_agents.Nodup := by
    have h_range_nodup : (List.range k).reverse.Nodup := by
      simp [List.nodup_reverse, List.nodup_range]
    unfold cycle_agents x_seq

    rw [List.nodup_map_iff_inj_on h_range_nodup]
    intros i hi j hj hf_ij
    have h_i : i < k := by
      exact List.mem_range.mp (List.mem_reverse.mp hi)
    have h_j : j < k := by
      exact List.mem_range.mp (List.mem_reverse.mp hj)

    -- Case analysis on i and j
    by_cases hlt : i < j
    case pos =>
      have h_cancel: j - i + i = j := by omega
      have h_contra1: f^[j - i] (f^[i] x) = f^[i] x := by
        -- j - i + i = j, so f^[j - i + i] x = f^[j] x
        rw [← Function.iterate_add_apply, hf_ij]
        rw [h_cancel]
      have h_eq: j - i = 0 := by
        apply (h_minimal (j-i) (f^[i] x))
        constructor
        · omega
        · exact h_contra1
      omega
    case neg =>
      have h_cancel: i - j + j = i := by omega
      have h_contra1: f^[i - j] (f^[j] x) = f^[j] x := by
        -- i - j + j = i, so f^[i - j + j] x = f^[i] x
        rw [← Function.iterate_add_apply, ← hf_ij]
        rw [h_cancel]
      have h_eq: i - j = 0 := by
        apply (h_minimal (i-j) (f^[j] x))
        constructor
        · omega
        · exact h_contra1
      omega

  -- Step 6: Construct the EnvyCycle structure and derive a contradiction
  have cycle : EnvyCycle c st := ⟨cycle_agents, h_nodup, h_ne, h_length_gt_one, h_chain, h_last⟩

  exact h_no_cycle cycle


def add_item_to_agent
  (c : FDContext Agent Item)
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
  Feasible c (add_item_to_agent c st source g) := by
  have h_disjoint : Disjoint (Finset.univ.biUnion st.A) st.U := h_feasible.disjoint
  have h_disjoint_i : ∀ i, Disjoint (st.A i) st.U := by
    intro i
    apply Finset.disjoint_left.2
    intro x hx_union hx_erase
    have hx_union' : x ∈ Finset.univ.biUnion st.A :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx_union⟩
    have hx_inter : x ∈ Finset.univ.biUnion st.A ∩ st.U := by
      exact Finset.mem_inter.mpr ⟨hx_union', hx_erase⟩
    have := h_disjoint.le_bot hx_inter
    simp at this
  have h_intersect_false : ∀ i x, x ∈ st.A i → x ∈ st.U → False := by
    intro i x hx_A hx_U
    have h_inter : x ∈ st.A i ∩ st.U := by
      exact Finset.mem_inter.mpr ⟨hx_A, hx_U⟩
    have := h_disjoint_i i
    -- simp at this
    have h_bot : st.A i ∩ st.U = ∅ := this.eq_bot
    simp [h_bot] at h_inter

  constructor
  · -- Show that the new allocation's items are disjoint from U
    simp [add_item_to_agent]
    apply Finset.disjoint_left.2
    intro x hx_union hx_erase

    have h_x_in_U : x ∈ st.U := by
      rcases Finset.mem_erase.mp hx_erase with ⟨hne, hxU⟩
      exact hxU

    rcases Finset.mem_biUnion.1 hx_union with ⟨i, ⟨h_i, h_mem_i⟩⟩
    by_cases hcase : i = source
    · simp [hcase] at h_mem_i
      rcases h_mem_i with hx_eq | hx_A
      · rw [hx_eq] at hx_erase
        exact (Finset.notMem_erase g st.U) hx_erase
      · exact h_intersect_false source x hx_A h_x_in_U
    · simp [hcase] at h_mem_i
      exact h_intersect_false i x h_mem_i h_x_in_U
  · -- Show that the union of the new allocation's items and U is equal to Items
    simp [add_item_to_agent]
    have h_cover : Finset.univ.biUnion st.A ∪ st.U = c.M := h_feasible.cover
    have h_allocation_change : Finset.univ.biUnion (add_item_to_agent c st source g).A =
      Finset.univ.biUnion st.A ∪ {g} := by
      simp [add_item_to_agent]
      rw [biUnion_update_add_g st.A source g]
      simp
    simp [add_item_to_agent] at h_allocation_change
    rw [h_allocation_change, ← h_cover]
    exact insert_union_erase_of_mem h_g_in_U


lemma utility_nondecreasing_after_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (source i : Agent)
  (g : Item) :
  let st1 := add_item_to_agent c st source g;
  c.u i (st.A i) ≤ c.u i (st1.A i) := by
  intro st1
  unfold st1
  by_cases h_source : i = source
  · rw [h_source]
    simp [add_item_to_agent]
    apply c.mono_u
    simp
  · apply c.mono_u
    simp [add_item_to_agent]
    simp [h_source]

lemma potential_decreases_after_add_item_to_agent
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_feasible : Feasible c st)
  (source : Agent)
  (g : Item)
  (h_g_in_U : g ∈ st.U) :
  let st1 := add_item_to_agent c st source g;
  potential c st1 < potential c st := by
  intro st1
  unfold st1

  have h_unalocated_decreases : st1.U.card < st.U.card := by
    unfold st1
    simp [add_item_to_agent]
    have :(st.U.erase g).card < st.U.card :=
      Finset.card_erase_lt_of_mem h_g_in_U
    simp
    exact this

  have h_social_welfare_nondecreasing :
    social_welfare c (add_item_to_agent c st source g) ≥ social_welfare c st :=
    by
    unfold social_welfare
    apply Finset.sum_le_sum
    intro i hi
    apply utility_nondecreasing_after_add_item_to_agent c st source i g

  have h_feasible1 : Feasible c st1 := by
    apply feasibility_preserved_under_add_item_to_agent c st source g h_g_in_U h_feasible

  exact (
    potential_lt_implied_by_unallocated_size_lt c st1 st h_feasible1 h_feasible
      h_social_welfare_nondecreasing h_unalocated_decreases
  )
