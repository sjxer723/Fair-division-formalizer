import Fairdivision.Basic
import Fairdivision.FinUtils

open fairdivision

variable {Agent Item : Type}
variable [Fintype Agent] [Inhabited Agent] [DecidableEq Agent]

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
  simp [h_find_idx]
  simp [h_i_lt_len]
  congr
  simp_all

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
