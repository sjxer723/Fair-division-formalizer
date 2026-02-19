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
import Fairdivision.FinUtils
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


lemma ef1ij_insert_i_of_ef1ij {c : FDContext Agent Item} {i j : Agent}
  {A : Allocation Agent Item} {g : Item}
  (h_ef1ij : EF1ij c.u A i j) :
  EF1ij c.u (fun a => if a = i then insert g (A a) else A a) i j :=
by
  unfold EF1ij at *
  unfold Envies
  intro h_envies
  by_cases h_ij_eq: i = j
  · simp [h_ij_eq] at *
  · simp at *
    have hji : j ≠ i := by
      simpa [ne_comm] using h_ij_eq
    simp [hji] at h_envies
    simp [hji]
    have h_envies_before: Envies c.u A i j := by
      have : c.u i (A i) ≤ c.u i (insert g (A i)) := by
        apply c.mono_u
        simp
      simp [Envies]
      linarith
    have h_ef1_before: ∃ g' ∈ A j, c.u i (A i) ≥ c.u i (A j \ {g'}) := (h_ef1ij h_envies_before)
    rcases h_ef1_before with ⟨g', ⟨hg_mem', hg_ef1⟩⟩
    use g'
    constructor
    · exact hg_mem'
    · have : c.u i (A i) ≤ c.u i (insert g (A i)) := by
        apply c.mono_u
        simp
      linarith


lemma ef1ij_maintained_after_adding_item_to_j (c : FDContext Agent Item)
  (i j : Agent) (A : Allocation Agent Item) (g : Item) (h_ef1ij : ¬ Envies c.u A i j) :
  EF1ij c.u (fun a => if a = j then insert g (A a) else A a) i j := by
  unfold EF1ij at *
  intro h_envies
  use g
  simp
  by_cases h_ij_eq: i = j
  · simp [h_ij_eq] at *
    apply c.mono_u
    simp
  · have : i ≠ j := by omega
    simp [this]
    have h_nonenvies_before : c.u i (A i) ≥ c.u i (A j) := by
      simp [Envies] at h_ef1ij
      linarith
    have h_insert_erase : c.u i (insert g (A j) \ {g}) ≤ c.u i (A j) := by
      apply c.mono_u
      rw [Finset.sdiff_singleton_eq_erase]
      apply Finset.erase_insert_subset
    linarith

def social_welfare (c : FDContext Agent Item) (st : FDState Agent Item) : ℕ :=
  ∑ i, c.u i (st.A i)

@[simp]
lemma upper_bound_of_social_welfare
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_feasible : Feasible c st) :
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
    simpa [h_feasible.cover] using this
  have h_alloc_subset : st.A i ⊆ (Finset.univ.biUnion st.A) := by
    apply Finset.subset_biUnion_of_mem
    exact Finset.mem_univ i
  exact h_alloc_subset.trans h_union_subset_M

def potential (c : FDContext Agent Item) (st : FDState Agent Item) : ℕ :=
   ∑ i, c.u i c.M  - ∑ i, c.u i (st.A i) + st.U.card

@[simp]
lemma potential_nonnegative
  (c : FDContext Agent Item)
  (st : FDState Agent Item)
  (h_fea : Feasible c st) :
  potential c st ≥ 0 := by
  unfold potential
  have h_sum_le : ∑ i, c.u i (st.A i) ≤ ∑ i, c.u i c.M := by
    apply upper_bound_of_social_welfare c st h_fea
  linarith

@[simp]
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

@[simp]
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

lemma bundle_subset_allocated_items (st : FDState Agent Item) :
  ∀ i, st.A i ⊆ (Finset.univ.biUnion st.A) := by
  intro i
  apply Finset.subset_biUnion_of_mem
  exact Finset.mem_univ i

end fairdivision
