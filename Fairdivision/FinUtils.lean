import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


variable {α : Type _} [DecidableEq α]

@[simp]
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

@[simp]
lemma fin_add_one_sub_one
  {n : Nat} (idx : Fin n) (h : 1 < n) :
  idx + ⟨1, h⟩ + ⟨n - 1, (by omega)⟩ = idx := by
  -- reduce equality of `Fin` to equality of the `.val` (nat) components
  ext
  simp only [Fin.val_add]
  simp
  rw [add_assoc]
  have h_fold: 1 + (n - 1) = n := by omega
  rw [h_fold]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt idx.is_lt]

@[simp]
lemma fin_sub_one_add_one {n : Nat} (i : Fin n) (h : 1 < n) :
  i + ⟨n - 1, (by omega)⟩ + ⟨1, h⟩  = i := by
  -- reduce equality of `Fin` to equality of the `.val` (nat) components
  ext
  simp only [Fin.val_add]
  simp
  rw [add_assoc]
  have h_fold: (n - 1 + 1) = n := by omega
  rw [h_fold]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt i.is_lt]

@[simp]
lemma fin_i_lt_n_add_one {n i : Nat} (h : 1 < n) (hi : i < n - 1) :
  (⟨i, by omega⟩ : Fin n) + ⟨1, h⟩ = (⟨i + 1, by omega⟩ : Fin n) := by
  ext
  simp only [Fin.val_add]
  have h_fold: (i + 1) = i + 1 := by omega
  have hi' : i + 1 < n := by omega
  rw [h_fold]
  rw [Nat.mod_eq_of_lt hi']


@[simp]
lemma fin_n_minus_one_add_one {n : Nat} (h : 1 < n) :
  (⟨n - 1, by omega⟩ : Fin n) + ⟨1, h⟩ = (⟨0, by omega⟩ : Fin n) := by
  ext
  simp only [Fin.val_add]
  have h_fold: (n - 1 + 1) = n := by omega
  have hn0 : n ≠ 0 := by omega
  rw [h_fold]
  simp [Nat.mod_self]

@[simp]
lemma insert_union_erase_eq_union_of_mem {α} [DecidableEq α] {g : α} {t s : Finset α} (h : g ∈ s) :
  insert g t ∪ s.erase g = t ∪ s :=
by
  have h1 := Finset.insert_erase h
  calc
    insert g t ∪ s.erase g
        = insert g (t ∪ s.erase g) := by
            simp [Finset.insert_union]
    _   = t ∪ insert g (s.erase g) := by
            simp [Finset.union_insert]
    _   = t ∪ s := by
            simp [h1]

@[simp]
lemma insert_union_erase_eq_union_of_mem' {α} [DecidableEq α] {g : α} {t s : Finset α} (h : g ∈ s) :
  insert g (t ∪ s.erase g) = t ∪ s :=
by
  rw [← insert_union_erase_eq_union_of_mem h]
  simp

@[simp]
lemma disjoint_erase_of_disjoint {α} [DecidableEq α] {g : α} {t s : Finset α}
  (h : Disjoint t s) : Disjoint t (s.erase g) :=
by
  apply Finset.disjoint_left.2
  intro x hx_union hx_erase

  have h_x_in_U : x ∈ s := by
    rcases Finset.mem_erase.mp hx_erase with ⟨hne, hxU⟩
    exact hxU

  rw [disjoint_iff] at h
  simp at h
  have h_x_in_intersection : x ∈ t ∩ s := by
    exact Finset.mem_inter.mpr ⟨hx_union, h_x_in_U⟩
  rw [h] at h_x_in_intersection
  simp_all


variable [DecidableEq β] {s : Finset α} {t : Finset β}

@[simp]
lemma biUnion_emptymap
  {α β} [DecidableEq β] (s : Finset α) :
  Finset.biUnion s (fun _ : α => (∅ : Finset β)) = (∅ : Finset β) := by
  ext x; simp [Finset.biUnion]

@[simp]
lemma univ_biUnion_inner_insert
  {α β} [Fintype α] [DecidableEq α] [DecidableEq β]
  (f : α → Finset β) (source : α) (g : β) :
  Finset.univ.biUnion (fun i => if i = source then insert g (f i) else f i)
    = Finset.univ.biUnion f ∪ {g} :=
by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hxAi⟩
    by_cases h : i = source
    · subst h
      simp at hxAi
      rcases hxAi with hx_eq | hxA
      · rw [hx_eq]; simp
      · have : f i ⊆ Finset.univ.biUnion f :=
          Finset.subset_biUnion_of_mem f (Finset.mem_univ i)
        apply Finset.mem_union.mpr
        left
        exact this hxA
    · -- i ≠ source
      simp [h] at hxAi; simp
      right; use i

  · intro hx
    rcases Finset.mem_union.mp hx with hxA | hxg
    · -- old biUnion
      rcases Finset.mem_biUnion.mp hxA with ⟨i, _, hxA⟩
      by_cases h : i = source
      · subst h; simp
        use i; simp
        right
        exact hxA
      · simp; use i
        simp [h]
        exact hxA
    · simp
      use source
      simp
      left
      simp at hxg
      omega
