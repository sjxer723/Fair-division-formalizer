import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic


open Finset
open Function


/-
Basic setup:
- We fix a finite type `Item` of indivisible goods.
- There are exactly three agents: A, B, C.
- Each agent has an additive valuation over items (nonnegative reals per item).
-/


inductive Agent
| A | B | C


open Agent


variable {Item : Type} [DecidableEq Item] [Fintype Item]


namespace FairDivision


structure FDValuation (Item : Type) where
  val : Agent → Item → ℝ
  nonneg : ∀ a i, 0 ≤ val a i


/-- Additive extension of a valuation to finite bundles. -/
def val_on {Item : Type} [DecidableEq Item] (v : FDValuation Item)
(a : Agent) (s : Finset Item) : ℝ :=
s.sum (fun i => v.val a i)


/-- An allocation partitions the `items` set into three disjoint bundles, one per agent. -/
structure Allocation (items : Finset Item) where
alloc : Agent → Finset Item
pairwise_disjoint : ∀ (x y : Agent), x ≠ y → (alloc x ∩ alloc y) = ∅
cover : (alloc A ∪ alloc B ∪ alloc C) = items

/-- EFX: Envy-freeness up to any item.
For all agents i, j and for every item g in j's bundle,
agent i's valuation of his own bundle is at least his valuation
of j's bundle after removing g. -/
def efx {items : Finset Item} (v : FDValuation Item) (α : Allocation items) : Prop :=
∀ (i j : Agent) (g : Item), g ∈ α.alloc j →
val_on v i (α.alloc i) ≥ val_on v i ((α.alloc j).erase g)


-- /-- Strong envy (negation of EFX at a particular pair (i,j)). -/
def strongly_envies {items : Finset Item} (v : FDValuation Item)
  (α : Allocation items) (i j : Agent) : Prop :=
∃ g, g ∈ α.alloc j ∧ val_on v i (α.alloc i) < val_on v i ((α.alloc j).erase g)


-- /-
-- Statement of the main theorem (skeleton). The proof will follow the
-- constructive algorithm described in the paper: repeatedly perform
-- swaps of (half-)bundles and show a potential strictly increases until
-- an EFX allocation is reached.
-- -/
-- theorem efx_exists_three (items : Finset Item) (v : FDValuation) :
-- ∃ (α : Allocation items), efx v α := by
-- -- Proof outline (to be filled in with machine-checked lemmas):
-- -- 1. Start from an arbitrary complete allocation α₀.
-- -- 2. Define "upper" and "lower" halves of bundles (according to some agent-ordering) and a splitting procedure.
-- -- 3. Define a potential function Φ on allocations that (a) is well-founded (takes values in a well-founded set), and (b) strictly increases when we perform the swap operations described in the paper.
-- -- 4. Show that as long as α is not EFX, there exists a swap (of half-bundles) that increases Φ while preserving necessary invariants (e.g., no agent's valuation drops below a maintained lower bound for a chosen focal agent).
-- -- 5. Conclude by well-foundedness that the algorithm terminates at an allocation that must be EFX.
-- -- We leave the formalization of each step as a sequence of lemmas. Below we `admit` the required lemmas and finish the proof sketch by assembling them.
-- -- TODO: replace admits by actual proofs.
-- have : True := by trivial
-- admit


-- /-
-- Suggested lemmas to formalize (each should be implemented/proved):
-- - lemma: any finite allocation can be represented as an `Allocation items`.
-- - lemma: splitting a bundle into upper/lower halves w.r.t. an agent's marginal values preserves key inequalities.
-- - lemma: the swap operation (move upper or lower half from one agent to another) maintains pairwise disjointness and cover.
-- - lemma: definition of the potential Φ and proof that it is bounded above and increases with certain swaps.
-- - lemma: termination (well-foundedness) of the swap process.
-- - lemma: if no improving swap exists, then allocation is EFX.


-- Implementation tips:
-- - Use `Finset` and `Fintype` combinatorics for finite sums and unions.
-- - Represent agents as the `Agent` inductive type (A, B, C). This makes case analysis explicit and manageable.
-- - Many inequalities rely on additivity: `val_on v a (s.erase g) = val_on v a s - v.val a g`.
-- - Keep the chosen "focal" agent in the potential function explicit: one of the ideas in the paper is to keep one agent's valuation non-decreasing.


-- If you want, I can now:
-- - Fill in the definitions + proofs of the helper lemmas one-by-one (e.g., formalize splitting bundles), or
-- - Translate a particular section of the paper (e.g., Section 3: Splitting bundles) into Lean lemmas.
-- -/


-- #print efx


-- end FairDivision
