import Mathlib

/-! The exact graph-theoretic target. No main theorem is assumed here. -/
namespace Cycle13

universe u

/-- A part is the edge set of a simple cycle, or one edge of the original graph. -/
def CycleOrSingleEdge {V : Type u} (G : SimpleGraph V) (s : Set (Sym2 V)) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet) ∨
  ∃ e ∈ G.edgeSet, s = {e}

/-- Every original edge occurs in exactly one of the `k` admissible parts. -/
def EdgeDecomposition {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ parts : Fin k → Set (Sym2 V),
    (∀ i, CycleOrSingleEdge G (parts i)) ∧
    Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
    (⋃ i, parts i) = G.edgeSet

/-- Isolated vertices are connected components as well. -/
noncomputable def componentCount {V : Type u} (G : SimpleGraph V) : ℕ :=
  Nat.card G.ConnectedComponent

theorem componentCount_le_card {V : Type u} [Fintype V] (G : SimpleGraph V) :
    componentCount G ≤ Fintype.card V := by
  have hs : Function.Surjective G.connectedComponentMk := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩
  simpa [componentCount] using Nat.card_le_card_of_surjective G.connectedComponentMk hs

/-- Final acceptance target: an explicit coefficient, and no graph-theoretic hypotheses. -/
def Coefficient13Statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∃ k : ℕ, EdgeDecomposition G k ∧ k ≤ 13 * (n - componentCount G)

theorem part_subset {V : Type u} {G : SimpleGraph V} {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v, p, hp, rfl⟩ | ⟨e, he, rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

theorem edgeless_decomposition {V : Type u} :
    EdgeDecomposition (⊥ : SimpleGraph V) 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · simp

end Cycle13
