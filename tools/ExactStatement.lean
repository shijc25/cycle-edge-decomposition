import Cycle12.Coefficient12Complete

/-- Independently expose the intended edge-partition statement, including
the exact component count and the absence of any additional graph hypothesis. -/
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (k : ℕ)
    (parts : Fin k → Set (Sym2 (Fin n))),
    (∀ j, (∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ parts j = p.edgeSet) ∨
      ∃ e ∈ G.edgeSet, parts j = {e}) ∧
    Pairwise (fun j l => Disjoint (parts j) (parts l)) ∧
    (⋃ j, parts j) = G.edgeSet ∧
    Nat.le k (Nat.mul 12 (Nat.sub n (Nat.card G.ConnectedComponent))) := by
  intro n G
  obtain ⟨k, ⟨parts, hp, hd, hu⟩, hk⟩ := Cycle12.coefficient12 n G
  exact ⟨k, parts, hp, hd, hu, hk⟩

#print axioms Cycle12.coefficient12
#print Cycle13.CycleOrSingleEdge
#print Cycle13.EdgeDecomposition
#print Cycle13.componentCount
#check SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length

