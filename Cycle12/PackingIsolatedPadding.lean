import Cycle12.StarComponents
import Cycle12.TerminalRelabeling

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem walk_support_of_incident_support (G : SimpleGraph V) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S)
    {u v : V} (p : G.Walk u v) (hu : u∈S) : ∀ x∈p.support, x∈S := by
  induction p with
  | nil =>
    intro x hx
    have he := List.mem_singleton.mp hx
    exact he ▸ hu
  | @cons a b c hab p ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact ih (hS a b hab).2 x hx

theorem cycle_support_of_incident_support (G : SimpleGraph V) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) : ∀ x∈p.support, x∈S := by
  have hu : u∈S := by
    cases p with
    | nil => exact False.elim (hp.not_nil (by simp))
    | cons h p => exact (hS _ _ h).1
  exact walk_support_of_incident_support G S hS p hu

/-- Every cycle in a graph supported on S restricts to an actual cycle
in the induced graph, with its exact edge set pulled back. -/
theorem cycle_induce_of_incident_support (G : SimpleGraph V) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∃ a : S, ∃ q : (G.induce S).Walk a a, q.IsCycle ∧
      q.edgeSet=(Sym2.map (Subtype.val : S → V)) ⁻¹' p.edgeSet := by
  have hs := cycle_support_of_incident_support G S hS p hp
  let q := p.induce S hs
  have hq : q.IsCycle := Walk.IsCycle.of_map
    (f:=(SimpleGraph.Embedding.induce (G:=G) S).toHom)
    (by simpa [q] using hp)
  refine ⟨⟨u,hs u p.start_mem_support⟩,q,hq,?_⟩
  have he : Sym2.map (Subtype.val : S → V) '' q.edgeSet=p.edgeSet := by
    have hh := congrArg Walk.edgeSet (p.map_induce hs)
    rw [Walk.edgeSet_map] at hh
    exact hh
  rw [←he,Set.preimage_image_eq _ (Sym2.map.injective Subtype.val_injective)]

/-- Isolated padding does not create a new forbidden cycle. -/
theorem noLongCycle_of_incident_support (G : SimpleGraph V) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) {T : ℕ}
    (hshort : Cycle13.NoCycleAtLeast (G.induce S) T) : Cycle13.NoCycleAtLeast G T := by
  intro u p hp
  have hs := cycle_support_of_incident_support G S hS p hp
  have hq : (p.induce S hs).IsCycle := Walk.IsCycle.of_map
    (f:=(SimpleGraph.Embedding.induce (G:=G) S).toHom)
    (by simpa using hp)
  have hh := hshort _ (p.induce S hs) hq
  have hlen := congrArg Walk.length (p.map_induce hs)
  rw [Walk.length_map] at hlen
  rwa [hlen] at hh

/-- Deleting isolated vertices preserves the exact edge count. -/
theorem edge_ncard_induce_of_incident_support (G : SimpleGraph V) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) :
    (G.induce S).edgeSet.ncard=G.edgeSet.ncard := by
  have hs : G.support ⊆ S := by
    rintro x ⟨y,hxy⟩
    exact (hS x y hxy).1
  simpa only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using
    (SimpleGraph.card_edgeFinset_induce_of_support_subset hs)

end
end Cycle12

namespace Cycle13.CyclePacking
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Restrict an actual packing across isolated padding. Each part is the
edge set of an actual induced cycle, not just an abstract edge subset. -/
def restrictSupported (P : CyclePacking G) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) : CyclePacking (G.induce S) where
  count := P.count
  parts i := Sym2.map (Subtype.val : S → V) ⁻¹' P.parts i
  cycles i := by
    obtain ⟨u,p,hp,he⟩ := P.cycles i
    obtain ⟨v,q,hq,hqe⟩ := Cycle12.cycle_induce_of_incident_support G S hS p hp
    exact ⟨v,q,hq,by rw [he,hqe]⟩
  disjoint := by
    intro i j hij
    exact (P.disjoint hij).preimage _

theorem used_restrictSupported (P : CyclePacking G) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) :
    (P.restrictSupported S hS).used=Sym2.map (Subtype.val : S → V) ⁻¹' P.used := by
  simp only [restrictSupported,used,Set.preimage_iUnion]

theorem residue_restrictSupported (P : CyclePacking G) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) :
    (P.restrictSupported S hS).residue=P.residue.induce S := by
  ext u v
  simp only [residue,deleteEdges_adj,induce_adj,used_restrictSupported,
    Set.mem_preimage,Sym2.map_mk]

theorem singles_restrictSupported (P : CyclePacking G) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) :
    (P.restrictSupported S hS).singles=P.singles := by
  unfold singles
  rw [residue_restrictSupported]
  exact Cycle12.edge_ncard_induce_of_incident_support P.residue S
    (fun x y hxy => hS x y (P.residue_le hxy))

/-- Isolated padding changes neither cycle count nor uncovered-edge cost. -/
theorem cost_restrictSupported (P : CyclePacking G) (S : Set V)
    (hS : ∀ x y, G.Adj x y → x∈S ∧ y∈S) :
    (P.restrictSupported S hS).cost=P.cost := by
  unfold cost
  rw [singles_restrictSupported]
  rfl

end
end Cycle13.CyclePacking
