import Cycle12.Foundations.RoutedGraph
import Cycle12.Foundations.GraphJanson

/-! Initial routed states and exact degree recovery whenever the indexed
multigraph is simple. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma out_pair_eq {V : Type} (e : Sym2 V) : s(e.out.1,e.out.2)=e := e.out_eq

namespace RoutedEdges
variable {I V W : Type} {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I)

def IsSimple : Prop := (∀ i, R.left i≠R.right i) ∧ Function.Injective R.edge

def edgeEquiv (hs : R.IsSimple) : I ≃ R.graph.edgeSet := Equiv.ofBijective
    (fun i => ⟨R.edge i,hs.1 i,i,rfl⟩) (by
  constructor
  · intro i j h
    exact hs.2 (congrArg Subtype.val h)
  · rintro ⟨⟨x,y⟩,hne,i,hi⟩
    exact ⟨i,Subtype.ext hi⟩)

theorem degree_eq_graph [Fintype I] [Fintype V] [DecidableEq V] (hs : R.IsSimple) (v : V) :
    R.degree v=R.graph.degree v := by
  have hp : ∀ i : I,
      ((if R.left i=v then (1:ℕ) else 0)+(if R.right i=v then 1 else 0))=
      (if v ∈ R.edge i then 1 else 0) := by
    intro i
    have hi := hs.1 i
    by_cases hl : R.left i=v <;> by_cases hr : R.right i=v <;>
      simp_all [edge,Sym2.mem_iff,eq_comm]
  unfold degree
  rw [sum_congr rfl (fun i _ => hp i)]
  calc
    _ = ∑ e : R.graph.edgeSet, if v ∈ e.val then (1:ℕ) else 0 :=
      Fintype.sum_equiv (R.edgeEquiv hs) _ _ (fun _ => rfl)
    _ = _ := by rw [sum_boole]; exact incident_edges_card R.graph v

end RoutedEdges

namespace RoutedEdges
variable {V : Type} (G : SimpleGraph V)

def original : RoutedEdges G (Function.Embedding.refl V) G.edgeSet where
  left e := e.val.out.1
  right e := e.val.out.2
  route e := (edge_out_adj G e).toWalk
  disjoint := by
    intro e f hne
    change Disjoint ((edge_out_adj G e).toWalk).edgeSet ((edge_out_adj G f).toWalk).edgeSet
    have he : ((edge_out_adj G e).toWalk).edgeSet={e.val} := by
      simp only [Adj.toWalk,Walk.edgeSet_cons,Walk.edgeSet_nil]
      rw [out_pair_eq]
      simp
    have hf : ((edge_out_adj G f).toWalk).edgeSet={f.val} := by
      simp only [Adj.toWalk,Walk.edgeSet_cons,Walk.edgeSet_nil]
      rw [out_pair_eq]
      simp
    rw [he,hf]
    exact Set.disjoint_singleton.mpr (Subtype.val_injective.ne hne)
  avoids := by
    intro e v hv
    change v ∈ ((edge_out_adj G e).toWalk).support at hv
    simpa only [Adj.toWalk,Walk.support_cons,Walk.support_nil,List.mem_cons,
      List.mem_singleton,List.not_mem_nil,or_false] using hv

theorem original_simple : (original G).IsSimple := by
  refine ⟨fun i => (edge_out_adj G i).ne,?_⟩
  intro i j h
  change s(i.val.out.1,i.val.out.2)=s(j.val.out.1,j.val.out.2) at h
  rw [out_pair_eq,out_pair_eq] at h
  exact Subtype.ext h

theorem original_graph : (original G).graph=G := by
  ext x y
  change (x≠y ∧ ∃ i : G.edgeSet, s(i.val.out.1,i.val.out.2)=s(x,y)) ↔ G.Adj x y
  constructor
  · rintro ⟨_,i,hi⟩
    rw [out_pair_eq] at hi
    change s(x,y) ∈ G.edgeSet
    exact hi ▸ i.property
  · intro h
    exact ⟨h.ne,⟨s(x,y),h⟩,s(x,y).out_eq⟩

theorem original_degree [Fintype V] [DecidableEq V] (v : V) :
    (original G).degree v=G.degree v := by
  rw [degree_eq_graph _ (original_simple G),original_graph]

end RoutedEdges
end
end Cycle13
