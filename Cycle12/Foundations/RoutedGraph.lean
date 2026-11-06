import Cycle12.Foundations.RoutedEdges

/-! The underlying simple graph of a routed multigraph strongly immerses
in the original host. No choice can merge paths for different simple edges. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V W : Type} {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I)

def edge (i : I) : Sym2 V := s(R.left i,R.right i)

def graph : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ i, R.edge i=s(x,y)
  symm := ⟨by
    rintro x y ⟨hne,i,hi⟩
    exact ⟨hne.symm,i,hi.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def graphIndex {x y : V} (h : R.graph.Adj x y) : I := h.2.choose

lemma graphIndex_spec {x y : V} (h : R.graph.Adj x y) :
    R.edge (R.graphIndex h)=s(x,y) := h.2.choose_spec

def graphWalk {x y : V} (h : R.graph.Adj x y) : G.Walk (φ x) (φ y) := by
  by_cases hd : R.left (R.graphIndex h)=x ∧ R.right (R.graphIndex h)=y
  · exact (R.route (R.graphIndex h)).copy (congrArg φ hd.1) (congrArg φ hd.2)
  · have hr : R.left (R.graphIndex h)=y ∧ R.right (R.graphIndex h)=x :=
      (Sym2.eq_iff.mp (R.graphIndex_spec h)).resolve_left hd
    exact (R.route (R.graphIndex h)).reverse.copy (congrArg φ hr.2) (congrArg φ hr.1)

lemma graphWalk_edgeSet {x y : V} (h : R.graph.Adj x y) :
    (R.graphWalk h).edgeSet=(R.route (R.graphIndex h)).edgeSet := by
  unfold graphWalk
  split_ifs <;> simp

lemma graphWalk_support {x y : V} (h : R.graph.Adj x y) (w : W) :
    w ∈ (R.graphWalk h).support ↔ w ∈ (R.route (R.graphIndex h)).support := by
  unfold graphWalk
  split_ifs <;> simp

def graphRouting : EdgeRouting R.graph G where
  vertex := φ
  route := R.graphWalk
  disjoint := by
    intro x y a b hxy hab hne
    rw [graphWalk_edgeSet,graphWalk_edgeSet]
    apply R.disjoint
    intro hidx
    exact hne ((R.graphIndex_spec hxy).symm.trans
      ((congrArg R.edge hidx).trans (R.graphIndex_spec hab)))
  avoids := by
    intro x y hxy a ha
    have hh := R.avoids _ a ((R.graphWalk_support hxy (φ a)).mp ha)
    rcases Sym2.eq_iff.mp (R.graphIndex_spec hxy) with hd | hr
    · exact hh.imp (fun h => h.trans hd.1) (fun h => h.trans hd.2)
    · exact hh.symm.imp (fun h => h.trans hr.2) (fun h => h.trans hr.1)

theorem clique_lifts {t : ℕ} (M : StrongCliqueImmersion t R.graph) :
    Nonempty (StrongCliqueImmersion t G) := ⟨M.lift R.graphRouting⟩

end RoutedEdges
end
end Cycle13
