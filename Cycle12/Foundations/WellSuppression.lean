import Cycle12.Foundations.ClonePortMatching

/-! A perfect matching in the actual clone complement produces a full
well-suppression, with simple external graph, unchanged crossing multiplicities,
unchanged retained degrees and actual edge-disjoint host routes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)

def externalGraph (X : Set {v : V // v≠z}) : SimpleGraph X :=
  (R.graph.comap (Subtype.val : {v : V // v≠z} → V)).comap (Subtype.val : X → _)

theorem well_suppression_of_clone_perfect (S X : Set {v : V // v≠z})
    (hXS : X⊆S) (hports : ∀ i, R.portTip z i∈S → R.portTip z i∈X)
    (hpos : ∀ x : X, 0<R.multiplicity z x.val.val)
    (hmax : ∀ x : X, R.multiplicity z x.val.val≤2)
    (heven : Even (R.degree z)) (hold : R.SimpleOn (Subtype.val '' S))
    (hperfect : ∃ M : (cloneGraph (R.externalGraph z X) (R.doubleExternal z X))ᶜ.Subgraph,
      M.IsMatching ∧ M.verts=Set.univ) :
    ∃ N : (⊤ : SimpleGraph (R.Ports z)).Subgraph, ∃ hN : N.IsMatching,
      N.verts=Set.univ ∧ (R.suppress z N hN).SimpleOn S ∧
      (∀ x y, x∈S → y∉S → (R.suppress z N hN).multiplicity x y=R.multiplicity x.val y.val) ∧
      (∀ v, (R.suppress z N hN).degree v=R.degree v.val) := by
  obtain ⟨E,hE,hErange⟩ := R.exists_clone_port_embedding z X hpos hmax
  obtain ⟨M,hM,hMcover⟩ := hperfect
  let H := R.graph.comap (Subtype.val : {v : V // v≠z} → V)
  let v : X ↪ {v : V // v≠z} := Function.Embedding.subtype X
  let D := R.doubleExternal z X
  let P := ClonePortMatching.ported H v D E M
  have hP : P.IsMatching := ClonePortMatching.ported_matching H v D E M hM
  have hPc : ∀ i, R.portTip z i∈S → i∈P.verts := by
    intro i hi
    exact ClonePortMatching.ported_covered H v D E M hMcover (hErange i (hports i hi))
  have hPe : ∀ i j, P.Adj i j → R.portTip z i∈S ∧ R.portTip z j∈S := by
    intro i j hij
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := ClonePortMatching.ported_ends H v D E (R.portTip z) hE M hij
    exact ⟨hXS (ha ▸ a.property),hXS (hb ▸ b.property)⟩
  have hPl : ∀ i j, P.Adj i j → R.portTip z i≠R.portTip z j := by
    intro i j hij
    exact ClonePortMatching.ported_no_loop H v D E (R.portTip z) hE M hij
  have hPi : Set.InjOn (Sym2.map (R.portTip z)) P.edgeSet :=
    ClonePortMatching.ported_output_injective H v D E (R.portTip z) hE M hM
  have hPa : ∀ i j, P.Adj i j →
      R.multiplicity (R.portTip z i).val (R.portTip z j).val=0 := by
    intro i j hij
    have hn := ClonePortMatching.ported_not_adj H v D E (R.portTip z) hE M hij
    have hne : (R.portTip z i).val≠(R.portTip z j).val := fun h => hPl i j hij (Subtype.ext h)
    change ¬R.graph.Adj (R.portTip z i).val (R.portTip z j).val at hn
    rw [graph_adj_iff_multiplicity] at hn
    have hz : ¬0<R.multiplicity (R.portTip z i).val (R.portTip z j).val :=
      fun h => hn ⟨hne,h⟩
    omega
  obtain ⟨N,hN,hNc,_,hNs,hcross,hdeg⟩ :=
    R.exists_controlled_suppression z S P hP heven hPc hPe hold hPl hPi hPa
  exact ⟨N,hN,hNc,hNs,hcross,hdeg⟩

end RoutedEdges
end
end Cycle13
