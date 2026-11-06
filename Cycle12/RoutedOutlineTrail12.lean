import Cycle12.RoutedOutlineLength12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem outline_rep_edge_map (c : CycleOutline G) (d : c.Q.Dart)
    (hd : d∈c.cycle.darts) : Sym2.map c.project (c.rep d).edge=d.edge := by
  change s(c.project (c.rep d).fst,c.project (c.rep d).snd)=s(d.fst,d.snd)
  rw [←(c.ports d hd).1,←(c.ports d hd).2,
    (c.projects d.fst (c.fst_mem hd)).2,(c.projects d.snd (c.snd_mem hd)).1]

theorem outline_rep_edge_injective (c : CycleOutline G) :
    Set.InjOn (fun d => (c.rep d).edge) {d | d∈c.cycle.darts} := by
  intro d hd e he hde
  apply List.inj_on_of_nodup_map c.isCycle.isTrail.edges_nodup hd he
  have hh := congrArg (Sym2.map c.project) hde
  simpa only [outline_rep_edge_map c d hd,outline_rep_edge_map c e he] using hh

theorem outline_edges_card (c : CycleOutline G) : c.edges.ncard=c.cycle.length := by
  have he : c.edges=↑(c.cycle.darts.toFinset.image (fun d => (c.rep d).edge)) := by
    ext e
    simp only [CycleOutline.edges,Set.mem_ofPred_eq,Finset.mem_coe,mem_image,List.mem_toFinset]
    exact ⟨fun ⟨d,hd,hde⟩ => ⟨d,hd,hde.symm⟩,fun ⟨d,hd,hde⟩ => ⟨d,hd,hde.symm⟩⟩
  rw [he,Set.ncard_coe_finset,Finset.card_image_of_injOn]
  · rw [List.toFinset_card_of_nodup (List.Nodup.of_map Dart.edge c.isCycle.isTrail.edges_nodup),Walk.length_darts]
  · intro d hd e he hde
    exact outline_rep_edge_injective c (List.mem_toFinset.mp hd) (List.mem_toFinset.mp he) hde

theorem disjoint_route_union_card {I : Type} [Fintype I]
    {x y : I → V} (route : ∀ i,G.Walk (x i) (y i))
    (hp : ∀ i,(route i).IsTrail)
    (hd : Pairwise (fun i j => Disjoint (route i).edgeSet (route j).edgeSet)) :
    (⋃ i,(route i).edgeSet).ncard=∑ i,(route i).length := by
  have he : (⋃ i,(route i).edgeSet)=↑(univ.biUnion (fun i => (route i).edges.toFinset)) := by
    ext e
    simp only [Set.mem_iUnion,Finset.mem_coe,mem_biUnion,mem_univ,true_and,
      List.mem_toFinset,Walk.mem_edgeSet]
  rw [he,Set.ncard_coe_finset,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [List.toFinset_card_of_nodup (hp i).edges_nodup,Walk.length_edges]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij) (List.mem_toFinset.mp hei) (List.mem_toFinset.mp hej)

theorem trail_of_edgeSet_card {u v : V} (p : G.Walk u v)
    (hc : p.edgeSet.ncard=p.length) : p.IsTrail := by
  have hh : p.edges.toFinset.card=p.edges.length := by
    rw [←Set.ncard_coe_finset,p.coe_edges_toFinset,hc,Walk.length_edges]
  exact ⟨(Multiset.toFinset_card_eq_card_iff_nodup (m:=(p.edges:Multiset (Sym2 V)))).mp hh⟩

/-- All edges of the routed outline occur once, even when routes meet
ordinary vertices of the outline. -/
theorem outlineClosedWalk_isTrail (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hp : ∀ z,(route z).IsPath)
    (hd : Pairwise (fun z w => Disjoint (route z).edgeSet (route w).edgeSet))
    (ho : ∀ z,Disjoint c.edges (route z).edgeSet) :
    (outlineClosedWalk c route).IsTrail := by
  apply trail_of_edgeSet_card
  rw [outlineClosedWalk_edges,Set.ncard_union_eq (Set.disjoint_iUnion_right.mpr ho),
    outline_edges_card,disjoint_route_union_card route (fun z => (hp z).isTrail) hd,
    outlineClosedWalk_length]

end
end Cycle12
