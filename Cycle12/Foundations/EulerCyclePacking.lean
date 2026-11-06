import Cycle12.Foundations.GraphParity
import Cycle12.Foundations.LongCycleRemoval

namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem closed_trail_edge_graph_even {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsTrail) (u : V) :
    Even ((walkEdgeGraph p).degree u) := by
  let q := p.transfer (walkEdgeGraph p) (by intro e he; rw [walkEdgeGraph_edges]; exact he)
  have hq : q.IsTrail := hp.transfer _
  have he : q.edgeSet=(walkEdgeGraph p).edgeSet := by
    simp only [q,Walk.edgeSet_transfer,walkEdgeGraph_edges]
  have hu : q.IsEulerian := hq.isEulerian_iff.mpr he
  exact (hu.even_degree_iff (x:=u)).mpr (by simp)

theorem even_degrees_delete_closed_trail {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsTrail) (heven : ∀ u, Even (G.degree u)) :
    ∀ u, Even ((G.deleteEdges p.edgeSet).degree u) := by
  have hgraph : G.deleteEdges p.edgeSet=G ∆ walkEdgeGraph p := by
    rw [symmDiff_of_ge (walkEdgeGraph_le p)]
    apply SimpleGraph.edgeSet_injective
    simp only [SimpleGraph.edgeSet_deleteEdges,SimpleGraph.edgeSet_sdiff,walkEdgeGraph_edges]
  intro u
  have hx : Even ((G ∆ walkEdgeGraph p).degree u) :=
    (graph_symmDiff_degree_even G (walkEdgeGraph p) u).mpr
      (iff_of_true (heven u) (closed_trail_edge_graph_even p hp u))
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx ⊢
  simpa only [hgraph] using hx

theorem acyclic_even_eq_bot (G : SimpleGraph V) (hforest : G.IsAcyclic)
    (heven : ∀ v, Even (G.degree v)) : G=⊥ := by
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro x y hxy
  let c := G.connectedComponentMk x
  have hx : x ∈ c := rfl
  have hy : y ∈ c := c.mem_supp_of_adj_mem_supp hx hxy
  letI : Nontrivial c := ⟨⟨⟨x,hx⟩,⟨y,hy⟩,fun he => hxy.ne (congrArg Subtype.val he)⟩⟩
  obtain ⟨v,hv⟩ := (hforest.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
  have hp := heven v.val
  rw [← component_degree_eq G c v,hv] at hp
  norm_num at hp

/-- Every finite graph with all degrees even admits an actual packing
covering every edge by simple cycles. -/
theorem exists_full_cycle_packing_of_even (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) : ∃ P : CyclePacking G, P.singles=0 := by
  have main : ∀ n : ℕ, ∀ P : CyclePacking G, P.singles=n →
      (∀ v, Even (P.residue.degree v)) → ∃ Q : CyclePacking G, Q.singles=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hPn hPeven
      by_cases hforest : P.residue.IsAcyclic
      · refine ⟨P,?_⟩
        rw [CyclePacking.singles,acyclic_even_eq_bot P.residue hforest hPeven]
        simp
      · obtain ⟨v,p,hp⟩ : ∃ v, ∃ p : P.residue.Walk v v, p.IsCycle := by
          simpa only [SimpleGraph.IsAcyclic,not_forall,Classical.not_not] using hforest
        let q := p.mapLe P.residue_le
        have hq : q.IsCycle := hp.mapLe _
        have he : q.edgeSet=p.edgeSet := Walk.edgeSet_mapLe_eq_edgeSet _ _
        have hsub : q.edgeSet ⊆ P.residue.edgeSet := by rw [he]; exact p.edges_subset_edgeSet
        let Q := P.addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
        have hs : Q.singles+p.length=P.singles := by
          have hh := P.singles_addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
          simpa only [Q,he,cycle_edgeSet_ncard hp] using hh
        have hsmall : Q.singles < n := by have hh := hp.three_le_length; omega
        have hQeven : ∀ u, Even (Q.residue.degree u) := by
          have hr : Q.residue=P.residue.deleteEdges p.edgeSet := by
            rw [CyclePacking.residue_addCycle,he]
          rw [hr]
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
            even_degrees_delete_closed_trail p hp.isTrail hPeven
        exact ih _ hsmall Q rfl hQeven
  apply main _ (CyclePacking.empty G) rfl
  have hres : (CyclePacking.empty G).residue=G := by
    apply SimpleGraph.edgeSet_injective
    simp [CyclePacking.residue,CyclePacking.used,CyclePacking.empty]
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,hres] using heven

/-- Each edge-disjoint cycle consumes a different edge outside a fixed
spanning tree. This supplies the exact m-n+1 bound needed for trails. -/
theorem CyclePacking.count_add_order_le (G : SimpleGraph V) (hG : G.Connected)
    (P : CyclePacking G) : P.count+Fintype.card V ≤ G.edgeSet.ncard+1 := by
  obtain ⟨T,hTG,hT⟩ := hG.exists_isTree_le
  have hout : ∀ i, ∃ e, e ∈ P.parts i ∧ e ∉ T.edgeSet := by
    intro i
    obtain ⟨v,p,hp,hparts⟩ := P.cycles i
    by_contra! hnot
    have hsub : ∀ e ∈ p.edges, e ∈ T.edgeSet := by intro e he; exact hnot e (hparts ▸ he)
    exact hT.isAcyclic (p.transfer T hsub) (hp.transfer _)
  choose e he hn using hout
  have hmem : ∀ i, e i ∈ G.edgeFinset\T.edgeFinset := by
    intro i
    simpa only [Finset.mem_sdiff,SimpleGraph.mem_edgeFinset] using And.intro (P.parts_subset i (he i)) (hn i)
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint hne) (he i) (hij.symm ▸ he j)
  have hcount : P.count ≤ (G.edgeFinset\T.edgeFinset).card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card_of_injOn e (fun i (_ : i ∈ (Finset.univ:Finset (Fin P.count))) => hmem i)
        (fun i _ j _ hij => hinj hij)
  have hsub : T.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hTG (SimpleGraph.mem_edgeFinset.mp he))
  rw [Finset.card_sdiff_of_subset hsub] at hcount
  have htree : T.edgeFinset.card+1=Fintype.card V := hT.card_edgeFinset
  have hTGcard := Finset.card_le_card hsub
  have hsize : G.edgeFinset.card=G.edgeSet.ncard := by
    simp only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']
  omega

theorem connected_even_cycle_decomposition (G : SimpleGraph V) (hG : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ P : CyclePacking G, P.singles=0 ∧ P.count+Fintype.card V ≤ G.edgeSet.ncard+1 := by
  obtain ⟨P,hP⟩ := exists_full_cycle_packing_of_even G heven
  exact ⟨P,hP,P.count_add_order_le G hG⟩

end
end Cycle13
