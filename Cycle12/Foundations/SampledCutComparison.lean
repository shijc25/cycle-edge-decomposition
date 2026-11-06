import Cycle12.Foundations.TruncatedCutGraph
import Cycle12.Foundations.GraphJanson
import Cycle12.Foundations.CoreExtraction

namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem sampledEdgeCount_embedding_le {H : SimpleGraph W} {G : SimpleGraph V}
    (f : H→g G) (hinj : Function.Injective f) (R : Set W) (U : Set V)
    (hRU : ∀ v∈R, f v∈U) : sampledEdgeCount H R ≤ sampledEdgeCount G U := by
  unfold sampledEdgeCount
  have hs : f.mapEdgeSet '' {e : H.edgeSet | (edgeVertexSet H e:Set W)⊆R} ⊆
      {e : G.edgeSet | (edgeVertexSet G e:Set V)⊆U} := by
    rintro e ⟨e',he',rfl⟩ v hv
    have hv' : v∈Sym2.map f e'.val := by simpa [edgeVertexSet] using hv
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv'
    exact hRU w (he' (by simpa [edgeVertexSet] using hw))
  have hh := Set.ncard_le_ncard hs
  rw [Set.ncard_image_of_injective _ (Hom.mapEdgeSet.injective f hinj)] at hh
  exact hh

theorem sampledEdgeCount_mono {H G : SimpleGraph V} (hHG : H≤G) (U : Set V) :
    sampledEdgeCount H U ≤ sampledEdgeCount G U :=
  sampledEdgeCount_embedding_le (Hom.ofLE hHG) Function.injective_id U U (fun _ h => h)

theorem sampledEdgeCount_induce_le (G : SimpleGraph V) (W : Finset V) (U : Set V) :
    sampledEdgeCount (G.induce (W:Set V)) {v : (W:Set V) | v.val∈U} ≤ sampledEdgeCount G U := by
  let f : G.induce (W:Set V)→g G := ⟨Subtype.val,fun h => h⟩
  exact sampledEdgeCount_embedding_le f Subtype.val_injective _ _ (fun _ h => h)

theorem sampledEdgeCount_eq_inducedEdgeCount (G : SimpleGraph V) (U : Finset V) :
    sampledEdgeCount G (U:Set V)=inducedEdgeCount G U := by
  let A := univ.filter (fun e : G.edgeSet => e.val.toFinset⊆U)
  have hA : sampledEdgeCount G (U:Set V)=A.card := by
    rw [sampledEdgeCount,Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp [A,edgeVertexSet]
  let f : G.edgeSet↪Sym2 V := Function.Embedding.subtype _
  have hm : A.map f=G.edgeFinset.filter (fun e => e.toFinset⊆U) := by
    ext e
    simp only [mem_map,mem_filter,mem_edgeFinset]
    constructor
    · rintro ⟨e',he',heq⟩
      have he₁ : e'.val=e := heq
      subst e
      exact ⟨e'.property,(mem_filter.mp he').2⟩
    · intro he
      exact ⟨⟨e,he.1⟩,mem_filter.mpr ⟨mem_univ _,he.2⟩,rfl⟩
  rw [hA,inducedEdgeCount,← G.card_filter_edgeFinset_toFinset_subset U,← hm,card_map]

theorem between_edge_count (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B) :
    (G.between (A:Set V) (B:Set V)).edgeSet.ncard=(G.interedges A B).card := by
  let H := G.between (A:Set V) (B:Set V)
  have hb : H.IsBipartiteWith (A:Set V) (B:Set V) :=
    G.between_isBipartiteWith (Finset.disjoint_coe.mpr hAB)
  have hd : ∀ v∈A, H.degree v=(neighborsIn G v B).card := by
    intro v hv
    rw [← ncard_neighborSet]
    have hn : H.neighborSet v=(neighborsIn G v B:Set V) := by
      ext w
      have hvB : v∉B := fun h => Finset.disjoint_left.mp hAB hv h
      simp [H,SimpleGraph.mem_neighborSet,between_adj,neighborsIn,hv,hvB,and_comm]
    rw [hn,Set.ncard_coe_finset]
  have hh := H.isBipartiteWith_sum_degrees_eq_card_edges hb
  have he : (∑ v∈A, H.degree v)=(G.interedges A B).card := by
    rw [card_interedges_eq_sum_neighborsIn]
    exact sum_congr rfl hd
  rw [he] at hh
  simpa only [H,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hh.symm

theorem sampled_cut_edge_count (G : SimpleGraph V) (S U : Finset V) :
    sampledEdgeCount (cutGraph G S) (U:Set V)=(G.interedges (U∩S) (U\S)).card := by
  rw [sampledEdgeCount_eq_inducedEdgeCount,inducedEdgeCount]
  have hh := (cutGraph G S).map_edgeFinset_induce (s:=(U:Set V))
  rw [toFinset_coe] at hh
  have he : (cutGraph G S).edgeFinset∩U.sym2=
      (G.between (↑(U∩S):Set V) (↑(U\S):Set V)).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ v w =>
      constructor
      · intro h
        have hg : (cutGraph G S).Adj v w :=
          ((cutGraph G S).mem_edgeSet).mp (mem_edgeFinset.mp (mem_inter.mp h).1)
        have hu := mk_mem_sym2_iff.mp (mem_inter.mp h).2
        apply mem_edgeFinset.mpr
        apply (G.between (↑(U∩S):Set V) (↑(U\S):Set V)).mem_edgeSet.mpr
        change G.Adj v w ∧ ((v∈U∩S ∧ w∈U\S) ∨ (v∈U\S ∧ w∈U∩S))
        change G.Adj v w ∧ ((v∈S ∧ w∉S) ∨ (v∉S ∧ w∈S)) at hg
        simp only [mem_inter,mem_sdiff]
        tauto
      · intro h
        have hg : (G.between (↑(U∩S):Set V) (↑(U\S):Set V)).Adj v w :=
          (G.between (↑(U∩S):Set V) (↑(U\S):Set V)).mem_edgeSet.mp (mem_edgeFinset.mp h)
        change G.Adj v w ∧ ((v∈U∩S ∧ w∈U\S) ∨ (v∈U\S ∧ w∈U∩S)) at hg
        simp only [mem_inter,mem_sdiff] at hg
        apply mem_inter.mpr
        constructor
        · apply mem_edgeFinset.mpr
          apply (cutGraph G S).mem_edgeSet.mpr
          change G.Adj v w ∧ ((v∈S ∧ w∉S) ∨ (v∉S ∧ w∈S))
          tauto
        · apply mk_mem_sym2_iff.mpr
          tauto
  have hc := congrArg Finset.card hh
  rw [card_map,he] at hc
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] at hc ⊢
  rw [hc]
  have hd : Disjoint (U∩S) (U\S) := Finset.disjoint_left.mpr
    (fun _ hx hy => (mem_sdiff.mp hy).2 (mem_inter.mp hx).2)
  have hb := between_edge_count G (U∩S) (U\S) hd
  simpa only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hb

theorem sampled_truncated_cut_le (G : SimpleGraph V) (S U W : Finset V) (k : ℕ) :
    sampledEdgeCount ((truncatedCut G S k).induce (W:Set V)) {v : (W:Set V) | v.val∈U} ≤
      (G.interedges (U∩S) (U\S)).card := by
  have hcut : truncatedCut G S k≤cutGraph G S := by
    intro v w h
    refine ⟨truncatedCut_le G S k h,?_⟩
    have hh := (truncatedCut_bipartite G S k).mem_of_adj h
    simpa only [coe_compl] using hh
  apply (sampledEdgeCount_induce_le (truncatedCut G S k) W (U:Set V)).trans
  rw [← sampled_cut_edge_count G S U]
  exact sampledEdgeCount_mono hcut _

end
end Cycle13
