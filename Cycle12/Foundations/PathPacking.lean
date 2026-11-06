import Cycle12.Foundations.DistinctEndpointPaths
import Cycle12.Foundations.Amplification

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

structure EndpointPathPacking (G : SimpleGraph V) where
  count : ℕ
  paths : Fin count → OAI.ErdosGallai.PositiveSimplePath G
  disjoint : Pairwise (fun i j => Disjoint (paths i).walk.edgeSet (paths j).walk.edgeSet)
  endpoint_injective : Function.Injective (fun z : Fin count × Bool =>
    if z.2 then (paths z.1).start else (paths z.1).finish)

namespace EndpointPathPacking
variable {G : SimpleGraph V}

def used (P : EndpointPathPacking G) : Set (Sym2 V) := ⋃ i, (P.paths i).walk.edgeSet
def singles (P : EndpointPathPacking G) : ℕ := (G.edgeSet \ P.used).ncard

theorem count_bound (P : EndpointPathPacking G) : 2 * P.count ≤ Fintype.card V := by
  have h := Fintype.card_le_of_injective _ P.endpoint_injective
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using h

def ofIndexed {I : Type} [Fintype I] (P : I → OAI.ErdosGallai.PositiveSimplePath G)
    (hd : Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet))
    (he : Function.Injective (fun z : I × Bool => if z.2 then (P z.1).start else (P z.1).finish)) :
    EndpointPathPacking G where
  count := Fintype.card I
  paths := fun i => P ((Fintype.equivFin I).symm i)
  disjoint := fun _ _ h => hd (fun heq => h ((Fintype.equivFin I).symm.injective heq))
  endpoint_injective := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hh := @he ((Fintype.equivFin I).symm i, b) ((Fintype.equivFin I).symm j, c) h
    have hi := congrArg Prod.fst hh
    have hb := congrArg Prod.snd hh
    exact Prod.ext ((Fintype.equivFin I).symm.injective hi) hb

theorem used_ofIndexed {I : Type} [Fintype I] (P : I → OAI.ErdosGallai.PositiveSimplePath G)
    (hd : Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet))
    (he : Function.Injective (fun z : I × Bool => if z.2 then (P z.1).start else (P z.1).finish)) :
    (ofIndexed P hd he).used = ⋃ i, (P i).walk.edgeSet := by
  ext e
  simp only [used, ofIndexed, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fintype.equivFin I i, ?_⟩
    exact Eq.mpr (congrArg (fun j : I => e ∈ (P j).walk.edgeSet)
      ((Fintype.equivFin I).symm_apply_apply i)) hi

end EndpointPathPacking

/-- All finite simple graphs admit edge-disjoint positive simple paths with
distinct endpoints after discarding at most n-c(G) edges. -/
theorem exists_distinct_endpoint_path_packing (G : SimpleGraph V) :
    ∃ P : EndpointPathPacking G, P.singles ≤ Fintype.card V - componentCount G := by
  classical
  have hlocal : ∀ c : G.ConnectedComponent, ∃ F : SimpleGraph c,
      F ≤ c.toSimpleGraph ∧ F.edgeSet.ncard ≤ Fintype.card c - 1 ∧
        Nonempty (DistinctEndpointPaths (c.toSimpleGraph \ F)) := by
    intro c
    obtain ⟨F, hF, _, hsize, hP⟩ := connected_forest_path_partition c.toSimpleGraph c.connected_toSimpleGraph
    rw [connected_componentCount_eq_one _ c.connected_toSimpleGraph] at hsize
    exact ⟨F, hF, hsize, hP⟩
  choose F hF hsize hP using hlocal
  let Q := fun c => Classical.choice (hP c)
  let I := Σ c : G.ConnectedComponent, Fin (Q c).count
  let P : I → OAI.ErdosGallai.PositiveSimplePath G := fun z =>
    { start := ((Q z.1).paths z.2).start.val
      finish := ((Q z.1).paths z.2).finish.val
      walk := (((Q z.1).paths z.2).walk.mapLe sdiff_le).map z.1.toSimpleGraph_hom
      isPath := (((Q z.1).paths z.2).isPath.mapLe sdiff_le).map Subtype.val_injective
      positive := by
        calc
          0 < ((Q z.1).paths z.2).walk.length := ((Q z.1).paths z.2).positive
          _ = (((Q z.1).paths z.2).walk.mapLe sdiff_le).length :=
            (Walk.length_mapLe _ _).symm
          _ = ((((Q z.1).paths z.2).walk.mapLe sdiff_le).map z.1.toSimpleGraph_hom).length :=
            (Walk.length_map _ _).symm }
  have hpedge (c : G.ConnectedComponent) (i : Fin (Q c).count) :
      (P ⟨c, i⟩).walk.edgeSet =
        Sym2.map c.toSimpleGraph_hom '' ((Q c).paths i).walk.edgeSet := by
    calc
      _ = Sym2.map c.toSimpleGraph_hom '' (((Q c).paths i).walk.mapLe sdiff_le).edgeSet :=
        Walk.edgeSet_map _ _
      _ = _ := congrArg (fun s => Sym2.map c.toSimpleGraph_hom '' s)
        (Walk.edgeSet_mapLe_eq_edgeSet _ _)
  have hpsub (c : G.ConnectedComponent) (i : Fin (Q c).count) :
      (P ⟨c, i⟩).walk.edgeSet ⊆ Sym2.map c.toSimpleGraph_hom '' c.toSimpleGraph.edgeSet := by
    rw [hpedge]
    apply Set.image_mono
    intro e he
    exact edgeSet_mono sdiff_le (((Q c).paths i).walk.edges_subset_edgeSet he)
  have hd : Pairwise (fun i j : I => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) := by
    rintro ⟨c, i⟩ ⟨d, j⟩ hne
    by_cases hcd : c = d
    · subst d
      rw [hpedge, hpedge]
      apply Set.disjoint_left.mpr
      rintro e ⟨a, ha, hea⟩ ⟨b, hb, heb⟩
      have hab := Sym2.map.injective Subtype.val_injective (hea.trans heb.symm)
      subst b
      exact Set.disjoint_left.mp ((Q c).disjoint (fun h => hne (by cases h; rfl))) ha hb
    · exact (component_edges_disjoint G hcd).mono (hpsub c i) (hpsub d j)
  have hei : Function.Injective (fun z : I × Bool =>
      if z.2 then (P z.1).start else (P z.1).finish) := by
    rintro ⟨⟨c, i⟩, bi⟩ ⟨⟨d, j⟩, bj⟩ heq
    let vi : c := if bi then ((Q c).paths i).start else ((Q c).paths i).finish
    let vj : d := if bj then ((Q d).paths j).start else ((Q d).paths j).finish
    have hv : vi.val = vj.val := by
      cases bi <;> cases bj <;> exact heq
    have hcd : c = d := ConnectedComponent.eq_of_common_vertex vi.property (hv ▸ vj.property)
    subst d
    have hverts : vi = vj := Subtype.ext hv
    have hij : (i, bi) = (j, bj) := (Q c).endpoint_injective hverts
    cases hij
    rfl
  let R := EndpointPathPacking.ofIndexed P hd hei
  let discarded := fun c : G.ConnectedComponent => Sym2.map c.toSimpleGraph_hom '' (F c).edgeSet
  have hres : G.edgeSet \ R.used ⊆ ⋃ c, discarded c := by
    rintro e ⟨heG, heR⟩
    rw [← component_edges_cover G] at heG
    obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.mp heG
    by_cases hfa : a ∈ (F c).edgeSet
    · exact Set.mem_iUnion.mpr ⟨c, a, hfa, rfl⟩
    · have hrem : a ∈ (c.toSimpleGraph \ F c).edgeSet := by
        rw [edgeSet_sdiff]
        exact ⟨ha, hfa⟩
      rw [← (Q c).cover] at hrem
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hrem
      apply (heR ?_).elim
      rw [EndpointPathPacking.used_ofIndexed]
      exact Set.mem_iUnion.mpr ⟨⟨c, i⟩, (hpedge c i).symm ▸ ⟨a, hi, rfl⟩⟩
  have hdd : Pairwise (fun c d => Disjoint (discarded c) (discarded d)) := by
    intro c d hcd
    exact (component_edges_disjoint G hcd).mono
      (Set.image_mono (edgeSet_mono (hF c))) (Set.image_mono (edgeSet_mono (hF d)))
  refine ⟨R, ?_⟩
  calc
    R.singles ≤ (⋃ c, discarded c).ncard := Set.ncard_le_ncard hres
    _ = ∑ c, (discarded c).ncard := ncard_iUnion_disjoint discarded hdd
    _ = ∑ c, (F c).edgeSet.ncard := by
      apply sum_congr rfl
      intro c _
      exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    _ ≤ ∑ c : G.ConnectedComponent, (Fintype.card c - 1) := sum_le_sum (fun c _ => hsize c)
    _ = Fintype.card V - componentCount G := sum_component_ranks G

end
end Cycle13
