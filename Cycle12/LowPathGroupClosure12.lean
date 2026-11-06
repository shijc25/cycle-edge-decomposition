import Cycle12.TwoEdgeIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G : SimpleGraph V}

theorem low_path_coloring_of_degrees (G : SimpleGraph V) (U : Finset V) (a b z : I → V)
    (ha : ∀ i,G.Adj (z i) (a i)) (hb : ∀ i,G.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i) (hUa : ∀ i,a i∈U) (hUb : ∀ i,b i∈U) (hUz : ∀ i,z i∉U)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet))
    {A D : ℕ} (hpalette : 0<2*A+D)
    (hcore : ∀ v∈U,G.degree v ≤ A) (hout : ∀ v,v∉U → G.degree v ≤ 2*D) :
    Nonempty ((lowPathConflict a b z).Coloring (Fin (2*A+D))) := by
  apply low_path_coloring a b z hpalette
  · intro v
    by_cases hv : v∈U
    · rw [←endpointLoad_eq_incident_card a b hne v]
      exact (endpointLoad_le_original_degree G a b (fun i => twoEdgeWalk (ha i) (hb i)) hne hd v).trans (hcore v hv)
    · have he : (univ.filter (fun i => a i=v ∨ b i=v))=∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi
        rcases hi with hi|hi
        · exact hv (hi ▸ hUa i)
        · exact hv (hi ▸ hUb i)
      rw [he,card_empty]
      omega
  · intro v
    by_cases hv : v∈U
    · have he : (univ.filter (fun i => z i=v))=∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i _ hi
        exact hUz i (hi.symm ▸ hv)
      rw [he,card_empty]
      omega
    · have hh := twoEdge_center_load a b z ha hb hne hd v
      have hh' := hout v hv
      omega

/-- The low-path branch after simultaneous routing. Only the actual
router output is needed: hard avoidance of the at most 2Q core ports,
edge disjointness globally, and disjoint interiors within each group. -/
theorem low_path_group_closure (U : Finset V) (a b z : I → V)
    (ha : ∀ i,G.Adj (z i) (a i)) (hb : ∀ i,G.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i) (hUa : ∀ i,a i∈U) (hUb : ∀ i,b i∈U) (hUz : ∀ i,z i∉U)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet))
    {A D Q : ℕ} (hQ : 0<Q)
    (color : (lowPathConflict a b z).Coloring (Fin (2*A+D)))
    (q : ∀ i,G.Walk (b i) (a (groupedCycleNext (coloredDemandGroup color Q) i)))
    (hq : ∀ i,(q i).IsPath) (hqs : ∀ i v,v∈(q i).support → v∈U)
    (hhard : ∀ i,Disjoint (routeInterior (q i))
      (groupPorts (coloredDemandGroup color Q) a b (coloredDemandGroup color Q i)))
    (hQQ : Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet))
    (hPQ : ∀ i j,Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet (q j).edgeSet)
    (hi : ∀ i j,i ≠ j → coloredDemandGroup color Q i=coloredDemandGroup color Q j →
      Disjoint (routeInterior (q i)) (routeInterior (q j))) :
    ∃ P : CyclePacking G,
      P.used=(⋃ i,(twoEdgeWalk (ha i) (hb i)).edgeSet)∪(⋃ i,(q i).edgeSet) ∧
      (P.count:ℝ) ≤ (Fintype.card I:ℝ)/Q+(2*A+D:ℕ) := by
  let group := coloredDemandGroup color Q
  have hv : ∀ i j,i ≠ j → group i=group j →
      Disjoint (twoEdgeWalk (ha i) (hb i)).support.toFinset
        (twoEdgeWalk (ha j) (hb j)).support.toFinset := by
    intro i j hij hg
    rw [twoEdgeWalk_support,twoEdgeWalk_support]
    exact low_path_same_color_disjoint a b z U hUa hUb hUz color hij
      (coloredDemandGroup_same_color color Q hg)
  have hnext : ∀ i,b i ≠ a (groupedCycleNext group i) :=
    grouped_reconnection_distinct group a b hne (by
      intro i j hij hg hba
      have hh := hv i j hij hg
      exact Finset.disjoint_left.mp hh (List.mem_toFinset.mpr (twoEdgeWalk (ha i) (hb i)).end_mem_support)
        (hba.symm ▸ List.mem_toFinset.mpr (twoEdgeWalk (ha j) (hb j)).start_mem_support))
  have hforbid : ∀ i j,group i=group j →
      Disjoint (routeInterior (q i)) (twoEdgeWalk (ha j) (hb j)).support.toFinset := by
    intro i j hg
    rw [twoEdgeWalk_support]
    apply Finset.disjoint_left.mpr
    intro v hv hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · exact Finset.disjoint_left.mp (hhard i) hv
        ((mem_groupPorts group a b (group i) _).mpr ⟨j,hg.symm,Or.inl rfl⟩)
    · exact Finset.disjoint_left.mp (hhard i) hv
        ((mem_groupPorts group a b (group i) _).mpr ⟨j,hg.symm,Or.inr rfl⟩)
    · exact hUz j (hqs i _ ((mem_routeInterior_iff _ _).mp hv).1)
  obtain ⟨P,hused,hcount⟩ := grouped_family_cycle_packing group a b
    (fun i => twoEdgeWalk (ha i) (hb i)) q (fun i => twoEdgeWalk_isPath _ _ (hne i))
    hq hnext hv hd hQQ hPQ hi hforbid
  refine ⟨P,hused,?_⟩
  have hc : (P.count:ℝ) ≤ Fintype.card (ColoredDemandGroups color Q) := by exact_mod_cast hcount
  exact hc.trans (by simpa only [Fintype.card_fin] using coloredDemandGroups_count_bound color hQ)

end
end Cycle12
