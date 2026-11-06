import Cycle12.ActualGlobalRouteIndex12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 500000
set_option maxRecDepth 100
set_option Elab.async false
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem classMatchingRoute_box_edges (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (label : Sym2 (Option ((F.active t.1).Index t.2))) (j : F.ClassMatchingIndex P t label) :
    (F.classMatchingRoute P Q D hi t label j).edgeSet =
    (F.boxRoute P Q D hi t.1 (.inr (.inl ⟨t.2,⟨label,j⟩⟩))).edgeSet := by
  unfold classMatchingRoute
  rfl



theorem quotientRoute_box_edges (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) :
    (F.actualQuotientRoute P Q D hi t j z).edgeSet =
    (F.boxRoute P Q D hi t.1 (.inr (.inr ⟨t.2,⟨j,z⟩⟩))).edgeSet := by
  unfold actualQuotientRoute
  rfl



theorem boxRoutes_cross_disjoint (hi : i≤L.stopIndex) {z t : L.FoldBoxIndex i} (hzt : z≠t)
    (j : (F.ActualJointFamily P Q D hi z).Index) (k : (F.ActualJointFamily P Q D hi t).Index) :
    Disjoint (F.boxRoute P Q D hi z j).edgeSet (F.boxRoute P Q D hi t k).edgeSet :=
  F.actualRoutes_cross_disjoint P Q D hi (fun h => hzt (congrArg Sigma.fst h)) _ _



theorem lowRoute_box_edges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    (F.actualLowRoute P Q D hi r j).edgeSet=
      (F.boxRoute P Q D hi r.1 (.inl (F.lowPairEmbedding P r.1 ⟨r.2,j⟩))).edgeSet := by
  rw [F.actualLowRoute_edges P Q D hi r j,F.actualRoutes_box_edges P Q D hi r]
  rfl



theorem lowRouteEdges_disjoint (hi : i≤L.stopIndex) : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.lowRouteEdges P Q D hi r) (F.lowRouteEdges P Q D hi t)) := by
  intro r t hrt
  exact (F.coreUsedRoutes_disjoint P Q D hi hrt).mono
    (Set.iUnion_subset (fun j => F.lowRoute_used P Q D hi r j))
    (Set.iUnion_subset (fun j => F.lowRoute_used P Q D hi t j))



theorem low_matching_routes_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.MatchingClassIndex) :
    Disjoint (F.lowRouteEdges P Q D hi r) (F.matchingRouteEdges P Q D hi t) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  rw [F.lowRoute_box_edges P Q D hi r j] at hj
  have hd : Disjoint
    (F.globalRouteEdges P Q D hi ⟨r.1,.inl (F.lowPairEmbedding P r.1 ⟨r.2,j⟩)⟩)
    (F.globalRouteEdges P Q D hi ⟨t.1.1,.inr (.inl ⟨t.1.2,⟨t.2,k⟩⟩)⟩) := by
      apply F.globalRouteEdges_disjoint P Q D hi
      intro hh
      exact Nat.zero_ne_one (congrArg (F.globalRouteKind P Q D hi) hh)
  rw [F.classMatchingRoute_box_edges P Q D hi t.1 t.2 k] at hk
  dsimp only [globalRouteEdges] at hd
  exact Set.disjoint_left.mp hd hj hk



theorem low_quotient_routes_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.BatchIndex) :
    Disjoint (F.lowRouteEdges P Q D hi r) (F.quotientRouteEdges P Q D hi t) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hk
  rw [F.lowRoute_box_edges P Q D hi r j] at hj
  have hd : Disjoint
    (F.globalRouteEdges P Q D hi ⟨r.1,.inl (F.lowPairEmbedding P r.1 ⟨r.2,j⟩)⟩)
    (F.globalRouteEdges P Q D hi ⟨t.1,.inr (.inr ⟨t.2,⟨k,x⟩⟩)⟩) := by
      apply F.globalRouteEdges_disjoint P Q D hi
      intro hh
      have hz : (0:ℕ)=2 := congrArg (F.globalRouteKind P Q D hi) hh
      omega
  rw [F.quotientRoute_box_edges P Q D hi t k x] at hx
  dsimp only [globalRouteEdges] at hd
  exact Set.disjoint_left.mp hd hj hx



theorem matching_quotient_routes_disjoint (hi : i≤L.stopIndex) (t : F.MatchingClassIndex)
    (u : F.BatchIndex) :
    Disjoint (F.matchingRouteEdges P Q D hi t) (F.quotientRouteEdges P Q D hi u) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hk
  have hd : Disjoint
    (F.globalRouteEdges P Q D hi ⟨t.1.1,.inr (.inl ⟨t.1.2,⟨t.2,j⟩⟩)⟩)
    (F.globalRouteEdges P Q D hi ⟨u.1,.inr (.inr ⟨u.2,⟨k,x⟩⟩)⟩) := by
      apply F.globalRouteEdges_disjoint P Q D hi
      intro hh
      have hz : (1:ℕ)=2 := congrArg (F.globalRouteKind P Q D hi) hh
      omega
  rw [F.classMatchingRoute_box_edges P Q D hi t.1 t.2 j] at hj
  rw [F.quotientRoute_box_edges P Q D hi u k x] at hx
  dsimp only [globalRouteEdges] at hd
  exact Set.disjoint_left.mp hd hj hx



theorem matchingRouteEdges_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.MatchingClassIndex =>
    Disjoint (F.matchingRouteEdges P Q D hi t) (F.matchingRouteEdges P Q D hi u)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  have hd : Disjoint
    (F.globalRouteEdges P Q D hi ⟨t.1.1,.inr (.inl ⟨t.1.2,⟨t.2,j⟩⟩)⟩)
    (F.globalRouteEdges P Q D hi ⟨u.1.1,.inr (.inl ⟨u.1.2,⟨u.2,k⟩⟩)⟩) := by
      apply F.globalRouteEdges_disjoint P Q D hi
      intro hh
      exact htu (Option.some.inj (congrArg (F.globalMatchingClass P Q D hi) hh))
  rw [F.classMatchingRoute_box_edges P Q D hi t.1 t.2 j] at hj
  rw [F.classMatchingRoute_box_edges P Q D hi u.1 u.2 k] at hk
  dsimp only [globalRouteEdges] at hd
  exact Set.disjoint_left.mp hd hj hk



theorem quotientRouteEdges_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.BatchIndex =>
    Disjoint (F.quotientRouteEdges P Q D hi t) (F.quotientRouteEdges P Q D hi u)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hj
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hk
  have hd : Disjoint
    (F.globalRouteEdges P Q D hi ⟨t.1,.inr (.inr ⟨t.2,⟨j,z⟩⟩)⟩)
    (F.globalRouteEdges P Q D hi ⟨u.1,.inr (.inr ⟨u.2,⟨k,x⟩⟩)⟩) := by
      apply F.globalRouteEdges_disjoint P Q D hi
      intro hh
      exact htu (Option.some.inj (congrArg (F.globalQuotientBatch P Q D hi) hh))
  rw [F.quotientRoute_box_edges P Q D hi t j z] at hz
  rw [F.quotientRoute_box_edges P Q D hi u k x] at hx
  dsimp only [globalRouteEdges] at hd
  exact Set.disjoint_left.mp hd hz hx



theorem lowRouteEdges_descendants (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (z : L.FoldBoxIndex i) :
    Disjoint (F.lowRouteEdges P Q D hi r) (L.foldDescendantGraph i z).edgeSet :=
  (F.coreUsedRoutes_descendants P Q D hi r z).mono_left
    (Set.iUnion_subset (fun j => F.lowRoute_used P Q D hi r j))



theorem matchingRouteEdges_descendants (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) (z : L.FoldBoxIndex i) :
    Disjoint (F.matchingRouteEdges P Q D hi t) (L.foldDescendantGraph i z).edgeSet := by
  apply Set.disjoint_iUnion_left.mpr
  intro j
  rw [F.classMatchingRoute_box_edges P Q D hi t.1 t.2 j]
  exact F.boxRoute_descendant_disjoint P Q D hi t.1.1 _ z



theorem quotientRouteEdges_descendants (hi : i≤L.stopIndex) (t : F.BatchIndex) (z : L.FoldBoxIndex i) :
    Disjoint (F.quotientRouteEdges P Q D hi t) (L.foldDescendantGraph i z).edgeSet := by
  apply Set.disjoint_iUnion_left.mpr
  intro j
  apply Set.disjoint_iUnion_left.mpr
  intro k
  rw [F.quotientRoute_box_edges P Q D hi t j k]
  exact F.boxRoute_descendant_disjoint P Q D hi t.1 _ z



end ActualFoldStage12
end
end Cycle12.Even12
