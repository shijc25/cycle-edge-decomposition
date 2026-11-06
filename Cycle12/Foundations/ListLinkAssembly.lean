import Cycle12.Foundations.ListLinks

/-! Combining complementary demand graphs routed in successive residuals. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
namespace ReservoirLinks
variable {W V : Type} [DecidableEq V] {R : SimpleGraph W} {G : SimpleGraph V}
    {D : Finset V} {φ : W ↪ V} (L : ReservoirLinks R G D φ)
    (K : ReservoirLinks Rᶜ L.residue D φ)

lemma residue_le : L.residue ≤ G := G.deleteEdges_le L.used

lemma cross_disjoint {x y a b : W} (h : R.Adj x y) (k : Rᶜ.Adj a b) :
    Disjoint (L.walk h).edgeSet (K.walk k).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hk
  have hk' := (K.walk k).edges_subset_edgeSet hk
  rw [residue,edgeSet_deleteEdges] at hk'
  exact hk'.2 (L.walk_edges_used h he)

def completeWalk {x y : W} (h : x ≠ y) : G.Walk (φ x) (φ y) :=
  if hR : R.Adj x y then L.walk hR
  else (K.walk ((compl_adj R x y).mpr ⟨h,hR⟩)).mapLe L.residue_le

lemma completeWalk_disjoint (hout : ∀ v, φ v ∉ D) {x y a b : W}
    (h : x ≠ y) (k : a ≠ b) (hne : s(x,y) ≠ s(a,b)) :
    Disjoint (L.completeWalk K h).edgeSet (L.completeWalk K k).edgeSet := by
  unfold completeWalk
  split_ifs with hR kR kR
  · exact L.walk_disjoint hout hR kR hne
  · rw [Walk.edgeSet_mapLe_eq_edgeSet]
    exact L.cross_disjoint K hR _
  · rw [Walk.edgeSet_mapLe_eq_edgeSet]
    exact (L.cross_disjoint K kR _).symm
  · simp only [Walk.edgeSet_mapLe_eq_edgeSet]
    exact K.walk_disjoint hout _ _ hne

lemma completeWalk_avoids (hout : ∀ v, φ v ∉ D) {x y : W} (h : x ≠ y) (v : W)
    (hv : φ v ∈ (L.completeWalk K h).support) : v=x ∨ v=y := by
  unfold completeWalk at hv
  split_ifs at hv with hR
  · exact L.walk_avoids hout hR v hv
  · rw [Walk.support_mapLe_eq_support] at hv
    exact K.walk_avoids hout _ v hv

def completeRouting (hout : ∀ v, φ v ∉ D) : EdgeRouting (completeGraph W) G where
  vertex := φ
  route := L.completeWalk K
  disjoint := L.completeWalk_disjoint K hout
  avoids := L.completeWalk_avoids K hout

end ReservoirLinks
end
end Cycle13
