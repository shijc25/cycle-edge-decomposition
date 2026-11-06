import Cycle12.Foundations.ListLinkAssembly
import Cycle12.Foundations.CliquePairs

/-! Complete a partial reservoir routing by the remaining direct branch edges. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

def EdgeRouting.cliqueModel {V : Type} {G : SimpleGraph V} {t : ℕ}
    (R : EdgeRouting (completeGraph (Fin t)) G) : StrongCliqueImmersion t G where
  branch := R.vertex
  route e := (R.route (ne_of_lt e.2)).toPath
  disjoint := by
    intro e d hed
    exact (R.disjoint (ne_of_lt e.2) (ne_of_lt d.2)
      (fun h => hed (CliquePair.edge_injective h))).mono
      (R.route (ne_of_lt e.2)).edges_toPath_subset_edges
      (R.route (ne_of_lt d.2)).edges_toPath_subset_edges
  avoids := by
    intro e i hi
    exact R.avoids _ i ((R.route (ne_of_lt e.2)).support_toPath_subset_support hi)

namespace ReservoirLinks
variable {W V : Type} [DecidableEq V] {R : SimpleGraph W} {G : SimpleGraph V}
    {D : Finset V} {φ : W ↪ V} (L : ReservoirLinks R G D φ)

lemma branch_edge_not_used (hout : ∀ v, φ v ∉ D) (x y : W) : s(φ x,φ y) ∉ L.used := by
  rintro ⟨d,v,hv,he⟩
  rcases Sym2.eq_iff.mp he with ⟨_,hy⟩ | ⟨hx,_⟩
  · exact hout y (hy ▸ L.mem d)
  · exact hout x (hx ▸ L.mem d)

lemma walk_direct_disjoint (hout : ∀ v, φ v ∉ D) {x y a b : W}
    (h : R.Adj x y) (k : G.Adj (φ a) (φ b)) :
    Disjoint (L.walk h).edgeSet k.toWalk.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hk
  have heq : e=s(φ a,φ b) := by simpa [Adj.toWalk] using hk
  exact L.branch_edge_not_used hout a b (heq ▸ L.walk_edges_used h he)

variable (hdirect : ∀ x y, Rᶜ.Adj x y → G.Adj (φ x) (φ y))

def completedWalk {x y : W} (h : x ≠ y) : G.Walk (φ x) (φ y) :=
  if hR : R.Adj x y then L.walk hR
  else (hdirect x y ((compl_adj R x y).mpr ⟨h,hR⟩)).toWalk

lemma completedWalk_disjoint (hout : ∀ v, φ v ∉ D) {x y a b : W}
    (h : x ≠ y) (k : a ≠ b) (hne : s(x,y) ≠ s(a,b)) :
    Disjoint (L.completedWalk hdirect h).edgeSet (L.completedWalk hdirect k).edgeSet := by
  unfold completedWalk
  split_ifs with hR kR kR
  · exact L.walk_disjoint hout hR kR hne
  · exact L.walk_direct_disjoint hout hR _
  · exact (L.walk_direct_disjoint hout kR _).symm
  · apply Set.disjoint_left.mpr
    intro e he hk
    have he' : e=s(φ x,φ y) := by simpa [Adj.toWalk] using he
    have hk' : e=s(φ a,φ b) := by simpa [Adj.toWalk] using hk
    exact hne (Sym2.map.injective φ.injective (he'.symm.trans hk'))

lemma completedWalk_avoids (hout : ∀ v, φ v ∉ D) {x y : W} (h : x ≠ y) (v : W)
    (hv : φ v ∈ (L.completedWalk hdirect h).support) : v=x ∨ v=y := by
  unfold completedWalk at hv
  split_ifs at hv with hR
  · exact L.walk_avoids hout hR v hv
  · have hv' : φ v=φ x ∨ φ v=φ y := by simpa [Adj.toWalk] using hv
    exact hv'.imp (fun h => φ.injective h) (fun h => φ.injective h)

def completedRouting (hout : ∀ v, φ v ∉ D) : EdgeRouting (completeGraph W) G where
  vertex := φ
  route := L.completedWalk hdirect
  disjoint := L.completedWalk_disjoint hdirect hout
  avoids := L.completedWalk_avoids hdirect hout

end ReservoirLinks
end
end Cycle13
