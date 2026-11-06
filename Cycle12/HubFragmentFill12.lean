import Cycle12.HubFragments12

namespace Cycle12
open SimpleGraph
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}

structure ReservoirLink (G : SimpleGraph V) (x y : V) where
  left : V
  right : V
  route : G.Walk left right
  left_adj : G.Adj x left
  right_adj : G.Adj y right
  isPath : route.IsPath

namespace ReservoirLink
variable {x y : V}
def edges (L : ReservoirLink G x y) : Set (Sym2 V) :=
  L.route.edgeSet ∪ {s(x,L.left),s(y,L.right)}
end ReservoirLink

namespace HubFragment

def fill (F : HubFragment G) (L : ∀ h : F.IsSplit, ReservoirLink G (F.near h false) (F.near h true)) :
    G.Walk (F.outer false) (F.outer true) := by
  cases F with
  | path P => exact P.walk
  | split A B hd =>
    let l := L trivial
    exact spliceArms A.walk B.walk l.route l.left_adj l.right_adj

@[simp] theorem fill_edges (F : HubFragment G)
    (L : ∀ h : F.IsSplit, ReservoirLink G (F.near h false) (F.near h true)) :
    (F.fill L).edgeSet = F.body ∪ ⋃ h : F.IsSplit, (L h).edges := by
  cases F with
  | path P =>
    change P.walk.edgeSet = _
    simp only [body,IsSplit,Set.iUnion_false,Set.union_empty]
  | split A B hd =>
    change (spliceArms A.walk B.walk (L trivial).route (L trivial).left_adj (L trivial).right_adj).edgeSet = _
    exact (spliceArms_edges A.walk B.walk (L trivial).route (L trivial).left_adj (L trivial).right_adj).trans (by
      simp only [body,IsSplit,Set.iUnion_true,ReservoirLink.edges,near,Bool.false_eq_true,if_false,if_true,Set.union_assoc])

theorem fill_isPath (F : HubFragment G)
    (L : ∀ h : F.IsSplit, ReservoirLink G (F.near h false) (F.near h true))
    (hsep : ∀ h, ∀ v ∈ (L h).route.support, v ∉ F.support) : (F.fill L).IsPath := by
  cases F with
  | path P => exact P.isPath
  | split A B hd =>
    apply spliceArms_isPath A.walk B.walk (L trivial).route (L trivial).left_adj (L trivial).right_adj A.isPath B.isPath (L trivial).isPath hd
    · intro v hv hp
      exact hsep trivial v hp (Or.inl hv)
    · intro v hv hp
      exact hsep trivial v hp (Or.inr hv)

theorem fill_support (F : HubFragment G)
    (L : ∀ h : F.IsSplit, ReservoirLink G (F.near h false) (F.near h true))
    {v : V} (hv : v ∈ (F.fill L).support) :
    v ∈ F.support ∨ ∃ h : F.IsSplit, v ∈ (L h).route.support := by
  cases F with
  | path P => exact Or.inl hv
  | split A B hd =>
    change v ∈ (spliceArms A.walk B.walk (L trivial).route (L trivial).left_adj (L trivial).right_adj).support at hv
    have hv' : v ∈ A.walk.support.reverse ++ (L trivial).route.support ++ B.walk.support :=
      spliceArms_support A.walk B.walk (L trivial).route (L trivial).left_adj (L trivial).right_adj ▸ hv
    simp only [List.mem_append,List.mem_reverse] at hv'
    rcases hv'  with (hv | hv) | hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inr ⟨trivial,hv⟩
    · exact Or.inl (Or.inr hv)

theorem fill_contains_body (F : HubFragment G)
    (L : ∀ h : F.IsSplit, ReservoirLink G (F.near h false) (F.near h true)) :
    F.body ⊆ (F.fill L).edgeSet := by
  rw [fill_edges]
  exact Set.subset_union_left

/-- All three types of cross-intersection are explicit: old/old,
link/link, and old/link. This applies even when a fragment is trivial. -/
theorem fill_family_disjoint {I : Type} (F : I → HubFragment G)
    (L : ∀ i, ∀ h : (F i).IsSplit, ReservoirLink G ((F i).near h false) ((F i).near h true))
    (hbody : Pairwise (fun i j => Disjoint (F i).body (F j).body))
    (hlink : ∀ i j, i ≠ j → ∀ hi hj, Disjoint (L i hi).edges (L j hj).edges)
    (hcross : ∀ i j hj, Disjoint (F i).body (L j hj).edges) :
    Pairwise (fun i j => Disjoint ((F i).fill (L i)).edgeSet ((F j).fill (L j)).edgeSet) := by
  intro i j hij
  rw [fill_edges,fill_edges]
  apply Set.disjoint_left.mpr
  intro e he hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Set.disjoint_left.mp (hbody hij) he hf
  · obtain ⟨hj,hf⟩ := Set.mem_iUnion.mp hf
    exact Set.disjoint_left.mp (hcross i j hj) he hf
  · obtain ⟨hi,he⟩ := Set.mem_iUnion.mp he
    exact Set.disjoint_left.mp (hcross j i hi) hf he
  · obtain ⟨hi,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨hj,hf⟩ := Set.mem_iUnion.mp hf
    exact Set.disjoint_left.mp (hlink i j hij hi hj) he hf

end HubFragment
end
end Cycle12
