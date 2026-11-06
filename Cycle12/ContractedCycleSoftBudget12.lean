import Cycle12.ContractedCycleSwitch12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
variable {G : SimpleGraph V} {A : I → Finset V} {S : Set (Sym2 V)}
variable {Q : SimpleGraph (ContractedVertices A)} {a : ContractedVertices A} {p : Q.Walk a a}

namespace RepresentedCyclePorts12
variable (r : RepresentedCyclePorts12 (G:=G) (contractVertex A) S p) (hp : p.IsCycle)

def softVertices (cores : I → Finset V) (z : (r.outline hp).Switch) : Finset V :=
  ((r.outline hp).vertices\blockUnion A)∩cores (r.switchOwner hp z)

theorem softVertices_total (cores : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (cores i) (cores j))) :
    (∑ z,(r.softVertices hp cores z).card)≤p.length := by
  have hdis : Pairwise (fun z w => Disjoint (r.softVertices hp cores z) (r.softVertices hp cores w)) := by
    intro z w hzw
    exact (hd (fun he => hzw (r.switchOwner_injective hp he))).mono
      inter_subset_right inter_subset_right
  have hc := Finset.card_biUnion (s:=univ) (t:=r.softVertices hp cores)
    (fun z _ w _ hzw => hdis hzw)
  rw [←hc]
  apply (Finset.card_le_card ?_).trans (r.ordinary_vertices_card_le hp)
  intro v hv
  obtain ⟨z,_,hv⟩ := mem_biUnion.mp hv
  exact (mem_inter.mp hv).1

/-- A route in its own core meets the original outline only at ordinary
uncontracted vertices. Its own two ports are absent from its interior. -/
theorem soft_collision_eq (cores : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (cores i) (cores j)))
    (hA : ∀ i,A i⊆cores i)
    (route : ∀ z : (r.outline hp).Switch,G.Walk (r.start z) (r.finish z))
    (hr : ∀ z,routeInterior (route z)⊆cores (r.switchOwner hp z))
    (z : (r.outline hp).Switch) :
    routeInterior (route z)∩(r.outline hp).vertices=
      routeInterior (route z)∩r.softVertices hp cores z := by
  have hAd : Pairwise (fun i j => Disjoint (A i) (A j)) :=
    fun i j hij => (hd hij).mono (hA i) (hA j)
  ext v
  constructor
  · intro hv
    obtain ⟨hi,hv⟩ := mem_inter.mp hv
    have hcore := hr z hi
    have hout : v∉blockUnion A := by
      intro hb
      obtain ⟨i,hiA⟩ := (mem_blockUnion A v).mp hb
      have hie : i=r.switchOwner hp z := by
        by_contra hne
        exact Finset.disjoint_left.mp (hd hne) (hA i hiA) hcore
      rw [hie] at hiA
      have hport := r.active_vertex_is_port hp hAd z hv hiA
      have hn := (mem_routeInterior_iff (route z) v).mp hi
      exact hport.elim hn.2.1 hn.2.2
    exact mem_inter.mpr ⟨hi,mem_inter.mpr ⟨mem_sdiff.mpr ⟨hv,hout⟩,hcore⟩⟩
  · intro hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1,
      (mem_sdiff.mp (mem_inter.mp (mem_inter.mp hv).2).1).1⟩

theorem route_interiors_disjoint (cores : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (cores i) (cores j)))
    (route : ∀ z : (r.outline hp).Switch,G.Walk (r.start z) (r.finish z))
    (hr : ∀ z,routeInterior (route z)⊆cores (r.switchOwner hp z)) :
    Pairwise (fun z w => Disjoint (routeInterior (route z)) (routeInterior (route w))) := by
  intro z w hzw
  exact (hd (fun he => hzw (r.switchOwner_injective hp he))).mono (hr z) (hr w)

/-- The actual quotient cycle closes with its weighted soft routing
budget, charged to at most its original number of edges. -/
theorem contracted_soft_packing (cores : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (cores i) (cores j))) (hA : ∀ i,A i⊆cores i)
    (route : ∀ z : (r.outline hp).Switch,G.Walk (r.start z) (r.finish z))
    (hr : ∀ z,routeInterior (route z)⊆cores (r.switchOwner hp z))
    (hpath : ∀ z,(route z).IsPath)
    (he : Pairwise (fun z w => Disjoint (route z).edgeSet (route w).edgeSet))
    (ho : ∀ z,Disjoint (r.outline hp).edges (route z).edgeSet)
    {β : ℝ} (hβ : 0≤β)
    (hsoft : ∀ z,((routeInterior (route z)∩r.softVertices hp cores z).card:ℝ)≤
      β*(r.softVertices hp cores z).card) :
    ∃ P : CyclePacking G, P.used=(r.outline hp).edges∪(⋃ z,(route z).edgeSet) ∧
      (P.count:ℝ)≤1+β*p.length := by
  obtain ⟨P,hP,hcount⟩ := soft_outline_packing_with_budget (r.outline hp) route hpath he ho
    (r.route_interiors_disjoint hp cores hd route hr)
    (fun z => β*(r.softVertices hp cores z).card) (fun z => by
      rw [r.soft_collision_eq hp cores hd hA route hr z]
      exact hsoft z)
  refine ⟨P,hP,hcount.trans ?_⟩
  rw [←Finset.mul_sum]
  apply add_le_add (le_refl 1)
  apply mul_le_mul_of_nonneg_left _ hβ
  have hh := Nat.cast_le (α:=ℝ).mpr (r.softVertices_total hp cores hd)
  push_cast at hh
  convert hh using 1
  apply Finset.sum_congr
  · ext z; simp only [Finset.mem_univ]
  · intro z _; rfl


end RepresentedCyclePorts12
end
end Cycle12
