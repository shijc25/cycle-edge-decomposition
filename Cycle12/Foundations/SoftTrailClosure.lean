import Cycle12.Foundations.ClosedTrailDecomposition
import Cycle12.Foundations.HaxellRoutingSelect

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]

theorem path_support_card {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) : p.support.toFinset.card=p.length+1 := by
  rw [List.toFinset_card_of_nodup hp.support_nodup,p.length_support]

theorem routeInterior_path_card {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (huv : u ≠ v) :
    (routeInterior p).card+1=p.length := by
  have hs : ({u,v}:Finset V) ⊆ p.support.toFinset := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  have hi : p.support.toFinset\{u,v}=routeInterior p := by
    ext x
    simp only [mem_sdiff,mem_insert,mem_singleton,List.mem_toFinset,mem_routeInterior_iff]
    tauto
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [hi,path_support_card p hp] at hc
  have htwo : ({u,v}:Finset V).card=2 := by simp [huv]
  rw [htwo] at hc
  omega

theorem reverse_endpoints_soft_intersection {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : G.Walk v u) :
    routeInterior q∩p.support.toFinset=routeInterior q∩routeInterior p := by
  ext x
  simp only [mem_inter,mem_routeInterior_iff,List.mem_toFinset]
  tauto

/-- A return path may meet the original path internally. Each such
intersection pays for at most one additional simple cycle; all edges are
retained exactly once. No disjoint-interior hypothesis is used. -/
theorem paths_soft_cycle_closure {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : G.Walk v u) (huv : u ≠ v)
    (hp : p.IsPath) (hq : q.IsPath) (hedge : Disjoint p.edgeSet q.edgeSet) :
    ∃ P : CyclePacking G, P.used=p.edgeSet∪q.edgeSet ∧
      P.count ≤ 1+(routeInterior q∩p.support.toFinset).card := by
  have ht : (p.append q).IsTrail := by
    apply (Walk.isTrail_append p q).mpr
    refine ⟨hp.isTrail,hq.isTrail,?_⟩
    intro e he he'
    exact Set.disjoint_left.mp hedge he he'
  obtain ⟨P,hused,hcount⟩ := closed_trail_cycle_decomposition (p.append q) ht
  have hs : (p.append q).support.toFinset=p.support.toFinset∪q.support.toFinset := by
    ext x
    simp only [List.mem_toFinset,mem_union,Walk.mem_support_append_iff]
  have hports : ({u,v}:Finset V) ⊆ p.support.toFinset∩q.support.toFinset := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  have hinter : (p.support.toFinset∩q.support.toFinset)\{u,v}=
      routeInterior q∩p.support.toFinset := by
    ext x
    simp only [mem_sdiff,mem_inter,mem_routeInterior_iff,List.mem_toFinset,
      mem_insert,mem_singleton]
    tauto
  have hi := Finset.card_sdiff_add_card_eq_card hports
  rw [hinter] at hi
  have htwo : ({u,v}:Finset V).card=2 := by simp [huv]
  rw [htwo] at hi
  have hsum := Finset.card_union_add_card_inter p.support.toFinset q.support.toFinset
  rw [path_support_card p hp,path_support_card q hq] at hsum
  rw [hs,Walk.length_append] at hcount
  refine ⟨P,by simpa only [Walk.edgeSet_append] using hused,?_⟩
  omega

namespace CyclePacking
variable {G : SimpleGraph V}

/-- Assemble packings in one ambient graph, assuming only edge disjointness
of their actual used sets. Shared vertices impose no restriction. -/
def joinFamily (P : I → CyclePacking G)
    (hd : Pairwise (fun i j => Disjoint (P i).used (P j).used)) : CyclePacking G :=
  ofIndexed (I:=Σ i,Fin (P i).count) (fun x => (P x.1).parts x.2)
    (fun x => (P x.1).cycles x.2) (by
      rintro ⟨i,a⟩ ⟨j,b⟩ hne
      by_cases hij : i=j
      · subst j
        exact (P i).disjoint (fun hab => hne (by cases hab; rfl))
      · apply (hd hij).mono
        · exact Set.subset_iUnion (fun a => (P i).parts a) a
        · exact Set.subset_iUnion (fun b => (P j).parts b) b)

theorem count_joinFamily (P : I → CyclePacking G)
    (hd : Pairwise (fun i j => Disjoint (P i).used (P j).used)) :
    (joinFamily P hd).count=∑ i,(P i).count := by
  simp only [joinFamily,ofIndexed,Fintype.card_sigma,Fintype.card_fin]

theorem used_joinFamily (P : I → CyclePacking G)
    (hd : Pairwise (fun i j => Disjoint (P i).used (P j).used)) :
    (joinFamily P hd).used=⋃ i,(P i).used := by
  unfold joinFamily
  calc
    _ = ⋃ x : (Σ i,Fin (P i).count),(P x.1).parts x.2 := used_ofIndexed _ _ _
    _ = _ := by simp only [Set.iUnion_sigma,used]

end CyclePacking

/-- The simultaneous version preserves every original and routing edge
and sums the exact integral intersection charges, without adding a unit
cost for every routed demand. -/
theorem paths_soft_family_closure {G : SimpleGraph V} (source target : I → V)
    (p : ∀ i,G.Walk (source i) (target i))
    (q : ∀ i,G.Walk (target i) (source i))
    (hne : ∀ i,source i ≠ target i)
    (hp : ∀ i,(p i).IsPath) (hq : ∀ i,(q i).IsPath)
    (hcross : ∀ i,Disjoint (p i).edgeSet (q i).edgeSet)
    (hd : Pairwise (fun i j => Disjoint ((p i).edgeSet∪(q i).edgeSet)
      ((p j).edgeSet∪(q j).edgeSet))) :
    ∃ P : CyclePacking G, P.used=⋃ i,((p i).edgeSet∪(q i).edgeSet) ∧
      P.count ≤ Fintype.card I+∑ i,(routeInterior (q i)∩(p i).support.toFinset).card := by
  choose P hused hcount using fun i => paths_soft_cycle_closure
    (p i) (q i) (hne i) (hp i) (hq i) (hcross i)
  have hP : Pairwise (fun i j => Disjoint (P i).used (P j).used) := by
    intro i j hij
    rw [hused i,hused j]
    exact hd hij
  refine ⟨CyclePacking.joinFamily P hP,?_,?_⟩
  · simp only [CyclePacking.used_joinFamily,hused]
  · rw [CyclePacking.count_joinFamily]
    have hb := Finset.sum_le_sum (fun i (_ : i∈(univ:Finset I)) => hcount i)
    simpa only [sum_add_distrib,sum_const,card_univ,smul_eq_mul,mul_one] using hb

end
end Cycle13
