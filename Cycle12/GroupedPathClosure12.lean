import Cycle12.CyclicSegmentChain12
import Cycle12.SoftCycleCounting12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A whole nonempty group costs at most one cycle. Original paths may
have arbitrary length; the connecting paths avoid their vertices internally.
The result preserves every original and connecting edge exactly once. -/
theorem grouped_path_cycle_closure {n : ℕ} (a b : Fin (n+1) → V)
    (p : ∀ i,G.Walk (a i) (b i))
    (q : ∀ i,G.Walk (b i) (a (finRotate (n+1) i)))
    (hp : ∀ i,(p i).IsPath) (hq : ∀ i,(q i).IsPath)
    (hne : ∀ i,b i ≠ a (finRotate (n+1) i))
    (hv : Pairwise (fun i j => Disjoint (p i).support.toFinset (p j).support.toFinset))
    (hPP : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    (hQQ : Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet))
    (hPQ : ∀ i j,Disjoint (p i).edgeSet (q j).edgeSet)
    (hi : Pairwise (fun i j => Disjoint (routeInterior (q i)) (routeInterior (q j))))
    (hf : ∀ i j,Disjoint (routeInterior (q i)) (p j).support.toFinset) :
    ∃ P : CyclePacking G, P.used=(⋃ i,(p i).edgeSet)∪(⋃ i,(q i).edgeSet) ∧ P.count ≤ 1 := by
  let D := univ.biUnion (fun i => (p i).support.toFinset)
  let Z := fun i => routeInterior (q i)
  let t := fun i => (p i).append (q i)
  have ht : ∀ i,(t i).IsTrail := by
    intro i
    apply (Walk.isTrail_append _ _).mpr
    exact ⟨(hp i).isTrail,(hq i).isTrail,fun e he he' => Set.disjoint_left.mp (hPQ i i) he he'⟩
  have htd : Pairwise (fun i j => Disjoint (t i).edgeSet (t j).edgeSet) := by
    intro i j hij
    simp only [t,Walk.edgeSet_append]
    apply Set.disjoint_left.mpr
    rintro e (he | he) (he' | he')
    · exact Set.disjoint_left.mp (hPP hij) he he'
    · exact Set.disjoint_left.mp (hPQ i j) he he'
    · exact Set.disjoint_left.mp (hPQ j i) he' he
    · exact Set.disjoint_left.mp (hQQ hij) he he'
  have hDcard : D.card=(∑ i,(p i).length)+(n+1) := by
    rw [show D=univ.biUnion (fun i => (p i).support.toFinset) from rfl,
      Finset.card_biUnion (fun i _ j _ hij => hv hij)]
    simp_rw [path_support_card _ (hp _)]
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]
  have hQlen : (∑ i,(q i).length)=(∑ i,(Z i).card)+(n+1) := by
    have he (i) := routeInterior_path_card (q i) (hq i) (hne i)
    simp_rw [←he]
    simp only [Z,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]
  have hsupport : (cyclicSegmentWalk a t).support.toFinset=D∪univ.biUnion Z := by
    ext v
    simp only [List.mem_toFinset,cyclicSegmentWalk_support,t,Walk.mem_support_append_iff,
      D,Z,mem_union,mem_biUnion,mem_univ,true_and,List.mem_toFinset]
    constructor
    · rintro ⟨i,hv | hv⟩
      · exact Or.inl ⟨i,hv⟩
      · by_cases hb : v=b i
        · exact Or.inl ⟨i,hb.symm ▸ (p i).end_mem_support⟩
        by_cases ha : v=a (finRotate (n+1) i)
        · exact Or.inl ⟨finRotate (n+1) i,ha.symm ▸ (p _).start_mem_support⟩
        exact Or.inr ⟨i,(mem_routeInterior_iff _ _).mpr ⟨hv,hb,ha⟩⟩
    · rintro (⟨i,hv⟩ | ⟨i,hv⟩)
      · exact ⟨i,Or.inl hv⟩
      · exact ⟨i,Or.inr ((mem_routeInterior_iff _ _).mp hv).1⟩
  have hlength : (cyclicSegmentWalk a t).length=D.card+∑ i,(Z i).card := by
    rw [cyclicSegmentWalk_length]
    simp only [t,Walk.length_append,sum_add_distrib]
    rw [hQlen,hDcard]
    omega
  obtain ⟨P,hused,hcount⟩ := soft_closed_trail_count (cyclicSegmentWalk a t)
    (cyclicSegmentWalk_isTrail a t ht htd) D Z hi hsupport hlength
  have hzero (i) : (Z i∩D).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.mpr
    intro v hv hd
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hd
    exact Finset.disjoint_left.mp (hf i j) hv hj
  refine ⟨P,?_,by simpa only [hzero,sum_const_zero,add_zero] using hcount⟩
  rw [hused,cyclicSegmentWalk_edges]
  simp only [t,Walk.edgeSet_append,Set.iUnion_union_distrib]

end
end Cycle12
