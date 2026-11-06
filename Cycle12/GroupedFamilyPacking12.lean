import Cycle12.GroupedDemandData12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I T : Type} [Fintype V] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I] [DecidableEq T] {G : SimpleGraph V}

/-- Close all groups after one simultaneous routing call. Vertex
disjointness is required within groups only; all used edges are accounted
for globally, and the cycle charge is the number of groups. -/
theorem grouped_family_cycle_packing (group : I → T) (a b : I → V)
    (p : ∀ i,G.Walk (a i) (b i))
    (q : ∀ i,G.Walk (b i) (a (groupedCycleNext group i)))
    (hp : ∀ i,(p i).IsPath) (hq : ∀ i,(q i).IsPath)
    (hne : ∀ i,b i ≠ a (groupedCycleNext group i))
    (hv : ∀ i j,i ≠ j → group i=group j →
      Disjoint (p i).support.toFinset (p j).support.toFinset)
    (hPP : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    (hQQ : Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet))
    (hPQ : ∀ i j,Disjoint (p i).edgeSet (q j).edgeSet)
    (hi : ∀ i j,i ≠ j → group i=group j →
      Disjoint (routeInterior (q i)) (routeInterior (q j)))
    (hf : ∀ i j,group i=group j → Disjoint (routeInterior (q i)) (p j).support.toFinset) :
    ∃ P : CyclePacking G, P.used=(⋃ i,(p i).edgeSet)∪(⋃ i,(q i).edgeSet) ∧
      P.count ≤ Fintype.card T := by
  have hlocal (t : T) : ∃ P : CyclePacking G,
      P.used=(⋃ i : {i : I // group i=t},(p i.val).edgeSet)∪
        (⋃ i : {i : I // group i=t},(q i.val).edgeSet) ∧ P.count ≤ 1 := by
    let q' := fun i : {i : I // group i=t} => (q i.val).copy rfl
      (congrArg a (groupedCycleNext_on_fiber group t i))
    obtain ⟨P,hP,hc⟩ := indexed_group_cycle_closure
      (fun i : {i : I // group i=t} => a i.val) (fun i => b i.val)
      (fun i => p i.val) q' (fun i => hp i.val)
      (fun i => by simpa only [q',Walk.isPath_copy] using hq i.val)
      (fun i => by simpa only [groupedCycleNext_on_fiber group t i] using hne i.val)
      (fun i j hij => hv i.val j.val (Subtype.val_injective.ne hij) (i.property.trans j.property.symm))
      (fun i j hij => hPP (Subtype.val_injective.ne hij))
      (fun i j hij => by simpa only [q',Walk.edgeSet_copy] using hQQ (Subtype.val_injective.ne hij))
      (fun i j => by simpa only [q',Walk.edgeSet_copy] using hPQ i.val j.val)
      (fun i j hij => by
        simpa only [q',routeInterior,Walk.support_copy,groupedCycleNext_on_fiber group t i,
          groupedCycleNext_on_fiber group t j] using
          hi i.val j.val (Subtype.val_injective.ne hij) (i.property.trans j.property.symm))
      (fun i j => by
        simpa only [q',routeInterior,Walk.support_copy,groupedCycleNext_on_fiber group t i] using
          hf i.val j.val (i.property.trans j.property.symm))
    exact ⟨P,by simpa only [q',Walk.edgeSet_copy] using hP,hc⟩
  choose P hused hcount using hlocal
  have hd : Pairwise (fun t u => Disjoint (P t).used (P u).used) := by
    intro t u htu
    rw [hused t,hused u]
    apply Set.disjoint_left.mpr
    intro e he hf
    have hne' (i : {i : I // group i=t}) (j : {i : I // group i=u}) : i.val ≠ j.val := by
      intro hij
      exact htu (i.property.symm.trans ((congrArg group hij).trans j.property))
    rcases he with he|he <;> rcases hf with hf|hf <;>
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he <;> obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hf
    · exact Set.disjoint_left.mp (hPP (hne' i j)) hi hj
    · exact Set.disjoint_left.mp (hPQ i.val j.val) hi hj
    · exact Set.disjoint_left.mp (hPQ j.val i.val) hj hi
    · exact Set.disjoint_left.mp (hQQ (hne' i j)) hi hj
  refine ⟨CyclePacking.joinFamily P hd,?_,?_⟩
  · rw [CyclePacking.used_joinFamily]
    simp only [hused]
    ext e
    simp only [Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨t,⟨i,hi⟩|⟨i,hi⟩⟩
      · exact Or.inl ⟨i.val,hi⟩
      · exact Or.inr ⟨i.val,hi⟩
    · rintro (⟨i,hi⟩|⟨i,hi⟩)
      · exact ⟨group i,Or.inl ⟨⟨i,rfl⟩,hi⟩⟩
      · exact ⟨group i,Or.inr ⟨⟨i,rfl⟩,hi⟩⟩
  · rw [CyclePacking.count_joinFamily]
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] using
      Finset.sum_le_sum (fun t (_ : t∈(univ:Finset T)) => hcount t)

end
end Cycle12
