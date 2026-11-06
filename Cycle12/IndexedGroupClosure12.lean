import Cycle12.GroupedPathClosure12
import Cycle12.Foundations.PathEndpointLoad

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G : SimpleGraph V}

def finiteCycleNext (I : Type) [Fintype I] : Equiv.Perm I :=
  (Fintype.equivFin I).trans ((finRotate (Fintype.card I)).trans (Fintype.equivFin I).symm)

theorem finiteCycleNext_equivFin (i : Fin (Fintype.card I)) :
    finiteCycleNext I ((Fintype.equivFin I).symm i)=
      (Fintype.equivFin I).symm (finRotate (Fintype.card I) i) := by
  simp only [finiteCycleNext,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem grouped_path_cycle_closure_fin {n : ℕ} (a b : Fin n → V)
    (p : ∀ i,G.Walk (a i) (b i))
    (q : ∀ i,G.Walk (b i) (a (finRotate n i)))
    (hp : ∀ i,(p i).IsPath) (hq : ∀ i,(q i).IsPath)
    (hne : ∀ i,b i ≠ a (finRotate n i))
    (hv : Pairwise (fun i j => Disjoint (p i).support.toFinset (p j).support.toFinset))
    (hPP : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    (hQQ : Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet))
    (hPQ : ∀ i j,Disjoint (p i).edgeSet (q j).edgeSet)
    (hi : Pairwise (fun i j => Disjoint (routeInterior (q i)) (routeInterior (q j))))
    (hf : ∀ i j,Disjoint (routeInterior (q i)) (p j).support.toFinset) :
    ∃ P : CyclePacking G, P.used=(⋃ i,(p i).edgeSet)∪(⋃ i,(q i).edgeSet) ∧ P.count ≤ 1 := by
  cases n with
  | zero => exact ⟨CyclePacking.empty G,by simp [CyclePacking.used,CyclePacking.empty],by norm_num [CyclePacking.empty]⟩
  | succ n => exact grouped_path_cycle_closure a b p q hp hq hne hv hPP hQQ hPQ hi hf

/-- Arbitrary finite groups, including empty groups, are closed without
an existence assumption on the resulting cycles. -/
theorem indexed_group_cycle_closure (a b : I → V)
    (p : ∀ i,G.Walk (a i) (b i))
    (q : ∀ i,G.Walk (b i) (a (finiteCycleNext I i)))
    (hp : ∀ i,(p i).IsPath) (hq : ∀ i,(q i).IsPath)
    (hne : ∀ i,b i ≠ a (finiteCycleNext I i))
    (hv : Pairwise (fun i j => Disjoint (p i).support.toFinset (p j).support.toFinset))
    (hPP : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    (hQQ : Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet))
    (hPQ : ∀ i j,Disjoint (p i).edgeSet (q j).edgeSet)
    (hi : Pairwise (fun i j => Disjoint (routeInterior (q i)) (routeInterior (q j))))
    (hf : ∀ i j,Disjoint (routeInterior (q i)) (p j).support.toFinset) :
    ∃ P : CyclePacking G, P.used=(⋃ i,(p i).edgeSet)∪(⋃ i,(q i).edgeSet) ∧ P.count ≤ 1 := by
  let e := Fintype.equivFin I
  let q' := fun i => (q (e.symm i)).copy rfl (congrArg a (finiteCycleNext_equivFin i))
  obtain ⟨P,hP,hcount⟩ := grouped_path_cycle_closure_fin
    (fun i => a (e.symm i)) (fun i => b (e.symm i)) (fun i => p (e.symm i)) q'
    (fun i => hp _) (fun i => by simpa only [q',Walk.isPath_copy] using hq (e.symm i))
    (fun i => by simpa only [e,finiteCycleNext_equivFin] using hne (e.symm i))
    (fun i j hij => hv (e.symm.injective.ne hij))
    (fun i j hij => hPP (e.symm.injective.ne hij))
    (fun i j hij => by simpa only [q',Walk.edgeSet_copy] using hQQ (e.symm.injective.ne hij))
    (fun i j => by simpa only [q',Walk.edgeSet_copy] using hPQ (e.symm i) (e.symm j))
    (fun i j hij => by simpa only [q',routeInterior,Walk.support_copy,e,finiteCycleNext_equivFin] using hi (e.symm.injective.ne hij))
    (fun i j => by simpa only [q',routeInterior,Walk.support_copy,e,finiteCycleNext_equivFin] using hf (e.symm i) (e.symm j))
  refine ⟨P,?_,hcount⟩
  rw [hP]
  simp only [q',Walk.edgeSet_copy]
  have hu (S : I → Set (Sym2 V)) : (⋃ i,S (e.symm i))=⋃ i,S i := by
    ext d
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e i,by simpa using hi⟩
  rw [hu (fun i => (p i).edgeSet),hu (fun i => (q i).edgeSet)]

theorem filter_card_permute (e : Equiv.Perm I) (f : I → V) (v : V) :
    (univ.filter (fun i => f (e i)=v)).card=(univ.filter (fun i => f i=v)).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    exact ⟨e.symm j,by simpa using hj,e.apply_symm_apply j⟩

/-- Cyclically reconnecting endpoints preserves the entire endpoint load,
so grouping creates no additional demand at any vertex. -/
theorem cycle_reconnection_endpointLoad (a b : I → V) (next : Equiv.Perm I) (v : V) :
    endpointLoad b (fun i => a (next i)) v=endpointLoad a b v := by
  rw [endpointLoad,endpointLoad,filter_card_permute]
  omega

theorem cycle_reconnection_load_le_degree (F : SimpleGraph V) (a b : I → V)
    (p : ∀ i,F.Walk (a i) (b i)) (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    (next : Equiv.Perm I) (v : V) :
    endpointLoad b (fun i => a (next i)) v ≤ F.degree v := by
  rw [cycle_reconnection_endpointLoad]
  exact endpointLoad_le_original_degree F a b p hne hd v

end
end Cycle12
