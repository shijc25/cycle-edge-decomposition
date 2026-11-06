import Cycle12.MatchingOriginalPorts12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def rotatedMatchingItem (M : (⊤ : SimpleGraph I).Subgraph) (next : Equiv.Perm M.edgeSet)
    (k : M.edgeSet × Bool) : I :=
  if k.2 then pairedOriginalItem M (next k.1,false) else pairedOriginalItem M (k.1,true)

theorem rotatedMatchingItem_injective (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (next : Equiv.Perm M.edgeSet) : Function.Injective (rotatedMatchingItem M next) := by
  rintro ⟨e,c⟩ ⟨f,d⟩ he
  cases c <;> cases d <;> simp only [rotatedMatchingItem,Bool.false_eq_true,ite_false,ite_true] at he
  · have hh := pairedOriginalItem_injective M hM he
    have hef : e=f := congrArg Prod.fst hh
    rw [hef]
  · have hh := pairedOriginalItem_injective M hM he
    have hh' : (true:Bool)=false := congrArg Prod.snd hh
    cases hh'
  · have hh := pairedOriginalItem_injective M hM he
    have hh' : (false:Bool)=true := congrArg Prod.snd hh
    cases hh'
  · have hh := pairedOriginalItem_injective M hM he
    have hef : e=f := next.injective (congrArg Prod.fst hh)
    rw [hef]

/-- Occurrences for the alternating routes on both sides of one original
matching. The U-side reconnection is a permutation of its original ports. -/
def matchingDemandPick (M : (⊤ : SimpleGraph I).Subgraph) (next : Equiv.Perm M.edgeSet)
    (k : (M.edgeSet ⊕ M.edgeSet) × Bool) : I × Bool :=
  match k.1 with
  | .inl e => (rotatedMatchingItem M next (e,k.2),false)
  | .inr e => (pairedOriginalItem M (e,k.2),true)

theorem matchingDemandPick_injective (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (next : Equiv.Perm M.edgeSet) : Function.Injective (matchingDemandPick M next) := by
  rintro ⟨e,c⟩ ⟨f,d⟩ he
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hh := rotatedMatchingItem_injective M hM next (congrArg Prod.fst he)
      have hee := congrArg Prod.fst hh
      have hcd := congrArg Prod.snd hh
      dsimp only at hee hcd
      rw [hee,hcd]
    | inr f =>
      have hh : (false:Bool)=true := congrArg Prod.snd he
      cases hh
  | inr e =>
    cases f with
    | inl f =>
      have hh : (true:Bool)=false := congrArg Prod.snd he
      cases hh
    | inr f =>
      have hh := pairedOriginalItem_injective M hM (congrArg Prod.fst he)
      have hee := congrArg Prod.fst hh
      have hcd := congrArg Prod.snd hh
      dsimp only at hee hcd
      rw [hee,hcd]

/-- Each directed occurrence of an oriented original edge is distinct.
The edge map, rather than a vertex degree bound, suffices here. -/
theorem oriented_edge_incidence_injective (a b : I → V) (hne : ∀ i,a i ≠ b i)
    (hedge : Function.Injective (fun i => s(a i,b i))) :
    Function.Injective (fun k : I × Bool =>
      ((if k.2 then b k.1 else a k.1),(if k.2 then a k.1 else b k.1))) := by
  rintro ⟨i,c⟩ ⟨j,d⟩ he
  have hij : i=j := by
    apply hedge
    have hh := congrArg (fun p : V × V => s(p.1,p.2)) he
    cases c <;> cases d <;> simpa [Sym2.eq_swap] using hh
  subst j
  have hcd : c=d := by
    have hv := congrArg Prod.fst he
    cases c <;> cases d <;> simp_all [eq_comm]
  rw [hcd]

/-- Both sides of every alternating matching group have one joint
incidence injection into the original matching edges. The permutation
may rotate separately within any chosen even groups. -/
theorem matching_demands_original_incidences (F : SimpleGraph V)
    (a b : I → V) (ha : ∀ i,F.Adj (a i) (b i))
    (hedge : Function.Injective (fun i => s(a i,b i)))
    (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (next : Equiv.Perm M.edgeSet) :
    let root := fun k : (M.edgeSet ⊕ M.edgeSet) × Bool =>
      if (matchingDemandPick M next k).2 then b (matchingDemandPick M next k).1
      else a (matchingDemandPick M next k).1
    ∃ neighbor : (M.edgeSet ⊕ M.edgeSet) × Bool → V,
      (∀ k,F.Adj (root k) (neighbor k) ∧
        s(root k,neighbor k)∈F.edgeSet) ∧
      Function.Injective (fun k => (root k,neighbor k)) := by
  dsimp only
  let neighbor := fun k : (M.edgeSet ⊕ M.edgeSet) × Bool =>
    if (matchingDemandPick M next k).2 then a (matchingDemandPick M next k).1
    else b (matchingDemandPick M next k).1
  refine ⟨neighbor,?_,?_⟩
  · intro k
    have hh : F.Adj
        (if (matchingDemandPick M next k).2 then b (matchingDemandPick M next k).1
          else a (matchingDemandPick M next k).1) (neighbor k) := by
      dsimp only [neighbor]
      split_ifs <;> first | exact (ha _).symm | exact ha _
    exact ⟨hh,hh⟩
  · exact (oriented_edge_incidence_injective a b (fun i => (ha i).ne) hedge).comp
      (matchingDemandPick_injective M hM next)


theorem pairedOriginalItem_mem (M : (⊤ : SimpleGraph I).Subgraph) (k : M.edgeSet × Bool) :
    pairedOriginalItem M k∈M.verts := by
  rcases k with ⟨e,d⟩
  have hh := edge_out_adj M.spanningCoe e
  cases d
  · exact hh.fst_mem
  · exact hh.snd_mem

theorem matchingDemandPick_mem (M : (⊤ : SimpleGraph I).Subgraph)
    (next : Equiv.Perm M.edgeSet) (k : (M.edgeSet ⊕ M.edgeSet) × Bool) :
    (matchingDemandPick M next k).1∈M.verts := by
  rcases k with ⟨e,d⟩
  cases e with
  | inl e =>
    cases d
    · exact pairedOriginalItem_mem M (e,true)
    · exact pairedOriginalItem_mem M (next e,false)
  | inr e => exact pairedOriginalItem_mem M (e,d)

/-- Matching requests use only paired original edges. The one retained
unpaired representative is excluded, which permits joint quotient routing. -/
theorem matching_demands_class_incidences (F : SimpleGraph V)
    (a b : I → V) (ha : ∀ i,F.Adj (a i) (b i))
    (hedge : Function.Injective (fun i => s(a i,b i)))
    (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (next : Equiv.Perm M.edgeSet) (S : Set (Sym2 V))
    (hS : ∀ i,i∈M.verts → s(a i,b i)∈S) :
    let root := fun k : (M.edgeSet ⊕ M.edgeSet) × Bool =>
      if (matchingDemandPick M next k).2 then b (matchingDemandPick M next k).1
      else a (matchingDemandPick M next k).1
    ∃ neighbor : (M.edgeSet ⊕ M.edgeSet) × Bool → V,
      (∀ k,F.Adj (root k) (neighbor k) ∧ s(root k,neighbor k)∈S) ∧
      Function.Injective (fun k => (root k,neighbor k)) := by
  dsimp only
  let neighbor := fun k : (M.edgeSet ⊕ M.edgeSet) × Bool =>
    if (matchingDemandPick M next k).2 then a (matchingDemandPick M next k).1
    else b (matchingDemandPick M next k).1
  refine ⟨neighbor,?_,?_⟩
  · intro k
    have hm := hS _ (matchingDemandPick_mem M next k)
    dsimp only [neighbor]
    split_ifs
    · exact ⟨(ha _).symm,by rwa [Sym2.eq_swap]⟩
    · exact ⟨ha _,hm⟩
  · exact (oriented_edge_incidence_injective a b (fun i => (ha i).ne) hedge).comp
      (matchingDemandPick_injective M hM next)

end
end Cycle12
