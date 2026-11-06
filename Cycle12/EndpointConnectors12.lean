import Cycle12.ReservoirRepresentatives12

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype I] [DecidableEq I] [DecidableEq V]

def endpointConflictGraph (source : I × Bool → V) : SimpleGraph (I × Bool) where
  Adj k l := k ≠ l ∧ (source k = source l ∨ k.1 = l.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem endpointConflictGraph_degree (source : I × Bool → V)
    (hload : ∀ v, (univ.filter (fun k => source k = v)).card ≤ 2) (k : I × Bool) :
    (endpointConflictGraph source).degree k ≤ 4 := by
  let A := univ.filter (fun l => source l = source k)
  let B := univ.filter (fun l : I × Bool => l.1 = k.1)
  have hsub : (endpointConflictGraph source).neighborFinset k ⊆ A ∪ B := by
    intro l hl
    have hh := ((endpointConflictGraph source).mem_neighborFinset k l).mp hl
    rcases hh.2 with hs | hi
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hs.symm⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hi.symm⟩)
  have hB : B = univ.image (fun b : Bool => (k.1,b)) := by
    ext l
    simp only [B,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro hl
      exact ⟨l.2,Prod.ext hl.symm rfl⟩
    · rintro ⟨b,h⟩
      exact (congrArg Prod.fst h).symm
  have hb : B.card = 2 := by
    rw [hB,card_image_of_injective _ (fun b c h => congrArg Prod.snd h),card_univ,Fintype.card_bool]
  have ha : A.card ≤ 2 := hload (source k)
  have hc := (card_le_card hsub).trans (card_union_le A B)
  rw [card_neighborFinset_eq_degree] at hc
  omega

/-- A bank receives at most two connector requests from each old vertex.
The chosen edges are distinct and mates have distinct representatives. -/
theorem choose_endpoint_connectors [Nonempty V] (G : SimpleGraph V) (U : Finset V)
    (source : I × Bool → V) {r z : ℝ}
    (hz : 8192 ≤ z) (hzr : z ≤ r) (hsquare : 2112*r ≤ z^2)
    (hcard : (Fintype.card I:ℝ) ≤ r)
    (hload : ∀ v, (univ.filter (fun k => source k = v)).card ≤ 2)
    (hout : ∀ k, source k ∉ U)
    (hN : ∀ k, (15/16)*z ≤ ((U.filter (G.Adj (source k))).card:ℝ)) :
    ∃ f : I × Bool → V, (∀ k, f k ∈ U ∧ G.Adj (source k) (f k)) ∧
      (∀ i, f (i,false) ≠ f (i,true)) ∧
      Function.Injective (fun k => s(source k,f k)) ∧
      (∀ v, (univ.filter (fun k => f k = v)).card ≤ ⌈8*r/z⌉₊) ∧
      (⌈8*r/z⌉₊:ℝ) < z/64 := by
  obtain ⟨f,hf,hsep,hinj,hcap,hstrict⟩ := choose_reservoir_connectors G U source
    (endpointConflictGraph source) hz hzr hsquare
    (by simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]; linarith only [hcard])
    (endpointConflictGraph_degree source hload)
    (fun i j hij he => ⟨hij,Or.inl he⟩) hout hN
  refine ⟨f,hf,?_,hinj,hcap,hstrict⟩
  intro i
  exact hsep (i,false) (i,true) ⟨by simp,Or.inr rfl⟩

end
end Cycle12
