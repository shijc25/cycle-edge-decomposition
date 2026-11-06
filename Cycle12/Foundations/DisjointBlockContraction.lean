import Cycle12.Foundations.Definitions

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def blockUnion (A : I → Finset V) : Finset V := univ.biUnion A

theorem mem_blockUnion (A : I → Finset V) (v : V) :
    v∈blockUnion A ↔ ∃ i,v∈A i := by simp [blockUnion]

/-- Each entire active block is replaced by one vertex. Every vertex
outside the blocks is retained with its original identity. -/
abbrev ContractedVertices (A : I → Finset V) := I ⊕ {v : V // v∉blockUnion A}

instance (A : I → Finset V) : Fintype (ContractedVertices A) :=
  inferInstanceAs (Fintype (I ⊕ {v : V // v∉blockUnion A}))

def contractVertex (A : I → Finset V) (v : V) : ContractedVertices A :=
  if h : ∃ i,v∈A i then Sum.inl h.choose
  else Sum.inr ⟨v,fun hv => h ((mem_blockUnion A v).mp hv)⟩

theorem contractVertex_of_mem (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {v : V} {i : I}
    (hv : v∈A i) : contractVertex A v=Sum.inl i := by
  unfold contractVertex
  split_ifs with h
  · congr 1
    by_contra hne
    exact Finset.disjoint_left.mp (hd hne) h.choose_spec hv
  · exact False.elim (h ⟨i,hv⟩)

theorem contractVertex_of_not_mem (A : I → Finset V) (v : V)
    (hv : v∉blockUnion A) : contractVertex A v=Sum.inr ⟨v,hv⟩ := by
  unfold contractVertex
  rw [dif_neg (fun h => hv ((mem_blockUnion A v).mpr h))]

theorem contractVertex_surjective (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hne : ∀ i,(A i).Nonempty) : Function.Surjective (contractVertex A) := by
  intro x
  cases x with
  | inl i => exact ⟨(hne i).choose,contractVertex_of_mem A hd (hne i).choose_spec⟩
  | inr v => exact ⟨v.val,contractVertex_of_not_mem A v.val v.property⟩

theorem contractVertex_eq_inl_iff (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (v : V) (i : I) :
    contractVertex A v=Sum.inl i ↔ v∈A i := by
  constructor
  · intro he
    unfold contractVertex at he
    split_ifs at he with h
    · have hi := Sum.inl.inj he
      exact hi ▸ h.choose_spec
  · exact contractVertex_of_mem A hd

theorem blockUnion_card (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (blockUnion A).card=∑ i,(A i).card := by
  exact Finset.card_biUnion (fun i _ j _ hij => hd hij)

/-- Exact order accounting, including vertices outside all active blocks. -/
theorem contracted_order_identity (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Fintype.card (ContractedVertices A)+(∑ i,(A i).card)=
      Fintype.card V+Fintype.card I := by
  have ho : Fintype.card {v : V // v∉blockUnion A}=(blockUnion A)ᶜ.card := by
    let e : {v : V // v∉blockUnion A} ≃ ↥((blockUnion A)ᶜ) :=
      Equiv.subtypeEquivRight (fun v => Finset.mem_compl.symm)
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  change Fintype.card (I ⊕ {v : V // v∉blockUnion A})+_= _
  rw [Fintype.card_sum,ho,Finset.card_compl,← blockUnion_card A hd]
  have hb := Finset.card_le_univ (blockUnion A)
  omega

/-- Uniform lower bounds on active block sizes give the exact contraction
saving used in the global potential, without counting any vertex twice. -/
theorem contracted_order_saving (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {L : ℝ} (hL : 0 < L) (hsize : ∀ i,L ≤ ((A i).card:ℝ)) :
    (Fintype.card (ContractedVertices A):ℝ) ≤
      Fintype.card V-(1-1/L)*(∑ i,((A i).card:ℝ)) := by
  have hi := contracted_order_identity A hd
  have hiR : (Fintype.card (ContractedVertices A):ℝ)+(∑ i,((A i).card:ℝ))=
      Fintype.card V+Fintype.card I := by exact_mod_cast hi
  have hs := Finset.sum_le_sum (fun i (_ : i∈(univ:Finset I)) => hsize i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have hn : (Fintype.card I:ℝ) ≤ (∑ i,((A i).card:ℝ))/L :=
    (le_div_iff₀ hL).mpr hs
  simp only [div_eq_mul_inv,one_mul] at hn ⊢
  nlinarith only [hiR,hn]

end
end Cycle13
