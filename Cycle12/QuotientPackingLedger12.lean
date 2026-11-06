import Cycle12.Foundations.SimpleEdgeQuotient
import Cycle12.Foundations.SoftTrailClosure
import Cycle12.PackingCompletionLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W]

/-- Unique original representatives preserve the cardinality of every
quotient edge subset, including the singleton residue of a packing. -/
theorem quotient_edge_pullback_card (H : SimpleGraph V) (π : V → W)
    (hproper : ∀ {x y}, H.Adj x y → π x≠π y)
    (hunique : Set.InjOn (Sym2.map π) H.edgeSet)
    (S : Set (Sym2 W)) (hS : S⊆(H.map π).edgeSet) :
    (H.edgeSet∩Sym2.map π ⁻¹' S).ncard=S.ncard := by
  have he : Sym2.map π '' (H.edgeSet∩Sym2.map π ⁻¹' S)=S := by
    apply Set.Subset.antisymm
    · rintro e ⟨d,hd,rfl⟩
      exact hd.2
    · intro e he
      have hm := hS he
      rw [edgeSet_map_of_no_internal H π hproper] at hm
      obtain ⟨d,hd,hde⟩ := hm
      exact ⟨d,⟨hd,by change Sym2.map π d∈S; rwa [hde]⟩,hde⟩
  calc
    _ = (Sym2.map π '' (H.edgeSet∩Sym2.map π ⁻¹' S)).ncard :=
      (hunique.mono Set.inter_subset_left).ncard_image.symm
    _ = _ := congrArg Set.ncard he

theorem quotient_packing_pullback_singles (H : SimpleGraph V) (π : V → W)
    (hproper : ∀ {x y}, H.Adj x y → π x≠π y)
    (hunique : Set.InjOn (Sym2.map π) H.edgeSet)
    (Q : CyclePacking (H.map π)) :
    (H.edgeSet\(H.edgeSet∩Sym2.map π ⁻¹' Q.used)).ncard=Q.singles := by
  have he : H.edgeSet\(H.edgeSet∩Sym2.map π ⁻¹' Q.used)=
      H.edgeSet∩Sym2.map π ⁻¹' Q.residue.edgeSet := by
    rw [CyclePacking.residue,SimpleGraph.edgeSet_deleteEdges]
    ext e
    have hm : e∈H.edgeSet → Sym2.map π e∈(H.map π).edgeSet :=
      (SimpleGraph.Hom.map π H hproper).map_mem_edgeSet
    simp only [Set.mem_sdiff,Set.mem_inter_iff,Set.mem_preimage]
    tauto
  rw [he]
  exact quotient_edge_pullback_card H π hproper hunique Q.residue.edgeSet
    (SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _))

/-- A lifted quotient packing retains exactly the quotient's singleton
cost. The only additional cost is the actual extra number of cycles. -/
theorem lifted_quotient_weight (G H : SimpleGraph V) (π : V → W)
    (hproper : ∀ {x y}, H.Adj x y → π x≠π y)
    (hunique : Set.InjOn (Sym2.map π) H.edgeSet)
    (Q : CyclePacking (H.map π)) (P : CyclePacking G) (R : Set (Sym2 V))
    (hcover : G.edgeSet=H.edgeSet∪R) (hdis : Disjoint H.edgeSet R)
    (hused : P.used=(H.edgeSet∩Sym2.map π ⁻¹' Q.used)∪R)
    {fee : ℝ} (hcount : (P.count:ℝ)≤Q.count+fee) :
    P.weight≤Q.weight+fee := by
  have hres : P.residue.edgeSet=H.edgeSet\(H.edgeSet∩Sym2.map π ⁻¹' Q.used) := by
    rw [CyclePacking.residue,SimpleGraph.edgeSet_deleteEdges,hcover,hused]
    ext e
    have hd := Set.disjoint_left.mp hdis
    simp only [Set.mem_sdiff,Set.mem_union,Set.mem_inter_iff,Set.mem_preimage]
    constructor
    · rintro ⟨he,hn⟩
      have heH : e∈H.edgeSet := he.resolve_right (fun hr => hn (Or.inr hr))
      exact ⟨heH,fun h => hn (Or.inl h)⟩
    · rintro ⟨he,hn⟩
      exact ⟨Or.inl he,fun h => h.elim hn (hd he)⟩
  have hs : P.singles=Q.singles := by
    rw [CyclePacking.singles,hres]
    exact quotient_packing_pullback_singles H π hproper hunique Q
  change (P.count:ℝ)+(23/42:ℝ)*P.singles ≤
    (Q.count:ℝ)+(23/42:ℝ)*Q.singles+fee
  rw [hs]
  linarith only [hcount]

/-- Disjoint original representatives and disjoint added routing edges
give a genuine packing after all quotient cycles are lifted. -/
theorem quotient_cycle_family_assembly (G H : SimpleGraph V) (π : V → W)
    (Q : CyclePacking (H.map π))
    (P : Fin Q.count → CyclePacking G) (R : Fin Q.count → Set (Sym2 V))
    (hused : ∀ i, (P i).used=(H.edgeSet∩Sym2.map π ⁻¹' Q.parts i)∪R i)
    (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hcross : ∀ i, Disjoint H.edgeSet (R i))
    (fee : Fin Q.count → ℝ) (hfee : ∀ i, ((P i).count:ℝ)≤1+fee i) :
    ∃ T : CyclePacking G,
      T.used=(H.edgeSet∩Sym2.map π ⁻¹' Q.used)∪(⋃ i,R i) ∧
      (T.count:ℝ)≤Q.count+∑ i,fee i := by
  have hd : Pairwise (fun i j => Disjoint (P i).used (P j).used) := by
    intro i j hij
    rw [hused i,hused j]
    apply Set.disjoint_left.mpr
    rintro e (he | he) (hf | hf)
    · exact Set.disjoint_left.mp (Q.disjoint hij) he.2 hf.2
    · exact Set.disjoint_left.mp (hcross j) he.1 hf
    · exact Set.disjoint_left.mp (hcross i) hf.1 he
    · exact Set.disjoint_left.mp (hR hij) he hf
  refine ⟨CyclePacking.joinFamily P hd,?_,?_⟩
  · rw [CyclePacking.used_joinFamily]
    simp_rw [hused]
    simp only [CyclePacking.used,Set.preimage_iUnion,Set.inter_iUnion]
    ext e
    simp only [Set.mem_iUnion,Set.mem_union]
    aesop
  · rw [CyclePacking.count_joinFamily]
    have hh := Finset.sum_le_sum (fun i (_ : i∈(univ:Finset (Fin Q.count))) => hfee i)
    simpa only [Nat.cast_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one] using hh

end
end Cycle12
