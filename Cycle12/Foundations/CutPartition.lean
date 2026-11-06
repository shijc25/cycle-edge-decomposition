import Cycle12.Foundations.GraphBranchCut

/-! Exact cut identities for a partition of a vertex set. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem interedges_card_union_left (G : SimpleGraph V) (A B C : Finset V)
    (hAB : Disjoint A B) :
    (G.interedges (A∪B) C).card = (G.interedges A C).card+(G.interedges B C).card := by
  have he : G.interedges (A∪B) C=G.interedges A C∪G.interedges B C := by
    simp only [interedges_def,union_product,filter_union]
  rw [he,card_union_of_disjoint (G.interedges_disjoint_left hAB C)]

theorem interedges_card_union_right (G : SimpleGraph V) (A B C : Finset V)
    (hBC : Disjoint B C) :
    (G.interedges A (B∪C)).card = (G.interedges A B).card+(G.interedges A C).card := by
  have he : G.interedges A (B∪C)=G.interedges A B∪G.interedges A C := by
    simp only [interedges_def,product_union,filter_union]
  rw [he,card_union_of_disjoint (G.interedges_disjoint_right A hBC)]

theorem interedges_card_symm (G : SimpleGraph V) (A B : Finset V) :
    (G.interedges A B).card=(G.interedges B A).card := by
  have := G.symm
  exact Rel.card_interedges_comm (r := G.Adj) A B

theorem cut_partition_identity (G : SimpleGraph V) (S T : Finset V) (hTS : T ⊆ S) :
    cutSize G T+cutSize G (S\T)=cutSize G S+2*(G.interedges T (S\T)).card := by
  have h₁ : Tᶜ=(S\T)∪Sᶜ := by ext v; simp only [mem_compl,mem_union,mem_sdiff]; grind
  have h₂ : (S\T)ᶜ=T∪Sᶜ := by ext v; simp only [mem_compl,mem_union,mem_sdiff]; grind
  have h₃ : S=T∪(S\T) := (union_sdiff_of_subset hTS).symm
  have hd₁ : Disjoint (S\T) Sᶜ := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    exact (mem_compl.mp hn) (mem_sdiff.mp hv).1
  have hd₂ : Disjoint T Sᶜ := disjoint_compl_right.mono_left hTS
  have hd₃ : Disjoint T (S\T) := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    exact (mem_sdiff.mp hn).2 hv
  simp only [cutSize_eq_interedges]
  rw [h₁,h₂,interedges_card_union_right G T _ _ hd₁,
    interedges_card_union_right G (S\T) _ _ hd₂,
    interedges_card_symm G (S\T) T]
  have hsum := interedges_card_union_left G T (S\T) Sᶜ hd₃
  rw [← h₃] at hsum
  rw [hsum]
  omega

theorem interedges_card_comap {U : Type} [Fintype U] [DecidableEq U]
    (G : SimpleGraph V) (f : U ↪ V) (A B : Finset U) :
    ((G.comap f).interedges A B).card=(G.interedges (A.image f) (B.image f)).card := by
  apply card_bij (fun e _ => (f e.1,f e.2))
  · intro e he
    have hh := ((G.comap f).mem_interedges_iff).mp he
    exact G.mem_interedges_iff.mpr ⟨mem_image_of_mem _ hh.1,mem_image_of_mem _ hh.2.1,hh.2.2⟩
  · intro a ha b hb hab
    exact Prod.ext (f.injective (congrArg Prod.fst hab)) (f.injective (congrArg Prod.snd hab))
  · intro e he
    have hh := G.mem_interedges_iff.mp he
    obtain ⟨a,ha,hea⟩ := mem_image.mp hh.1
    obtain ⟨b,hb,heb⟩ := mem_image.mp hh.2.1
    refine ⟨(a,b),(G.comap f).mem_interedges_iff.mpr ⟨ha,hb,?_⟩,?_⟩
    · change G.Adj (f a) (f b)
      simpa only [hea,heb] using hh.2.2
    · exact Prod.ext hea heb

theorem cutSize_induce (G : SimpleGraph V) (S : Finset V) (T : Finset S) :
    cutSize (G.induce (S : Set V)) T=
      (G.interedges (T.image Subtype.val) (S\T.image Subtype.val)).card := by
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (Tᶜ.image f)=S\T.image Subtype.val := by
    ext v
    simp only [mem_image,mem_compl,mem_sdiff]
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      rintro ⟨y,hy,hyx⟩
      exact hx (by simpa only [Subtype.ext hyx] using hy)
    · rintro ⟨hv,hn⟩
      refine ⟨⟨v,hv⟩,?_,rfl⟩
      intro hx
      exact hn ⟨⟨v,hv⟩,hx,rfl⟩
  rw [cutSize_eq_interedges]
  change ((G.comap f).interedges T Tᶜ).card=_
  rw [interedges_card_comap,he]
  rfl

end
end Cycle13
