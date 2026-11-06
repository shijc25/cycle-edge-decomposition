import Cycle12.Foundations.PartitionListColoring
import Cycle12.Foundations.DirectLinkAssembly

/-! DY Lemma 6: complete multipartite graphs of minimum degree at least t
strongly immerse K_t. A direct blockwise HJ construction avoids induction. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def samePartGraph {W A : Type} (r : W → A) : SimpleGraph W where
  Adj x y := x ≠ y ∧ r x=r y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem strong_model_of_partite_branches {V A : Type} [DecidableEq V] {t : ℕ}
    (G : SimpleGraph V) (r : V → A) (φ : Fin t ↪ V) (D : Finset V)
    (hout : ∀ i, φ i ∉ D) (hcross : ∀ x y, r x ≠ r y → G.Adj x y)
    (hroom : ∀ i, (univ.filter (fun j => r (φ j)=r (φ i))).card ≤
      (D.filter (fun v => r v ≠ r (φ i))).card) :
    Nonempty (StrongCliqueImmersion t G) := by
  classical
  let R := samePartGraph (r ∘ φ)
  let L := fun e : R.edgeSet => commonChoices G D (φ e.val.out.1) (φ e.val.out.2)
  obtain ⟨f,hf⟩ := exists_list_edge_coloring_partition R (r ∘ φ)
    (fun _ _ h => h.2) L (by
      intro e i hi
      have he := edge_out_adj R e
      have hout' : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
      have hir : r (φ i)=r (φ e.val.out.1) := by
        rw [← hout'] at hi
        rcases Sym2.mem_iff.mp hi with rfl | rfl
        · rfl
        · exact he.2.symm
      have hsub : D.filter (fun v => r v ≠ r (φ e.val.out.1)) ⊆ L e := by
        intro v hv
        obtain ⟨hvD,hv⟩ := mem_filter.mp hv
        apply mem_filter.mpr
        refine ⟨hvD,hcross _ _ hv.symm,hcross _ _ ?_⟩
        have he' : r (φ e.val.out.1)=r (φ e.val.out.2) := he.2
        exact fun h => hv (h.symm.trans he'.symm)
      change (univ.filter (fun j => r (φ j)=r (φ i))).card ≤ (L e).card
      rw [hir]
      exact (hroom _).trans (card_le_card hsub))
  let K : ReservoirLinks R G D φ := {
    color := f
    mem := fun e => (mem_filter.mp (hf e)).1
    adjacent := by
      intro e v hv
      have hout' : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
      rw [← hout'] at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact (mem_filter.mp (hf e)).2.1
      · exact (mem_filter.mp (hf e)).2.2 }
  exact ⟨(K.completedRouting (fun x y h => hcross _ _ (by
    have h' := (compl_adj R x y).mp h
    exact fun he => h'.2 ⟨h'.1,he⟩)) hout).cliqueModel⟩

lemma outside_selected_block_count {V A : Type} [Fintype V] [DecidableEq V] {t : ℕ}
    (r : V → A) (φ : Fin t ↪ V) (i : Fin t)
    (hdeg : t ≤ (univ.filter (fun v : V => r v ≠ r (φ i))).card) :
    (univ.filter (fun j => r (φ j)=r (φ i))).card ≤
      ((univ \ univ.image φ).filter (fun v => r v ≠ r (φ i))).card := by
  classical
  let X := univ.filter (fun v : V => r v ≠ r (φ i))
  let B := univ.image φ
  let J := univ.filter (fun j => r (φ j) ≠ r (φ i))
  have hinter : X ∩ B=J.image φ := by
    ext v
    simp only [X,B,J,mem_inter,mem_filter,mem_univ,true_and,mem_image]
    aesop
  have hsplit := card_sdiff_add_card_inter X B
  rw [hinter,card_image_of_injective _ φ.injective] at hsplit
  have hclasses := card_filter_add_card_filter_not (s := (univ : Finset (Fin t)))
    (fun j => r (φ j)=r (φ i))
  simp only [card_univ,Fintype.card_fin] at hclasses
  have heq : (univ \ univ.image φ).filter (fun v => r v ≠ r (φ i))=X \ B := by
    ext v
    simp [X,B,and_left_comm,and_comm]
  rw [heq]
  change t ≤ X.card at hdeg
  change (univ.filter (fun j => r (φ j)=r (φ i))).card+J.card=t at hclasses
  omega

theorem strong_model_of_complete_multipartite {V A : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (r : V → A) (t : ℕ)
    (hcross : ∀ x y, r x ≠ r y → G.Adj x y)
    (hdeg : ∀ v, t ≤ (univ.filter (fun w => r w ≠ r v)).card) :
    Nonempty (StrongCliqueImmersion t G) := by
  classical
  let v₀ : V := Classical.choice inferInstance
  have htV : t ≤ Fintype.card V := (hdeg v₀).trans (by simpa using card_filter_le univ _)
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin t) ≤ Fintype.card V by simpa using htV)
  exact strong_model_of_partite_branches G r φ (univ \ univ.image φ)
    (by intro i; simp) hcross (fun i => outside_selected_block_count r φ i (hdeg (φ i)))

end
end Cycle13
