import LeanPool.ListEdgeColoringComplete

/-! Häggkvist--Janssen for arbitrary simple subgraphs, with no extra colours
in the conclusion. The imported proof is pinned and independently rebuilt. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section

theorem exists_list_edge_coloring {V C : Type} [Fintype V]
    (R : SimpleGraph V) (L : R.edgeSet → Finset C)
    (hL : ∀ e, Fintype.card V ≤ (L e).card) :
    ∃ f : R.lineGraph.Coloring C, ∀ e, f e ∈ L e := by
  classical
  by_cases h : Nonempty R.edgeSet
  · let e₀ : R.edgeSet := Classical.choice h
    let lift : R.edgeSet → (⊤ : SimpleGraph V).edgeSet :=
      fun e => ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩
    let L' : (⊤ : SimpleGraph V).edgeSet → Finset C :=
      fun e => if h : e.val ∈ R.edgeSet then L ⟨e.val,h⟩ else L e₀
    obtain ⟨f,hf⟩ := LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete
      L' (by intro e; dsimp [L']; split <;> apply hL)
    refine ⟨Coloring.mk (fun e => f (lift e)) ?_,?_⟩
    · intro e d hadj
      apply f.valid
      obtain ⟨hne,v,hv,hw⟩ := lineGraph_adj_iff_exists.mp hadj
      exact lineGraph_adj_iff_exists.mpr
        ⟨fun h => hne (Subtype.ext
          (congrArg (fun x : (⊤ : SimpleGraph V).edgeSet => x.val) h)),v,hv,hw⟩
    · intro e
      change f (lift e) ∈ L e
      simpa [L',lift] using hf (lift e)
  · letI : IsEmpty R.edgeSet := not_nonempty_iff.mp h
    exact ⟨Coloring.mk (fun e => isEmptyElim e) (fun {e} => isEmptyElim e),
      fun e => isEmptyElim e⟩

theorem exists_list_edge_coloring_supported {V C : Type} [Fintype V]
    (R : SimpleGraph V) (S : Finset V) (hs : R.support ⊆ (S : Set V))
    (L : R.edgeSet → Finset C) (hL : ∀ e, S.card ≤ (L e).card) :
    ∃ f : R.lineGraph.Coloring C, ∀ e, f e ∈ L e := by
  classical
  let E := (SimpleGraph.Copy.induce R (S : Set V)).toLineGraphEmbedding
  have hc : Fintype.card (R.induce (S : Set V)).edgeSet = Fintype.card R.edgeSet := by
    have h := R.card_edgeFinset_induce_of_support_subset hs
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
    exact h
  have he : Function.Surjective E :=
    ((Fintype.bijective_iff_injective_and_card E).mpr ⟨E.injective,hc⟩).2
  let F : (R.induce (S : Set V)).lineGraph ≃g R.lineGraph := RelIso.ofSurjective E he
  have hS : Fintype.card (S : Set V)=S.card := Fintype.card_coe _
  obtain ⟨f,hf⟩ := exists_list_edge_coloring (R.induce (S : Set V))
    (fun e => L (F e)) (by intro e; rw [hS]; exact hL _)
  refine ⟨f.comp F.symm.toHom,fun e => ?_⟩
  change f (F.symm e) ∈ L e
  simpa only [F.apply_symm_apply] using hf (F.symm e)

end
end Cycle13
