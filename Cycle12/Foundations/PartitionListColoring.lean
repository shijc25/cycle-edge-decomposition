import Cycle12.Foundations.ListEdgeColoring

/-! List edge colouring of graphs supported on disjoint vertex blocks.
Each edge needs only as many list entries as vertices in its own block. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma edge_out_adj {W : Type} (R : SimpleGraph W) (e : R.edgeSet) :
    R.Adj e.val.out.1 e.val.out.2 := by
  change s(e.val.out.1,e.val.out.2) ∈ R.edgeSet
  rw [show s(e.val.out.1,e.val.out.2)=e.val from e.val.out_eq]
  exact e.property

def partitionPiece {W A : Type} (R : SimpleGraph W) (r : W → A) (a : A) : SimpleGraph W where
  Adj x y := R.Adj x y ∧ r x=a ∧ r y=a
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => R.irrefl h.1⟩

theorem exists_list_edge_coloring_partition {W A C : Type} [Fintype W]
    (R : SimpleGraph W) (r : W → A) (hr : ∀ x y, R.Adj x y → r x=r y)
    (L : R.edgeSet → Finset C)
    (hL : ∀ e (v : W), v ∈ e.val →
      (univ.filter (fun w => r w=r v)).card ≤ (L e).card) :
    ∃ f : R.lineGraph.Coloring C, ∀ e, f e ∈ L e := by
  classical
  let block : R.edgeSet → A := fun e => r e.val.out.1
  have hb : ∀ e : R.edgeSet, ∀ v ∈ e.val, r v=block e := by
    intro e v hv
    have hout : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
    rw [← hout] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · rfl
    · exact (hr _ _ (edge_out_adj R e)).symm
  let lift := fun (a : A) (e : (partitionPiece R r a).edgeSet) =>
    (⟨e.val,edgeSet_mono (show partitionPiece R r a ≤ R from fun _ _ h => h.1)
      e.property⟩ : R.edgeSet)
  have hex : ∀ a : A, ∃ f : (partitionPiece R r a).lineGraph.Coloring C,
      ∀ e, f e ∈ L (lift a e) := by
    intro a
    let S := univ.filter (fun v => r v=a)
    apply exists_list_edge_coloring_supported (partitionPiece R r a) S
    · intro v hv
      obtain ⟨w,hw⟩ := (partitionPiece R r a).mem_support.mp hv
      exact mem_filter.mpr ⟨mem_univ _,hw.2.1⟩
    · intro e
      have he := edge_out_adj (partitionPiece R r a) e
      have h := hL (lift a e) e.val.out.1 (Sym2.out_fst_mem e.val)
      rw [he.2.1] at h
      exact h
  choose F hF using hex
  have htransport : ∀ (a b : A) (hab : a=b) (e : Sym2 W)
      (ha : e ∈ (partitionPiece R r a).edgeSet) (hb : e ∈ (partitionPiece R r b).edgeSet),
      F a ⟨e,ha⟩ = F b ⟨e,hb⟩ := by
    intro a b hab e ha hb
    subst b
    rfl
  have hedge : ∀ e : R.edgeSet, e.val ∈ (partitionPiece R r (block e)).edgeSet := by
    intro e
    have hout : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
    rw [← hout]
    exact ⟨edge_out_adj R e,rfl,(hr _ _ (edge_out_adj R e)).symm⟩
  refine ⟨Coloring.mk (fun e => F (block e) ⟨e.val,hedge e⟩) ?_,?_⟩
  · intro e d hadj hcol
    obtain ⟨hne,v,hv,hw⟩ := lineGraph_adj_iff_exists.mp hadj
    have hbd : block e=block d := (hb e v hv).symm.trans (hb d v hw)
    change F (block e) ⟨e.val,hedge e⟩ = F (block d) ⟨d.val,hedge d⟩ at hcol
    have hde : d.val ∈ (partitionPiece R r (block e)).edgeSet := hbd.symm ▸ hedge d
    have hcol' := hcol.trans (htransport _ _ hbd.symm d.val (hedge d) hde)
    apply (F (block e)).valid _ hcol'
    exact lineGraph_adj_iff_exists.mpr
      ⟨fun h => hne (Subtype.ext (congrArg
        (fun z : (partitionPiece R r (block e)).edgeSet => z.val) h)),v,hv,hw⟩
  · intro e
    change F (block e) ⟨e.val,hedge e⟩ ∈ L e
    exact hF (block e) ⟨e.val,hedge e⟩

end
end Cycle13
