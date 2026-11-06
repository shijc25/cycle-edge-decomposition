import Cycle12.Foundations.EquitableColoring
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-! Every proper edge coloring of a finite simple graph can be balanced
without increasing its palette. No edge-coloring theorem is assumed. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

theorem lineGraph_twoColor_degree_le_two (G : SimpleGraph V) (f : G.lineGraph.Coloring C)
    (a b : C) (hab : a ≠ b) (e : G.edgeSet) :
    (twoColorGraph G.lineGraph f a b).degree e ≤ 2 := by
  classical
  rcases e with ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    let e : G.edgeSet := ⟨s(x,y),he⟩
    let H := twoColorGraph G.lineGraph f a b
    let N := H.neighborSet e
    have hcolors : ∀ z w : N, f z.val = f w.val := by
      intro z w
      have hz : (f e=a ∧ f z.val=b) ∨ (f e=b ∧ f z.val=a) := z.property.2
      have hw : (f e=a ∧ f w.val=b) ∨ (f e=b ∧ f w.val=a) := w.property.2
      rcases hz with hz | hz <;> rcases hw with hw | hw <;> grind
    have hcover : ∀ z : N, x ∈ z.val.val ∨ y ∈ z.val.val := by
      intro z
      obtain ⟨v,hv,hvz⟩ := (lineGraph_adj_iff_exists.mp z.property.1).2
      change v ∈ s(x,y) at hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact Or.inl hvz
      · exact Or.inr hvz
    let code : N → Bool := fun z => decide (x ∈ z.val.val)
    have hinj : Function.Injective code := by
      intro z w hcode
      apply Subtype.ext
      by_contra hne
      have hshare : ∃ v, v ∈ z.val.val ∧ v ∈ w.val.val := by
        have hx : (x ∈ z.val.val) ↔ (x ∈ w.val.val) := by
          simpa only [code, decide_eq_decide] using hcode
        by_cases hz : x ∈ z.val.val
        · exact ⟨x,hz,hx.mp hz⟩
        · exact ⟨y,(hcover z).resolve_left hz,
            (hcover w).resolve_left (fun hw => hz (hx.mpr hw))⟩
      exact f.valid (lineGraph_adj_iff_exists.mpr ⟨hne,hshare⟩) (hcolors z w)
    have hc := Fintype.card_le_of_injective code hinj
    simpa only [N, Fintype.card_bool, card_neighborSet_eq_degree] using hc

theorem exists_equitable_edge_coloring (G : SimpleGraph V) (f₀ : G.lineGraph.Coloring C) :
    ∃ f : G.lineGraph.Coloring C, IsEquitableColoring f := by
  classical
  exact exists_equitable_coloring G.lineGraph f₀
    (fun f a b hab => lineGraph_twoColor_degree_le_two G f a b hab)

theorem exists_edge_coloring_class_bound (G : SimpleGraph V)
    (f₀ : G.lineGraph.Coloring C) :
    ∃ f : G.lineGraph.Coloring C, ∀ a : C,
      colorSize f a ≤ (G.edgeFinset.card+Fintype.card C-1)/Fintype.card C := by
  obtain ⟨f,hf⟩ := exists_equitable_edge_coloring G f₀
  refine ⟨f,fun a => ?_⟩
  simpa only [← G.edgeFinset_card] using hf.class_le_ceil a

end
end Cycle13
