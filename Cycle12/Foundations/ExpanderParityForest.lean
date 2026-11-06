import Cycle12.Foundations.ExpanderComponentCount
import Cycle12.Foundations.ParityForestReduction
import Cycle12.Foundations.BoundedDeletionExpansion

namespace Cycle13
open SimpleGraph Finset Real
open scoped symmDiff
noncomputable section
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutExpansion_mono_parameter {G : SimpleGraph V} [DecidableRel G.Adj] {h k : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion G h) (hkh : k ≤ h) :
    OAI.ErdosGallai.CutExpansion G k := by
  intro S
  exact (mul_le_mul_of_nonneg_right hkh (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hexp S)

theorem exists_bounded_parity_forest (G : SimpleGraph V) {q : ℕ}
    (hG : G.Preconnected)
    (hcomp : ∀ U : Set V, U.Nonempty →
      Nat.card (G.induce Uᶜ).ConnectedComponent ≤ q*U.ncard) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V-componentCount G ∧
      (∀ v, F.degree v ≤ q+1) ∧ (∀ v, Even ((G\F).degree v)) := by
  obtain ⟨H,hHG,hH⟩ := exists_bounded_parity_subgraph_general G hG hcomp
  obtain ⟨F,hFH,hforest,hpar⟩ := exists_acyclic_parity_subgraph H
  have hFG := hFH.trans hHG
  have hsize := forest_subgraph_edge_bound G F hFG hforest
  refine ⟨F,hFG,hforest,?_,?_,?_⟩
  · simpa only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hsize
  · intro v
    exact (SimpleGraph.degree_le_of_le hFH (v:=v)).trans (hH v).1
  · intro v
    have he := (graph_symmDiff_degree_even G F v).mpr ((hpar v).trans (hH v).2).symm
    have hx : G ∆ F=G\F := symmDiff_of_ge hFG
    simp only [← ncard_neighborSet] at he ⊢
    simpa only [hx] using he

/-- The exact replacement for the parity use of Win's theorem: a real
forest, the same r/h+2 degree loss, and retained cut expansion. -/
theorem expander_parity_forest [Nonempty V] (G : SimpleGraph V) {h : ℝ}
    (hh : 0 < h) (hexp : OAI.ErdosGallai.CutExpansion G h) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V-componentCount G ∧
      (∀ v, (F.degree v:ℝ) < (Fintype.card V:ℝ)/h+2) ∧
      (∀ v, Even ((G\F).degree v)) ∧
      OAI.ErdosGallai.CutExpansion (G\F) (h-((Fintype.card V:ℝ)/h+2)) := by
  let q : ℕ := ⌈(Fintype.card V:ℝ)/h⌉₊
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hr : 0 < (Fintype.card V:ℝ)/h := div_pos hn hh
  have hq : 1 ≤ q := Nat.ceil_pos.mpr hr
  have hsize : (Fintype.card V:ℝ) ≤ q*h :=
    (div_le_iff₀ hh).mp (Nat.le_ceil _)
  obtain ⟨F,hFG,hforest,hsizeF,hdeg,heven⟩ := exists_bounded_parity_forest G (q:=q)
    (connected_of_cutExpansion G hh hexp).preconnected
    (expander_deleted_components_bound G (q:=q) hh hexp hq hsize)
  have hceil : (q:ℝ) < (Fintype.card V:ℝ)/h+1 := Nat.ceil_lt_add_one hr.le
  have hdegR : ∀ v, (F.degree v:ℝ) < (Fintype.card V:ℝ)/h+2 := by
    intro v
    have hv : (F.degree v:ℝ) ≤ (q:ℝ)+1 := by
      simpa only [Nat.cast_add,Nat.cast_one] using (Nat.cast_le (α:=ℝ)).mpr (hdeg v)
    linarith only [hv,hceil]
  refine ⟨F,hFG,hforest,hsizeF,hdegR,heven,?_⟩
  apply cutExpansion_mono_parameter (G:=G\F)
    (cutExpansion_sdiff_degree_bound G F hFG hexp hdeg)
  push_cast
  linarith only [hceil]

/-- This matches the original global parity budget without invoking a
bounded-degree spanning-tree theorem. -/
theorem expander_parity_forest_1023 [Nonempty V] (G : SimpleGraph V) {h : ℝ}
    (hh : 4096 < h) (hsquare : 2048*(Fintype.card V:ℝ) < h^2)
    (hexp : OAI.ErdosGallai.CutExpansion G h) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V-componentCount G ∧
      (∀ v, (F.degree v:ℝ) < h/1024) ∧
      (∀ v, Even ((G\F).degree v)) ∧
      OAI.ErdosGallai.CutExpansion (G\F) ((1023/1024)*h) := by
  have hh₀ : 0 < h := by linarith
  have hdiv : (Fintype.card V:ℝ)/h < h/2048 := (div_lt_iff₀ hh₀).mpr (by nlinarith)
  have hpay : (Fintype.card V:ℝ)/h+2 < h/1024 := by linarith
  obtain ⟨F,hFG,hforest,hsize,hdeg,heven,hremain⟩ := expander_parity_forest G hh₀ hexp
  exact ⟨F,hFG,hforest,hsize,fun v => (hdeg v).trans hpay,heven,
    cutExpansion_mono_parameter hremain (by linarith)⟩

end
end Cycle13
