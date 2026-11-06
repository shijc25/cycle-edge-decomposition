import Cycle12.Foundations.EquitableEdgeColoring
import Cycle12.Foundations.BranchBudgetArithmetic

/-! The large-palette carrier regime needs no Vizing or list-coloring
input for its residual graph: integer endpoint sums give a proper coloring,
which can then be balanced by bichromatic component switches. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def endpointSumColoring (G : SimpleGraph V) {p : ℕ} (hp : 2*Fintype.card V ≤ p) :
    G.lineGraph.Coloring (Fin p) := by
  let r := Fintype.equivFin V
  let label : Sym2 V → Fin p := Sym2.lift
    ⟨fun v w => ⟨(r v).val+(r w).val, by
      have hv := (r v).isLt
      have hw := (r w).isLt
      omega⟩,
      fun v w => Fin.ext (Nat.add_comm _ _)⟩
  refine Coloring.mk (fun e => label e.val) ?_
  intro e₁ e₂ hadj heq
  obtain ⟨hne,v,hv₁,hv₂⟩ := lineGraph_adj_iff_exists.mp hadj
  obtain ⟨w₁,hw₁⟩ := Sym2.mem_iff_exists.mp hv₁
  obtain ⟨w₂,hw₂⟩ := Sym2.mem_iff_exists.mp hv₂
  have hsum : (r v).val+(r w₁).val = (r v).val+(r w₂).val := by
    have h := congrArg Fin.val heq
    simpa only [hw₁,hw₂,label,Sym2.lift_mk] using h
  have hw : w₁=w₂ := r.injective (Fin.ext (Nat.add_left_cancel hsum))
  apply hne
  apply Subtype.ext
  rw [hw₁,hw₂,hw]

theorem exists_balanced_carrier_coloring (R : SimpleGraph V) {t p : ℕ}
    (hcard : Fintype.card V = t-p) (hp : p ≤ t) (hthree : 3*t < 4*p) :
    ∃ f : R.lineGraph.Coloring (Fin p), ∀ a : Fin p,
      colorSize f a ≤ (R.edgeFinset.card+p-1)/p := by
  have hpalette : 2*Fintype.card V ≤ p := by omega
  simpa only [Fintype.card_fin] using
    exists_edge_coloring_class_bound R (endpointSumColoring R hpalette)

lemma twice_edges_le_order_product (R : SimpleGraph V) :
    2*R.edgeFinset.card ≤ Fintype.card V*(Fintype.card V-1) := by
  classical
  rw [← R.sum_degrees_eq_twice_card_edges]
  calc
    _ ≤ ∑ _v : V, (Fintype.card V-1) := by
      apply sum_le_sum
      intro v _
      exact Nat.le_sub_one_of_lt (R.degree_lt_card_verts v)
    _ = _ := by simp

/-- The carrier's actual residual graph admits a proper edge coloring
whose every color class satisfies the target branch-use budget. -/
theorem exists_carrier_coloring_budget (R : SimpleGraph V) {t p : ℕ}
    (hcard : Fintype.card V = t-p) (ht : 4 ≤ t) (heven : Even t)
    (hp : p < t) (hthree : 3*t < 4*p) :
    ∃ f : R.lineGraph.Coloring (Fin p), ∀ a : Fin p,
      10*(t-1+2*colorSize f a) ≤ 11*t := by
  obtain ⟨f,hf⟩ := exists_balanced_carrier_coloring R hcard hp.le hthree
  have he : 2*R.edgeFinset.card ≤ (t-p)*(t-p-1) := by
    simpa only [hcard] using twice_edges_le_order_product R
  have hb := balanced_class_branch_budget ht heven hp hthree he
  refine ⟨f,fun a => ?_⟩
  have ha := hf a
  omega

end
end Cycle13
