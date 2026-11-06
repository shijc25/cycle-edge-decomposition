import Cycle12.Foundations.NearPortMatching

/-! Reindex routed vertices and edge labels without changing any graph or
multiplicity data; used to keep the iterative suppression state in fixed types. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V V' W : Type} {G : SimpleGraph W} {φ : V ↪ W}
    (R : RoutedEdges G φ I) (e : V' ≃ V) (ψ : V' ↪ W)
    (he : ∀ v, ψ v=φ (e v))

def reindexVertices : RoutedEdges G ψ I where
  left i := e.symm (R.left i)
  right i := e.symm (R.right i)
  route i := (R.route i).copy (by rw [he,Equiv.apply_symm_apply])
    (by rw [he,Equiv.apply_symm_apply])
  disjoint := by intro i j hij; simpa only [Walk.edgeSet_copy] using R.disjoint hij
  avoids := by
    intro i v hv
    rw [Walk.support_copy,he] at hv
    exact (R.avoids i (e v) hv).imp
      (fun h => by simpa only [Equiv.symm_apply_apply] using congrArg e.symm h)
      (fun h => by simpa only [Equiv.symm_apply_apply] using congrArg e.symm h)

variable [Fintype I] [DecidableEq V] [DecidableEq V']

theorem degree_reindexVertices (v : V') :
    (R.reindexVertices e ψ he).degree v=R.degree (e v) := by
  unfold degree reindexVertices
  simp only [Equiv.symm_apply_eq]

theorem multiplicity_reindexVertices (x y : V') :
    (R.reindexVertices e ψ he).multiplicity x y=R.multiplicity (e x) (e y) := by
  unfold multiplicity
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  change s(e.symm (R.left i),e.symm (R.right i))=s(x,y) ↔ s(R.left i,R.right i)=s(e x,e y)
  simp only [Sym2.eq_iff,Equiv.symm_apply_eq]

theorem graph_reindexVertices : (R.reindexVertices e ψ he).graph=R.graph.comap e := by
  ext x y
  rw [graph_adj_iff_multiplicity,multiplicity_reindexVertices]
  change (x≠y ∧ 0<R.multiplicity (e x) (e y)) ↔ R.graph.Adj (e x) (e y)
  rw [graph_adj_iff_multiplicity]
  simp only [e.injective.ne_iff]

variable [DecidableEq I]

theorem multiplicity_normalize (x y : V) : R.normalize.multiplicity x y=R.multiplicity x y := by
  rw [multiplicity_eq_sum,multiplicity_eq_sum]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem graph_normalize : R.normalize.graph=R.graph := by
  ext x y
  rw [graph_adj_iff_multiplicity,graph_adj_iff_multiplicity,multiplicity_normalize]

end RoutedEdges
end
end Cycle13
