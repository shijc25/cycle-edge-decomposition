import Cycle12.Foundations.DemandRoutingOperations

/-! Reindexing and reversing selected demand edges changes neither the
degree ledger nor the existence of actual routes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype I] [Fintype J] [DecidableEq V]

theorem incidence_relabel (a b : I → V) (c d : J → V) (e : J ≃ I)
    (hends : ∀ j, (c j=a (e j) ∧ d j=b (e j)) ∨ (c j=b (e j) ∧ d j=a (e j))) (v : V) :
    Suppression.incidenceDegree c d v=Suppression.incidenceDegree a b v := by
  unfold Suppression.incidenceDegree
  apply Fintype.sum_equiv e
  intro j
  rcases hends j with h | h <;> simp [h.1,h.2,add_comm]

def DemandRouting.relabel {G : SimpleGraph V} {a b : I → V} {c d : J → V}
    (R : DemandRouting G c d) (e : J ≃ I)
    (hends : ∀ j, (c j=a (e j) ∧ d j=b (e j)) ∨ (c j=b (e j) ∧ d j=a (e j))) :
    DemandRouting G a b := by
  have hex : ∀ i, ∃ p : G.Walk (a i) (b i), p.edgeSet=(R.route (e.symm i)).edgeSet := by
    intro i
    have hh := hends (e.symm i)
    rw [e.apply_symm_apply] at hh
    rcases hh with h | h
    · exact ⟨(R.route (e.symm i)).copy h.1 h.2,Walk.edgeSet_copy _ _ _⟩
    · exact ⟨(R.route (e.symm i)).reverse.copy h.2 h.1,by rw [Walk.edgeSet_copy,Walk.edgeSet_reverse]⟩
  choose p hp using hex
  refine ⟨p,?_⟩
  intro i j hij
  rw [hp i,hp j]
  exact R.disjoint (e.symm.injective.ne hij)

theorem DemandRouting.relabel_edgeSet {G : SimpleGraph V} {a b : I → V} {c d : J → V}
    (R : DemandRouting G c d) (e : J ≃ I)
    (hends : ∀ j, (c j=a (e j) ∧ d j=b (e j)) ∨ (c j=b (e j) ∧ d j=a (e j))) (i : I) :
    ((R.relabel e hends).route i).edgeSet=(R.route (e.symm i)).edgeSet := by
  exact Classical.choose_spec (show ∃ p : G.Walk (a i) (b i),
    p.edgeSet=(R.route (e.symm i)).edgeSet from by
      have hh := hends (e.symm i)
      rw [e.apply_symm_apply] at hh
      rcases hh with h | h
      · exact ⟨(R.route (e.symm i)).copy h.1 h.2,Walk.edgeSet_copy _ _ _⟩
      · exact ⟨(R.route (e.symm i)).reverse.copy h.2 h.1,by rw [Walk.edgeSet_copy,Walk.edgeSet_reverse]⟩)

end
end Cycle13
