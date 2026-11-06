import Cycle12.Foundations.SuppressionRoutes
import Cycle12.Foundations.RoutedSimple
import Cycle12.Foundations.MatchingExtension

/-! A suppression result with a finite natural-number edge index, suitable
for iteration without retaining a growing dependent edge-index expression. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I)

def normalize : RoutedEdges G φ (Fin (Fintype.card I)) :=
  R.restrict (Fintype.equivFin I).symm.toEmbedding

theorem degree_normalize (v : V) : R.normalize.degree v=R.degree v :=
  Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem exists_suppressed (z : V) (heven : Even (R.degree z)) :
    ∃ m : ℕ, ∃ S : RoutedEdges G (afterVertex (φ:=φ) z) (Fin m),
      ∀ v : {v : V // v≠z}, S.degree v=R.degree v.val := by
  obtain ⟨M,hM,hcover⟩ := R.exists_suppression_matching z heven
  refine ⟨Fintype.card ((R.Kept z) ⊕ M.edgeSet),(R.suppress z M hM).normalize,?_⟩
  intro v
  rw [degree_normalize]
  exact R.degree_suppress z M hM hcover v

theorem exists_suppressed_prescribed (z : V)
    (M : (⊤ : SimpleGraph (R.Ports z)).Subgraph) (hM : M.IsMatching)
    (heven : Even (R.degree z)) :
    ∃ N : (⊤ : SimpleGraph (R.Ports z)).Subgraph,
      ∃ hN : N.IsMatching, N.verts=Set.univ ∧ M≤N ∧
      (∀ x y, N.Adj x y → ¬M.Adj x y → x∉M.verts ∧ y∉M.verts) ∧
      (∀ v : {v : V // v≠z}, (R.suppress z N hN).degree v=R.degree v.val) := by
  have he := Suppression.even_ports_of_even_degree R.left R.right z heven
  obtain ⟨N,hN,hcover,hle,hnew⟩ := matching_extends_to_perfect M hM he
  exact ⟨N,hN,hcover,hle,hnew,R.degree_suppress z N hN hcover⟩

end RoutedEdges
end
end Cycle13
