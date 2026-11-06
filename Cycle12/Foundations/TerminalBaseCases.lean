import Cycle12.Foundations.TerminalReduction
import Cycle12.Foundations.IndexedDegreeSum

/-! Terminal-pairability base cases, using the same proved three-color
routing construction as the induction step. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem degree_two_terminal_routing (a b : I → V) (hne : ∀ i, a i≠b i)
    (hn : 7 ≤ Fintype.card V) (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    Nonempty (DemandRouting (completeGraph V) a b) := by
  obtain ⟨w,hsep⟩ := exists_independent_three a b hne hd (by omega)
  obtain ⟨f,hfixed,_⟩ := exists_cyclic_balanced_lifting_coloring a b w hsep hd
  exact ⟨hubColorRouting a b w f hfixed⟩

theorem zero_degree_terminal_routing (a b : I → V)
    (hd : ∀ v, Suppression.incidenceDegree a b v=0) :
    Nonempty (DemandRouting (completeGraph V) a b) := by
  have hI : ∀ i : I, False := by
    intro i
    have hp := single_le_sum (s:=univ)
      (fun j _ => Nat.zero_le ((if a j=a i then 1 else 0)+(if b j=a i then 1 else 0))) (mem_univ i)
    have hh := hd (a i)
    unfold Suppression.incidenceDegree at hh
    simp only [ite_true] at hp
    omega
  exact ⟨⟨fun i => (hI i).elim,fun i j h => (hI i).elim⟩⟩

theorem gmm_small_order_routing (a b : I → V) (hne : ∀ i, a i≠b i)
    (hn : Fintype.card V < 24)
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2*(Fintype.card V/6-2)) :
    Nonempty (DemandRouting (completeGraph V) a b) := by
  by_cases hsmall : Fintype.card V < 18
  · apply zero_degree_terminal_routing a b
    intro v; have hh := hd v; omega
  · apply degree_two_terminal_routing a b hne (by omega)
    intro v; have hh := hd v; omega

end
end Cycle13
