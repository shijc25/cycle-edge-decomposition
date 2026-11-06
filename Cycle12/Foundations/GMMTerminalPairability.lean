import Cycle12.Foundations.SixVertexReduction
import Cycle12.Foundations.DemandRegularization
import Cycle12.Foundations.TerminalBaseCases

/-! Terminal-pairability in the range of Gyori--Mezei--Meszaros:
maximum indexed demand degree at most 2 floor(n/6)-4. The natural-number
form truncates the bound to zero for small n. Every parallel demand is
kept as a separate index; loops are resolved by empty walks. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1500000 in
theorem gmm_terminal_pairability {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] (a b : I → V)
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2*(Fintype.card V/6-2)) :
    Nonempty (DemandRouting (completeGraph V) a b) := by
  have aux : ∀ n (V I : Type) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I],
      Fintype.card V=n → ∀ a b : I → V,
      (∀ v, Suppression.incidenceDegree a b v ≤ 2*(Fintype.card V/6-2)) →
      Nonempty (DemandRouting (completeGraph V) a b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V I instV instI decV decI hn a b hd
      let J := {i // a i≠b i}
      let a' : J → V := fun i => a i.val
      let b' : J → V := fun i => b i.val
      have hne : ∀ i, a' i≠b' i := fun i => i.property
      have hd' : ∀ v, Suppression.incidenceDegree a' b' v ≤ 2*(Fintype.card V/6-2) :=
        fun v => (nonloop_degree_le a b v).trans (hd v)
      suffices hroute : Nonempty (DemandRouting (completeGraph V) a' b') by
        obtain ⟨R⟩ := hroute
        exact ⟨R.restore_loops⟩
      by_cases hsmall : Fintype.card V < 24
      · exact gmm_small_order_routing a' b' hne hsmall hd'
      · obtain ⟨E,hE⟩ := exists_even_regular_completion a' b' hne (by omega) hd'
        obtain ⟨R⟩ := regular_six_vertex_reduction E.left E.right E.loopless (by omega) hE (by omega)
        have horder := R.order
        have hlt : Fintype.card R.Vertices < n := by omega
        have hdegree : ∀ v, Suppression.incidenceDegree R.left R.right v ≤
            2*(Fintype.card R.Vertices/6-2) := by
          intro v
          have hh := R.degree v
          omega
        have hres := ih (Fintype.card R.Vertices) hlt R.Vertices R.Edges rfl R.left R.right hdegree
        exact E.pullback (R.pullback hres)
  exact aux (Fintype.card V) V I rfl a b hd

theorem gmm_terminal_paths {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] (a b : I → V)
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2*(Fintype.card V/6-2)) :
    ∃ p : ∀ i, (completeGraph V).Walk (a i) (b i), (∀ i, (p i).IsPath) ∧
      Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet) := by
  obtain ⟨R⟩ := gmm_terminal_pairability a b hd
  exact R.simple_paths

end
end Cycle13
