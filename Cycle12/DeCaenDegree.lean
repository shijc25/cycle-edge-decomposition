import Cycle12.DeCaenMatrix
import Cycle12.Foundations.IncidentSampleEdges

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- de Caen's degree-square bound for every actual finite simple graph of
order at least three. It is proved here, not introduced as a literature axiom. -/
theorem de_caen_degree_square_bound (G : SimpleGraph V) (hn : 2 < Fintype.card V) :
    (∑ v, (G.degree v:ℝ)^2) ≤ (Fintype.card G.edgeSet:ℝ)*
      (2*(Fintype.card G.edgeSet:ℝ)/((Fintype.card V:ℝ)-1)+(Fintype.card V:ℝ)-2) := by
  let A : V → V → ℝ := fun v w => if G.Adj v w then 1 else 0
  have hsym (v w : V) : A v w=A w v := by simp only [A,G.adj_comm]
  have hsquare (v w : V) : (A v w)^2=A v w := by
    dsimp only [A]
    split_ifs <;> norm_num
  have hdiag (v : V) : A v v=0 := by simp [A]
  have hrow (v : V) : (∑ w, A v w)=(G.degree v:ℝ) := by
    have he : univ.filter (fun w => G.Adj v w)=G.neighborFinset v := by
      ext w
      simp
    simp only [A,sum_boole,he,G.card_neighborFinset_eq_degree]
  have hh := symmetric_boolean_degree_square_bound A (fun v => (G.degree v:ℝ))
    hsym hrow hsquare hdiag hn
  have ht : (∑ v, (G.degree v:ℝ))=2*(Fintype.card G.edgeSet:ℝ) := by
    have hn := G.sum_degrees_eq_twice_card_edges
    have he : G.edgeFinset.card=Fintype.card G.edgeSet := by
      simp only [SimpleGraph.edgeFinset,Set.toFinset_card]
    rw [he] at hn
    exact_mod_cast hn
  rw [ht] at hh
  apply hh.trans_eq
  have hden : (Fintype.card V:ℝ)-1≠0 := by
    have hnR : (2:ℝ)<(Fintype.card V:ℝ) := by exact_mod_cast hn
    linarith
  field_simp
  ring

end
end Cycle12
