import Cycle12.Foundations.CoreExtraction
import Cycle12.Foundations.GraphJanson

namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem degree_induced_le (G : SimpleGraph V) (S : Finset V) (v : (S:Set V)) :
    (G.induce (S:Set V)).degree v≤G.degree v.val := by
  rw [← ncard_neighborSet,← ncard_neighborSet]
  have hs : Subtype.val '' (G.induce (S:Set V)).neighborSet v⊆G.neighborSet v.val := by
    rintro w ⟨x,hx,rfl⟩
    exact hx
  have hh := Set.ncard_le_ncard hs
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem edge_count_delete_vertices (G : SimpleGraph V) (T : Finset V) :
    G.edgeFinset.card ≤ inducedEdgeCount G (univ\T)+∑ v∈T, G.degree v := by
  induction T using Finset.induction_on with
  | empty => simp [inducedEdgeCount_univ]
  | @insert v T hv ih =>
    have hvS : v∈univ\T := mem_sdiff.mpr ⟨mem_univ _,hv⟩
    have he := inducedEdgeCount_erase G (univ\T) hvS
    have hd := degree_induced_le G (univ\T) ⟨v,hvS⟩
    have hs : (univ\T).erase v=univ\insert v T := by
      ext w; simp [and_comm,and_left_comm,and_assoc]
    rw [hs] at he
    rw [sum_insert hv]
    simp only [← ncard_neighborSet] at he hd ih ⊢
    omega

theorem edge_count_delete_vertices_bounded (G : SimpleGraph V) (T : Finset V) {k : ℕ}
    (hdeg : ∀ v∈T, G.degree v≤k) :
    (G.edgeSet.ncard:ℝ)-(k:ℝ)*T.card ≤ (inducedEdgeCount G (univ\T):ℝ) := by
  have hh := edge_count_delete_vertices G T
  have hs : (∑ v∈T, G.degree v)≤T.card*k := by
    calc
      _ ≤ ∑ _v∈T, k := sum_le_sum hdeg
      _ = _ := by simp
  have he : G.edgeSet.ncard=G.edgeFinset.card := by
    simp only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']
  rw [he]
  have hr : (G.edgeFinset.card:ℝ)≤(inducedEdgeCount G (univ\T):ℝ)+(T.card:ℝ)*k := by
    exact_mod_cast (show G.edgeFinset.card ≤ inducedEdgeCount G (univ\T)+T.card*k by omega)
  nlinarith

theorem edgeSet_card_eq_inducedEdgeCount (G : SimpleGraph V) (S : Finset V) :
    Fintype.card (G.induce (S:Set V)).edgeSet=inducedEdgeCount G S := by
  exact (G.induce (S:Set V)).card_edgeSet

end
end Cycle13
