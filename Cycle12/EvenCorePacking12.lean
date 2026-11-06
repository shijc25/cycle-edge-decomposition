import Cycle12.ActualEvenScaleLayers12
import Cycle12.EvenActualLayerMass12
import Cycle12.CompletionInduction12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem pastPieces_mem_level (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V))
    {P : AssignedPiece V} (hP : P∈pastPieces s j k L) :
    ∃ i<k, P∈levelPieces s (j+i) (advance s j i L) := by
  induction k with
  | zero => simp only [pastPieces,List.not_mem_nil] at hP
  | succ k ih =>
    rcases List.mem_append.mp hP with hp | hp
    · obtain ⟨i,hi,h⟩ := ih hp
      exact ⟨i,by omega,h⟩
    · exact ⟨k,by omega,hp⟩

namespace Even12
open Global12

/-- The smaller-order IH is applied on the induced core and then its
cycles are lifted to the ambient graph, paying only assigned vertices. -/
theorem assigned_even_core_packing (P : AssignedPiece V) {w : ℝ}
    (hw : w0≤w) (hlower : (2:ℝ)^(s*w)<P.vertices.card)
    (horder : (P.vertices.card:ℝ)≤(2:ℝ)^(rho*w))
    (hexp : CutExpansionOn P.graph P.vertices ((1023/1024)*(2:ℝ)^(s*w)))
    (heven : ∀ v, Even (P.graph.degree v))
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m) :
    ∃ Q : CyclePacking P.graph, Q.weight≤(1+C*eta)*P.vertices.card := by
  have hp : (0:ℝ)<P.vertices.card := (Real.rpow_pos_of_pos (by norm_num) _).trans hlower
  have hpN : 0<P.vertices.card := by exact_mod_cast hp
  letI : Nonempty (P.vertices:Set V) := (Finset.card_pos.mp hpN).to_subtype
  have hc : Fintype.card (P.vertices:Set V)=P.vertices.card :=
    Fintype.card_of_finset' P.vertices (fun _ => Iff.rfl)
  have hlin := (bank_preparation_scale_bounds hw hp horder).1
  have hn : 2≤Fintype.card (P.vertices:Set V) := by
    rw [hc]
    have : (2:ℝ)≤P.vertices.card := by linarith only [hlin,hlower]
    exact_mod_cast this
  have he : ∀ v, Even ((P.graph.induce (P.vertices:Set V)).degree v) := by
    intro v
    rw [supported_induced_degree P.graph P.vertices P.supported v]
    exact heven v.val
  have hi : ∀ m, m<Fintype.card (P.vertices:Set V) → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m := by
    intro m hm
    rw [hc] at hm
    exact ih m (hm.trans_le (Finset.card_le_univ _))
  have hcomp : ∃ Q : CyclePacking (P.graph.induce (P.vertices:Set V)),
      Q.weight≤(1+C*eta)*Fintype.card (P.vertices:Set V) := by
    apply even_core_completion_weight (w:=w) _ hn hw
    · simpa only [hc] using horder
    · convert cutExpansionOn_induce hexp using 1
    · simpa only [←SimpleGraph.ncard_neighborSet] using he
    · exact hi
  obtain ⟨Q,hQ⟩ := hcomp
  refine ⟨liftInducedPacking P.graph P.vertices Q,?_⟩
  rw [liftInducedPacking_weight P.graph P.vertices Q (fun _ _ h => P.supported h)]
  simpa only [hc] using hQ

theorem EvenScaleLayers12.core_packing {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i<L.stopIndex+3)
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m)
    (R : AssignedPiece V) (hR : R∈levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G])) :
    ∃ Q : CyclePacking R.graph, Q.weight≤(1+C*eta)*R.vertices.card := by
  obtain ⟨P,hP,B,hB,hR⟩ := (by simpa [levelPieces,List.mem_flatMap] using hR :
    ∃ P∈advance L.splitter 0 i [originalPiece G], ∃ B∈(L.splitter i P).boxes,
      R∈(L.splitter i P).pieces B)
  have hb := (L.bounds i hi P hP).2.2.2.1 B hB R hR
  exact assigned_even_core_packing R
    (logScale_minimum L.initial_log_pos.le L.phase_lower hi) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 ih

theorem EvenScaleLayers12.past_core_packing {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {k : ℕ} (hk : k≤L.stopIndex+3)
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m)
    (R : AssignedPiece V) (hR : R∈pastPieces L.splitter 0 k [originalPiece G]) :
    ∃ Q : CyclePacking R.graph, Q.weight≤(1+C*eta)*R.vertices.card := by
  obtain ⟨i,hi,hr⟩ := pastPieces_mem_level _ _ _ _ hR
  exact L.core_packing (i:=i) (by omega) ih R (by simpa only [Nat.zero_add] using hr)

end Even12
end
end Cycle12
