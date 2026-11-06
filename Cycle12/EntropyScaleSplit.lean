import Cycle12.DFSBoxes
import Cycle12.EntropyRemainder

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All bounds refer to the actual partition in `s`. -/
def EntropyStageBounds {P : AssignedPiece V} (s : StageSplit P)
    (D ell L h : ℝ) : Prop :=
  (s.cycles.length:ℝ)*ell ≤ D*P.vertices.card/2 ∧
  vertexMass s.boxes ≤ (1+2*ell/(L-ell-2))*P.vertices.card ∧
  (∀ B∈s.boxes, (B.vertices.card:ℝ)≤L) ∧
  (∀ B∈s.boxes, ∀ R∈s.pieces B,
    h<(R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ)≤L ∧
      CutExpansionOn R.graph R.vertices h) ∧
  (∀ B∈s.boxes, 2*(edgeCount (s.remainder B):ℝ) ≤
    h*(1+log (L/h)/log 2)*B.vertices.card)

theorem exists_entropy_stage_split (P : AssignedPiece V) {D ell L h : ℝ}
    (hell : 1≤ell) (hL : ell+2<L) (hh : 1≤h) (hhL : h≤L)
    (hdeg : 2*(edgeCount P.graph:ℝ)≤D*P.vertices.card) :
    ∃ s : StageSplit P, EntropyStageBounds s D ell L h := by
  obtain ⟨H,C,hHG,hcycle,hC,hpart,hcost⟩ := remove_long_cycles P.graph ell
  have hs : SupportedOn H P.vertices := fun _ _ h => P.supported (hHG h)
  obtain ⟨boxes,hboxes,hcover,hboxpart,hmass⟩ := exists_dfs_boxes H P.vertices hs hell hL hcycle
  have hres (B : AssignedPiece V) :
      ∃ (R : List (AssignedPiece V)) (K : SimpleGraph V), B∈boxes →
        (∀ Q∈R, Q.vertices⊆B.vertices ∧ h<(Q.vertices.card:ℝ) ∧
          (Q.vertices.card:ℝ)≤L ∧ CutExpansionOn Q.graph Q.vertices h) ∧
        R.Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition B.graph (K::R.map AssignedPiece.graph) ∧
        SupportedOn K B.vertices ∧
        2*(edgeCount K:ℝ)≤h*(1+log (L/h)/log 2)*B.vertices.card := by
    by_cases hB : B∈boxes
    · obtain ⟨R,K,hRK⟩ := entropy_cut_extraction_bounded B.graph B.vertices B.supported
        hh hhL (hboxes B hB).2.2
      exact ⟨R,K,fun _ => hRK⟩
    · exact ⟨[],⊥,fun hB' => False.elim (hB hB')⟩
  choose pieces remainder hpieces using hres
  have hp : GraphPartition P.graph (C++boxes.map AssignedPiece.graph) := by
    intro x y
    have h1 := hpart x y
    rw [edgeOccurrences_cons] at h1
    rw [edgeOccurrences_append,hboxpart x y]
    omega
  let s : StageSplit P := {
    cycles := C
    boxes := boxes
    pieces := pieces
    remainder := remainder
    cycles_good := fun K hK => (hC K hK).1
    box_subset := fun B hB => (hboxes B hB).1
    box_nonempty := fun _ B hB => (hboxes B hB).2.1
    box_cover := hcover
    piece_subset := fun B hB Q hQ => ((hpieces B hB).1 Q hQ).1
    piece_disjoint := fun B hB => (hpieces B hB).2.1
    remainder_supported := fun B hB => (hpieces B hB).2.2.2.1
    box_partition := fun B hB => (hpieces B hB).2.2.1
    partition := hp }
  refine ⟨s,?_,hmass,fun B hB => (hboxes B hB).2.2,?_,?_⟩
  · have he : (0:ℝ)≤edgeCount H := Nat.cast_nonneg _
    change (C.length:ℝ)*ell ≤ D*P.vertices.card/2
    linarith only [hcost,hdeg,he]
  · exact fun B hB Q hQ => ((hpieces B hB).1 Q hQ).2
  · exact fun B hB => (hpieces B hB).2.2.2.2

end
end Cycle12
