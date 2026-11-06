import Cycle12.LocalDescendantMass12
import Cycle12.GlobalLossFunctions12

namespace Cycle12
open SimpleGraph Finset
open OAI.ErdosGallai.Indexing
noncomputable section
attribute [local instance] Classical.propDecidable

theorem disjoint_core_mass_le {V R : Type} [DecidableEq V] [Fintype R]
    (U : R → Finset V) (Y : Finset V) (hd : Pairwise fun r t => Disjoint (U r) (U t))
    (hsub : ∀ r,U r⊆Y) : (∑ r,((U r).card:ℝ))≤Y.card := by
  have he : (univ.biUnion U).card=∑ r,(U r).card :=
    card_biUnion (fun r _ t _ hrt => hd hrt)
  have hs : univ.biUnion U⊆Y := by
    intro v hv
    obtain ⟨r,_,hr⟩ := mem_biUnion.mp hv
    exact hsub r hr
  have hh := card_le_card hs
  rw [he] at hh
  exact_mod_cast hh

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches ActiveFamily)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V R : Type} [Fintype V] [Fintype R] [DecidableEq V]

/-- Actual descendant batches and actual active blocks, together with the
unrounded mass deficit. Every batch uses a core at most once. -/
theorem EvenScaleLayers12.prepare_active_descendants {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) {P : AssignedPiece V}
    (hP : P∈advance L.splitter 0 (i+1) [originalPiece G])
    (U : R → Finset V) (hd : Pairwise fun r t => Disjoint (U r) (U t))
    (hsub : ∀ r,U r⊆P.vertices)
    (hlarge : ∀ r,(2:ℝ)^(s*logScale (originalLog V) L.stopIndex i)≤((U r).card:ℝ)) :
    let w := logScale (originalLog V) L.stopIndex i
    let F := graphUnion ((advance L.splitter (i+1) 2 [P]).map AssignedPiece.graph)
    ∃ B : GraphBatches F P.vertices ((2:ℝ)^(b*w)) (M*P.vertices.card),
      ∃ A : ActiveFamily F P.vertices B.vertices U ((2:ℝ)^(alpha*w)) ((2:ℝ)^(lam*w)),
        (∀ t,Function.Injective (A.router t)) ∧
        (∑ r,((U r).card:ℝ))-
          (entropyRemainder12 (q0*w)*M*P.vertices.card)/(2:ℝ)^(alpha*w)-
          (2:ℝ)^(lam*w)*(1+2*(M*P.vertices.card)/(2:ℝ)^(b*w))*
            ((P.vertices.card:ℝ)/(2:ℝ)^(s*w))≤
          ∑ t,∑ j,((A.vertices t j).card:ℝ) ∧
        (∑ t,∑ j,((A.vertices t j).card:ℝ))+P.vertices.card≤
          (∑ r,((U r).card:ℝ))+M*P.vertices.card := by
  dsimp only
  let w := logScale (originalLog V) L.stopIndex i
  let F := graphUnion ((advance L.splitter (i+1) 2 [P]).map AssignedPiece.graph)
  have hpow (t : ℝ) : 0<(2:ℝ)^(t*w) := rpow_pos_of_pos (by norm_num) _
  obtain ⟨hB,he⟩ := L.actual_descendant_batches hi hP
  obtain ⟨B0⟩ := hB
  have hm := L.descendant_mass_bound hi hP
  obtain ⟨B⟩ := graphBatches_enlarge_mass B0 (hpow b) hm
  obtain ⟨A,hinj⟩ := choose_injective_active_family F P.vertices B.vertices U
    ((2:ℝ)^(alpha*w)) ((2:ℝ)^(lam*w)) (hpow lam).le B.subset hsub B.vertex_cover hd
  have hcount : (Fintype.card R:ℝ)≤(P.vertices.card:ℝ)/(2:ℝ)^(s*w) :=
    (core_count_from_mass (hpow s) hlarge).trans
      (div_le_div_of_nonneg_right (disjoint_core_mass_le U P.vertices hd hsub) (hpow s).le)
  have hlow := active_mass_deficit_with_counts A (hpow alpha) (hpow lam).le B.count_le hcount
  have hw := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hD : 0≤entropyRemainder12 (q0*w) := entropyRemainder12_nonneg
    (mul_nonneg (by norm_num [q0,theta1,theta2]) ((by norm_num [wA] : (0:ℝ)≤wA).trans hw))
  have hE : 2*(F.edgeFinset.card:ℝ)≤entropyRemainder12 (q0*w)*M*P.vertices.card := by
    have hh := he.trans (mul_le_mul_of_nonneg_left hm hD)
    simpa only [F,w,edgeCount,mul_assoc] using hh
  have hdiv := div_le_div_of_nonneg_right hE (hpow alpha).le
  have hup := A.upper
  refine ⟨B,A,hinj,?_,?_⟩
  · linarith only [hlow,hdiv]
  · have hh := B.mass_le
    linarith only [hup,hh]

end
end Cycle12.Even12
