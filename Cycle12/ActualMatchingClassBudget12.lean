import Cycle12.ActualFoldQuotients12
import Cycle12.GlobalFoldLedger12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

/-- An actual batch meets each selected core at most once. The disjoint
core orders therefore bound its number of active blocks. -/
theorem active_count_upper (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) (t : F.BatchIndex) :
    (Fintype.card ((F.active t.1).Index t.2):ℝ) ≤
      (2:ℝ)^((rho-s)*logScale (originalLog V) L.stopIndex i) := by
  let w := logScale (originalLog V) L.stopIndex i
  let U := fun r : Fin (L.foldCores i t.1).length => ((L.foldCores i t.1).get r).vertices
  have data := L.actual_box_data hi (L.foldParent_mem i t.1) (L.foldBox_mem i t.1)
  have hd : Pairwise (fun r j => Disjoint (U r) (U j)) := data.2.1
  have hs : ∀ r,U r⊆(L.foldBox i t.1).vertices := data.2.2.1
  have hl : ∀ r,(2:ℝ)^(s*w) ≤ ((U r).card:ℝ) := fun r => (data.2.2.2.1 r).1.le
  have hp : 0 < (2:ℝ)^(s*w) := rpow_pos_of_pos (by norm_num) _
  have hc := (core_count_from_mass hp hl).trans
    (div_le_div_of_nonneg_right (disjoint_core_mass_le U (L.foldBox i t.1).vertices hd hs) hp.le)
  have hb := div_le_div_of_nonneg_right (L.fold_box_order hi t.1) hp.le
  have hn : (Fintype.card ((F.active t.1).Index t.2):ℝ) ≤ Fintype.card (Fin (L.foldCores i t.1).length) := by
    exact_mod_cast Fintype.card_le_of_injective ((F.active t.1).router t.2) (F.injective t.1 t.2)
  have he : (2:ℝ)^(rho*w)/(2:ℝ)^(s*w)=(2:ℝ)^((rho-s)*w) := by
    rw [two_power_ratio]
    congr 1
    ring
  exact hn.trans ((hc.trans hb).trans_eq he)

/-- One ceiling charge for each unordered pair of distinct active
blocks is paid by the actual active mass, with no per-vertex color fee. -/
theorem matching_class_budget (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) (t : F.BatchIndex) :
    (Fintype.card (⊤ : SimpleGraph ((F.active t.1).Index t.2)).edgeSet:ℝ) ≤
      batchFee (logScale (originalLog V) L.stopIndex i)*
        ∑ j,(((F.active t.1).vertices t.2 j).card:ℝ) := by
  let w := logScale (originalLog V) L.stopIndex i
  let N : ℝ := Fintype.card ((F.active t.1).Index t.2)
  let mass : ℝ := ∑ j,(((F.active t.1).vertices t.2 j).card:ℝ)
  have hn0 : 0 ≤ N := Nat.cast_nonneg _
  have hm0 : 0 ≤ mass := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hp : 0 < (2:ℝ)^(lam*w) := rpow_pos_of_pos (by norm_num) _
  have hn : N ≤ (2:ℝ)^((rho-s)*w) := F.active_count_upper hi t
  have hl : N ≤ mass/(2:ℝ)^(lam*w) := core_count_from_mass hp ((F.active t.1).large t.2)
  have hc := Cycle13.MixedSample.twice_graph_edges_le_order_sq (⊤ : SimpleGraph ((F.active t.1).Index t.2))
  have hE : 2*(Fintype.card (⊤ : SimpleGraph ((F.active t.1).Index t.2)).edgeSet:ℝ) ≤ N^2 := by
    convert hc using 1 <;> congr!
  have hmul := mul_le_mul hn hl hn0 (rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
  have hcost : (Fintype.card (⊤ : SimpleGraph ((F.active t.1).Index t.2)).edgeSet:ℝ) ≤
      ((2:ℝ)^((rho-s)*w)/(2:ℝ)^(lam*w)/2)*mass := by
    have he : (2:ℝ)^((rho-s)*w)*(mass/(2:ℝ)^(lam*w))=
        ((2:ℝ)^((rho-s)*w)/(2:ℝ)^(lam*w))*mass := by ring
    rw [he] at hmul
    nlinarith only [hmul,hE]
  have he : (2:ℝ)^((rho-s)*w)/(2:ℝ)^(lam*w)=(2:ℝ)^((rho-s-lam)*w) := by
    rw [two_power_ratio]
    congr 1
    ring
  rw [he] at hcost
  have hfee : (2:ℝ)^((rho-s-lam)*w)/2 ≤ batchFee w := by
    rw [batchFee_identity]
    have hh : 0 ≤ (2:ℝ)^((rho-s-alpha)*w)/(4*c*teamGrowth w) :=
      div_nonneg (rpow_nonneg (by norm_num) _) (by have hg := (teamGrowth_pos w).le; unfold c; positivity)
    linarith only [hh]
  exact hcost.trans (mul_le_mul_of_nonneg_right hfee hm0)

theorem total_matching_class_budget (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    (∑ t : F.BatchIndex,(Fintype.card (⊤ : SimpleGraph ((F.active t.1).Index t.2)).edgeSet:ℝ)) ≤
      batchFee (logScale (originalLog V) L.stopIndex i)*F.activeMass := by
  have hh := sum_le_sum (fun t (_ : t∈(univ:Finset F.BatchIndex)) => F.matching_class_budget hi t)
  rw [←mul_sum] at hh
  have he : (∑ t : F.BatchIndex,∑ j,(((F.active t.1).vertices t.2 j).card:ℝ))=F.activeMass := by
    rw [Fintype.sum_sigma]
    rfl
  rwa [he] at hh

end ActualFoldStage12
end
end Cycle12.Even12
