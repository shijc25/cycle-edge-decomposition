import Cycle12.ActualFoldEdges12
import Cycle12.PotentialSmallerGraph12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def verticesWithin (W A : Finset V) : Finset W := univ.filter (fun v => v.val∈A)

theorem mem_verticesWithin (W A : Finset V) (v : W) : v∈verticesWithin W A ↔ v.val∈A := by
  simp only [verticesWithin,mem_filter,mem_univ,true_and]

theorem verticesWithin_card (W A : Finset V) (hA : A⊆W) : (verticesWithin W A).card=A.card := by
  have he : (verticesWithin W A).image Subtype.val=A := by
    ext v
    simp only [mem_image,mem_verticesWithin]
    exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun hv => ⟨⟨v,hA hv⟩,hv,rfl⟩⟩
  have hh := card_image_of_injective (verticesWithin W A) Subtype.val_injective
  rw [he] at hh
  exact hh.symm

theorem verticesWithin_disjoint (W : Finset V) {A B : Finset V} (hd : Disjoint A B) :
    Disjoint (verticesWithin W A) (verticesWithin W B) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp hd ((mem_verticesWithin W A v).mp hv) ((mem_verticesWithin W B v).mp hw)

end
end Cycle12

namespace Cycle12.Global12
open Cycle13 Real
noncomputable section

theorem active_contraction_saving {w : ℝ} (hw : wA ≤ w) :
    1 ≤ (2:ℝ)^(lam*w) ∧ kappa ≤ 1-1/(2:ℝ)^(lam*w) := by
  have he : (20:ℝ) ≤ lam*w := by
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ lam by norm_num [lam])
    have h20 : (20:ℝ) ≤ lam*wA := by norm_num [lam,wA]
    exact h20.trans hh
  have hp := rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) he
  norm_num only [rpow_natCast,Nat.reducePow] at hp
  have hq : 1/(2:ℝ)^(lam*w) ≤ (1/1000000:ℝ) := by
    apply (div_le_iff₀ (rpow_pos_of_pos (by norm_num) _)).mpr
    linarith only [hp]
  constructor
  · linarith only [hp]
  · unfold kappa
    linarith only [hq]

end
end Cycle12.Global12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.order_positive {G : SimpleGraph V} (L : EvenScaleLayers12 G) :
    0 < Fintype.card V := by
  by_contra h
  have he : Fintype.card V=0 := by omega
  have hh := L.initial_log_pos
  simp only [originalLog,he,Nat.cast_zero,logb_zero] at hh
  exact lt_irrefl _ hh

theorem EvenScaleLayers12.active_log_upper {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) : logScale (originalLog V) L.stopIndex i ≤ originalLog V := by
  unfold logScale
  rw [three_rate_regular _ _ _ _ (by omega)]
  exact mul_le_of_le_one_left L.initial_log_pos.le
    (pow_le_one₀ (by norm_num [theta2]) (by norm_num [theta2]))

theorem EvenScaleLayers12.active_batch_order_strict {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) :
    (2:ℝ)^(b*logScale (originalLog V) L.stopIndex i) < Fintype.card V := by
  have hw := (show 0 < wA by norm_num [wA]).trans_le
    (logScale_active L.initial_log_pos.le L.phase_lower hi)
  have hb : b*logScale (originalLog V) L.stopIndex i < logScale (originalLog V) L.stopIndex i :=
    mul_lt_of_lt_one_left hw (by norm_num [b])
  have hh := rpow_lt_rpow_of_exponent_lt (show (1:ℝ) < 2 by norm_num)
    (hb.trans_le (L.active_log_upper hi))
  rwa [originalLog,rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    (Nat.cast_pos.mpr L.order_positive)] at hh

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def batchVertices (F : ActualFoldStage12 L i) (t : F.BatchIndex) : Finset V :=
  (F.batches t.1).vertices t.2

def batchActive (F : ActualFoldStage12 L i) (t : F.BatchIndex)
    (j : (F.active t.1).Index t.2) : Finset (F.batchVertices t) :=
  verticesWithin (F.batchVertices t) ((F.active t.1).vertices t.2 j)

theorem batchActive_card (F : ActualFoldStage12 L i) (t : F.BatchIndex)
    (j : (F.active t.1).Index t.2) :
    (F.batchActive t j).card=((F.active t.1).vertices t.2 j).card :=
  verticesWithin_card _ _ ((F.active t.1).subset_batch t.2 j)

theorem batchActive_disjoint (F : ActualFoldStage12 L i) (t : F.BatchIndex) :
    Pairwise (fun j k => Disjoint (F.batchActive t j) (F.batchActive t k)) := by
  intro j k hjk
  exact verticesWithin_disjoint _ ((F.active t.1).disjoint t.2 hjk)

theorem batch_order_strict (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) (t : F.BatchIndex) :
    Fintype.card (F.batchVertices t) < Fintype.card V := by
  have hh := ((F.batches t.1).order_le t.2).trans_lt (L.active_batch_order_strict hi)
  rw [Fintype.card_coe]
  exact_mod_cast hh

/-- Apply the strengthened IH to the actual batch vertex type and
its actual active blocks, and discharge the current kappa saving. -/
theorem contracted_batch_packing (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (ih : PotentialBelow (Fintype.card V)) (t : F.BatchIndex)
    (H : SimpleGraph (F.batchVertices t)) :
    ∃ P : CyclePacking (H.map (contractVertex (F.batchActive t))),
      P.weight ≤ C*globalPhi (b*logScale (originalLog V) L.stopIndex i)*
        (((F.batchVertices t).card:ℝ)-kappa*∑ j,(((F.active t.1).vertices t.2 j).card:ℝ)) := by
  let w := logScale (originalLog V) L.stopIndex i
  have hw : wA ≤ w := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hsave := active_contraction_saving hw
  have hsize : ∀ j,(2:ℝ)^(lam*w) ≤ ((F.batchActive t j).card:ℝ) := by
    intro j
    rw [F.batchActive_card]
    exact (F.active t.1).large t.2 j
  have hc : Fintype.card (F.batchVertices t)=(F.batchVertices t).card := Fintype.card_coe _
  have ho : (Fintype.card (F.batchVertices t):ℝ) ≤ (2:ℝ)^(b*w) := by
    rw [hc]
    exact (F.batches t.1).order_le t.2
  obtain ⟨P,hP⟩ := ih.contracted_at_scale (x:=b*w) (L:=(2:ℝ)^(lam*w))
    H (F.batchActive t) (F.batchActive_disjoint t)
    (F.batch_order_strict hi t) ho
    hsave.1 hsize
  refine ⟨P,hP.trans ?_⟩
  simp only [Fintype.card_coe,F.batchActive_card]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num [C]) (globalPhi_bounds _).1.le)
  have hh := mul_le_mul_of_nonneg_right hsave.2
    (show 0 ≤ ∑ j,(((F.active t.1).vertices t.2 j).card:ℝ) from
      sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  linarith only [hh]

end ActualFoldStage12
end
end Cycle12.Even12
