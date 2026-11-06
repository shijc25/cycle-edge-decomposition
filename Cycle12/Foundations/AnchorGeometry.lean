import Cycle12.Foundations.OutsideCopyError
import Cycle12.Foundations.SampledCutPopulation

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def SampleCutExpansion (G : SimpleGraph V) (U : Finset V) (β : ℝ) : Prop :=
  ∀ C⊆U, 2*C.card ≤ U.card → β*C.card ≤ ((G.interedges C (U\C)).card:ℝ)

def BadAnchorCut (G : SimpleGraph V) (U X C : Finset V) (L : ℝ) : Prop :=
  Disjoint X U ∧ C⊆U ∧ 2*C.card ≤ U.card ∧ 0 < (X.card:ℝ) ∧
    ((G.interedges X (U\C)).card:ℝ)+((G.interedges C (U\C)).card:ℝ) ≤ L*X.card

theorem bad_anchor_cut_sizes (G : SimpleGraph V) (U X C : Finset V) {δ β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L)
    (hdeg : ∀ v∈X, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hexp : SampleCutExpansion G U β) (hbad : BadAnchorCut G U X C L) :
    (C.card:ℝ) ≤ L*X.card/β ∧ δ-L ≤ (C.card:ℝ) ∧ β*(δ-L)/L ≤ (X.card:ℝ) := by
  have hcut := hexp C hbad.2.1 hbad.2.2.1
  have hnon : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
  have hnon' : (0:ℝ) ≤ (G.interedges C (U\C)).card := Nat.cast_nonneg _
  have hcost := hbad.2.2.2.2
  have hC : (C.card:ℝ) ≤ L*X.card/β := (le_div_iff₀ hβ).mpr (by linarith)
  have hlo : (δ-(C.card:ℝ))*X.card ≤ ((G.interedges X (U\C)).card:ℝ) := by
    apply cut_card_lower_of_neighbors G X (U\C) X (Subset.refl _) (δ-C.card)
    intro v hv
    have hp := neighborsIn_partition_card G v C U hbad.2.1
    have hpR : ((neighborsIn G v U).card:ℝ)=((neighborsIn G v C).card:ℝ)+
        ((neighborsIn G v (U\C)).card:ℝ) := by exact_mod_cast hp
    have hc : ((neighborsIn G v C).card:ℝ) ≤ C.card := by
      exact_mod_cast card_le_card (filter_subset (G.Adj v) C)
    have hd := hdeg v hv
    linarith
  have hy : δ-L ≤ (C.card:ℝ) := by
    have hh : δ-(C.card:ℝ) ≤ L := (mul_le_mul_iff_left₀ hbad.2.2.2.1).mp
      (show (δ-(C.card:ℝ))*X.card ≤ L*X.card by linarith)
    linarith
  refine ⟨hC,hy,?_⟩
  apply (div_le_iff₀ hL).mpr
  have hb := mul_le_mul_of_nonneg_left hy hβ.le
  linarith

theorem bad_anchor_copy_weight_expect (G : SimpleGraph V) (U X C : Finset V)
    (q : unitInterval) {δ β L : ℝ} (hδ : 0 < δ) (hβ : 0 < β) (hL : 0 < L)
    (hmark : 1 ≤ (q:ℝ)*δ)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hexp : SampleCutExpansion G U β) (hbad : BadAnchorCut G U X C L) :
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).expect (fun ξ =>
      sampledErrorWeight G U C (U∩copiedSide T ξ (C∩T)))) ≤
      (2+(δ/β)*exp (-(q:ℝ)*δ))*L*X.card := by
  have hb := neighborCopy_total_error G U C hbad.2.1 q hδ hmark hdeg
  have hcut := hexp C hbad.2.1 hbad.2.2.1
  have hcost := hbad.2.2.2.2
  have hnon : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
  have hC : (C.card:ℝ) ≤ L*X.card/β := (le_div_iff₀ hβ).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hC (mul_nonneg hδ.le (exp_pos (-(q:ℝ)*δ)).le)
  apply hb.trans
  have he : δ*exp (-(q:ℝ)*δ)*(L*X.card/β)=(δ/β)*exp (-(q:ℝ)*δ)*L*X.card := by ring
  rw [he] at hm
  nlinarith

theorem bad_anchor_copy_misses_expect (G : SimpleGraph V) (U X C : Finset V)
    (q : unitInterval) {δ L : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ v∈X, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : BadAnchorCut G U X C L) :
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).expect
      (outsideCopyMisses X C T)) ≤ (L/δ+exp (-(q:ℝ)*δ))*X.card := by
  apply (outsideCopyMisses_expect G U X C hbad.1 q hδ hdeg).trans
  have hcost := hbad.2.2.2.2
  have hnon : (0:ℝ) ≤ (G.interedges C (U\C)).card := Nat.cast_nonneg _
  have hh := div_le_div_of_nonneg_right
    (show ((G.interedges X (U\C)).card:ℝ) ≤ L*X.card by linarith) hδ.le
  calc
    _ ≤ L*X.card/δ+exp (-(q:ℝ)*δ)*X.card := by linarith
    _ = _ := by ring

end
end Cycle13
