import Cycle12.Foundations.AnchorGeometry
import Cycle12.Foundations.SubsetUpperChernoff
import Cycle12.Foundations.TwoWeightWitness

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem anchor_copy_witness_probability (G : SimpleGraph V) (U X C : Finset V)
    (q : unitInterval) {δ β L err miss upper cap : ℝ}
    (hδ : 0 < δ) (hβ : 0 < β) (hL : 0 < L) (hLδ : L < δ)
    (herr : 0 < err) (hmiss : 0 < miss) (hmark : 1 ≤ (q:ℝ)*δ)
    (hdeg : ∀ v, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hexp : SampleCutExpansion G U β) (hbad : BadAnchorCut G U X C L)
    (hupper : (U.card:ℝ) ≤ upper) (hcap : (q:ℝ)*upper ≤ cap) :
    1-(2+(δ/β)*exp (-(q:ℝ)*δ))/err-(L/δ+exp (-(q:ℝ)*δ))/miss-
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) ≤
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).prob (fun ξ =>
      sampledErrorWeight G U C (U∩copiedSide T ξ (C∩T)) ≤ err*L*X.card ∧
        outsideCopyMisses X C T ξ ≤ miss*X.card ∧ (T.card:ℝ) ≤ cap)) := by
  let μ := (subsetBernoulli U q).joint (neighborCopyLaw G)
  let W : Finset V×(V→Option V)→ℝ := fun x =>
    sampledErrorWeight G U C (U∩copiedSide x.1 x.2 (C∩x.1))
  let Z : Finset V×(V→Option V)→ℝ := fun x => outsideCopyMisses X C x.1 x.2
  have hx := hbad.2.2.2.1
  have hW : ∀ x, 0 ≤ W x := fun _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hZ : ∀ x, 0 ≤ Z x := fun _ => Nat.cast_nonneg _
  have hs : 0 < err*L*X.card := mul_pos (mul_pos herr hL) hx
  have ht : 0 < miss*X.card := mul_pos hmiss hx
  have hw : μ.expect W ≤ (2+(δ/β)*exp (-(q:ℝ)*δ))*L*X.card := by
    rw [FiniteLaw.expect_joint]
    exact bad_anchor_copy_weight_expect G U X C q hδ hβ hL hmark (fun v _ => hdeg v) hexp hbad
  have hz : μ.expect Z ≤ (L/δ+exp (-(q:ℝ)*δ))*X.card := by
    rw [FiniteLaw.expect_joint]
    exact bad_anchor_copy_misses_expect G U X C q hδ (fun v _ => hdeg v) hbad
  have hwdiv : μ.expect W/(err*L*X.card) ≤ (2+(δ/β)*exp (-(q:ℝ)*δ))/err := by
    apply (div_le_div_of_nonneg_right hw hs.le).trans_eq
    field_simp [herr.ne',hL.ne',hx.ne']
  have hzdiv : μ.expect Z/(miss*X.card) ≤ (L/δ+exp (-(q:ℝ)*δ))/miss := by
    apply (div_le_div_of_nonneg_right hz ht.le).trans_eq
    field_simp [hmiss.ne',hx.ne']
  have hq : 0 < (q:ℝ) := by nlinarith [q.2.1]
  have hc := (bad_anchor_cut_sizes G U X C hβ hL (fun v _ => hdeg v) hexp hbad).2.1
  have hCpos : 0 < (C.card:ℝ) := (sub_pos.mpr hLδ).trans_le hc
  have hUpos : 0 < (U.card:ℝ) := hCpos.trans_le (by exact_mod_cast card_le_card hbad.2.1)
  have hμ : 0 < (q:ℝ)*U.card := mul_pos hq hUpos
  have hμmax := mul_le_mul_of_nonneg_left hupper q.2.1
  have hcapU : (q:ℝ)*U.card ≤ cap := hμmax.trans hcap
  have hcap0 : 0 < cap := hμ.trans_le hcapU
  have htail : exp (-(cap-(q:ℝ)*U.card)^2/(2*cap)) ≤
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) := by
    apply exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num : (0:ℝ) < 2) hcap0)).mpr
    nlinarith
  have hbadmark : μ.prob (fun x => cap < (x.1.card:ℝ)) ≤
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) := by
    rw [FiniteLaw.prob_joint_fst (subsetBernoulli U q) (neighborCopyLaw G)
      (fun T : Finset V => cap < (T.card:ℝ))]
    exact ((FiniteLaw.prob_mono _ (fun T h => h.le)).trans
      (subsetBernoulli_card_upper_tail U q hμ hcapU)).trans htail
  have hg := μ.prob_good_two_weights W Z (fun x => cap < (x.1.card:ℝ)) hW hZ hs ht
  simp only [not_lt] at hg
  have htotal : 1-(2+(δ/β)*exp (-(q:ℝ)*δ))/err-(L/δ+exp (-(q:ℝ)*δ))/miss-
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) ≤
      μ.prob (fun x => W x ≤ err*L*X.card ∧ Z x ≤ miss*X.card ∧ (x.1.card:ℝ) ≤ cap) := by
    linarith
  rw [FiniteLaw.prob_joint] at htotal
  exact htotal

end
end Cycle13
