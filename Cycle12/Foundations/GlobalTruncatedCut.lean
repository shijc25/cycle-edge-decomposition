import Cycle12.Foundations.QuantitativeTruncation

/-! Three scale cut-profile bounds suffice for the global retained-edge
estimate. Constant lower profiles on each range avoid any need for an
upper bound on the profile function. -/
namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def GlobalCutProfile (G : SimpleGraph V) (h : ℝ) : Prop :=
  (∀ X : Finset V, 2*(X.card:ℝ) ≤ Fintype.card V → h*X.card ≤ (cutSize G X:ℝ)) ∧
  (∀ X : Finset V, 4*(X.card:ℝ) ≤ Fintype.card V → (3/2:ℝ)*h*X.card ≤ (cutSize G X:ℝ)) ∧
  (∀ X : Finset V, 8*(X.card:ℝ) ≤ Fintype.card V → (9/5:ℝ)*h*X.card ≤ (cutSize G X:ℝ))

theorem global_truncated_cut_retained (G : SimpleGraph V) (S : Finset V) {h : ℝ}
    (hh : 0 < h) (hr : 9*h ≤ (Fintype.card V:ℝ)) (hG : GlobalCutProfile G h)
    (hlarge : (107/100:ℝ)*h ≤ S.card) (hsmall : 2*(S.card:ℝ) ≤ Fintype.card V) :
    (1-h/Fintype.card V)*h*S.card ≤ ((truncatedCut G S S.card).edgeSet.ncard:ℝ) := by
  have hn : 0 < (Fintype.card V:ℝ) := (mul_pos (by norm_num : (0:ℝ) < 9) hh).trans_le hr
  have hu : 0 < (S.card:ℝ) := (mul_pos (by norm_num : (0:ℝ) < 107/100) hh).trans_le hlarge
  have hweak : (1-h/Fintype.card V)*h*S.card ≤ h*S.card := by
    have hd : 0 ≤ h/(Fintype.card V:ℝ) := div_nonneg hh.le hn.le
    nlinarith [mul_nonneg hd (mul_nonneg hh.le hu.le)]
  by_cases h8 : 8*(S.card:ℝ) ≤ Fintype.card V
  · apply hweak.trans
    have hb := truncatedCut_profile_bound G S S.card hh (show (0:ℝ) < 107/100 by norm_num)
      (L:=1) (by norm_num) hlarge (α:=9/5) (α₀:=9/5) (α₁:=9/5)
      (le_refl _) (le_refl _) (k₀:=1)
      (by norm_num [truncationProfile]) (by simp) (fun X hX => by
        apply hG.2.2 X
        have hc : (X.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card hX
        linarith)
    simpa only [one_mul] using hb
  by_cases h4 : 4*(S.card:ℝ) ≤ Fintype.card V
  · apply hweak.trans
    have ht : (9/8:ℝ)*h ≤ S.card := by linarith
    have hb := truncatedCut_profile_bound G S S.card hh (show (0:ℝ) < 9/8 by norm_num)
      (L:=1) (by norm_num) ht (α:=3/2) (α₀:=3/2) (α₁:=3/2)
      (le_refl _) (le_refl _) (k₀:=1)
      (by norm_num [truncationProfile]) (by simp) (fun X hX => by
        apply hG.2.1 X
        have hc : (X.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card hX
        linarith)
    simpa only [one_mul] using hb
  have hb := truncatedCut_retained_scaled_cap G S S.card h 1 (by simp) (fun X hX => by
    apply hG.1 X
    have hc : (X.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card hX
    linarith)
  simp only [sub_self,zero_mul,sub_zero,max_eq_left hh.le] at hb
  have hratio : (1/4:ℝ) ≤ (S.card:ℝ)/Fintype.card V :=
    (le_div_iff₀ hn).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hratio (sq_nonneg h)
  have hid : (1-h/Fintype.card V)*h*S.card=h*S.card-h^2*((S.card:ℝ)/Fintype.card V) := by ring
  rw [hid]
  nlinarith

theorem global_truncated_after_marks (G : SimpleGraph V) (S T : Finset V)
    {h cap κ : ℝ} (hh : 0 < h) (hr : 9*h ≤ (Fintype.card V:ℝ))
    (hG : GlobalCutProfile G h) (hlarge : (107/100:ℝ)*h ≤ S.card)
    (hsmall : 2*(S.card:ℝ) ≤ Fintype.card V) (hT : (T.card:ℝ) ≤ cap)
    (hκ : κ ≤ 1-h/Fintype.card V-cap/h) :
    κ*h*S.card ≤
      (Fintype.card ((truncatedCut G S S.card).induce (↑(univ\T):Set V)).edgeSet:ℝ) := by
  have hb := global_truncated_cut_retained G S hh hr hG hlarge hsmall
  have hd := edge_count_delete_vertices_bounded (truncatedCut G S S.card) T
    (fun v _ => truncatedCut_degree_bound G S S.card (le_refl _) v)
  rw [edgeSet_card_eq_inducedEdgeCount]
  have hc := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg (α:=ℝ) S.card)
  have hm := mul_le_mul_of_nonneg_right hκ (mul_nonneg hh.le (Nat.cast_nonneg (α:=ℝ) S.card))
  have hid : (1-h/Fintype.card V-cap/h)*(h*S.card)=
      (1-h/Fintype.card V)*h*S.card-cap*S.card := by field_simp [hh.ne'] <;> ring
  rw [hid] at hm
  nlinarith

end
end Cycle13
