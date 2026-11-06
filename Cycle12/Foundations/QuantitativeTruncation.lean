import Cycle12.Foundations.TruncationProfile
import Cycle12.Foundations.TruncatedCutJanson

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem truncationProfile_rescale (α L : ℝ) {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    α*h*u-(max (α*h-L*u) 0)^2/4 = h*u*truncationProfile α L (u/h) := by
  have he : max (α*h-L*u) 0 = h*max (α-L*(u/h)) 0 := by
    rw [mul_max_of_nonneg _ _ hh.le,mul_zero]
    congr 1
    field_simp
  rw [he,truncationProfile]
  field_simp

theorem truncatedCut_profile_bound (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    {α α₀ α₁ L h t₀ k₀ : ℝ} (hh : 0 < h) (ht₀ : 0 < t₀)
    (hL : 1 ≤ L) (ht : t₀*h ≤ (S.card:ℝ)) (hα₀ : α₀ ≤ α) (hα₁ : α ≤ α₁)
    (hk₀ : k₀ ≤ min (truncationProfile α₀ (L-1) t₀) (truncationProfile α₁ (L-1) t₀))
    (hcap : L*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, α*h*X.card ≤ (cutSize G X:ℝ)) :
    k₀*h*S.card ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  have hu : 0 < (S.card:ℝ) := (mul_pos ht₀ hh).trans_le ht
  have ht' : t₀ ≤ (S.card:ℝ)/h := (le_div_iff₀ hh).mpr ht
  have he := truncationProfile_endpoint_lower (show 0 ≤ L-1 by linarith) ht₀ ht' hα₀ hα₁
  have hb := truncatedCut_retained_scaled_cap G S k (α*h) L hcap hprofile
  rw [truncationProfile_rescale α (L-1) hh hu] at hb
  have hm := mul_le_mul_of_nonneg_left (hk₀.trans he) (mul_nonneg hh.le hu.le)
  nlinarith

theorem truncatedCut_profile_after_marks (G : SimpleGraph V) (S T : Finset V) (k : ℕ)
    {α α₀ α₁ L h t₀ k₀ κ cap : ℝ} (hh : 0 < h) (ht₀ : 0 < t₀)
    (hL : 1 ≤ L) (ht : t₀*h ≤ (S.card:ℝ)) (hα₀ : α₀ ≤ α) (hα₁ : α ≤ α₁)
    (hk₀ : k₀ ≤ min (truncationProfile α₀ (L-1) t₀) (truncationProfile α₁ (L-1) t₀))
    (hcap : L*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, α*h*X.card ≤ (cutSize G X:ℝ))
    (hT : (T.card:ℝ) ≤ cap) (hloss : (k:ℝ)*cap ≤ (k₀-κ)*h*S.card) :
    κ*h*S.card ≤ (Fintype.card ((truncatedCut G S k).induce (↑(univ\T):Set V)).edgeSet:ℝ) := by
  have hu : 0 ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hks : S.card ≤ k := by
    have hmul : (S.card:ℝ) ≤ L*S.card := by nlinarith
    exact_mod_cast hmul.trans hcap
  have hr := truncatedCut_profile_bound G S k hh ht₀ hL ht hα₀ hα₁ hk₀ hcap hprofile
  have hd := edge_count_delete_vertices_bounded (truncatedCut G S k) T
    (fun v _ => truncatedCut_degree_bound G S k hks v)
  rw [edgeSet_card_eq_inducedEdgeCount]
  have hmark := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ k by positivity)
  nlinarith

end
end Cycle13
