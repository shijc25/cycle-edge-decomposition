import Mathlib

namespace Cycle13
noncomputable section
open Set

def truncationProfile (a L t : ℝ) : ℝ := a-(max (a-L*t) 0)^2/(4*t)

theorem truncationProfile_concave (L : ℝ) {t : ℝ} (ht : 0<t) :
    ConcaveOn ℝ Set.univ (fun a => truncationProfile a L t) := by
  have hid : ConvexOn ℝ Set.univ (fun a : ℝ => a-L*t) := by
    convert (convexOn_id (𝕜:=ℝ) (s:=Set.univ) convex_univ).add_const (-L*t) using 1
    funext a
    simp only [Pi.add_apply,id_eq]
    ring
  have hmax : ConvexOn ℝ Set.univ (fun a : ℝ => max (a-L*t) 0) :=
    hid.sup (convexOn_const 0 convex_univ)
  have hs := hmax.pow (fun _ _ => le_max_right _ _) 2
  have hc := hs.smul (c:=1/(4*t)) (by positivity)
  have hh := (concaveOn_id (𝕜:=ℝ) (s:=Set.univ) convex_univ).sub hc
  convert hh using 1
  funext a
  simp only [truncationProfile,Pi.sub_apply,id_eq,smul_eq_mul,Pi.pow_apply]
  ring

theorem truncationProfile_mono_scale (a : ℝ) {L t₀ t : ℝ}
    (hL : 0≤L) (ht₀ : 0<t₀) (ht : t₀≤t) :
    truncationProfile a L t₀≤truncationProfile a L t := by
  have htpos : 0<t := ht₀.trans_le ht
  unfold truncationProfile
  suffices hh : (max (a-L*t) 0)^2/(4*t) ≤ (max (a-L*t₀) 0)^2/(4*t₀) by linarith
  by_cases hsmall : a-L*t₀≤0
  · have hlarge : a-L*t≤0 := by nlinarith
    rw [max_eq_right hsmall,max_eq_right hlarge]
    simp
  · rw [max_eq_left (le_of_not_ge hsmall)]
    by_cases hlarge : a-L*t≤0
    · rw [max_eq_right hlarge]
      simp only [zero_pow (by norm_num : 2≠0),zero_div]
      positivity
    · rw [max_eq_left (le_of_not_ge hlarge)]
      apply (div_le_div_iff₀ (by positivity : 0<4*t) (by positivity : 0<4*t₀)).mpr
      have hprod : 0≤L*L*t*(t-t₀) := by positivity
      have ha : a^2≥L^2*t^2 := by
        have hh := mul_self_le_mul_self (mul_nonneg hL htpos.le) (show L*t≤a by linarith)
        nlinarith
      have hmain : 0≤(t-t₀)*(a^2-L^2*t*t₀) := mul_nonneg (sub_nonneg.mpr ht) (by nlinarith)
      nlinarith

theorem truncationProfile_endpoint_lower {a₀ a₁ a L t₀ t : ℝ}
    (hL : 0≤L) (ht₀ : 0<t₀) (ht : t₀≤t) (ha₀ : a₀≤a) (ha₁ : a≤a₁) :
    min (truncationProfile a₀ L t₀) (truncationProfile a₁ L t₀) ≤ truncationProfile a L t := by
  have hh := (truncationProfile_concave L ht₀).min_le_of_mem_Icc
    (mem_univ a₀) (mem_univ a₁) ⟨ha₀,ha₁⟩
  exact hh.trans (truncationProfile_mono_scale a hL ht₀ ht)

end
end Cycle13
