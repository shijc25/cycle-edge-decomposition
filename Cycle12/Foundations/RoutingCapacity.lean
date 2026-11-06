import Cycle12.Foundations.SampledCyclePacking

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section

theorem even_gmm_capacity_lower {t : ℕ} (ht : Even t) :
    (t:ℝ)/3-16/3 ≤ (2*(t/6-2):ℕ) := by
  obtain ⟨k,hk⟩ := ht
  have hnat : t ≤ 3*(2*(t/6-2))+16 := by omega
  have hr : (t:ℝ) ≤ 3*(2*(t/6-2):ℕ)+16 := by exact_mod_cast hnat
  linarith

theorem rounded_pairing_capacity {t : ℕ} {T : ℝ} (ht : Even t)
    (hT : 3 ≤ T) (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ)) :
    T^2/3-(22/3)*T ≤ (t:ℝ)*(2*(t/6-2):ℕ) := by
  have hc := mul_le_mul_of_nonneg_left (even_gmm_capacity_lower ht) (Nat.cast_nonneg (α:=ℝ) t)
  have hs : (T-3)^2 ≤ (t:ℝ)^2 := sq_le_sq₀ (by linarith) (Nat.cast_nonneg _) |>.mpr hTt
  nlinarith

theorem rounded_branch_capacity {t : ℕ} {T h d K : ℝ}
    (hT : 3 ≤ T) (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ))
    (hh : 0 < h) (hK : 0 ≤ K) (hKT : 1 ≤ K*T)
    (hbudget : K*T*(T+h) ≤ h*d) :
    K*T^2-(3*K+1)*T ≤ (t:ℝ)*(⌊h*d/((t:ℝ)+h)⌋₊:ℝ) := by
  have hden : 0 < (t:ℝ)+h := by positivity
  have hk : K*T ≤ h*d/((t:ℝ)+h) := by
    apply (le_div_iff₀ hden).mpr
    exact (mul_le_mul_of_nonneg_left (show (t:ℝ)+h ≤ T+h by linarith)
      (show 0 ≤ K*T by linarith)).trans hbudget
  have hf := Nat.lt_floor_add_one (h*d/((t:ℝ)+h))
  have hlo : K*T-1 ≤ (⌊h*d/((t:ℝ)+h)⌋₊:ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α:=ℝ) t)
  have hn := mul_le_mul_of_nonneg_right hTt (sub_nonneg.mpr hKT)
  nlinarith

theorem rounded_large_capacity {t : ℕ} {T H : ℝ}
    (ht : 0 < t) (htT : (t:ℝ) ≤ T) :
    H-T ≤ (t:ℝ)*(⌊H/(t:ℝ)⌋₊:ℝ) := by
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  have hh := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (H/(t:ℝ))) htR
  rw [mul_div_cancel₀ _ htR.ne'] at hh
  nlinarith

/-- All three real capacity lower bounds produce one actual integer
capacity satisfying both branch-cut budgets and the GMM limit. -/
theorem exists_integer_routing_capacity {t : ℕ} {n T h d K H : ℝ}
    (ht : 0 < t) (hteven : Even t) (hT : 3 ≤ T)
    (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ))
    (hh : 0 < h) (hd : 0 ≤ d) (hH : 0 ≤ H) (hK : 0 ≤ K) (hKT : 1 ≤ K*T)
    (hbudget : K*T*(T+h) ≤ h*d)
    (hpair : n ≤ T^2/3-(22/3)*T)
    (hfan : n ≤ K*T^2-(3*K+1)*T) (hlarge : n ≤ H-T) :
    ∃ c : ℕ, c ≤ 2*(t/6-2) ∧ n ≤ (c:ℝ)*t ∧
      (c:ℝ)*((t:ℝ)+h) ≤ h*d ∧ (t:ℝ)*c ≤ H := by
  let c := min (2*(t/6-2)) (min ⌊h*d/((t:ℝ)+h)⌋₊ ⌊H/(t:ℝ)⌋₊)
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  have hden : 0 < (t:ℝ)+h := by positivity
  have h₁ := hpair.trans (rounded_pairing_capacity hteven hT htT hTt)
  have h₂ := hfan.trans (rounded_branch_capacity hT htT hTt hh hK hKT hbudget)
  have h₃ := hlarge.trans (rounded_large_capacity ht htT)
  have hc₁ : c ≤ 2*(t/6-2) := min_le_left _ _
  have hc₂ : c ≤ ⌊h*d/((t:ℝ)+h)⌋₊ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₃ : c ≤ ⌊H/(t:ℝ)⌋₊ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,hc₁,?_,?_,?_⟩
  · dsimp [c]
    rw [Nat.cast_min,Nat.cast_min,min_mul_of_nonneg _ _ htR.le,min_mul_of_nonneg _ _ htR.le]
    exact le_min (by simpa [mul_comm] using h₁)
      (le_min (by simpa [mul_comm] using h₂) (by simpa [mul_comm] using h₃))
  · have hf := (Nat.cast_le.mpr hc₂).trans (Nat.floor_le (by positivity : 0 ≤ h*d/((t:ℝ)+h)))
    exact (le_div_iff₀ hden).mp hf
  · have hf := (Nat.cast_le.mpr hc₃).trans (Nat.floor_le (div_nonneg hH htR.le))
    have hm := (le_div_iff₀ htR).mp hf
    simpa only [mul_comm] using hm

end
end Cycle13
