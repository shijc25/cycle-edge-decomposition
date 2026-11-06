import Mathlib

namespace Cycle13
open Real Set
noncomputable section

/-- The integer core threshold actually used by the DFS partition. -/
def finiteCoreThreshold (b : ℝ) (T : ℕ) : ℕ := ⌈b*T⌉₊

theorem finiteCoreThreshold_pos {b : ℝ} {T : ℕ} (hb : 0 < b) (hT : 0 < T) :
    0 < finiteCoreThreshold b T := by
  apply Nat.ceil_pos.mpr
  positivity

theorem rounded_core_bounds {b eps : ℝ} {T s : ℕ}
    (hb : 0 < b) (hT : 0 < T) (heps : 1 ≤ eps*T)
    (hslo : finiteCoreThreshold b T ≤ s) (hshi : s < 2*finiteCoreThreshold b T) :
    b*T ≤ (s:ℝ) ∧ (s:ℝ) ≤ (2*b+eps)*T := by
  have hT₀ : (0:ℝ) < T := by exact_mod_cast hT
  have h₁ := Nat.le_ceil (b*(T:ℝ))
  have h₂ := Nat.ceil_lt_add_one (by positivity : 0 ≤ b*(T:ℝ))
  have hsloR : (finiteCoreThreshold b T:ℝ) ≤ s := by exact_mod_cast hslo
  have hshiN : s+1 ≤ 2*finiteCoreThreshold b T := by omega
  have hshiR : (s:ℝ)+1 ≤ 2*(finiteCoreThreshold b T:ℝ) := by exact_mod_cast hshiN
  unfold finiteCoreThreshold at hsloR hshiR
  constructor <;> nlinarith

theorem rounded_core_gamma {b eps : ℝ} {T s : ℕ}
    (hb : 0 < b) (hT : 0 < T) (heps : 1 ≤ eps*T)
    (hslo : finiteCoreThreshold b T ≤ s) (hshi : s < 2*finiteCoreThreshold b T) :
    (T:ℝ)/s ∈ Icc (1/(2*b+eps)) (1/b) := by
  have hT₀ : (0:ℝ) < T := by exact_mod_cast hT
  have hsN : 0 < s := (finiteCoreThreshold_pos hb hT).trans_le hslo
  have hs : (0:ℝ) < s := by exact_mod_cast hsN
  have heps₀ : 0 < eps := by nlinarith
  have hH : 0 < 2*b+eps := by positivity
  obtain ⟨hl,hu⟩ := rounded_core_bounds hb hT heps hslo hshi
  constructor
  · apply (div_le_div_iff₀ hH hs).mpr
    nlinarith
  · apply (div_le_div_iff₀ hs hb).mpr
    nlinarith

theorem rounded_component_bound {b : ℝ} {T s : ℕ}
    (hb : 0 < b) (hT : 0 < T) (hs : s ≤ finiteCoreThreshold b T) :
    (s:ℝ) ≤ b*T+1 := by
  have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ b*(T:ℝ))
  have hsR : (s:ℝ) ≤ (finiteCoreThreshold b T:ℝ) := by exact_mod_cast hs
  exact hsR.trans hh.le

theorem finite_core_rounding_error {T : ℕ} (hT : 2^20 ≤ T) :
    (1:ℝ) ≤ (1/1048576)*(T:ℝ) := by
  have hh : (1048576:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  linarith

end
end Cycle13
