import Cycle12.Foundations.RoundedTruncation

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem janson_rate_from_linear_edge_bound {m u κ h ρ L u₀ d τ : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hu₀ : 0 < u₀) (hu : u₀ ≤ u) (hd : 0 ≤ d) (hdu : d ≤ (L+1)*u)
    (hm : κ*h*u ≤ m) :
    (1-τ)^2*κ*h*ρ/(2*(L+1+1/(ρ*u₀))) ≤ (1-τ)^2*m*ρ^2/(2*(1+d*ρ)) := by
  have hu0 : 0 < u := hu₀.trans_le hu
  have ha : 0 < L+1+1/(ρ*u₀) := by positivity
  have hden : 0 < 1+d*ρ := by positivity
  have hratio : 1 ≤ u/u₀ := (le_div_iff₀ hu₀).mpr (by simpa using hu)
  have hid : u*ρ*(L+1+1/(ρ*u₀))=(L+1)*u*ρ+u/u₀ := by field_simp <;> ring
  have hb : 1+d*ρ ≤ u*ρ*(L+1+1/(ρ*u₀)) := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hdu hρ.le
    linarith
  have hC : 0 ≤ (1-τ)^2*κ*h*ρ := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hb hC
  have h₂ := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg (1-τ)) (sq_nonneg ρ))
  have h₃ := mul_le_mul_of_nonneg_right h₂ ha.le
  apply (div_le_div_iff₀ (by positivity : 0 < 2*(L+1+1/(ρ*u₀)))
    (by positivity : 0 < 2*(1+d*ρ))).mpr
  nlinarith

theorem rounded_truncated_janson_rate (G : SimpleGraph V) (S T : Finset V)
    {κ h ρ L u₀ τ : ℝ} (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hρ : 0 < ρ)
    (hL : 1 ≤ L) (hu₀ : 0 < u₀) (hu : u₀ ≤ (S.card:ℝ))
    (hm : κ*h*S.card ≤ (Fintype.card
      ((truncatedCut G S (roundedCutCap L S)).induce (↑(univ\T):Set V)).edgeSet:ℝ)) :
    (1-τ)^2*κ*h*ρ/(2*(L+1+1/(ρ*u₀))) ≤
      (1-τ)^2*(Fintype.card
        ((truncatedCut G S (roundedCutCap L S)).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2/
        (2*(1+((roundedCutCap L S+S.card-2:ℕ):ℝ)*ρ)) := by
  have hS : 0 < S.card := by exact_mod_cast hu₀.trans_le hu
  exact janson_rate_from_linear_edge_bound hκ hh hρ (by linarith) hu₀ hu
    (Nat.cast_nonneg _) (roundedCutCap_endpoint_budget hL S hS).2 hm

end
end Cycle13
