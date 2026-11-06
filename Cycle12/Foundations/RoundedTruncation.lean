import Cycle12.Foundations.QuantitativeTruncation

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def roundedCutCap (L : ℝ) (S : Finset V) : ℕ := ⌈L*S.card⌉₊

theorem roundedCutCap_lower (L : ℝ) (S : Finset V) :
    L*S.card ≤ (roundedCutCap L S:ℝ) := Nat.le_ceil _

theorem roundedCutCap_upper {L : ℝ} (hL : 0 ≤ L) (S : Finset V) :
    (roundedCutCap L S:ℝ) ≤ L*S.card+1 :=
  (Nat.ceil_lt_add_one (mul_nonneg hL (Nat.cast_nonneg _))).le

theorem roundedCutCap_scaled_upper {L u₀ : ℝ} (hL : 0 ≤ L) (hu₀ : 0 < u₀)
    (S : Finset V) (hu : u₀ ≤ (S.card:ℝ)) :
    (roundedCutCap L S:ℝ) ≤ (L+1/u₀)*S.card := by
  have hh : 1 ≤ (S.card:ℝ)/u₀ := (le_div_iff₀ hu₀).mpr (by simpa using hu)
  have hb := roundedCutCap_upper hL S
  calc
    _ ≤ L*S.card+1 := hb
    _ ≤ L*S.card+(S.card:ℝ)/u₀ := by linarith
    _ = _ := by ring

theorem roundedCutCap_endpoint_budget {L : ℝ} (hL : 1 ≤ L) (S : Finset V)
    (hS : 0 < S.card) :
    2 ≤ roundedCutCap L S+S.card ∧
      ((roundedCutCap L S+S.card-2:ℕ):ℝ) ≤ (L+1)*S.card := by
  have hlow := roundedCutCap_lower L S
  have hcard : S.card ≤ roundedCutCap L S := by
    have hh : (S.card:ℝ) ≤ L*S.card := by nlinarith [Nat.cast_nonneg (α:=ℝ) S.card]
    exact_mod_cast hh.trans hlow
  have htwo : 2 ≤ roundedCutCap L S+S.card := by omega
  refine ⟨htwo,?_⟩
  rw [Nat.cast_sub htwo,Nat.cast_add]
  have hup := roundedCutCap_upper (show 0 ≤ L by linarith) S
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem rounded_truncation_retained (G : SimpleGraph V) (S T : Finset V)
    {α α₀ α₁ L h t₀ k₀ κ cap : ℝ} (hh : 0 < h) (ht₀ : 0 < t₀)
    (hL : 1 ≤ L) (ht : t₀*h ≤ (S.card:ℝ)) (hα₀ : α₀ ≤ α) (hα₁ : α ≤ α₁)
    (hk₀ : k₀ ≤ min (truncationProfile α₀ (L-1) t₀) (truncationProfile α₁ (L-1) t₀))
    (hprofile : ∀ X⊆S, α*h*X.card ≤ (cutSize G X:ℝ))
    (hT : (T.card:ℝ) ≤ cap) (hκ : κ ≤ k₀-(cap/h)*(L+1/(t₀*h))) :
    κ*h*S.card ≤ (Fintype.card
      ((truncatedCut G S (roundedCutCap L S)).induce (↑(univ\T):Set V)).edgeSet:ℝ) := by
  apply truncatedCut_profile_after_marks G S T (roundedCutCap L S)
    hh ht₀ hL ht hα₀ hα₁ hk₀ (roundedCutCap_lower L S) hprofile hT
  have hc : 0 ≤ cap := (Nat.cast_nonneg T.card).trans hT
  have hb := mul_le_mul_of_nonneg_right
    (roundedCutCap_scaled_upper (show 0 ≤ L by linarith) (mul_pos ht₀ hh) S ht) hc
  have hκ' : cap*(L+1/(t₀*h)) ≤ (k₀-κ)*h := by
    have hmul := mul_le_mul_of_nonneg_right hκ hh.le
    have he : (cap/h)*(L+1/(t₀*h))*h=cap*(L+1/(t₀*h)) := by field_simp
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hκ' (Nat.cast_nonneg (α:=ℝ) S.card)
  nlinarith

end
end Cycle13
