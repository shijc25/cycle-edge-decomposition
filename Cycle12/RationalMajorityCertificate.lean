import Cycle12.MajorityCubicEnvelope

namespace Cycle12
open Real

def ratMajorityCubicSlope (a b c x : ℚ) : ℚ := 3*b*c-a-2*b*(2*c+3)*x+6*b*x^2
def ratMajorityCubicBox (a b c lo hi : ℚ) : ℚ :=
  a*c+(3*b*c-a)*(if 0 ≤ 3*b*c-a then hi else lo)-b*(2*c+3)*lo^2+2*b*hi^3

theorem cast_rat_majority_cubic_slope (a b c x : ℚ) :
    (ratMajorityCubicSlope a b c x:ℝ)=majorityCubicSlope a b c x := by
  unfold ratMajorityCubicSlope majorityCubicSlope
  push_cast
  rfl

theorem cast_rat_majority_cubic_box (a b c lo hi : ℚ) :
    (ratMajorityCubicBox a b c lo hi:ℝ)=majorityCubicBox a b c lo hi := by
  by_cases h : 0 ≤ 3*b*c-a
  · have hr : (0:ℝ) ≤ 3*(b:ℝ)*c-a := by exact_mod_cast h
    simp only [ratMajorityCubicBox,majorityCubicBox,if_pos h,if_pos hr]
    push_cast
    rfl
  · have hr : ¬(0:ℝ) ≤ 3*(b:ℝ)*c-a := by exact_mod_cast h
    simp only [ratMajorityCubicBox,majorityCubicBox,if_neg h,if_neg hr]
    push_cast
    rfl

structure RatMajorityCertificate where
  a : ℚ
  b : ℚ
  c : ℚ
  lo : ℚ
  hi : ℚ
  bound : ℚ
  zeroMax : Bool

def RatMajorityCertificate.Valid (s : RatMajorityCertificate) : Prop :=
  0 ≤ s.b ∧ 1 ≤ s.c ∧
    if s.zeroMax=true then 3*s.b*s.c ≤ s.a ∧ s.a*s.c ≤ s.bound else
      0 ≤ s.lo ∧ s.lo ≤ s.hi ∧ s.hi ≤ 3/4 ∧
      0 ≤ ratMajorityCubicSlope s.a s.b s.c s.lo ∧
      ratMajorityCubicSlope s.a s.b s.c s.hi ≤ 0 ∧
      ratMajorityCubicBox s.a s.b s.c s.lo s.hi ≤ s.bound

instance (s : RatMajorityCertificate) : Decidable s.Valid := by
  unfold RatMajorityCertificate.Valid
  infer_instance

theorem rat_majority_certificate_sound (s : RatMajorityCertificate) (h : s.Valid) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → majorityCubic s.a s.b s.c x ≤ (s.bound:ℝ) := by
  obtain ⟨hb,hc,hrest⟩ := h
  have hbR : (0:ℝ) ≤ (s.b:ℝ) := by exact_mod_cast hb
  have hcR : (1:ℝ) ≤ (s.c:ℝ) := by exact_mod_cast hc
  by_cases hz : s.zeroMax=true
  · rw [if_pos hz] at hrest
    intro x hx0 hx1
    exact (majority_cubic_zero_max hbR hcR (by exact_mod_cast hrest.1) hx0 hx1).trans
      (by exact_mod_cast hrest.2)
  · rw [if_neg hz] at hrest
    obtain ⟨hlo,hlh,hhi,hslo,hshi,hbox⟩ := hrest
    apply majority_cubic_interval_bound (lo:=(s.lo:ℝ)) (hi:=(s.hi:ℝ)) hbR hcR
      (by exact_mod_cast hlo) (by exact_mod_cast hlh)
      (by have hh := (Rat.cast_le (K:=ℝ)).mpr hhi; norm_num at hh; exact hh)
    · simpa only [cast_rat_majority_cubic_slope] using
        (show (0:ℝ) ≤ (ratMajorityCubicSlope s.a s.b s.c s.lo:ℝ) by exact_mod_cast hslo)
    · simpa only [cast_rat_majority_cubic_slope] using
        (show (ratMajorityCubicSlope s.a s.b s.c s.hi:ℝ) ≤ 0 by exact_mod_cast hshi)
    · simpa only [cast_rat_majority_cubic_box] using
        (show (ratMajorityCubicBox s.a s.b s.c s.lo s.hi:ℝ) ≤ (s.bound:ℝ) by exact_mod_cast hbox)

end Cycle12
