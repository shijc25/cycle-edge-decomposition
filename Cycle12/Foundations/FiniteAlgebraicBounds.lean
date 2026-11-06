import Cycle12.Foundations.FiniteDensityCoordinates
import Cycle12.Foundations.FiniteComponentPayment

namespace Cycle13
open Real MixedSample
noncomputable section

theorem cubeScale_cube {x : ℝ} (hx : 0 ≤ x) : (cubeScale x)^3=x := by
  unfold cubeScale
  rw [← rpow_mul_natCast hx]
  norm_num

theorem powerPerspective_cube {g : ℝ} (hg : 0 < g) :
    (powerPerspective (4/3) g)^3=(1+g)^4/g := by
  unfold powerPerspective positivePerspective
  rw [mul_pow,← rpow_mul_natCast (by positivity : 0 ≤ (1+g)/g)]
  norm_num
  field_simp <;> ring

theorem powerPerspective_square {g : ℝ} (hg : 0 < g) :
    (powerPerspective (3/2) g)^2=(1+g)^3/g := by
  unfold powerPerspective positivePerspective
  rw [mul_pow,← rpow_mul_natCast (by positivity : 0 ≤ (1+g)/g)]
  norm_num
  field_simp <;> ring

theorem coreDensityA_cube {T t g : ℝ} (hT : 0 < T) (ht : 0 < t) (hg : 0 < g) :
    (coreDensityA T t g)^3=108*T^2*(1+g)^3/(g*t^3) := by
  unfold coreDensityA
  rw [mul_pow,mul_pow,cubeScale_cube (by positivity),powerPerspective_cube hg]
  field_simp <;> ring

theorem coreDensityB_cube {T g : ℝ} (hT : 0 < T) (hg : 0 < g) :
    (coreDensityB T g)^3=864*(47/200:ℝ)^3*(1+g)^4/T := by
  unfold coreDensityB
  rw [mul_pow,cubeScale_cube (by positivity)]
  field_simp <;> ring

theorem coreDensitySquare_square {T t g : ℝ} (hT : 0 < T) (ht : 0 < t) (hg : 0 < g) :
    ((2*sqrt T/t)*powerPerspective (3/2) g)^2=4*T*(1+g)^3/(g*t^2) := by
  rw [mul_pow,div_pow,mul_pow,sq_sqrt hT.le,powerPerspective_square hg]
  field_simp <;> ring

theorem componentDensityA_cube {M T t : ℝ} (hM : 0 < M) (hT : 0 < T) (ht : 0 < t) :
    (componentDensityA M T t)^3=108*M*T/t^3 := by
  unfold componentDensityA
  rw [mul_pow,cubeScale_cube (by positivity)]
  field_simp <;> ring

theorem componentDensitySquare_square {M t : ℝ} (hM : 0 < M) (ht : 0 < t) :
    (2*sqrt M/t)^2=4*M/t^2 := by
  rw [div_pow,mul_pow,sq_sqrt hM.le]
  ring

theorem nonneg_cube_interval {a l u q : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (he : a^3=q) (hlo : l^3 ≤ q) (hhi : q ≤ u^3) : l ≤ a ∧ a ≤ u := by
  constructor
  · by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) ha (by decide : (3:ℕ) ≠ 0)
    linarith
  · by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) hu (by decide : (3:ℕ) ≠ 0)
    linarith

theorem nonneg_square_upper {a u q : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (he : a^2=q) (hhi : q ≤ u^2) : a ≤ u := by nlinarith

/-- Replacing a cube root by rational bounds also controls both inverse
powers in the derivative; no real-number computation is trusted. -/
theorem densityFee_root_coordinates {a b x : ℝ} (hx : 0 < x) :
    densityFee a b x=a*cubeScale x-x/2-b/cubeScale x ∧
    densityFeeDeriv a b x=a/(3*(cubeScale x)^2)-1/2+b/(3*(cubeScale x)^4) := by
  have he (n : ℕ) : x^(-((1/3:ℝ)*n))=((cubeScale x)^n)⁻¹ := by
    rw [rpow_neg hx.le,rpow_mul_natCast hx.le]
    norm_num [cubeScale]
  constructor
  · unfold densityFee cubeScale
    rw [rpow_neg hx.le]
    ring
  · unfold densityFeeDeriv
    have h₂ := he 2
    have h₄ := he 4
    norm_num only at h₂ h₄
    rw [h₂,h₄]
    ring

theorem densityFee_rational_enclosures {a b x al au bl bu rl ru : ℝ}
    (hx : 0 < x) (hal : 0 ≤ al) (hbl : 0 ≤ bl) (hrl : 0 < rl)
    (ha : al ≤ a ∧ a ≤ au) (hb : bl ≤ b ∧ b ≤ bu)
    (hr : rl ≤ cubeScale x ∧ cubeScale x ≤ ru) :
    densityFee a b x ≤ au*ru-x/2-bl/ru ∧
    al/(3*ru^2)-1/2+bl/(3*ru^4) ≤ densityFeeDeriv a b x ∧
    densityFeeDeriv a b x ≤ au/(3*rl^2)-1/2+bu/(3*rl^4) := by
  have hr₀ : 0 < cubeScale x := hrl.trans_le hr.1
  have ha₀ : 0 ≤ a := hal.trans ha.1
  have hb₀ : 0 ≤ b := hbl.trans hb.1
  have hau : 0 ≤ au := ha₀.trans ha.2
  have hbu : 0 ≤ bu := hb₀.trans hb.2
  have hru : 0 < ru := hr₀.trans_le hr.2
  have hmul : a*cubeScale x ≤ au*ru := mul_le_mul ha.2 hr.2 hr₀.le hau
  have hinv : bl/ru ≤ b/cubeScale x := by
    exact div_le_div₀ hb₀ hb.1 hr₀ hr.2
  have hAlo : al/(3*ru^2) ≤ a/(3*(cubeScale x)^2) := by
    apply div_le_div₀ ha₀ ha.1 (by positivity)
    gcongr
    exact hr.2
  have hBlo : bl/(3*ru^4) ≤ b/(3*(cubeScale x)^4) := by
    apply div_le_div₀ hb₀ hb.1 (by positivity)
    gcongr
    exact hr.2
  have hAhi : a/(3*(cubeScale x)^2) ≤ au/(3*rl^2) := by
    apply div_le_div₀ hau ha.2 (by positivity)
    gcongr
    exact hr.1
  have hBhi : b/(3*(cubeScale x)^4) ≤ bu/(3*rl^4) := by
    apply div_le_div₀ hbu hb.2 (by positivity)
    gcongr
    exact hr.1
  rw [(densityFee_root_coordinates hx).1,(densityFee_root_coordinates hx).2]
  exact ⟨by linarith only [hmul,hinv],by linarith only [hAlo,hBlo],by linarith only [hAhi,hBhi]⟩

end
end Cycle13
