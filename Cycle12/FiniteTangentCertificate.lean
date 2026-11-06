import Cycle12.FiniteAlgebraicBounds

namespace Cycle12
open Cycle13 Real Cycle13.MixedSample

structure FiniteCoreCertificate (T t g K : ℚ) where
  T_pos : 0 < T
  t_large : (79507/250) ≤ t
  g_pos : 0 < g
  x : ℚ
  tangent : RationalDensityTangent ((79507/2000)*T^2*(1+g)^3/(g*t^3))
    ((79507/250)*(47/200)^3*(1+g)^4/T) x
  square : RationalSquareUpper (9*T*(1+g)^3/(g*t^2))
  lower_density : t*(1+g)/T ≤ x
  descending : tangent.derivHi ≤ 0
  payment : (1/2+2/t)*(1+g)+square.hi+tangent.value+
    tangent.derivLo*(t*(1+g)/T-x) ≤ K

/-- A concrete finite certificate controls the entire real density half-line. -/
theorem FiniteCoreCertificate.bound {T t g K : ℚ} (E : FiniteCoreCertificate T t g K)
    {d : ℝ} (hd : (t:ℝ) ≤ d) : coreFeeAtDensity T t d g ≤ (K:ℝ) := by
  have hT : (0:ℝ) < T := by exact_mod_cast E.T_pos
  have ht : (4*(43/10)^3:ℝ) ≤ t := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr E.t_large
    norm_num at hh ⊢
    exact hh
  have ht₀ : (0:ℝ) < t := by linarith
  have hg : (0:ℝ) < g := by exact_mod_cast E.g_pos
  have ha := coreDensityA_nonneg hT ht₀ hg
  have hb := coreDensityB_nonneg hT hg
  have hA : (coreDensityA T t g)^3=(((79507/2000)*T^2*(1+g)^3/(g*t^3):ℚ):ℝ) := by
    push_cast
    exact coreDensityA_cube hT ht₀ hg
  have hB : (coreDensityB T g)^3=(((79507/250)*(47/200)^3*(1+g)^4/T:ℚ):ℝ) := by
    push_cast
    exact coreDensityB_cube hT hg
  have hh := E.tangent.bounds ha hb hA hB
  have hsq := E.square.bound (a := (3*sqrt (T:ℝ)/t)*powerPerspective (3/2) g)
    (by unfold powerPerspective positivePerspective; positivity)
    (by push_cast; exact coreDensitySquare_square hT ht₀ hg)
  apply coreFee_endpoint_of_tangent hT ht hg (by exact_mod_cast E.tangent.x_pos)
    (by exact_mod_cast E.lower_density) hh.1 hh.2.1 hh.2.2
    (by exact_mod_cast E.descending) _ hd
  have hpay := (Rat.cast_le (K:=ℝ)).mpr E.payment
  push_cast at hpay
  unfold coreDensityConstant
  linarith only [hsq,hpay]

structure FiniteComponentCertificate (M T t K : ℚ) where
  M_pos : 0 < M
  T_pos : 0 < T
  t_pos : 0 < t
  x : ℚ
  tangent : RationalDensityTangent ((79507/2000)*M*T/t^3) 0 x
  square : RationalSquareUpper (9*M/t^2)
  descending : tangent.derivHi ≤ 0
  payment : 1/2+1/t+square.hi+max 0 (tangent.value-tangent.derivLo*x) ≤ K

/-- Every smaller component, with arbitrary nonnegative edge density,
is paid by the same rational certificate. -/
theorem FiniteComponentCertificate.bound {M T t K : ℚ} (E : FiniteComponentCertificate M T t K)
    {s m : ℝ} (hs : 0 < s) (hsM : s ≤ (M:ℝ)) (hm : 0 ≤ m) :
    terminalBlockFee s T t m ≤ (K:ℝ)*s := by
  have hM : (0:ℝ) < M := by exact_mod_cast E.M_pos
  have hT : (0:ℝ) < T := by exact_mod_cast E.T_pos
  have ht : (0:ℝ) < t := by exact_mod_cast E.t_pos
  have ha : 0 ≤ componentDensityA M T t := by unfold componentDensityA cubeScale; positivity
  have hA : (componentDensityA M T t)^3=(((79507/2000)*M*T/t^3:ℚ):ℝ) := by
    push_cast
    exact componentDensityA_cube hM hT ht
  have hh := E.tangent.bounds ha (by norm_num : (0:ℝ) ≤ 0) hA (by norm_num)
  have hsq := E.square.bound (a := 3*sqrt (M:ℝ)/t) (by positivity)
    (by push_cast; exact componentDensitySquare_square hM ht)
  apply terminalBlockFee_bound_of_tangent hM hT ht (by exact_mod_cast E.tangent.x_pos)
    hh.1 hh.2.1 hh.2.2 (by exact_mod_cast E.descending) _ hs hsM hm
  have hpay := (Rat.cast_le (K:=ℝ)).mpr E.payment
  push_cast at hpay
  linarith only [hsq,hpay]

end Cycle12
