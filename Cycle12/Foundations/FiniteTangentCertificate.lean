import Cycle12.Foundations.FiniteAlgebraicBounds

namespace Cycle13
open Real MixedSample

/-- All fields are rational inequalities checked by the Lean kernel. -/
structure RationalCubeBracket (q : ℚ) where
  lo : ℚ
  hi : ℚ
  lo_nonneg : 0 ≤ lo
  hi_nonneg : 0 ≤ hi
  lower : lo^3 ≤ q
  upper : q ≤ hi^3

theorem RationalCubeBracket.bounds {q : ℚ} (E : RationalCubeBracket q)
    {a : ℝ} (ha : 0 ≤ a) (he : a^3=(q:ℝ)) : (E.lo:ℝ) ≤ a ∧ a ≤ (E.hi:ℝ) := by
  exact nonneg_cube_interval ha (by exact_mod_cast E.lo_nonneg)
    (by exact_mod_cast E.hi_nonneg) he
    (by exact_mod_cast E.lower) (by exact_mod_cast E.upper)

structure RationalSquareUpper (q : ℚ) where
  hi : ℚ
  hi_nonneg : 0 ≤ hi
  upper : q ≤ hi^2

theorem RationalSquareUpper.bound {q : ℚ} (E : RationalSquareUpper q)
    {a : ℝ} (ha : 0 ≤ a) (he : a^2=(q:ℝ)) : a ≤ (E.hi:ℝ) :=
  nonneg_square_upper ha (by exact_mod_cast E.hi_nonneg) he (by exact_mod_cast E.upper)

structure RationalDensityTangent (a3 b3 x : ℚ) where
  A : RationalCubeBracket a3
  B : RationalCubeBracket b3
  X : RationalCubeBracket x
  x_pos : 0 < x
  root_pos : 0 < X.lo

def RationalDensityTangent.value {a3 b3 x : ℚ} (E : RationalDensityTangent a3 b3 x) : ℚ :=
  E.A.hi*E.X.hi-x/2-E.B.lo/E.X.hi

def RationalDensityTangent.derivLo {a3 b3 x : ℚ} (E : RationalDensityTangent a3 b3 x) : ℚ :=
  E.A.lo/(3*E.X.hi^2)-1/2+E.B.lo/(3*E.X.hi^4)

def RationalDensityTangent.derivHi {a3 b3 x : ℚ} (E : RationalDensityTangent a3 b3 x) : ℚ :=
  E.A.hi/(3*E.X.lo^2)-1/2+E.B.hi/(3*E.X.lo^4)

theorem RationalDensityTangent.bounds {a3 b3 x : ℚ} (E : RationalDensityTangent a3 b3 x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha3 : a^3=(a3:ℝ)) (hb3 : b^3=(b3:ℝ)) :
    densityFee a b x ≤ (E.value:ℝ) ∧ (E.derivLo:ℝ) ≤ densityFeeDeriv a b x ∧
    densityFeeDeriv a b x ≤ (E.derivHi:ℝ) := by
  have hx : (0:ℝ) < x := by exact_mod_cast E.x_pos
  have hroot := E.X.bounds (rpow_nonneg hx.le _) (cubeScale_cube hx.le)
  have h := densityFee_rational_enclosures hx (by exact_mod_cast E.A.lo_nonneg)
    (by exact_mod_cast E.B.lo_nonneg) (by exact_mod_cast E.root_pos)
    (E.A.bounds ha ha3) (E.B.bounds hb hb3) hroot
  simpa only [RationalDensityTangent.value,RationalDensityTangent.derivLo,
    RationalDensityTangent.derivHi,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] using h

structure FiniteCoreCertificate (T t g K : ℚ) where
  T_pos : 0 < T
  t_large : 864 ≤ t
  g_pos : 0 < g
  x : ℚ
  tangent : RationalDensityTangent (108*T^2*(1+g)^3/(g*t^3))
    (864*(47/200)^3*(1+g)^4/T) x
  square : RationalSquareUpper (4*T*(1+g)^3/(g*t^2))
  lower_density : t*(1+g)/T ≤ x
  descending : tangent.derivHi ≤ 0
  payment : (1/2+2/t)*(1+g)+square.hi+tangent.value+
    tangent.derivLo*(t*(1+g)/T-x) ≤ K

/-- A concrete finite certificate controls the entire real density half-line. -/
theorem FiniteCoreCertificate.bound {T t g K : ℚ} (E : FiniteCoreCertificate T t g K)
    {d : ℝ} (hd : (t:ℝ) ≤ d) : coreFeeAtDensity T t d g ≤ (K:ℝ) := by
  have hT : (0:ℝ) < T := by exact_mod_cast E.T_pos
  have ht : (864:ℝ) ≤ t := by exact_mod_cast E.t_large
  have ht₀ : (0:ℝ) < t := by linarith
  have hg : (0:ℝ) < g := by exact_mod_cast E.g_pos
  have ha := coreDensityA_nonneg hT ht₀ hg
  have hb := coreDensityB_nonneg hT hg
  have hA : (coreDensityA T t g)^3=((108*T^2*(1+g)^3/(g*t^3):ℚ):ℝ) := by
    push_cast
    exact coreDensityA_cube hT ht₀ hg
  have hB : (coreDensityB T g)^3=((864*(47/200)^3*(1+g)^4/T:ℚ):ℝ) := by
    push_cast
    exact coreDensityB_cube hT hg
  have hh := E.tangent.bounds ha hb hA hB
  have hsq := E.square.bound (a := (2*sqrt (T:ℝ)/t)*powerPerspective (3/2) g)
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
  tangent : RationalDensityTangent (108*M*T/t^3) 0 x
  square : RationalSquareUpper (4*M/t^2)
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
  have hA : (componentDensityA M T t)^3=((108*M*T/t^3:ℚ):ℝ) := by
    push_cast
    exact componentDensityA_cube hM hT ht
  have hh := E.tangent.bounds ha (by norm_num : (0:ℝ) ≤ 0) hA (by norm_num)
  have hsq := E.square.bound (a := 2*sqrt (M:ℝ)/t) (by positivity)
    (by push_cast; exact componentDensitySquare_square hM ht)
  apply terminalBlockFee_bound_of_tangent hM hT ht (by exact_mod_cast E.tangent.x_pos)
    hh.1 hh.2.1 hh.2.2 (by exact_mod_cast E.descending) _ hs hsM hm
  have hpay := (Rat.cast_le (K:=ℝ)).mpr E.payment
  push_cast at hpay
  linarith only [hsq,hpay]

end Cycle13
