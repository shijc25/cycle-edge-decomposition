import Cycle12.FiniteDensityCoordinates
import Cycle12.FiniteComponentPayment
import Cycle12.Foundations.FiniteTangentCertificate

namespace Cycle12
open Cycle13 Real Cycle13.MixedSample
noncomputable section

theorem coreDensityA_cube {T t g : ℝ} (hT : 0 < T) (ht : 0 < t) (hg : 0 < g) :
    (coreDensityA T t g)^3=(79507/2000)*T^2*(1+g)^3/(g*t^3) := by
  unfold coreDensityA
  rw [mul_pow,mul_pow,Cycle13.cubeScale_cube (by positivity),powerPerspective_cube hg]
  field_simp <;> ring

theorem coreDensityB_cube {T g : ℝ} (hT : 0 < T) (hg : 0 < g) :
    (coreDensityB T g)^3=(79507/250)*(47/200:ℝ)^3*(1+g)^4/T := by
  unfold coreDensityB
  rw [mul_pow,Cycle13.cubeScale_cube (by positivity)]
  field_simp <;> ring

theorem coreDensitySquare_square {T t g : ℝ} (hT : 0 < T) (ht : 0 < t) (hg : 0 < g) :
    ((3*sqrt T/t)*powerPerspective (3/2) g)^2=9*T*(1+g)^3/(g*t^2) := by
  rw [mul_pow,div_pow,mul_pow,sq_sqrt hT.le,powerPerspective_square hg]
  field_simp <;> ring

theorem componentDensityA_cube {M T t : ℝ} (hM : 0 < M) (hT : 0 < T) (ht : 0 < t) :
    (componentDensityA M T t)^3=(79507/2000)*M*T/t^3 := by
  unfold componentDensityA
  rw [mul_pow,Cycle13.cubeScale_cube (by positivity)]
  field_simp <;> ring

theorem componentDensitySquare_square {M t : ℝ} (hM : 0 < M) (ht : 0 < t) :
    (3*sqrt M/t)^2=9*M/t^2 := by
  rw [div_pow,mul_pow,sq_sqrt hM.le]
  ring

end
end Cycle12
