import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap065
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(39587/250),158,(87/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,465047970473067799169018204287490036104415588528⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((39587/250):ℚ):ℝ)≤(465047970473067799169018204287490036104415588528:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap065
