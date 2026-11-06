import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap034
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(152361/1000),152,(361/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,7332147100343783966064903925133557246958936853⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((152361/1000):ℚ):ℝ)≤(7332147100343783966064903925133557246958936853:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap034
