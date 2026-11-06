import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap059
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(34843/250),139,(93/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,901887890325242653234841072585542127242369⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((34843/250):ℚ):ℝ)≤(901887890325242653234841072585542127242369:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap059
