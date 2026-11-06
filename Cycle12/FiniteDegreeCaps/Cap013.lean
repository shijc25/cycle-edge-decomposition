import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap013
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(131261/1000),131,(261/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,3262107440672726068804752957763647316036⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((131261/1000):ℚ):ℝ)≤(3262107440672726068804752957763647316036:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap013
