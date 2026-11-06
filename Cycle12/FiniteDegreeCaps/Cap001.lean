import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(1129/8),141,(1/8),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,3039891885399407640496161951118285510805163⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((1129/8):ℚ):ℝ)≤(3039891885399407640496161951118285510805163:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap001
