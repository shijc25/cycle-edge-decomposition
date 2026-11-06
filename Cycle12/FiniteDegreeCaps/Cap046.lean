import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap046
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(19336/125),154,(86/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,36789845946173851273415601531116182343975926952⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((19336/125):ℚ):ℝ)≤(36789845946173851273415601531116182343975926952:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap046
