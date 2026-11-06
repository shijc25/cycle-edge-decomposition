import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap074
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(68713/500),137,(213/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,234071309143466037595495689614326634279890⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((68713/500):ℚ):ℝ)≤(234071309143466037595495689614326634279890:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap074
