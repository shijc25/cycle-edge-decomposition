import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap037
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(15637/125),125,(12/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,45461979058570194230553750618457693529⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((15637/125):ℚ):ℝ)≤(45461979058570194230553750618457693529:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap037
