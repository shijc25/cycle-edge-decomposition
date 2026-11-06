import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap030
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(14867/125),118,(117/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,635775172365981020656871097119045640⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((14867/125):ℚ):ℝ)≤(635775172365981020656871097119045640:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap030
