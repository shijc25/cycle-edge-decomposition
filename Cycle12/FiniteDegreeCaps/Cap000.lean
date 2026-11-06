import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(1091/8),136,(3/8),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,112970658092375372859298640165435821012540⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((1091/8):ℚ):ℝ)≤(112970658092375372859298640165435821012540:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap000
