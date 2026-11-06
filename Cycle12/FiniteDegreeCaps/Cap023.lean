import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap023
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(14237/100),142,(37/100),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,7205107795661628692346291366055370776205323⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((14237/100):ℚ):ℝ)≤(7205107795661628692346291366055370776205323:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap023
