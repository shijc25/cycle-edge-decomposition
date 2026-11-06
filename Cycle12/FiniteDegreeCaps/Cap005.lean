import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(11897/100),118,(97/100),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,650936439596268340441058798985218262⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((11897/100):ℚ):ℝ)≤(650936439596268340441058798985218262:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap005
