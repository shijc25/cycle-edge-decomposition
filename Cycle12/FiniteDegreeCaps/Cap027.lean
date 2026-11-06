import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap027
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(146057/1000),146,(57/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,92797884694681216266763081339696743637575094⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((146057/1000):ℚ):ℝ)≤(92797884694681216266763081339696743637575094:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap027
