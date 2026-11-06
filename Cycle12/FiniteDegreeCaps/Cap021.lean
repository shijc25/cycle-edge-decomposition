import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap021
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(140371/1000),140,(371/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,1802525931768420610924728584098284233749251⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((140371/1000):ℚ):ℝ)≤(1802525931768420610924728584098284233749251:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap021
