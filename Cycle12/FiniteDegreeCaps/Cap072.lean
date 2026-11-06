import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap072
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(66247/500),132,(247/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,7667755311569313281707891913330983260422⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((66247/500):ℚ):ℝ)≤(7667755311569313281707891913330983260422:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap072
