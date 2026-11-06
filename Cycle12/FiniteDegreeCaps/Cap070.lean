import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap070
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(6519/50),130,(19/50),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,1771294746972267594110951210370077539383⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((6519/50):ℚ):ℝ)≤(1771294746972267594110951210370077539383:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap070
