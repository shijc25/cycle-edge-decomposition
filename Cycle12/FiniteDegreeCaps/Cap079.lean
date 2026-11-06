import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap079
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(78179/500),156,(179/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,117070658727617178208706121255070553593363867540⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((78179/500):ℚ):ℝ)≤(117070658727617178208706121255070553593363867540:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap079
