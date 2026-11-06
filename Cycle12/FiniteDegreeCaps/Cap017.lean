import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap017
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(134377/1000),134,(377/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,28281844320756810232884099595061470447267⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((134377/1000):ℚ):ℝ)≤(28281844320756810232884099595061470447267:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap017
