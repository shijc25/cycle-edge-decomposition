import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap061
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(37341/250),149,(91/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,918426216874059306343638407390554876606939737⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((37341/250):ℚ):ℝ)≤(918426216874059306343638407390554876606939737:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap061
