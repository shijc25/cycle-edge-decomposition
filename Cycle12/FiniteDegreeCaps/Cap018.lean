import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap018
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(136193/1000),136,(193/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,99581393534143965369121777346071746617179⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((136193/1000):ℚ):ℝ)≤(99581393534143965369121777346071746617179:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap018
