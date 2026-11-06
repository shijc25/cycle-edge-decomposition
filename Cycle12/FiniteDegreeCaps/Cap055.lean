import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap055
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(30041/250),120,(41/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,1489252709682361412914201481594710078⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((30041/250):ℚ):ℝ)≤(1489252709682361412914201481594710078:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap055
