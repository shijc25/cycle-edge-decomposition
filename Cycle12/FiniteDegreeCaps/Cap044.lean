import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap044
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(18046/125),144,(46/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,28780505262346231490450551414217538830476226⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((18046/125):ℚ):ℝ)≤(28780505262346231490450551414217538830476226:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap044
