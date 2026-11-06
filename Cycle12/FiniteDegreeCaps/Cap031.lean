import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap031
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(14876/125),119,(1/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,668309637461686303667006309182830588⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((14876/125):ℚ):ℝ)≤(668309637461686303667006309182830588:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap031
