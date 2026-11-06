import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(118941/1000),118,(941/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,637982423873021492762282650366549757⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((118941/1000):ℚ):ℝ)≤(637982423873021492762282650366549757:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap004
