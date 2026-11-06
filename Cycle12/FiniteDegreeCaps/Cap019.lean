import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap019
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(138373/1000),138,(373/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,451256624040523736523531848712918757867505⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((138373/1000):ℚ):ℝ)≤(451256624040523736523531848712918757867505:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap019
