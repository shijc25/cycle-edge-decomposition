import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap032
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(150363/1000),150,(363/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,1835579665821270196720681221859538388573575915⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((150363/1000):ℚ):ℝ)≤(1835579665821270196720681221859538388573575915:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap032
