import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap053
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(29733/250),118,(233/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,634014870717104921314378551967008356⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((29733/250):ℚ):ℝ)≤(634014870717104921314378551967008356:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap053
