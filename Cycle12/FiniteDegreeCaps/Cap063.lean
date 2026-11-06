import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap063
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(3834/25),153,(9/25),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,14654133208445845084091815472796863769924657963⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((3834/25):ℚ):ℝ)≤(14654133208445845084091815472796863769924657963:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap063
