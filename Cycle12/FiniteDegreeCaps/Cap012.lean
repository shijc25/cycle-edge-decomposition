import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap012
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(129381/1000),129,(381/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,886261470271176549143066578794950581920⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((129381/1000):ℚ):ℝ)≤(886261470271176549143066578794950581920:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap012
