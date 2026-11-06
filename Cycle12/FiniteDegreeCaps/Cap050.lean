import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap050
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(25759/200),128,(159/200),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,590416235719178453698163031795489042151⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((25759/200):ℚ):ℝ)≤(590416235719178453698163031795489042151:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap050
