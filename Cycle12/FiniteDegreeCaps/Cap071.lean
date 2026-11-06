import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap071
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(66189/500),132,(189/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,7075363649256870067621444241642950425959⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((66189/500):ℚ):ℝ)≤(7075363649256870067621444241642950425959:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap071
