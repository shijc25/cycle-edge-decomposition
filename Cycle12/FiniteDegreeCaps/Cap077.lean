import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap077
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(75681/500),151,(181/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,3668615559608479642466654557436404169499093393⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((75681/500):ℚ):ℝ)≤(3668615559608479642466654557436404169499093393:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap077
