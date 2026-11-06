import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap033
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(150989/1000),150,(989/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,2832813708003270942547750922133747110809466749⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((150989/1000):ℚ):ℝ)≤(2832813708003270942547750922133747110809466749:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap033
