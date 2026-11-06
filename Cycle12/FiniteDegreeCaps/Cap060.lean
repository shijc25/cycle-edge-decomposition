import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap060
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(34973/250),139,(223/250),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,1293266873453804653556125559966894103654592⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((34973/250):ℚ):ℝ)≤(1293266873453804653556125559966894103654592:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap060
