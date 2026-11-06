import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(127383/1000),127,(383/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,221872735389386493941675456855404527667⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((127383/1000):ℚ):ℝ)≤(221872735389386493941675456855404527667:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap011
