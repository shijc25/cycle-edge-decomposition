import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap028
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(14729/100),147,(29/100),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,218126314418172357851918308863105554711732126⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((14729/100):ℚ):ℝ)≤(218126314418172357851918308863105554711732126:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap028
