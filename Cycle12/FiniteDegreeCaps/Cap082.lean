import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap082
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(79147/500),158,(147/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,447962988848113113918344572173810198109414915141⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((79147/500):ℚ):ℝ)≤(447962988848113113918344572173810198109414915141:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap082
