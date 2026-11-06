import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap052
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(29673/200),148,(73/200),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,459531521049072570022287326917420601122279056⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((29673/200):ℚ):ℝ)≤(459531521049072570022287326917420601122279056:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap052
