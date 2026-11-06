import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap075
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(71179/500),142,(179/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,7145425947730540662152473221134677343344963⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((71179/500):ℚ):ℝ)≤(7145425947730540662152473221134677343344963:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap075
