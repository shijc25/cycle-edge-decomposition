import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap029
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(148523/1000),148,(523/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,512717387882252224949043097362666392898070124⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((148523/1000):ℚ):ℝ)≤(512717387882252224949043097362666392898070124:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap029
