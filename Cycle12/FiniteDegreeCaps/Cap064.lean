import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap064
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(3859/25),154,(9/25),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,29308266416891690168183630945593727539849315925⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((3859/25):ℚ):ℝ)≤(29308266416891690168183630945593727539849315925:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap064
