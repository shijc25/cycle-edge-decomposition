import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap058
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(3374/25),134,(24/25),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,42365097945960121146926278486644754657825⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((3374/25):ℚ):ℝ)≤(42365097945960121146926278486644754657825:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap058
