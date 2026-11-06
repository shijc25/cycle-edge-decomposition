import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap051
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(29473/200),147,(73/200),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,229765760524536285011143663458710300561139528⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((29473/200):ℚ):ℝ)≤(229765760524536285011143663458710300561139528:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap051
