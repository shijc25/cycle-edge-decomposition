import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap045
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(18103/125),144,(103/125),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,39479177130817191290082603947867834945483390⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((18103/125):ℚ):ℝ)≤(39479177130817191290082603947867834945483390:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap045
