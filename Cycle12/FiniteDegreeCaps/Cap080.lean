import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap080
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(78577/500),157,(77/500),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,203267496626395180845420118032383754425194337737⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((78577/500):ℚ):ℝ)≤(203267496626395180845420118032383754425194337737:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap080
