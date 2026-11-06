import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap015
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(133377/1000),133,(377/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,14140922160378405116442049797530735223634⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((133377/1000):ℚ):ℝ)≤(14140922160378405116442049797530735223634:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap015
