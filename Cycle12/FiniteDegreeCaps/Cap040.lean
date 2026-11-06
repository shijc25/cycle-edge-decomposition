import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap040
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(158231/1000),158,(231/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,428822183552157062742188631835523708768739838525⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((158231/1000):ℚ):ℝ)≤(428822183552157062742188631835523708768739838525:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap040
