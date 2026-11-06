import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap048
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(2379/20),118,(19/20),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,641974805276305857157267965746045865⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((2379/20):ℚ):ℝ)≤(641974805276305857157267965746045865:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap048
