import Cycle12.RationalRoutedCase
import Cycle12.CapacityCertificates.Batch0000
import Cycle12.SamplerCases.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.RoutedCases.Batch0000

def certificate0 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate0,SamplerCases.Batch000.certificate0⟩
theorem matches0 : certificate0.Matches := by decide +kernel
theorem sound0 : certificate0.rectangle.Sound := rat_routed_case_sound certificate0 matches0 CapacityCertificates.Batch0000.sound0 SamplerCases.Batch000.sound0

def certificate1 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate1,SamplerCases.Batch000.certificate1⟩
theorem matches1 : certificate1.Matches := by decide +kernel
theorem sound1 : certificate1.rectangle.Sound := rat_routed_case_sound certificate1 matches1 CapacityCertificates.Batch0000.sound1 SamplerCases.Batch000.sound1

def certificate2 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate2,SamplerCases.Batch000.certificate2⟩
theorem matches2 : certificate2.Matches := by decide +kernel
theorem sound2 : certificate2.rectangle.Sound := rat_routed_case_sound certificate2 matches2 CapacityCertificates.Batch0000.sound2 SamplerCases.Batch000.sound2

def certificate3 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate3,SamplerCases.Batch000.certificate2⟩
theorem matches3 : certificate3.Matches := by decide +kernel
theorem sound3 : certificate3.rectangle.Sound := rat_routed_case_sound certificate3 matches3 CapacityCertificates.Batch0000.sound3 SamplerCases.Batch000.sound2

def certificate4 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate4,SamplerCases.Batch000.certificate2⟩
theorem matches4 : certificate4.Matches := by decide +kernel
theorem sound4 : certificate4.rectangle.Sound := rat_routed_case_sound certificate4 matches4 CapacityCertificates.Batch0000.sound4 SamplerCases.Batch000.sound2

def certificate5 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate5,SamplerCases.Batch000.certificate2⟩
theorem matches5 : certificate5.Matches := by decide +kernel
theorem sound5 : certificate5.rectangle.Sound := rat_routed_case_sound certificate5 matches5 CapacityCertificates.Batch0000.sound5 SamplerCases.Batch000.sound2

def certificate6 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate6,SamplerCases.Batch000.certificate2⟩
theorem matches6 : certificate6.Matches := by decide +kernel
theorem sound6 : certificate6.rectangle.Sound := rat_routed_case_sound certificate6 matches6 CapacityCertificates.Batch0000.sound6 SamplerCases.Batch000.sound2

def certificate7 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate7,SamplerCases.Batch000.certificate2⟩
theorem matches7 : certificate7.Matches := by decide +kernel
theorem sound7 : certificate7.rectangle.Sound := rat_routed_case_sound certificate7 matches7 CapacityCertificates.Batch0000.sound7 SamplerCases.Batch000.sound2

def certificate8 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate8,SamplerCases.Batch000.certificate2⟩
theorem matches8 : certificate8.Matches := by decide +kernel
theorem sound8 : certificate8.rectangle.Sound := rat_routed_case_sound certificate8 matches8 CapacityCertificates.Batch0000.sound8 SamplerCases.Batch000.sound2

def certificate9 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate9,SamplerCases.Batch000.certificate2⟩
theorem matches9 : certificate9.Matches := by decide +kernel
theorem sound9 : certificate9.rectangle.Sound := rat_routed_case_sound certificate9 matches9 CapacityCertificates.Batch0000.sound9 SamplerCases.Batch000.sound2

def certificate10 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate10,SamplerCases.Batch000.certificate2⟩
theorem matches10 : certificate10.Matches := by decide +kernel
theorem sound10 : certificate10.rectangle.Sound := rat_routed_case_sound certificate10 matches10 CapacityCertificates.Batch0000.sound10 SamplerCases.Batch000.sound2

def certificate11 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate11,SamplerCases.Batch000.certificate3⟩
theorem matches11 : certificate11.Matches := by decide +kernel
theorem sound11 : certificate11.rectangle.Sound := rat_routed_case_sound certificate11 matches11 CapacityCertificates.Batch0000.sound11 SamplerCases.Batch000.sound3

def certificate12 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate12,SamplerCases.Batch000.certificate3⟩
theorem matches12 : certificate12.Matches := by decide +kernel
theorem sound12 : certificate12.rectangle.Sound := rat_routed_case_sound certificate12 matches12 CapacityCertificates.Batch0000.sound12 SamplerCases.Batch000.sound3

def certificate13 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate13,SamplerCases.Batch000.certificate3⟩
theorem matches13 : certificate13.Matches := by decide +kernel
theorem sound13 : certificate13.rectangle.Sound := rat_routed_case_sound certificate13 matches13 CapacityCertificates.Batch0000.sound13 SamplerCases.Batch000.sound3

def certificate14 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate14,SamplerCases.Batch000.certificate3⟩
theorem matches14 : certificate14.Matches := by decide +kernel
theorem sound14 : certificate14.rectangle.Sound := rat_routed_case_sound certificate14 matches14 CapacityCertificates.Batch0000.sound14 SamplerCases.Batch000.sound3

def certificate15 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate15,SamplerCases.Batch000.certificate3⟩
theorem matches15 : certificate15.Matches := by decide +kernel
theorem sound15 : certificate15.rectangle.Sound := rat_routed_case_sound certificate15 matches15 CapacityCertificates.Batch0000.sound15 SamplerCases.Batch000.sound3

def certificate16 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate16,SamplerCases.Batch000.certificate3⟩
theorem matches16 : certificate16.Matches := by decide +kernel
theorem sound16 : certificate16.rectangle.Sound := rat_routed_case_sound certificate16 matches16 CapacityCertificates.Batch0000.sound16 SamplerCases.Batch000.sound3

def certificate17 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate17,SamplerCases.Batch000.certificate3⟩
theorem matches17 : certificate17.Matches := by decide +kernel
theorem sound17 : certificate17.rectangle.Sound := rat_routed_case_sound certificate17 matches17 CapacityCertificates.Batch0000.sound17 SamplerCases.Batch000.sound3

def certificate18 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate18,SamplerCases.Batch000.certificate3⟩
theorem matches18 : certificate18.Matches := by decide +kernel
theorem sound18 : certificate18.rectangle.Sound := rat_routed_case_sound certificate18 matches18 CapacityCertificates.Batch0000.sound18 SamplerCases.Batch000.sound3

def certificate19 : RatRoutedCase := ⟨CapacityCertificates.Batch0000.certificate19,SamplerCases.Batch000.certificate3⟩
theorem matches19 : certificate19.Matches := by decide +kernel
theorem sound19 : certificate19.rectangle.Sound := rat_routed_case_sound certificate19 matches19 CapacityCertificates.Batch0000.sound19 SamplerCases.Batch000.sound3

end Cycle12.RoutedCases.Batch0000
