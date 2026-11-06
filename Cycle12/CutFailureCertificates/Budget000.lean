import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay000
import Cycle12.CutFailureCertificates.Decay001
import Cycle12.CutFailureCertificates.Decay002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget000

def certificate0 : RatFailureBudget := ⟨(418570030056423833731/62500000000000000),(35401393350581/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate0),(2,CutFailureCertificates.Decay000.certificate1),(2,CutFailureCertificates.Decay000.certificate2)]⟩
theorem numericValid0 : certificate0.NumericValid := by decide +kernel
theorem sound0 : certificate0.Sound := rat_failure_budget_sound certificate0 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound0,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound1,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound2,List.forall_mem_nil _⟩⟩⟩) numericValid0

def certificate1 : RatFailureBudget := ⟨(418570030056423833731/62500000000000000),(83003961671269/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate3),(2,CutFailureCertificates.Decay000.certificate4)]⟩
theorem numericValid1 : certificate1.NumericValid := by decide +kernel
theorem sound1 : certificate1.Sound := rat_failure_budget_sound certificate1 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound3,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound4,List.forall_mem_nil _⟩⟩) numericValid1

def certificate2 : RatFailureBudget := ⟨(13394240961805562679393/1000000000000000000),(607327306281/15625000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate5),(2,CutFailureCertificates.Decay000.certificate6),(2,CutFailureCertificates.Decay000.certificate7)]⟩
theorem numericValid2 : certificate2.NumericValid := by decide +kernel
theorem sound2 : certificate2.Sound := rat_failure_budget_sound certificate2 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound5,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound6,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound7,List.forall_mem_nil _⟩⟩⟩) numericValid2

def certificate3 : RatFailureBudget := ⟨(13394240961805562679393/1000000000000000000),(9082938330563/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate8),(2,CutFailureCertificates.Decay000.certificate9)]⟩
theorem numericValid3 : certificate3.NumericValid := by decide +kernel
theorem sound3 : certificate3.Sound := rat_failure_budget_sound certificate3 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound8,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound9,List.forall_mem_nil _⟩⟩) numericValid3

def certificate4 : RatFailureBudget := ⟨(3750800945834192207617/1000000000000000000),(79939348740341/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate10),(2,CutFailureCertificates.Decay000.certificate11),(2,CutFailureCertificates.Decay000.certificate12)]⟩
theorem numericValid4 : certificate4.NumericValid := by decide +kernel
theorem sound4 : certificate4.Sound := rat_failure_budget_sound certificate4 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound10,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound11,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound12,List.forall_mem_nil _⟩⟩⟩) numericValid4

def certificate5 : RatFailureBudget := ⟨(3750800945834192207617/1000000000000000000),(194407288344551/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate13),(2,CutFailureCertificates.Decay000.certificate14)]⟩
theorem numericValid5 : certificate5.NumericValid := by decide +kernel
theorem sound5 : certificate5.Sound := rat_failure_budget_sound certificate5 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound13,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound14,List.forall_mem_nil _⟩⟩) numericValid5

def certificate6 : RatFailureBudget := ⟨(597512157261602792499/250000000000000000),(136503168553943/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate15),(2,CutFailureCertificates.Decay000.certificate16),(2,CutFailureCertificates.Decay000.certificate17)]⟩
theorem numericValid6 : certificate6.NumericValid := by decide +kernel
theorem sound6 : certificate6.Sound := rat_failure_budget_sound certificate6 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound15,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound16,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound17,List.forall_mem_nil _⟩⟩⟩) numericValid6

def certificate7 : RatFailureBudget := ⟨(597512157261602792499/250000000000000000),(224006804693287/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay000.certificate18),(2,CutFailureCertificates.Decay000.certificate19)]⟩
theorem numericValid7 : certificate7.NumericValid := by decide +kernel
theorem sound7 : certificate7.Sound := rat_failure_budget_sound certificate7 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound18,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay000.sound19,List.forall_mem_nil _⟩⟩) numericValid7

def certificate8 : RatFailureBudget := ⟨(103280017745185957791/62500000000000000),(78097896465881/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate20),(2,CutFailureCertificates.Decay001.certificate21),(2,CutFailureCertificates.Decay001.certificate22)]⟩
theorem numericValid8 : certificate8.NumericValid := by decide +kernel
theorem sound8 : certificate8.Sound := rat_failure_budget_sound certificate8 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound20,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound21,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound22,List.forall_mem_nil _⟩⟩⟩) numericValid8

def certificate9 : RatFailureBudget := ⟨(103280017745185957791/62500000000000000),(316298204831381/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate23),(2,CutFailureCertificates.Decay001.certificate24)]⟩
theorem numericValid9 : certificate9.NumericValid := by decide +kernel
theorem sound9 : certificate9.Sound := rat_failure_budget_sound certificate9 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound23,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound24,List.forall_mem_nil _⟩⟩) numericValid9

def certificate10 : RatFailureBudget := ⟨(60435757821562209223/50000000000000000),(66048167550361/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate25),(2,CutFailureCertificates.Decay001.certificate26),(2,CutFailureCertificates.Decay001.certificate27)]⟩
theorem numericValid10 : certificate10.NumericValid := by decide +kernel
theorem sound10 : certificate10.Sound := rat_failure_budget_sound certificate10 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound25,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound26,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound27,List.forall_mem_nil _⟩⟩⟩) numericValid10

def certificate11 : RatFailureBudget := ⟨(60435757821562209223/50000000000000000),(425422815297647/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate28),(2,CutFailureCertificates.Decay001.certificate29)]⟩
theorem numericValid11 : certificate11.NumericValid := by decide +kernel
theorem sound11 : certificate11.Sound := rat_failure_budget_sound certificate11 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound28,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound29,List.forall_mem_nil _⟩⟩) numericValid11

def certificate12 : RatFailureBudget := ⟨(46065997685764341929/50000000000000000),(21417810641833/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate30),(2,CutFailureCertificates.Decay001.certificate31),(2,CutFailureCertificates.Decay001.certificate32)]⟩
theorem numericValid12 : certificate12.NumericValid := by decide +kernel
theorem sound12 : certificate12.Sound := rat_failure_budget_sound certificate12 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound30,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound31,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound32,List.forall_mem_nil _⟩⟩⟩) numericValid12

def certificate13 : RatFailureBudget := ⟨(46065997685764341929/50000000000000000),(139352950232467/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate33),(2,CutFailureCertificates.Decay001.certificate34)]⟩
theorem numericValid13 : certificate13.NumericValid := by decide +kernel
theorem sound13 : certificate13.Sound := rat_failure_budget_sound certificate13 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound33,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound34,List.forall_mem_nil _⟩⟩) numericValid13

def certificate14 : RatFailureBudget := ⟨(144942215441399063451/200000000000000000),(430825444878177/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate35),(2,CutFailureCertificates.Decay001.certificate36),(2,CutFailureCertificates.Decay001.certificate37)]⟩
theorem numericValid14 : certificate14.NumericValid := by decide +kernel
theorem sound14 : certificate14.Sound := rat_failure_budget_sound certificate14 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound35,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound36,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound37,List.forall_mem_nil _⟩⟩⟩) numericValid14

def certificate15 : RatFailureBudget := ⟨(144942215441399063451/200000000000000000),(35032887032953/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay001.certificate38),(2,CutFailureCertificates.Decay001.certificate39)]⟩
theorem numericValid15 : certificate15.NumericValid := by decide +kernel
theorem sound15 : certificate15.Sound := rat_failure_budget_sound certificate15 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound38,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay001.sound39,List.forall_mem_nil _⟩⟩) numericValid15

def certificate16 : RatFailureBudget := ⟨(146096017909295143181/250000000000000000),(211620523762297/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate40),(2,CutFailureCertificates.Decay002.certificate41),(2,CutFailureCertificates.Decay002.certificate42)]⟩
theorem numericValid16 : certificate16.NumericValid := by decide +kernel
theorem sound16 : certificate16.Sound := rat_failure_budget_sound certificate16 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound40,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound41,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound42,List.forall_mem_nil _⟩⟩⟩) numericValid16

def certificate17 : RatFailureBudget := ⟨(146096017909295143181/250000000000000000),(107380007139111/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate43),(2,CutFailureCertificates.Decay002.certificate44)]⟩
theorem numericValid17 : certificate17.NumericValid := by decide +kernel
theorem sound17 : certificate17.Sound := rat_failure_budget_sound certificate17 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound43,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound44,List.forall_mem_nil _⟩⟩) numericValid17

def certificate18 : RatFailureBudget := ⟨(240392192378436071551/500000000000000000),(635830324796969/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate45),(2,CutFailureCertificates.Decay002.certificate46),(2,CutFailureCertificates.Decay002.certificate47)]⟩
theorem numericValid18 : certificate18.NumericValid := by decide +kernel
theorem sound18 : certificate18.Sound := rat_failure_budget_sound certificate18 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound45,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound46,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound47,List.forall_mem_nil _⟩⟩⟩) numericValid18

def certificate19 : RatFailureBudget := ⟨(240392192378436071551/500000000000000000),(129474791460183/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate48),(2,CutFailureCertificates.Decay002.certificate49)]⟩
theorem numericValid19 : certificate19.NumericValid := by decide +kernel
theorem sound19 : certificate19.Sound := rat_failure_budget_sound certificate19 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound48,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound49,List.forall_mem_nil _⟩⟩) numericValid19

end Cycle12.CutFailureCertificates.Budget000
