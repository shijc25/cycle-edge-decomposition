import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay015
import Cycle12.CutFailureCertificates.Decay016
import Cycle12.CutFailureCertificates.Decay017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget006

def certificate120 : RatFailureBudget := ⟨(23925557571886382669/1000000000000000000),(1865337385141901/100000000000000000),(158912571277136839/500000000000000000),[(2,CutFailureCertificates.Decay015.certificate300),(2,CutFailureCertificates.Decay015.certificate301),(2,CutFailureCertificates.Decay015.certificate302)]⟩
theorem numericValid120 : certificate120.NumericValid := by decide +kernel
theorem sound120 : certificate120.Sound := rat_failure_budget_sound certificate120 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound300,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound301,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound302,List.forall_mem_nil _⟩⟩⟩) numericValid120

def certificate121 : RatFailureBudget := ⟨(23925557571886382669/1000000000000000000),(3991286971397407/250000000000000000),(6356242585919/250000000000000000),[(2,CutFailureCertificates.Decay015.certificate303),(2,CutFailureCertificates.Decay015.certificate304)]⟩
theorem numericValid121 : certificate121.NumericValid := by decide +kernel
theorem sound121 : certificate121.Sound := rat_failure_budget_sound certificate121 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound303,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound304,List.forall_mem_nil _⟩⟩) numericValid121

def certificate122 : RatFailureBudget := ⟨(11815244441221309253/500000000000000000),(3624716262704283/200000000000000000),(73325806724014683/250000000000000000),[(2,CutFailureCertificates.Decay015.certificate305),(2,CutFailureCertificates.Decay015.certificate306),(2,CutFailureCertificates.Decay015.certificate307)]⟩
theorem numericValid122 : certificate122.NumericValid := by decide +kernel
theorem sound122 : certificate122.Sound := rat_failure_budget_sound certificate122 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound305,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound306,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound307,List.forall_mem_nil _⟩⟩⟩) numericValid122

def certificate123 : RatFailureBudget := ⟨(11815244441221309253/500000000000000000),(8056932884057883/500000000000000000),(21489312464539/1000000000000000000),[(2,CutFailureCertificates.Decay015.certificate308),(2,CutFailureCertificates.Decay015.certificate309)]⟩
theorem numericValid123 : certificate123.NumericValid := by decide +kernel
theorem sound123 : certificate123.Sound := rat_failure_budget_sound certificate123 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound308,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound309,List.forall_mem_nil _⟩⟩) numericValid123

def certificate124 : RatFailureBudget := ⟨(2881904042286074339/125000000000000000),(18525832173662303/1000000000000000000),(372520750561153461/1000000000000000000),[(2,CutFailureCertificates.Decay015.certificate310),(2,CutFailureCertificates.Decay015.certificate311),(2,CutFailureCertificates.Decay015.certificate312)]⟩
theorem numericValid124 : certificate124.NumericValid := by decide +kernel
theorem sound124 : certificate124.Sound := rat_failure_budget_sound certificate124 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound310,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound311,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound312,List.forall_mem_nil _⟩⟩⟩) numericValid124

def certificate125 : RatFailureBudget := ⟨(2881904042286074339/125000000000000000),(16500281713273063/1000000000000000000),(263943700446291/500000000000000000),[(2,CutFailureCertificates.Decay015.certificate313),(2,CutFailureCertificates.Decay015.certificate314)]⟩
theorem numericValid125 : certificate125.NumericValid := by decide +kernel
theorem sound125 : certificate125.Sound := rat_failure_budget_sound certificate125 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound313,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound314,List.forall_mem_nil _⟩⟩) numericValid125

def certificate126 : RatFailureBudget := ⟨(22774827094450476843/1000000000000000000),(923854462074151/50000000000000000),(275948700136873489/1000000000000000000),[(2,CutFailureCertificates.Decay015.certificate315),(2,CutFailureCertificates.Decay015.certificate316),(2,CutFailureCertificates.Decay015.certificate317)]⟩
theorem numericValid126 : certificate126.NumericValid := by decide +kernel
theorem sound126 : certificate126.Sound := rat_failure_budget_sound certificate126 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound315,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound316,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound317,List.forall_mem_nil _⟩⟩⟩) numericValid126

def certificate127 : RatFailureBudget := ⟨(22774827094450476843/1000000000000000000),(16614355637323123/1000000000000000000),(113932320190909/500000000000000000),[(2,CutFailureCertificates.Decay015.certificate318),(2,CutFailureCertificates.Decay015.certificate319)]⟩
theorem numericValid127 : certificate127.NumericValid := by decide +kernel
theorem sound127 : certificate127.Sound := rat_failure_budget_sound certificate127 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound318,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay015.sound319,List.forall_mem_nil _⟩⟩) numericValid127

def certificate128 : RatFailureBudget := ⟨(22499097179828279839/1000000000000000000),(2346611273304627/125000000000000000),(268123794275254711/1000000000000000000),[(2,CutFailureCertificates.Decay016.certificate320),(2,CutFailureCertificates.Decay016.certificate321),(2,CutFailureCertificates.Decay016.certificate322)]⟩
theorem numericValid128 : certificate128.NumericValid := by decide +kernel
theorem sound128 : certificate128.Sound := rat_failure_budget_sound certificate128 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound320,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound321,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound322,List.forall_mem_nil _⟩⟩⟩) numericValid128

def certificate129 : RatFailureBudget := ⟨(22499097179828279839/1000000000000000000),(16763617652531573/1000000000000000000),(47287435250621/250000000000000000),[(2,CutFailureCertificates.Decay016.certificate323),(2,CutFailureCertificates.Decay016.certificate324)]⟩
theorem numericValid129 : certificate129.NumericValid := by decide +kernel
theorem sound129 : certificate129.Sound := rat_failure_budget_sound certificate129 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound323,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound324,List.forall_mem_nil _⟩⟩) numericValid129

def certificate130 : RatFailureBudget := ⟨(22227941112471521667/1000000000000000000),(189134591845649/10000000000000000),(131532047275969947/500000000000000000),[(2,CutFailureCertificates.Decay016.certificate325),(2,CutFailureCertificates.Decay016.certificate326),(2,CutFailureCertificates.Decay016.certificate327)]⟩
theorem numericValid130 : certificate130.NumericValid := by decide +kernel
theorem sound130 : certificate130.Sound := rat_failure_budget_sound certificate130 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound325,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound326,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound327,List.forall_mem_nil _⟩⟩⟩) numericValid130

def certificate131 : RatFailureBudget := ⟨(22227941112471521667/1000000000000000000),(1694248547148687/100000000000000000),(16606001405867/100000000000000000),[(2,CutFailureCertificates.Decay016.certificate328),(2,CutFailureCertificates.Decay016.certificate329)]⟩
theorem numericValid131 : certificate131.NumericValid := by decide +kernel
theorem sound131 : certificate131.Sound := rat_failure_budget_sound certificate131 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound328,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound329,List.forall_mem_nil _⟩⟩) numericValid131

def certificate132 : RatFailureBudget := ⟨(2196126012990289823/100000000000000000),(9571374745885839/500000000000000000),(3972538381860703/15625000000000000),[(2,CutFailureCertificates.Decay016.certificate330),(2,CutFailureCertificates.Decay016.certificate331),(2,CutFailureCertificates.Decay016.certificate332)]⟩
theorem numericValid132 : certificate132.NumericValid := by decide +kernel
theorem sound132 : certificate132.Sound := rat_failure_budget_sound certificate132 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound330,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound331,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound332,List.forall_mem_nil _⟩⟩⟩) numericValid132

def certificate133 : RatFailureBudget := ⟨(2196126012990289823/100000000000000000),(2140235680809759/125000000000000000),(69413183298801/500000000000000000),[(2,CutFailureCertificates.Decay016.certificate333),(2,CutFailureCertificates.Decay016.certificate334)]⟩
theorem numericValid133 : certificate133.NumericValid := by decide +kernel
theorem sound133 : certificate133.Sound := rat_failure_budget_sound certificate133 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound333,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound334,List.forall_mem_nil _⟩⟩) numericValid133

def certificate134 : RatFailureBudget := ⟨(2712369762803864527/125000000000000000),(9659543499585613/500000000000000000),(58500795899767191/250000000000000000),[(2,CutFailureCertificates.Decay016.certificate335),(2,CutFailureCertificates.Decay016.certificate336),(2,CutFailureCertificates.Decay016.certificate337)]⟩
theorem numericValid134 : certificate134.NumericValid := by decide +kernel
theorem sound134 : certificate134.Sound := rat_failure_budget_sound certificate134 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound335,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound336,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound337,List.forall_mem_nil _⟩⟩⟩) numericValid134

def certificate135 : RatFailureBudget := ⟨(2712369762803864527/125000000000000000),(17261601033569953/1000000000000000000),(24500057645001/200000000000000000),[(2,CutFailureCertificates.Decay016.certificate338),(2,CutFailureCertificates.Decay016.certificate339)]⟩
theorem numericValid135 : certificate135.NumericValid := by decide +kernel
theorem sound135 : certificate135.Sound := rat_failure_budget_sound certificate135 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound338,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay016.sound339,List.forall_mem_nil _⟩⟩) numericValid135

def certificate136 : RatFailureBudget := ⟨(21440941449663158427/1000000000000000000),(9807417994622857/500000000000000000),(22885053662261791/100000000000000000),[(2,CutFailureCertificates.Decay017.certificate340),(2,CutFailureCertificates.Decay017.certificate341),(2,CutFailureCertificates.Decay017.certificate342)]⟩
theorem numericValid136 : certificate136.NumericValid := by decide +kernel
theorem sound136 : certificate136.Sound := rat_failure_budget_sound certificate136 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound340,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound341,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound342,List.forall_mem_nil _⟩⟩⟩) numericValid136

def certificate137 : RatFailureBudget := ⟨(21440941449663158427/1000000000000000000),(3488591932857647/200000000000000000),(102807304393071/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate343),(2,CutFailureCertificates.Decay017.certificate344)]⟩
theorem numericValid137 : certificate137.NumericValid := by decide +kernel
theorem sound137 : certificate137.Sound := rat_failure_budget_sound certificate137 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound343,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound344,List.forall_mem_nil _⟩⟩) numericValid137

def certificate138 : RatFailureBudget := ⟨(5296779765021499049/250000000000000000),(9841111148733423/500000000000000000),(223718505651596653/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate345),(2,CutFailureCertificates.Decay017.certificate346),(2,CutFailureCertificates.Decay017.certificate347)]⟩
theorem numericValid138 : certificate138.NumericValid := by decide +kernel
theorem sound138 : certificate138.Sound := rat_failure_budget_sound certificate138 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound345,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound346,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound347,List.forall_mem_nil _⟩⟩⟩) numericValid138

def certificate139 : RatFailureBudget := ⟨(5296779765021499049/250000000000000000),(8809778830044911/500000000000000000),(17392940373459/200000000000000000),[(2,CutFailureCertificates.Decay017.certificate348),(2,CutFailureCertificates.Decay017.certificate349)]⟩
theorem numericValid139 : certificate139.NumericValid := by decide +kernel
theorem sound139 : certificate139.Sound := rat_failure_budget_sound certificate139 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound348,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound349,List.forall_mem_nil _⟩⟩) numericValid139

end Cycle12.CutFailureCertificates.Budget006
