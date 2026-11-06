import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay012
import Cycle12.CutFailureCertificates.Decay013
import Cycle12.CutFailureCertificates.Decay014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget005

def certificate100 : RatFailureBudget := ⟨(28272455108468384129/1000000000000000000),(79144450974431/5000000000000000),(49573630505012039/100000000000000000),[(2,CutFailureCertificates.Decay012.certificate250),(2,CutFailureCertificates.Decay012.certificate251),(2,CutFailureCertificates.Decay012.certificate252)]⟩
theorem numericValid100 : certificate100.NumericValid := by decide +kernel
theorem sound100 : certificate100.Sound := rat_failure_budget_sound certificate100 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound250,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound251,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound252,List.forall_mem_nil _⟩⟩⟩) numericValid100

def certificate101 : RatFailureBudget := ⟨(28272455108468384129/1000000000000000000),(1713406996608393/125000000000000000),(3621804580371/250000000000000000),[(2,CutFailureCertificates.Decay012.certificate253),(2,CutFailureCertificates.Decay012.certificate254)]⟩
theorem numericValid101 : certificate101.NumericValid := by decide +kernel
theorem sound101 : certificate101.Sound := rat_failure_budget_sound certificate101 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound253,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound254,List.forall_mem_nil _⟩⟩) numericValid101

def certificate102 : RatFailureBudget := ⟨(27900829796345877247/1000000000000000000),(15932492568383909/1000000000000000000),(369641604038915029/1000000000000000000),[(2,CutFailureCertificates.Decay012.certificate255),(2,CutFailureCertificates.Decay012.certificate256),(2,CutFailureCertificates.Decay012.certificate257)]⟩
theorem numericValid102 : certificate102.NumericValid := by decide +kernel
theorem sound102 : certificate102.Sound := rat_failure_budget_sound certificate102 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound255,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound256,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound257,List.forall_mem_nil _⟩⟩⟩) numericValid102

def certificate103 : RatFailureBudget := ⟨(27900829796345877247/1000000000000000000),(13817534106188837/1000000000000000000),(2860157030591/500000000000000000),[(2,CutFailureCertificates.Decay012.certificate258),(2,CutFailureCertificates.Decay012.certificate259)]⟩
theorem numericValid103 : certificate103.NumericValid := by decide +kernel
theorem sound103 : certificate103.Sound := rat_failure_budget_sound certificate103 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound258,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay012.sound259,List.forall_mem_nil _⟩⟩) numericValid103

def certificate104 : RatFailureBudget := ⟨(27535959003721291749/1000000000000000000),(16122433242096841/1000000000000000000),(98181674846256363/250000000000000000),[(2,CutFailureCertificates.Decay013.certificate260),(2,CutFailureCertificates.Decay013.certificate261),(2,CutFailureCertificates.Decay013.certificate262)]⟩
theorem numericValid104 : certificate104.NumericValid := by decide +kernel
theorem sound104 : certificate104.Sound := rat_failure_budget_sound certificate104 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound260,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound261,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound262,List.forall_mem_nil _⟩⟩⟩) numericValid104

def certificate105 : RatFailureBudget := ⟨(27535959003721291749/1000000000000000000),(1745288301884129/125000000000000000),(2422533928763/500000000000000000),[(2,CutFailureCertificates.Decay013.certificate263),(2,CutFailureCertificates.Decay013.certificate264)]⟩
theorem numericValid105 : certificate105.NumericValid := by decide +kernel
theorem sound105 : certificate105.Sound := rat_failure_budget_sound certificate105 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound263,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound264,List.forall_mem_nil _⟩⟩) numericValid105

def certificate106 : RatFailureBudget := ⟨(6706461380862321011/250000000000000000),(8243987427291237/500000000000000000),(15150151574059211/31250000000000000),[(2,CutFailureCertificates.Decay013.certificate265),(2,CutFailureCertificates.Decay013.certificate266),(2,CutFailureCertificates.Decay013.certificate267)]⟩
theorem numericValid106 : certificate106.NumericValid := by decide +kernel
theorem sound106 : certificate106.Sound := rat_failure_budget_sound certificate106 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound265,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound266,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound267,List.forall_mem_nil _⟩⟩⟩) numericValid106

def certificate107 : RatFailureBudget := ⟨(6706461380862321011/250000000000000000),(2914065394149237/200000000000000000),(224467046831319/1000000000000000000),[(2,CutFailureCertificates.Decay013.certificate268),(2,CutFailureCertificates.Decay013.certificate269)]⟩
theorem numericValid107 : certificate107.NumericValid := by decide +kernel
theorem sound107 : certificate107.Sound := rat_failure_budget_sound certificate107 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound268,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound269,List.forall_mem_nil _⟩⟩) numericValid107

def certificate108 : RatFailureBudget := ⟨(26140889609024163467/1000000000000000000),(1682133912675229/100000000000000000),(116828212016924751/250000000000000000),[(2,CutFailureCertificates.Decay013.certificate270),(2,CutFailureCertificates.Decay013.certificate271),(2,CutFailureCertificates.Decay013.certificate272)]⟩
theorem numericValid108 : certificate108.NumericValid := by decide +kernel
theorem sound108 : certificate108.Sound := rat_failure_budget_sound certificate108 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound270,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound271,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound272,List.forall_mem_nil _⟩⟩⟩) numericValid108

def certificate109 : RatFailureBudget := ⟨(26140889609024163467/1000000000000000000),(14882396783682889/1000000000000000000),(39476754399999/250000000000000000),[(2,CutFailureCertificates.Decay013.certificate273),(2,CutFailureCertificates.Decay013.certificate274)]⟩
theorem numericValid109 : certificate109.NumericValid := by decide +kernel
theorem sound109 : certificate109.Sound := rat_failure_budget_sound certificate109 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound273,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound274,List.forall_mem_nil _⟩⟩) numericValid109

def certificate110 : RatFailureBudget := ⟨(1290374107000689903/50000000000000000),(16922674780676677/1000000000000000000),(337844993735306571/1000000000000000000),[(2,CutFailureCertificates.Decay013.certificate275),(2,CutFailureCertificates.Decay013.certificate276),(2,CutFailureCertificates.Decay013.certificate277)]⟩
theorem numericValid110 : certificate110.NumericValid := by decide +kernel
theorem sound110 : certificate110.Sound := rat_failure_budget_sound certificate110 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound275,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound276,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound277,List.forall_mem_nil _⟩⟩⟩) numericValid110

def certificate111 : RatFailureBudget := ⟨(1290374107000689903/50000000000000000),(749788919544419/50000000000000000),(64090669303251/1000000000000000000),[(2,CutFailureCertificates.Decay013.certificate278),(2,CutFailureCertificates.Decay013.certificate279)]⟩
theorem numericValid111 : certificate111.NumericValid := by decide +kernel
theorem sound111 : certificate111.Sound := rat_failure_budget_sound certificate111 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound278,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay013.sound279,List.forall_mem_nil _⟩⟩) numericValid111

def certificate112 : RatFailureBudget := ⟨(6369984013696635067/250000000000000000),(2154398048992629/125000000000000000),(170861676972295013/500000000000000000),[(2,CutFailureCertificates.Decay014.certificate280),(2,CutFailureCertificates.Decay014.certificate281),(2,CutFailureCertificates.Decay014.certificate282)]⟩
theorem numericValid112 : certificate112.NumericValid := by decide +kernel
theorem sound112 : certificate112.Sound := rat_failure_budget_sound certificate112 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound280,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound281,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound282,List.forall_mem_nil _⟩⟩⟩) numericValid112

def certificate113 : RatFailureBudget := ⟨(6369984013696635067/250000000000000000),(15154698806036059/1000000000000000000),(5396232064731/100000000000000000),[(2,CutFailureCertificates.Decay014.certificate283),(2,CutFailureCertificates.Decay014.certificate284)]⟩
theorem numericValid113 : certificate113.NumericValid := by decide +kernel
theorem sound113 : certificate113.Sound := rat_failure_budget_sound certificate113 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound283,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound284,List.forall_mem_nil _⟩⟩) numericValid113

def certificate114 : RatFailureBudget := ⟨(24841894796692238297/1000000000000000000),(17799805684244561/1000000000000000000),(218571460982147101/500000000000000000),[(2,CutFailureCertificates.Decay014.certificate285),(2,CutFailureCertificates.Decay014.certificate286),(2,CutFailureCertificates.Decay014.certificate287)]⟩
theorem numericValid114 : certificate114.NumericValid := by decide +kernel
theorem sound114 : certificate114.Sound := rat_failure_budget_sound certificate114 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound285,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound286,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound287,List.forall_mem_nil _⟩⟩⟩) numericValid114

def certificate115 : RatFailureBudget := ⟨(24841894796692238297/1000000000000000000),(3881923734943149/250000000000000000),(8110771563743/100000000000000000),[(2,CutFailureCertificates.Decay014.certificate288),(2,CutFailureCertificates.Decay014.certificate289)]⟩
theorem numericValid115 : certificate115.NumericValid := by decide +kernel
theorem sound115 : certificate115.Sound := rat_failure_budget_sound certificate115 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound288,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound289,List.forall_mem_nil _⟩⟩) numericValid115

def certificate116 : RatFailureBudget := ⟨(24531142369496734013/1000000000000000000),(9008369922735401/500000000000000000),(315661516963902499/1000000000000000000),[(2,CutFailureCertificates.Decay014.certificate290),(2,CutFailureCertificates.Decay014.certificate291),(2,CutFailureCertificates.Decay014.certificate292)]⟩
theorem numericValid116 : certificate116.NumericValid := by decide +kernel
theorem sound116 : certificate116.Sound := rat_failure_budget_sound certificate116 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound290,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound291,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound292,List.forall_mem_nil _⟩⟩⟩) numericValid116

def certificate117 : RatFailureBudget := ⟨(24531142369496734013/1000000000000000000),(15643595291777973/1000000000000000000),(34184371346249/1000000000000000000),[(2,CutFailureCertificates.Decay014.certificate293),(2,CutFailureCertificates.Decay014.certificate294)]⟩
theorem numericValid117 : certificate117.NumericValid := by decide +kernel
theorem sound117 : certificate117.Sound := rat_failure_budget_sound certificate117 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound293,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound294,List.forall_mem_nil _⟩⟩) numericValid117

def certificate118 : RatFailureBudget := ⟨(24225736566934492529/1000000000000000000),(17756889553589381/1000000000000000000),(321296392471560457/1000000000000000000),[(2,CutFailureCertificates.Decay014.certificate295),(2,CutFailureCertificates.Decay014.certificate296),(2,CutFailureCertificates.Decay014.certificate297)]⟩
theorem numericValid118 : certificate118.NumericValid := by decide +kernel
theorem sound118 : certificate118.Sound := rat_failure_budget_sound certificate118 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound295,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound296,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound297,List.forall_mem_nil _⟩⟩⟩) numericValid118

def certificate119 : RatFailureBudget := ⟨(24225736566934492529/1000000000000000000),(3158301324237303/200000000000000000),(28733069951083/1000000000000000000),[(2,CutFailureCertificates.Decay014.certificate298),(2,CutFailureCertificates.Decay014.certificate299)]⟩
theorem numericValid119 : certificate119.NumericValid := by decide +kernel
theorem sound119 : certificate119.Sound := rat_failure_budget_sound certificate119 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound298,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay014.sound299,List.forall_mem_nil _⟩⟩) numericValid119

end Cycle12.CutFailureCertificates.Budget005
