import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay022
import Cycle12.CutFailureCertificates.Decay023
import Cycle12.CutFailureCertificates.Decay024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget009

def certificate180 : RatFailureBudget := ⟨(16686931111337825223/1000000000000000000),(23004735207723603/1000000000000000000),(16533947657547861/250000000000000000),[(2,CutFailureCertificates.Decay022.certificate450),(2,CutFailureCertificates.Decay022.certificate451),(2,CutFailureCertificates.Decay022.certificate452)]⟩
theorem numericValid180 : certificate180.NumericValid := by decide +kernel
theorem sound180 : certificate180.Sound := rat_failure_budget_sound certificate180 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound450,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound451,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound452,List.forall_mem_nil _⟩⟩⟩) numericValid180

def certificate181 : RatFailureBudget := ⟨(16686931111337825223/1000000000000000000),(1064063261370663/50000000000000000),(178716267717373/500000000000000000),[(2,CutFailureCertificates.Decay022.certificate453),(2,CutFailureCertificates.Decay022.certificate454)]⟩
theorem numericValid181 : certificate181.NumericValid := by decide +kernel
theorem sound181 : certificate181.Sound := rat_failure_budget_sound certificate181 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound453,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound454,List.forall_mem_nil _⟩⟩) numericValid181

def certificate182 : RatFailureBudget := ⟨(515827485430871273/31250000000000000),(23150053882451661/1000000000000000000),(6628918136521791/100000000000000000),[(2,CutFailureCertificates.Decay022.certificate455),(2,CutFailureCertificates.Decay022.certificate456),(2,CutFailureCertificates.Decay022.certificate457)]⟩
theorem numericValid182 : certificate182.NumericValid := by decide +kernel
theorem sound182 : certificate182.Sound := rat_failure_budget_sound certificate182 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound455,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound456,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound457,List.forall_mem_nil _⟩⟩⟩) numericValid182

def certificate183 : RatFailureBudget := ⟨(515827485430871273/31250000000000000),(21436952112152783/1000000000000000000),(304673460332891/1000000000000000000),[(2,CutFailureCertificates.Decay022.certificate458),(2,CutFailureCertificates.Decay022.certificate459)]⟩
theorem numericValid183 : certificate183.NumericValid := by decide +kernel
theorem sound183 : certificate183.Sound := rat_failure_budget_sound certificate183 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound458,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound459,List.forall_mem_nil _⟩⟩) numericValid183

def certificate184 : RatFailureBudget := ⟨(163286601437693719/10000000000000000),(23310645902042811/1000000000000000000),(28492739309454973/500000000000000000),[(2,CutFailureCertificates.Decay023.certificate460),(2,CutFailureCertificates.Decay023.certificate461),(2,CutFailureCertificates.Decay023.certificate462)]⟩
theorem numericValid184 : certificate184.NumericValid := by decide +kernel
theorem sound184 : certificate184.Sound := rat_failure_budget_sound certificate184 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound460,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound461,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound462,List.forall_mem_nil _⟩⟩⟩) numericValid184

def certificate185 : RatFailureBudget := ⟨(163286601437693719/10000000000000000),(10820349285422457/500000000000000000),(1848377071469953/1000000000000000000),[(2,CutFailureCertificates.Decay023.certificate463),(2,CutFailureCertificates.Decay023.certificate464)]⟩
theorem numericValid185 : certificate185.NumericValid := by decide +kernel
theorem sound185 : certificate185.Sound := rat_failure_budget_sound certificate185 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound463,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound464,List.forall_mem_nil _⟩⟩) numericValid185

def certificate186 : RatFailureBudget := ⟨(16153423088889835177/1000000000000000000),(23433049767490481/1000000000000000000),(448708059453523/8000000000000000),[(2,CutFailureCertificates.Decay023.certificate465),(2,CutFailureCertificates.Decay023.certificate466),(2,CutFailureCertificates.Decay023.certificate467)]⟩
theorem numericValid186 : certificate186.NumericValid := by decide +kernel
theorem sound186 : certificate186.Sound := rat_failure_budget_sound certificate186 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound465,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound466,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound467,List.forall_mem_nil _⟩⟩⟩) numericValid186

def certificate187 : RatFailureBudget := ⟨(16153423088889835177/1000000000000000000),(21798988617038939/1000000000000000000),(312318576807277/200000000000000000),[(2,CutFailureCertificates.Decay023.certificate468),(2,CutFailureCertificates.Decay023.certificate469)]⟩
theorem numericValid187 : certificate187.NumericValid := by decide +kernel
theorem sound187 : certificate187.Sound := rat_failure_budget_sound certificate187 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound468,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound469,List.forall_mem_nil _⟩⟩) numericValid187

def certificate188 : RatFailureBudget := ⟨(7990359840914203949/500000000000000000),(23613903562597717/1000000000000000000),(10634614633366891/200000000000000000),[(2,CutFailureCertificates.Decay023.certificate470),(2,CutFailureCertificates.Decay023.certificate471),(2,CutFailureCertificates.Decay023.certificate472)]⟩
theorem numericValid188 : certificate188.NumericValid := by decide +kernel
theorem sound188 : certificate188.Sound := rat_failure_budget_sound certificate188 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound470,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound471,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound472,List.forall_mem_nil _⟩⟩⟩) numericValid188

def certificate189 : RatFailureBudget := ⟨(7990359840914203949/500000000000000000),(10995409974422989/500000000000000000),(172007082411103/125000000000000000),[(2,CutFailureCertificates.Decay023.certificate473),(2,CutFailureCertificates.Decay023.certificate474)]⟩
theorem numericValid189 : certificate189.NumericValid := by decide +kernel
theorem sound189 : certificate189.Sound := rat_failure_budget_sound certificate189 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound473,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound474,List.forall_mem_nil _⟩⟩) numericValid189

def certificate190 : RatFailureBudget := ⟨(3952625591985861747/250000000000000000),(2974189607747253/125000000000000000),(47948847575566193/1000000000000000000),[(2,CutFailureCertificates.Decay023.certificate475),(2,CutFailureCertificates.Decay023.certificate476),(2,CutFailureCertificates.Decay023.certificate477)]⟩
theorem numericValid190 : certificate190.NumericValid := by decide +kernel
theorem sound190 : certificate190.Sound := rat_failure_budget_sound certificate190 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound475,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound476,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound477,List.forall_mem_nil _⟩⟩⟩) numericValid190

def certificate191 : RatFailureBudget := ⟨(3952625591985861747/250000000000000000),(4429268067607709/200000000000000000),(232641923079529/200000000000000000),[(2,CutFailureCertificates.Decay023.certificate478),(2,CutFailureCertificates.Decay023.certificate479)]⟩
theorem numericValid191 : certificate191.NumericValid := by decide +kernel
theorem sound191 : certificate191.Sound := rat_failure_budget_sound certificate191 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound478,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay023.sound479,List.forall_mem_nil _⟩⟩) numericValid191

def certificate192 : RatFailureBudget := ⟨(1564272469392366107/100000000000000000),(23961143530321269/1000000000000000000),(11151854993831269/250000000000000000),[(2,CutFailureCertificates.Decay024.certificate480),(2,CutFailureCertificates.Decay024.certificate481),(2,CutFailureCertificates.Decay024.certificate482)]⟩
theorem numericValid192 : certificate192.NumericValid := by decide +kernel
theorem sound192 : certificate192.Sound := rat_failure_budget_sound certificate192 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound480,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound481,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound482,List.forall_mem_nil _⟩⟩⟩) numericValid192

def certificate193 : RatFailureBudget := ⟨(1564272469392366107/100000000000000000),(5588753035487239/250000000000000000),(123311506611511/125000000000000000),[(2,CutFailureCertificates.Decay024.certificate483),(2,CutFailureCertificates.Decay024.certificate484)]⟩
theorem numericValid193 : certificate193.NumericValid := by decide +kernel
theorem sound193 : certificate193.Sound := rat_failure_budget_sound certificate193 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound483,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound484,List.forall_mem_nil _⟩⟩) numericValid193

def certificate194 : RatFailureBudget := ⟨(3869335319361141499/250000000000000000),(24642979932975421/1000000000000000000),(21048462035581251/500000000000000000),[(2,CutFailureCertificates.Decay024.certificate485),(2,CutFailureCertificates.Decay024.certificate486),(2,CutFailureCertificates.Decay024.certificate487)]⟩
theorem numericValid194 : certificate194.NumericValid := by decide +kernel
theorem sound194 : certificate194.Sound := rat_failure_budget_sound certificate194 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound485,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound486,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound487,List.forall_mem_nil _⟩⟩⟩) numericValid194

def certificate195 : RatFailureBudget := ⟨(3869335319361141499/250000000000000000),(4501975931612269/200000000000000000),(83616726844589/100000000000000000),[(2,CutFailureCertificates.Decay024.certificate488),(2,CutFailureCertificates.Decay024.certificate489)]⟩
theorem numericValid195 : certificate195.NumericValid := by decide +kernel
theorem sound195 : certificate195.Sound := rat_failure_budget_sound certificate195 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound488,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound489,List.forall_mem_nil _⟩⟩) numericValid195

def certificate196 : RatFailureBudget := ⟨(3828576944448409413/250000000000000000),(24340975160738451/1000000000000000000),(10189511121797953/250000000000000000),[(2,CutFailureCertificates.Decay024.certificate490),(2,CutFailureCertificates.Decay024.certificate491),(2,CutFailureCertificates.Decay024.certificate492)]⟩
theorem numericValid196 : certificate196.NumericValid := by decide +kernel
theorem sound196 : certificate196.Sound := rat_failure_budget_sound certificate196 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound490,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound491,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound492,List.forall_mem_nil _⟩⟩⟩) numericValid196

def certificate197 : RatFailureBudget := ⟨(3828576944448409413/250000000000000000),(355012944309087/15625000000000000),(750851699845797/1000000000000000000),[(2,CutFailureCertificates.Decay024.certificate493),(2,CutFailureCertificates.Decay024.certificate494)]⟩
theorem numericValid197 : certificate197.NumericValid := by decide +kernel
theorem sound197 : certificate197.Sound := rat_failure_budget_sound certificate197 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound493,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound494,List.forall_mem_nil _⟩⟩) numericValid197

def certificate198 : RatFailureBudget := ⟨(7497559102219071473/500000000000000000),(25323929085689743/1000000000000000000),(43692000100562163/250000000000000000),[(2,CutFailureCertificates.Decay024.certificate495),(2,CutFailureCertificates.Decay024.certificate496),(2,CutFailureCertificates.Decay024.certificate497)]⟩
theorem numericValid198 : certificate198.NumericValid := by decide +kernel
theorem sound198 : certificate198.Sound := rat_failure_budget_sound certificate198 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound495,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound496,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound497,List.forall_mem_nil _⟩⟩⟩) numericValid198

def certificate199 : RatFailureBudget := ⟨(7497559102219071473/500000000000000000),(23102787131753207/1000000000000000000),(1093665959268909/1000000000000000000),[(2,CutFailureCertificates.Decay024.certificate498),(2,CutFailureCertificates.Decay024.certificate499)]⟩
theorem numericValid199 : certificate199.NumericValid := by decide +kernel
theorem sound199 : certificate199.Sound := rat_failure_budget_sound certificate199 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound498,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay024.sound499,List.forall_mem_nil _⟩⟩) numericValid199

end Cycle12.CutFailureCertificates.Budget009
