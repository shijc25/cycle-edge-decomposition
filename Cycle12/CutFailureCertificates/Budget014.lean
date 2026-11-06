import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay035
import Cycle12.CutFailureCertificates.Decay036
import Cycle12.CutFailureCertificates.Decay037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget014

def certificate280 : RatFailureBudget := ⟨(10705984450122921257/1000000000000000000),(31558628588687789/1000000000000000000),(1699378952354073/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate700),(2,CutFailureCertificates.Decay035.certificate701),(2,CutFailureCertificates.Decay035.certificate702)]⟩
theorem numericValid280 : certificate280.NumericValid := by decide +kernel
theorem sound280 : certificate280.Sound := rat_failure_budget_sound certificate280 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound700,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound701,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound702,List.forall_mem_nil _⟩⟩⟩) numericValid280

def certificate281 : RatFailureBudget := ⟨(10705984450122921257/1000000000000000000),(14791902329808399/500000000000000000),(1866503679321283/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate703),(2,CutFailureCertificates.Decay035.certificate704)]⟩
theorem numericValid281 : certificate281.NumericValid := by decide +kernel
theorem sound281 : certificate281.Sound := rat_failure_budget_sound certificate281 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound703,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound704,List.forall_mem_nil _⟩⟩) numericValid281

def certificate282 : RatFailureBudget := ⟨(1065590580728723149/100000000000000000),(3950294426469121/125000000000000000),(406659125041589/250000000000000000),[(2,CutFailureCertificates.Decay035.certificate705),(2,CutFailureCertificates.Decay035.certificate706),(2,CutFailureCertificates.Decay035.certificate707)]⟩
theorem numericValid282 : certificate282.NumericValid := by decide +kernel
theorem sound282 : certificate282.Sound := rat_failure_budget_sound certificate282 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound705,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound706,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound707,List.forall_mem_nil _⟩⟩⟩) numericValid282

def certificate283 : RatFailureBudget := ⟨(1065590580728723149/100000000000000000),(7419432137928933/250000000000000000),(1656496245807937/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate708),(2,CutFailureCertificates.Decay035.certificate709)]⟩
theorem numericValid283 : certificate283.NumericValid := by decide +kernel
theorem sound283 : certificate283.Sound := rat_failure_budget_sound certificate283 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound708,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound709,List.forall_mem_nil _⟩⟩) numericValid283

def certificate284 : RatFailureBudget := ⟨(662883426219344259/62500000000000000),(30472014659581883/1000000000000000000),(1550245048137171/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate710),(2,CutFailureCertificates.Decay035.certificate711),(2,CutFailureCertificates.Decay035.certificate712)]⟩
theorem numericValid284 : certificate284.NumericValid := by decide +kernel
theorem sound284 : certificate284.Sound := rat_failure_budget_sound certificate284 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound710,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound711,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound712,List.forall_mem_nil _⟩⟩⟩) numericValid284

def certificate285 : RatFailureBudget := ⟨(662883426219344259/62500000000000000),(7454604975185519/250000000000000000),(1477226108591711/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate713),(2,CutFailureCertificates.Decay035.certificate714)]⟩
theorem numericValid285 : certificate285.NumericValid := by decide +kernel
theorem sound285 : certificate285.Sound := rat_failure_budget_sound certificate285 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound713,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound714,List.forall_mem_nil _⟩⟩) numericValid285

def certificate286 : RatFailureBudget := ⟨(5278334519814354867/500000000000000000),(31488690224834909/1000000000000000000),(272400407864889/200000000000000000),[(2,CutFailureCertificates.Decay035.certificate715),(2,CutFailureCertificates.Decay035.certificate716),(2,CutFailureCertificates.Decay035.certificate717)]⟩
theorem numericValid286 : certificate286.NumericValid := by decide +kernel
theorem sound286 : certificate286.Sound := rat_failure_budget_sound certificate286 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound715,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound716,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound717,List.forall_mem_nil _⟩⟩⟩) numericValid286

def certificate287 : RatFailureBudget := ⟨(5278334519814354867/500000000000000000),(29830160507474979/1000000000000000000),(1259233621354453/1000000000000000000),[(2,CutFailureCertificates.Decay035.certificate718),(2,CutFailureCertificates.Decay035.certificate719)]⟩
theorem numericValid287 : certificate287.NumericValid := by decide +kernel
theorem sound287 : certificate287.Sound := rat_failure_budget_sound certificate287 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound718,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay035.sound719,List.forall_mem_nil _⟩⟩) numericValid287

def certificate288 : RatFailureBudget := ⟨(2626876511130089209/250000000000000000),(15827718684110439/500000000000000000),(65549630748623/50000000000000000),[(2,CutFailureCertificates.Decay036.certificate720),(2,CutFailureCertificates.Decay036.certificate721),(2,CutFailureCertificates.Decay036.certificate722)]⟩
theorem numericValid288 : certificate288.NumericValid := by decide +kernel
theorem sound288 : certificate288.Sound := rat_failure_budget_sound certificate288 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound720,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound721,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound722,List.forall_mem_nil _⟩⟩⟩) numericValid288

def certificate289 : RatFailureBudget := ⟨(2626876511130089209/250000000000000000),(14956913735381829/500000000000000000),(553706135423543/500000000000000000),[(2,CutFailureCertificates.Decay036.certificate723),(2,CutFailureCertificates.Decay036.certificate724)]⟩
theorem numericValid289 : certificate289.NumericValid := by decide +kernel
theorem sound289 : certificate289.Sound := rat_failure_budget_sound certificate289 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound723,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound724,List.forall_mem_nil _⟩⟩) numericValid289

def certificate290 : RatFailureBudget := ⟨(2614660858703792597/250000000000000000),(15948265934529739/500000000000000000),(1228778574600309/1000000000000000000),[(2,CutFailureCertificates.Decay036.certificate725),(2,CutFailureCertificates.Decay036.certificate726),(2,CutFailureCertificates.Decay036.certificate727)]⟩
theorem numericValid290 : certificate290.NumericValid := by decide +kernel
theorem sound290 : certificate290.Sound := rat_failure_budget_sound certificate290 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound725,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound726,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound727,List.forall_mem_nil _⟩⟩⟩) numericValid290

def certificate291 : RatFailureBudget := ⟨(2614660858703792597/250000000000000000),(14998698482049631/500000000000000000),(60881801113167/62500000000000000),[(2,CutFailureCertificates.Decay036.certificate728),(2,CutFailureCertificates.Decay036.certificate729)]⟩
theorem numericValid291 : certificate291.NumericValid := by decide +kernel
theorem sound291 : certificate291.Sound := rat_failure_budget_sound certificate291 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound728,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound729,List.forall_mem_nil _⟩⟩) numericValid291

def certificate292 : RatFailureBudget := ⟨(5205039417310767161/500000000000000000),(3207954511861031/100000000000000000),(294341144155949/250000000000000000),[(2,CutFailureCertificates.Decay036.certificate730),(2,CutFailureCertificates.Decay036.certificate731),(2,CutFailureCertificates.Decay036.certificate732)]⟩
theorem numericValid292 : certificate292.NumericValid := by decide +kernel
theorem sound292 : certificate292.Sound := rat_failure_budget_sound certificate292 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound730,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound731,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound732,List.forall_mem_nil _⟩⟩⟩) numericValid292

def certificate293 : RatFailureBudget := ⟨(5205039417310767161/500000000000000000),(3760095432385871/125000000000000000),(214339615773997/250000000000000000),[(2,CutFailureCertificates.Decay036.certificate733),(2,CutFailureCertificates.Decay036.certificate734)]⟩
theorem numericValid293 : certificate293.NumericValid := by decide +kernel
theorem sound293 : certificate293.Sound := rat_failure_budget_sound certificate293 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound733,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound734,List.forall_mem_nil _⟩⟩) numericValid293

def certificate294 : RatFailureBudget := ⟨(2590452472812930829/250000000000000000),(5092273717861/160000000000000),(1154458087088753/1000000000000000000),[(2,CutFailureCertificates.Decay036.certificate735),(2,CutFailureCertificates.Decay036.certificate736),(2,CutFailureCertificates.Decay036.certificate737)]⟩
theorem numericValid294 : certificate294.NumericValid := by decide +kernel
theorem sound294 : certificate294.Sound := rat_failure_budget_sound certificate294 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound735,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound736,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound737,List.forall_mem_nil _⟩⟩⟩) numericValid294

def certificate295 : RatFailureBudget := ⟨(2590452472812930829/250000000000000000),(60337863425613/2000000000000000),(756462013978869/1000000000000000000),[(2,CutFailureCertificates.Decay036.certificate738),(2,CutFailureCertificates.Decay036.certificate739)]⟩
theorem numericValid295 : certificate295.NumericValid := by decide +kernel
theorem sound295 : certificate295.Sound := rat_failure_budget_sound certificate295 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound738,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay036.sound739,List.forall_mem_nil _⟩⟩) numericValid295

def certificate296 : RatFailureBudget := ⟨(10313834274951837531/1000000000000000000),(32125102000871069/1000000000000000000),(1070754217048887/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate740),(2,CutFailureCertificates.Decay037.certificate741),(2,CutFailureCertificates.Decay037.certificate742)]⟩
theorem numericValid296 : certificate296.NumericValid := by decide +kernel
theorem sound296 : certificate296.Sound := rat_failure_budget_sound certificate296 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound740,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound741,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound742,List.forall_mem_nil _⟩⟩⟩) numericValid296

def certificate297 : RatFailureBudget := ⟨(10313834274951837531/1000000000000000000),(3780636171426801/125000000000000000),(2109081481450581/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate743),(2,CutFailureCertificates.Decay037.certificate744)]⟩
theorem numericValid297 : certificate297.NumericValid := by decide +kernel
theorem sound297 : certificate297.Sound := rat_failure_budget_sound certificate297 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound743,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound744,List.forall_mem_nil _⟩⟩) numericValid297

def certificate298 : RatFailureBudget := ⟨(10266149678635387143/1000000000000000000),(16195851671782833/500000000000000000),(1038987871023541/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate745),(2,CutFailureCertificates.Decay037.certificate746),(2,CutFailureCertificates.Decay037.certificate747)]⟩
theorem numericValid298 : certificate298.NumericValid := by decide +kernel
theorem sound298 : certificate298.Sound := rat_failure_budget_sound certificate298 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound745,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound746,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound747,List.forall_mem_nil _⟩⟩⟩) numericValid298

def certificate299 : RatFailureBudget := ⟨(10266149678635387143/1000000000000000000),(30327285031933253/1000000000000000000),(1851142951880523/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate748),(2,CutFailureCertificates.Decay037.certificate749)]⟩
theorem numericValid299 : certificate299.NumericValid := by decide +kernel
theorem sound299 : certificate299.Sound := rat_failure_budget_sound certificate299 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound748,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound749,List.forall_mem_nil _⟩⟩) numericValid299

end Cycle12.CutFailureCertificates.Budget014
