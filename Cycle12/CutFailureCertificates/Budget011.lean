import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay027
import Cycle12.CutFailureCertificates.Decay028
import Cycle12.CutFailureCertificates.Decay029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget011

def certificate220 : RatFailureBudget := ⟨(13390269966443149833/1000000000000000000),(1663414505955651/62500000000000000),(300816598678067/20000000000000000),[(2,CutFailureCertificates.Decay027.certificate550),(2,CutFailureCertificates.Decay027.certificate551),(2,CutFailureCertificates.Decay027.certificate552)]⟩
theorem numericValid220 : certificate220.NumericValid := by decide +kernel
theorem sound220 : certificate220.Sound := rat_failure_budget_sound certificate220 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound550,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound551,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound552,List.forall_mem_nil _⟩⟩⟩) numericValid220

def certificate221 : RatFailureBudget := ⟨(13390269966443149833/1000000000000000000),(12549599567290579/500000000000000000),(2835358775425901/1000000000000000000),[(2,CutFailureCertificates.Decay027.certificate553),(2,CutFailureCertificates.Decay027.certificate554)]⟩
theorem numericValid221 : certificate221.NumericValid := by decide +kernel
theorem sound221 : certificate221.Sound := rat_failure_budget_sound certificate221 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound553,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound554,List.forall_mem_nil _⟩⟩) numericValid221

def certificate222 : RatFailureBudget := ⟨(13256000331978180397/1000000000000000000),(26814122963973243/1000000000000000000),(6612264373857371/500000000000000000),[(2,CutFailureCertificates.Decay027.certificate555),(2,CutFailureCertificates.Decay027.certificate556),(2,CutFailureCertificates.Decay027.certificate557)]⟩
theorem numericValid222 : certificate222.NumericValid := by decide +kernel
theorem sound222 : certificate222.Sound := rat_failure_budget_sound certificate222 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound555,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound556,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound557,List.forall_mem_nil _⟩⟩⟩) numericValid222

def certificate223 : RatFailureBudget := ⟨(13256000331978180397/1000000000000000000),(25252728792474909/1000000000000000000),(2411512564894419/1000000000000000000),[(2,CutFailureCertificates.Decay027.certificate558),(2,CutFailureCertificates.Decay027.certificate559)]⟩
theorem numericValid223 : certificate223.NumericValid := by decide +kernel
theorem sound223 : certificate223.Sound := rat_failure_budget_sound certificate223 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound558,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay027.sound559,List.forall_mem_nil _⟩⟩) numericValid223

def certificate224 : RatFailureBudget := ⟨(13123523113560400721/1000000000000000000),(13516799924613263/500000000000000000),(6101829257958761/500000000000000000),[(2,CutFailureCertificates.Decay028.certificate560),(2,CutFailureCertificates.Decay028.certificate561),(2,CutFailureCertificates.Decay028.certificate562)]⟩
theorem numericValid224 : certificate224.NumericValid := by decide +kernel
theorem sound224 : certificate224.Sound := rat_failure_budget_sound certificate224 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound560,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound561,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound562,List.forall_mem_nil _⟩⟩⟩) numericValid224

def certificate225 : RatFailureBudget := ⟨(13123523113560400721/1000000000000000000),(25478828132664471/1000000000000000000),(1028560127376423/500000000000000000),[(2,CutFailureCertificates.Decay028.certificate563),(2,CutFailureCertificates.Decay028.certificate564)]⟩
theorem numericValid225 : certificate225.NumericValid := by decide +kernel
theorem sound225 : certificate225.Sound := rat_failure_budget_sound certificate225 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound563,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound564,List.forall_mem_nil _⟩⟩) numericValid225

def certificate226 : RatFailureBudget := ⟨(2611589389328495617/200000000000000000),(27099958230213001/1000000000000000000),(29064854000799/2500000000000000),[(2,CutFailureCertificates.Decay028.certificate565),(2,CutFailureCertificates.Decay028.certificate566),(2,CutFailureCertificates.Decay028.certificate567)]⟩
theorem numericValid226 : certificate226.NumericValid := by decide +kernel
theorem sound226 : certificate226.Sound := rat_failure_budget_sound certificate226 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound565,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound566,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound567,List.forall_mem_nil _⟩⟩⟩) numericValid226

def certificate227 : RatFailureBudget := ⟨(2611589389328495617/200000000000000000),(6373998954494737/250000000000000000),(372076117106977/250000000000000000),[(2,CutFailureCertificates.Decay028.certificate568),(2,CutFailureCertificates.Decay028.certificate569)]⟩
theorem numericValid227 : certificate227.NumericValid := by decide +kernel
theorem sound227 : certificate227.Sound := rat_failure_budget_sound certificate227 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound568,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound569,List.forall_mem_nil _⟩⟩) numericValid227

def certificate228 : RatFailureBudget := ⟨(12992807310559625963/1000000000000000000),(27290145427084069/1000000000000000000),(71768549296467/6250000000000000),[(2,CutFailureCertificates.Decay028.certificate570),(2,CutFailureCertificates.Decay028.certificate571),(2,CutFailureCertificates.Decay028.certificate572)]⟩
theorem numericValid228 : certificate228.NumericValid := by decide +kernel
theorem sound228 : certificate228.Sound := rat_failure_budget_sound certificate228 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound570,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound571,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound572,List.forall_mem_nil _⟩⟩⟩) numericValid228

def certificate229 : RatFailureBudget := ⟨(12992807310559625963/1000000000000000000),(6393488962020893/250000000000000000),(28381697829839/20000000000000000),[(2,CutFailureCertificates.Decay028.certificate573),(2,CutFailureCertificates.Decay028.certificate574)]⟩
theorem numericValid229 : certificate229.NumericValid := by decide +kernel
theorem sound229 : certificate229.Sound := rat_failure_budget_sound certificate229 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound573,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound574,List.forall_mem_nil _⟩⟩) numericValid229

def certificate230 : RatFailureBudget := ⟨(514552903344468501/40000000000000000),(13693271250278519/500000000000000000),(10557898578501229/1000000000000000000),[(2,CutFailureCertificates.Decay028.certificate575),(2,CutFailureCertificates.Decay028.certificate576),(2,CutFailureCertificates.Decay028.certificate577)]⟩
theorem numericValid230 : certificate230.NumericValid := by decide +kernel
theorem sound230 : certificate230.Sound := rat_failure_budget_sound certificate230 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound575,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound576,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound577,List.forall_mem_nil _⟩⟩⟩) numericValid230

def certificate231 : RatFailureBudget := ⟨(514552903344468501/40000000000000000),(25859479469644017/1000000000000000000),(1578845459593693/1000000000000000000),[(2,CutFailureCertificates.Decay028.certificate578),(2,CutFailureCertificates.Decay028.certificate579)]⟩
theorem numericValid231 : certificate231.NumericValid := by decide +kernel
theorem sound231 : certificate231.Sound := rat_failure_budget_sound certificate231 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound578,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay028.sound579,List.forall_mem_nil _⟩⟩) numericValid231

def certificate232 : RatFailureBudget := ⟨(1273653923783853421/100000000000000000),(27771005950602637/1000000000000000000),(2916731563713761/250000000000000000),[(2,CutFailureCertificates.Decay029.certificate580),(2,CutFailureCertificates.Decay029.certificate581),(2,CutFailureCertificates.Decay029.certificate582)]⟩
theorem numericValid232 : certificate232.NumericValid := by decide +kernel
theorem sound232 : certificate232.Sound := rat_failure_budget_sound certificate232 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound580,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound581,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound582,List.forall_mem_nil _⟩⟩⟩) numericValid232

def certificate233 : RatFailureBudget := ⟨(1273653923783853421/100000000000000000),(26013314557937917/1000000000000000000),(1351232942359899/1000000000000000000),[(2,CutFailureCertificates.Decay029.certificate583),(2,CutFailureCertificates.Decay029.certificate584)]⟩
theorem numericValid233 : certificate233.NumericValid := by decide +kernel
theorem sound233 : certificate233.Sound := rat_failure_budget_sound certificate233 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound583,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound584,List.forall_mem_nil _⟩⟩) numericValid233

def certificate234 : RatFailureBudget := ⟨(6305464103280704679/500000000000000000),(13940301166934373/500000000000000000),(2469771856900823/250000000000000000),[(2,CutFailureCertificates.Decay029.certificate585),(2,CutFailureCertificates.Decay029.certificate586),(2,CutFailureCertificates.Decay029.certificate587)]⟩
theorem numericValid234 : certificate234.NumericValid := by decide +kernel
theorem sound234 : certificate234.Sound := rat_failure_budget_sound certificate234 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound585,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound586,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound587,List.forall_mem_nil _⟩⟩⟩) numericValid234

def certificate235 : RatFailureBudget := ⟨(6305464103280704679/500000000000000000),(6561071781341719/250000000000000000),(1272214969268599/250000000000000000),[(2,CutFailureCertificates.Decay029.certificate588),(2,CutFailureCertificates.Decay029.certificate589)]⟩
theorem numericValid235 : certificate235.NumericValid := by decide +kernel
theorem sound235 : certificate235.Sound := rat_failure_budget_sound certificate235 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound588,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound589,List.forall_mem_nil _⟩⟩) numericValid235

def certificate236 : RatFailureBudget := ⟨(12486961035491489733/1000000000000000000),(27662162195154499/1000000000000000000),(2045386247265047/250000000000000000),[(2,CutFailureCertificates.Decay029.certificate590),(2,CutFailureCertificates.Decay029.certificate591),(2,CutFailureCertificates.Decay029.certificate592)]⟩
theorem numericValid236 : certificate236.NumericValid := by decide +kernel
theorem sound236 : certificate236.Sound := rat_failure_budget_sound certificate236 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound590,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound591,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound592,List.forall_mem_nil _⟩⟩⟩) numericValid236

def certificate237 : RatFailureBudget := ⟨(12486961035491489733/1000000000000000000),(26395790366834957/1000000000000000000),(4318178027988209/1000000000000000000),[(2,CutFailureCertificates.Decay029.certificate593),(2,CutFailureCertificates.Decay029.certificate594)]⟩
theorem numericValid237 : certificate237.NumericValid := by decide +kernel
theorem sound237 : certificate237.Sound := rat_failure_budget_sound certificate237 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound593,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound594,List.forall_mem_nil _⟩⟩) numericValid237

def certificate238 : RatFailureBudget := ⟨(1530480928390214573/125000000000000000),(30116829065019949/1000000000000000000),(37339707371396291/1000000000000000000),[(2,CutFailureCertificates.Decay029.certificate595),(2,CutFailureCertificates.Decay029.certificate596),(2,CutFailureCertificates.Decay029.certificate597)]⟩
theorem numericValid238 : certificate238.NumericValid := by decide +kernel
theorem sound238 : certificate238.Sound := rat_failure_budget_sound certificate238 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound595,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound596,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound597,List.forall_mem_nil _⟩⟩⟩) numericValid238

def certificate239 : RatFailureBudget := ⟨(1530480928390214573/125000000000000000),(13426106944505309/500000000000000000),(2970702156830151/500000000000000000),[(2,CutFailureCertificates.Decay029.certificate598),(2,CutFailureCertificates.Decay029.certificate599)]⟩
theorem numericValid239 : certificate239.NumericValid := by decide +kernel
theorem sound239 : certificate239.Sound := rat_failure_budget_sound certificate239 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound598,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay029.sound599,List.forall_mem_nil _⟩⟩) numericValid239

end Cycle12.CutFailureCertificates.Budget011
