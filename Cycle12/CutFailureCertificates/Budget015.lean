import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay037
import Cycle12.CutFailureCertificates.Decay038
import Cycle12.CutFailureCertificates.Decay039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget015

def certificate300 : RatFailureBudget := ⟨(10218753817620470541/1000000000000000000),(16258435397160067/500000000000000000),(976039807317173/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate750),(2,CutFailureCertificates.Decay037.certificate751),(2,CutFailureCertificates.Decay037.certificate752)]⟩
theorem numericValid300 : certificate300.NumericValid := by decide +kernel
theorem sound300 : certificate300.Sound := rat_failure_budget_sound certificate300 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound750,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound751,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound752,List.forall_mem_nil _⟩⟩⟩) numericValid300

def certificate301 : RatFailureBudget := ⟨(10218753817620470541/1000000000000000000),(7602349722463749/250000000000000000),(1625695944944831/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate753),(2,CutFailureCertificates.Decay037.certificate754)]⟩
theorem numericValid301 : certificate301.NumericValid := by decide +kernel
theorem sound301 : certificate301.Sound := rat_failure_budget_sound certificate301 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound753,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound754,List.forall_mem_nil _⟩⟩) numericValid301

def certificate302 : RatFailureBudget := ⟨(2542911107342622739/250000000000000000),(32719282867172671/1000000000000000000),(960254357979809/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate755),(2,CutFailureCertificates.Decay037.certificate756),(2,CutFailureCertificates.Decay037.certificate757)]⟩
theorem numericValid302 : certificate302.NumericValid := by decide +kernel
theorem sound302 : certificate302.Sound := rat_failure_budget_sound certificate302 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound755,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound756,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound757,List.forall_mem_nil _⟩⟩⟩) numericValid302

def certificate303 : RatFailureBudget := ⟨(2542911107342622739/250000000000000000),(30491781283398417/1000000000000000000),(1427996726584507/1000000000000000000),[(2,CutFailureCertificates.Decay037.certificate758),(2,CutFailureCertificates.Decay037.certificate759)]⟩
theorem numericValid303 : certificate303.NumericValid := by decide +kernel
theorem sound303 : certificate303.Sound := rat_failure_budget_sound certificate303 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound758,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay037.sound759,List.forall_mem_nil _⟩⟩) numericValid303

def certificate304 : RatFailureBudget := ⟨(158200301144349333/15625000000000000),(509555602155087/15625000000000000),(909635637880119/1000000000000000000),[(2,CutFailureCertificates.Decay038.certificate760),(2,CutFailureCertificates.Decay038.certificate761),(2,CutFailureCertificates.Decay038.certificate762)]⟩
theorem numericValid304 : certificate304.NumericValid := by decide +kernel
theorem sound304 : certificate304.Sound := rat_failure_budget_sound certificate304 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound760,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound761,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound762,List.forall_mem_nil _⟩⟩⟩) numericValid304

def certificate305 : RatFailureBudget := ⟨(158200301144349333/15625000000000000),(30574456867578659/1000000000000000000),(1255055988794609/1000000000000000000),[(2,CutFailureCertificates.Decay038.certificate763),(2,CutFailureCertificates.Decay038.certificate764)]⟩
theorem numericValid305 : certificate305.NumericValid := by decide +kernel
theorem sound305 : certificate305.Sound := rat_failure_budget_sound certificate305 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound763,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound764,List.forall_mem_nil _⟩⟩) numericValid305

def certificate306 : RatFailureBudget := ⟨(5039138065107057977/500000000000000000),(8180047192955141/250000000000000000),(106688384143559/125000000000000000),[(2,CutFailureCertificates.Decay038.certificate765),(2,CutFailureCertificates.Decay038.certificate766),(2,CutFailureCertificates.Decay038.certificate767)]⟩
theorem numericValid306 : certificate306.NumericValid := by decide +kernel
theorem sound306 : certificate306.Sound := rat_failure_budget_sound certificate306 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound765,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound766,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound767,List.forall_mem_nil _⟩⟩⟩) numericValid306

def certificate307 : RatFailureBudget := ⟨(5039138065107057977/500000000000000000),(15337148727533541/500000000000000000),(44119028540629/40000000000000000),[(2,CutFailureCertificates.Decay038.certificate768),(2,CutFailureCertificates.Decay038.certificate769)]⟩
theorem numericValid307 : certificate307.NumericValid := by decide +kernel
theorem sound307 : certificate307.Sound := rat_failure_budget_sound certificate307 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound768,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound769,List.forall_mem_nil _⟩⟩) numericValid307

def certificate308 : RatFailureBudget := ⟨(2508003200668990217/250000000000000000),(16464430125123609/500000000000000000),(105415857505417/125000000000000000),[(2,CutFailureCertificates.Decay038.certificate770),(2,CutFailureCertificates.Decay038.certificate771),(2,CutFailureCertificates.Decay038.certificate772)]⟩
theorem numericValid308 : certificate308.NumericValid := by decide +kernel
theorem sound308 : certificate308.Sound := rat_failure_budget_sound certificate308 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound770,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound771,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound772,List.forall_mem_nil _⟩⟩⟩) numericValid308

def certificate309 : RatFailureBudget := ⟨(2508003200668990217/250000000000000000),(15378649729959309/500000000000000000),(193984945072923/200000000000000000),[(2,CutFailureCertificates.Decay038.certificate773),(2,CutFailureCertificates.Decay038.certificate774)]⟩
theorem numericValid309 : certificate309.NumericValid := by decide +kernel
theorem sound309 : certificate309.Sound := rat_failure_budget_sound certificate309 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound773,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound774,List.forall_mem_nil _⟩⟩) numericValid309

def certificate310 : RatFailureBudget := ⟨(4993013557072285449/500000000000000000),(32998532471796423/1000000000000000000),(780864107039811/1000000000000000000),[(2,CutFailureCertificates.Decay038.certificate775),(2,CutFailureCertificates.Decay038.certificate776),(2,CutFailureCertificates.Decay038.certificate777)]⟩
theorem numericValid310 : certificate310.NumericValid := by decide +kernel
theorem sound310 : certificate310.Sound := rat_failure_budget_sound certificate310 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound775,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound776,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound777,List.forall_mem_nil _⟩⟩⟩) numericValid310

def certificate311 : RatFailureBudget := ⟨(4993013557072285449/500000000000000000),(30840462011912921/1000000000000000000),(53327514714689/62500000000000000),[(2,CutFailureCertificates.Decay038.certificate778),(2,CutFailureCertificates.Decay038.certificate779)]⟩
theorem numericValid311 : certificate311.NumericValid := by decide +kernel
theorem sound311 : certificate311.Sound := rat_failure_budget_sound certificate311 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound778,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay038.sound779,List.forall_mem_nil _⟩⟩) numericValid311

def certificate312 : RatFailureBudget := ⟨(4970158454520361661/500000000000000000),(4130574257981889/125000000000000000),(726558434149331/1000000000000000000),[(2,CutFailureCertificates.Decay039.certificate780),(2,CutFailureCertificates.Decay039.certificate781),(2,CutFailureCertificates.Decay039.certificate782)]⟩
theorem numericValid312 : certificate312.NumericValid := by decide +kernel
theorem sound312 : certificate312.Sound := rat_failure_budget_sound certificate312 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound780,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound781,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound782,List.forall_mem_nil _⟩⟩⟩) numericValid312

def certificate313 : RatFailureBudget := ⟨(4970158454520361661/500000000000000000),(15462094877256493/500000000000000000),(750731145233927/1000000000000000000),[(2,CutFailureCertificates.Decay039.certificate783),(2,CutFailureCertificates.Decay039.certificate784)]⟩
theorem numericValid313 : certificate313.NumericValid := by decide +kernel
theorem sound313 : certificate313.Sound := rat_failure_budget_sound certificate313 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound783,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound784,List.forall_mem_nil _⟩⟩) numericValid313

def certificate314 : RatFailureBudget := ⟨(9894880052446134049/1000000000000000000),(33098500359480089/1000000000000000000),(644222442443887/1000000000000000000),[(2,CutFailureCertificates.Decay039.certificate785),(2,CutFailureCertificates.Decay039.certificate786),(2,CutFailureCertificates.Decay039.certificate787)]⟩
theorem numericValid314 : certificate314.NumericValid := by decide +kernel
theorem sound314 : certificate314.Sound := rat_failure_budget_sound certificate314 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound785,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound786,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound787,List.forall_mem_nil _⟩⟩⟩) numericValid314

def certificate315 : RatFailureBudget := ⟨(9894880052446134049/1000000000000000000),(31008609774699839/1000000000000000000),(330926479471079/500000000000000000),[(2,CutFailureCertificates.Decay039.certificate788),(2,CutFailureCertificates.Decay039.certificate789)]⟩
theorem numericValid315 : certificate315.NumericValid := by decide +kernel
theorem sound315 : certificate315.Sound := rat_failure_budget_sound certificate315 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound788,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound789,List.forall_mem_nil _⟩⟩) numericValid315

def certificate316 : RatFailureBudget := ⟨(4924857214933737757/500000000000000000),(33360848907741823/1000000000000000000),(31758697104793/50000000000000000),[(2,CutFailureCertificates.Decay039.certificate790),(2,CutFailureCertificates.Decay039.certificate791),(2,CutFailureCertificates.Decay039.certificate792)]⟩
theorem numericValid316 : certificate316.NumericValid := by decide +kernel
theorem sound316 : certificate316.Sound := rat_failure_budget_sound certificate316 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound790,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound791,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound792,List.forall_mem_nil _⟩⟩⟩) numericValid316

def certificate317 : RatFailureBudget := ⟨(4924857214933737757/500000000000000000),(7777450020417219/250000000000000000),(72838010111393/125000000000000000),[(2,CutFailureCertificates.Decay039.certificate793),(2,CutFailureCertificates.Decay039.certificate794)]⟩
theorem numericValid317 : certificate317.NumericValid := by decide +kernel
theorem sound317 : certificate317.Sound := rat_failure_budget_sound certificate317 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound793,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound794,List.forall_mem_nil _⟩⟩) numericValid317

def certificate318 : RatFailureBudget := ⟨(1960963589400704839/200000000000000000),(33412079198293589/1000000000000000000),(609593943283571/1000000000000000000),[(2,CutFailureCertificates.Decay039.certificate795),(2,CutFailureCertificates.Decay039.certificate796),(2,CutFailureCertificates.Decay039.certificate797)]⟩
theorem numericValid318 : certificate318.NumericValid := by decide +kernel
theorem sound318 : certificate318.Sound := rat_failure_budget_sound certificate318 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound795,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound796,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound797,List.forall_mem_nil _⟩⟩⟩) numericValid318

def certificate319 : RatFailureBudget := ⟨(1960963589400704839/200000000000000000),(3899267918358347/125000000000000000),(513233304156227/1000000000000000000),[(2,CutFailureCertificates.Decay039.certificate798),(2,CutFailureCertificates.Decay039.certificate799)]⟩
theorem numericValid319 : certificate319.NumericValid := by decide +kernel
theorem sound319 : certificate319.Sound := rat_failure_budget_sound certificate319 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound798,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay039.sound799,List.forall_mem_nil _⟩⟩) numericValid319

end Cycle12.CutFailureCertificates.Budget015
