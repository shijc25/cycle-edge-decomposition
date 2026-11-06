import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay047
import Cycle12.CutFailureCertificates.Decay048
import Cycle12.CutFailureCertificates.Decay049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget019

def certificate380 : RatFailureBudget := ⟨(147929067133845158561/1000000000000000000),(3426929342808047/1000000000000000000),(29/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate950),(2,CutFailureCertificates.Decay047.certificate951),(2,CutFailureCertificates.Decay047.certificate952)]⟩
theorem numericValid380 : certificate380.NumericValid := by decide +kernel
theorem sound380 : certificate380.Sound := rat_failure_budget_sound certificate380 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound950,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound951,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound952,List.forall_mem_nil _⟩⟩⟩) numericValid380

def certificate381 : RatFailureBudget := ⟨(147929067133845158561/1000000000000000000),(31882751505031/10000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate953),(2,CutFailureCertificates.Decay047.certificate954)]⟩
theorem numericValid381 : certificate381.NumericValid := by decide +kernel
theorem sound381 : certificate381.Sound := rat_failure_budget_sound certificate381 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound953,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound954,List.forall_mem_nil _⟩⟩) numericValid381

def certificate382 : RatFailureBudget := ⟨(68433625112009156493/500000000000000000),(3700322588892879/1000000000000000000),(33/250000000000000000),[(2,CutFailureCertificates.Decay047.certificate955),(2,CutFailureCertificates.Decay047.certificate956),(2,CutFailureCertificates.Decay047.certificate957)]⟩
theorem numericValid382 : certificate382.NumericValid := by decide +kernel
theorem sound382 : certificate382.Sound := rat_failure_budget_sound certificate382 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound955,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound956,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound957,List.forall_mem_nil _⟩⟩⟩) numericValid382

def certificate383 : RatFailureBudget := ⟨(68433625112009156493/500000000000000000),(1709514791790849/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate958),(2,CutFailureCertificates.Decay047.certificate959)]⟩
theorem numericValid383 : certificate383.NumericValid := by decide +kernel
theorem sound383 : certificate383.Sound := rat_failure_budget_sound certificate383 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound958,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound959,List.forall_mem_nil _⟩⟩) numericValid383

def certificate384 : RatFailureBudget := ⟨(126952512400278619267/1000000000000000000),(982791801739351/250000000000000000),(29/50000000000000000),[(2,CutFailureCertificates.Decay048.certificate960),(2,CutFailureCertificates.Decay048.certificate961),(2,CutFailureCertificates.Decay048.certificate962)]⟩
theorem numericValid384 : certificate384.NumericValid := by decide +kernel
theorem sound384 : certificate384.Sound := rat_failure_budget_sound certificate384 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound960,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound961,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound962,List.forall_mem_nil _⟩⟩⟩) numericValid384

def certificate385 : RatFailureBudget := ⟨(126952512400278619267/1000000000000000000),(725204858549667/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay048.certificate963),(2,CutFailureCertificates.Decay048.certificate964)]⟩
theorem numericValid385 : certificate385.NumericValid := by decide +kernel
theorem sound385 : certificate385.Sound := rat_failure_budget_sound certificate385 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound963,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound964,List.forall_mem_nil _⟩⟩) numericValid385

def certificate386 : RatFailureBudget := ⟨(29508253281651770749/250000000000000000),(26109451123069/6250000000000000),(4181/250000000000000000),[(2,CutFailureCertificates.Decay048.certificate965),(2,CutFailureCertificates.Decay048.certificate966),(2,CutFailureCertificates.Decay048.certificate967)]⟩
theorem numericValid386 : certificate386.NumericValid := by decide +kernel
theorem sound386 : certificate386.Sound := rat_failure_budget_sound certificate386 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound965,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound966,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound967,List.forall_mem_nil _⟩⟩⟩) numericValid386

def certificate387 : RatFailureBudget := ⟨(29508253281651770749/250000000000000000),(1936448257834409/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay048.certificate968),(2,CutFailureCertificates.Decay048.certificate969)]⟩
theorem numericValid387 : certificate387.NumericValid := by decide +kernel
theorem sound387 : certificate387.Sound := rat_failure_budget_sound certificate387 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound968,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound969,List.forall_mem_nil _⟩⟩) numericValid387

def certificate388 : RatFailureBudget := ⟨(54990570427380060659/500000000000000000),(444565042415777/100000000000000000),(9057/100000000000000000),[(2,CutFailureCertificates.Decay048.certificate970),(2,CutFailureCertificates.Decay048.certificate971),(2,CutFailureCertificates.Decay048.certificate972)]⟩
theorem numericValid388 : certificate388.NumericValid := by decide +kernel
theorem sound388 : certificate388.Sound := rat_failure_budget_sound certificate388 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound970,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound971,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound972,List.forall_mem_nil _⟩⟩⟩) numericValid388

def certificate389 : RatFailureBudget := ⟨(54990570427380060659/500000000000000000),(4127902780019731/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay048.certificate973),(2,CutFailureCertificates.Decay048.certificate974)]⟩
theorem numericValid389 : certificate389.NumericValid := by decide +kernel
theorem sound389 : certificate389.Sound := rat_failure_budget_sound certificate389 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound973,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound974,List.forall_mem_nil _⟩⟩) numericValid389

def certificate390 : RatFailureBudget := ⟨(102689025408210014927/1000000000000000000),(117628769522511/25000000000000000),(331/800000000000000),[(2,CutFailureCertificates.Decay048.certificate975),(2,CutFailureCertificates.Decay048.certificate976),(2,CutFailureCertificates.Decay048.certificate977)]⟩
theorem numericValid390 : certificate390.NumericValid := by decide +kernel
theorem sound390 : certificate390.Sound := rat_failure_budget_sound certificate390 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound975,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound976,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound977,List.forall_mem_nil _⟩⟩⟩) numericValid390

def certificate391 : RatFailureBudget := ⟨(102689025408210014927/1000000000000000000),(217580133765473/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay048.certificate978),(2,CutFailureCertificates.Decay048.certificate979)]⟩
theorem numericValid391 : certificate391.NumericValid := by decide +kernel
theorem sound391 : certificate391.Sound := rat_failure_budget_sound certificate391 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound978,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay048.sound979,List.forall_mem_nil _⟩⟩) numericValid391

def certificate392 : RatFailureBudget := ⟨(9606499003605273279/100000000000000000),(990810123650341/200000000000000000),(866001/500000000000000000),[(2,CutFailureCertificates.Decay049.certificate980),(2,CutFailureCertificates.Decay049.certificate981),(2,CutFailureCertificates.Decay049.certificate982)]⟩
theorem numericValid392 : certificate392.NumericValid := by decide +kernel
theorem sound392 : certificate392.Sound := rat_failure_budget_sound certificate392 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound980,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound981,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound982,List.forall_mem_nil _⟩⟩⟩) numericValid392

def certificate393 : RatFailureBudget := ⟨(9606499003605273279/100000000000000000),(4619526817112969/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate983),(2,CutFailureCertificates.Decay049.certificate984)]⟩
theorem numericValid393 : certificate393.NumericValid := by decide +kernel
theorem sound393 : certificate393.Sound := rat_failure_budget_sound certificate393 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound983,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound984,List.forall_mem_nil _⟩⟩) numericValid393

def certificate394 : RatFailureBudget := ⟨(90030724948873378429/1000000000000000000),(2598592157493257/500000000000000000),(419249/200000000000000000),[(2,CutFailureCertificates.Decay049.certificate985),(2,CutFailureCertificates.Decay049.certificate986),(2,CutFailureCertificates.Decay049.certificate987)]⟩
theorem numericValid394 : certificate394.NumericValid := by decide +kernel
theorem sound394 : certificate394.Sound := rat_failure_budget_sound certificate394 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound985,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound986,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound987,List.forall_mem_nil _⟩⟩⟩) numericValid394

def certificate395 : RatFailureBudget := ⟨(90030724948873378429/1000000000000000000),(2448016377023213/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate988),(2,CutFailureCertificates.Decay049.certificate989)]⟩
theorem numericValid395 : certificate395.NumericValid := by decide +kernel
theorem sound395 : certificate395.Sound := rat_failure_budget_sound certificate395 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound988,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound989,List.forall_mem_nil _⟩⟩) numericValid395

def certificate396 : RatFailureBudget := ⟨(16903803902081400477/200000000000000000),(2750445640206703/500000000000000000),(6976857/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate990),(2,CutFailureCertificates.Decay049.certificate991),(2,CutFailureCertificates.Decay049.certificate992)]⟩
theorem numericValid396 : certificate396.NumericValid := by decide +kernel
theorem sound396 : certificate396.Sound := rat_failure_budget_sound certificate396 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound990,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound991,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound992,List.forall_mem_nil _⟩⟩⟩) numericValid396

def certificate397 : RatFailureBudget := ⟨(16903803902081400477/200000000000000000),(2567027225698353/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate993),(2,CutFailureCertificates.Decay049.certificate994)]⟩
theorem numericValid397 : certificate397.NumericValid := by decide +kernel
theorem sound397 : certificate397.Sound := rat_failure_budget_sound certificate397 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound993,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound994,List.forall_mem_nil _⟩⟩) numericValid397

def certificate398 : RatFailureBudget := ⟨(39735965222884822823/500000000000000000),(5796505973055277/1000000000000000000),(22139333/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate995),(2,CutFailureCertificates.Decay049.certificate996),(2,CutFailureCertificates.Decay049.certificate997)]⟩
theorem numericValid398 : certificate398.NumericValid := by decide +kernel
theorem sound398 : certificate398.Sound := rat_failure_budget_sound certificate398 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound995,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound996,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound997,List.forall_mem_nil _⟩⟩⟩) numericValid398

def certificate399 : RatFailureBudget := ⟨(39735965222884822823/500000000000000000),(5422766727703843/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay049.certificate998),(2,CutFailureCertificates.Decay049.certificate999)]⟩
theorem numericValid399 : certificate399.NumericValid := by decide +kernel
theorem sound399 : certificate399.Sound := rat_failure_budget_sound certificate399 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound998,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay049.sound999,List.forall_mem_nil _⟩⟩) numericValid399

end Cycle12.CutFailureCertificates.Budget019
