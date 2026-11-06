import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay065
import Cycle12.CutFailureCertificates.Decay066
import Cycle12.CutFailureCertificates.Decay067

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget026

def certificate520 : RatFailureBudget := ⟨(87172255218264550371/125000000000000000),(783732980653209/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1300),(2,CutFailureCertificates.Decay065.certificate1301),(2,CutFailureCertificates.Decay065.certificate1302)]⟩
theorem numericValid520 : certificate520.NumericValid := by decide +kernel
theorem sound520 : certificate520.Sound := rat_failure_budget_sound certificate520 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1300,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1301,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1302,List.forall_mem_nil _⟩⟩⟩) numericValid520

def certificate521 : RatFailureBudget := ⟨(87172255218264550371/125000000000000000),(188011526034287/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1303),(2,CutFailureCertificates.Decay065.certificate1304)]⟩
theorem numericValid521 : certificate521.NumericValid := by decide +kernel
theorem sound521 : certificate521.Sound := rat_failure_budget_sound certificate521 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1303,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1304,List.forall_mem_nil _⟩⟩) numericValid521

def certificate522 : RatFailureBudget := ⟨(125904482924188692167/200000000000000000),(34303760552179/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1305),(2,CutFailureCertificates.Decay065.certificate1306),(2,CutFailureCertificates.Decay065.certificate1307)]⟩
theorem numericValid522 : certificate522.NumericValid := by decide +kernel
theorem sound522 : certificate522.Sound := rat_failure_budget_sound certificate522 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1305,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1306,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1307,List.forall_mem_nil _⟩⟩⟩) numericValid522

def certificate523 : RatFailureBudget := ⟨(125904482924188692167/200000000000000000),(206881907472191/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1308),(2,CutFailureCertificates.Decay065.certificate1309)]⟩
theorem numericValid523 : certificate523.NumericValid := by decide +kernel
theorem sound523 : certificate523.Sound := rat_failure_budget_sound certificate523 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1308,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1309,List.forall_mem_nil _⟩⟩) numericValid523

def certificate524 : RatFailureBudget := ⟨(114167855278157797031/200000000000000000),(934093668684447/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1310),(2,CutFailureCertificates.Decay065.certificate1311),(2,CutFailureCertificates.Decay065.certificate1312)]⟩
theorem numericValid524 : certificate524.NumericValid := by decide +kernel
theorem sound524 : certificate524.Sound := rat_failure_budget_sound certificate524 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1310,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1311,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1312,List.forall_mem_nil _⟩⟩⟩) numericValid524

def certificate525 : RatFailureBudget := ⟨(114167855278157797031/200000000000000000),(1132934613376329/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1313),(2,CutFailureCertificates.Decay065.certificate1314)]⟩
theorem numericValid525 : certificate525.NumericValid := by decide +kernel
theorem sound525 : certificate525.Sound := rat_failure_budget_sound certificate525 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1313,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1314,List.forall_mem_nil _⟩⟩) numericValid525

def certificate526 : RatFailureBudget := ⟨(259878740177620710551/500000000000000000),(31505159667067/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1315),(2,CutFailureCertificates.Decay065.certificate1316),(2,CutFailureCertificates.Decay065.certificate1317)]⟩
theorem numericValid526 : certificate526.NumericValid := by decide +kernel
theorem sound526 : certificate526.Sound := rat_failure_budget_sound certificate526 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1315,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1316,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1317,List.forall_mem_nil _⟩⟩⟩) numericValid526

def certificate527 : RatFailureBudget := ⟨(259878740177620710551/500000000000000000),(306737926916159/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay065.certificate1318),(2,CutFailureCertificates.Decay065.certificate1319)]⟩
theorem numericValid527 : certificate527.NumericValid := by decide +kernel
theorem sound527 : certificate527.Sound := rat_failure_budget_sound certificate527 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1318,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay065.sound1319,List.forall_mem_nil _⟩⟩) numericValid527

def certificate528 : RatFailureBudget := ⟨(95005518140300851637/200000000000000000),(548254706428033/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1320),(2,CutFailureCertificates.Decay066.certificate1321),(2,CutFailureCertificates.Decay066.certificate1322)]⟩
theorem numericValid528 : certificate528.NumericValid := by decide +kernel
theorem sound528 : certificate528.Sound := rat_failure_budget_sound certificate528 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1320,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1321,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1322,List.forall_mem_nil _⟩⟩⟩) numericValid528

def certificate529 : RatFailureBudget := ⟨(95005518140300851637/200000000000000000),(1332759751987063/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1323),(2,CutFailureCertificates.Decay066.certificate1324)]⟩
theorem numericValid529 : certificate529.NumericValid := by decide +kernel
theorem sound529 : certificate529.Sound := rat_failure_budget_sound certificate529 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1323,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1324,List.forall_mem_nil _⟩⟩) numericValid529

def certificate530 : RatFailureBudget := ⟨(435646048538307062267/1000000000000000000),(590357814544379/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1325),(2,CutFailureCertificates.Decay066.certificate1326),(2,CutFailureCertificates.Decay066.certificate1327)]⟩
theorem numericValid530 : certificate530.NumericValid := by decide +kernel
theorem sound530 : certificate530.Sound := rat_failure_budget_sound certificate530 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1325,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1326,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1327,List.forall_mem_nil _⟩⟩⟩) numericValid530

def certificate531 : RatFailureBudget := ⟨(435646048538307062267/1000000000000000000),(17912699451749/12500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1328),(2,CutFailureCertificates.Decay066.certificate1329)]⟩
theorem numericValid531 : certificate531.NumericValid := by decide +kernel
theorem sound531 : certificate531.Sound := rat_failure_budget_sound certificate531 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1328,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1329,List.forall_mem_nil _⟩⟩) numericValid531

def certificate532 : RatFailureBudget := ⟨(40079938802876286037/100000000000000000),(633589209981383/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1330),(2,CutFailureCertificates.Decay066.certificate1331),(2,CutFailureCertificates.Decay066.certificate1332)]⟩
theorem numericValid532 : certificate532.NumericValid := by decide +kernel
theorem sound532 : certificate532.Sound := rat_failure_budget_sound certificate532 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1330,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1331,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1332,List.forall_mem_nil _⟩⟩⟩) numericValid532

def certificate533 : RatFailureBudget := ⟨(40079938802876286037/100000000000000000),(386053575112201/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1333),(2,CutFailureCertificates.Decay066.certificate1334)]⟩
theorem numericValid533 : certificate533.NumericValid := by decide +kernel
theorem sound533 : certificate533.Sound := rat_failure_budget_sound certificate533 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1333,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1334,List.forall_mem_nil _⟩⟩) numericValid533

def certificate534 : RatFailureBudget := ⟨(369822667834612896403/1000000000000000000),(339003811692693/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1335),(2,CutFailureCertificates.Decay066.certificate1336),(2,CutFailureCertificates.Decay066.certificate1337)]⟩
theorem numericValid534 : certificate534.NumericValid := by decide +kernel
theorem sound534 : certificate534.Sound := rat_failure_budget_sound certificate534 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1335,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1336,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1337,List.forall_mem_nil _⟩⟩⟩) numericValid534

def certificate535 : RatFailureBudget := ⟨(369822667834612896403/1000000000000000000),(1651779698807101/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay066.certificate1338),(2,CutFailureCertificates.Decay066.certificate1339)]⟩
theorem numericValid535 : certificate535.NumericValid := by decide +kernel
theorem sound535 : certificate535.Sound := rat_failure_budget_sound certificate535 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1338,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay066.sound1339,List.forall_mem_nil _⟩⟩) numericValid535

def certificate536 : RatFailureBudget := ⟨(68433625112009156493/200000000000000000),(1449428536980661/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1340),(2,CutFailureCertificates.Decay067.certificate1341),(2,CutFailureCertificates.Decay067.certificate1342)]⟩
theorem numericValid536 : certificate536.NumericValid := by decide +kernel
theorem sound536 : certificate536.Sound := rat_failure_budget_sound certificate536 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1340,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1341,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1342,List.forall_mem_nil _⟩⟩⟩) numericValid536

def certificate537 : RatFailureBudget := ⟨(68433625112009156493/200000000000000000),(1766533162546739/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1343),(2,CutFailureCertificates.Decay067.certificate1344)]⟩
theorem numericValid537 : certificate537.NumericValid := by decide +kernel
theorem sound537 : certificate537.Sound := rat_failure_budget_sound certificate537 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1343,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1344,List.forall_mem_nil _⟩⟩) numericValid537

def certificate538 : RatFailureBudget := ⟨(39672660125087068521/125000000000000000),(771431198337369/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1345),(2,CutFailureCertificates.Decay067.certificate1346),(2,CutFailureCertificates.Decay067.certificate1347)]⟩
theorem numericValid538 : certificate538.NumericValid := by decide +kernel
theorem sound538 : certificate538.Sound := rat_failure_budget_sound certificate538 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1345,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1346,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1347,List.forall_mem_nil _⟩⟩⟩) numericValid538

def certificate539 : RatFailureBudget := ⟨(39672660125087068521/125000000000000000),(1883121635670639/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1348),(2,CutFailureCertificates.Decay067.certificate1349)]⟩
theorem numericValid539 : certificate539.NumericValid := by decide +kernel
theorem sound539 : certificate539.Sound := rat_failure_budget_sound certificate539 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1348,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1349,List.forall_mem_nil _⟩⟩) numericValid539

end Cycle12.CutFailureCertificates.Budget026
