import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay067
import Cycle12.CutFailureCertificates.Decay068
import Cycle12.CutFailureCertificates.Decay069

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget027

def certificate540 : RatFailureBudget := ⟨(29508253281651770749/100000000000000000),(204755790035551/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1350),(2,CutFailureCertificates.Decay067.certificate1351),(2,CutFailureCertificates.Decay067.certificate1352)]⟩
theorem numericValid540 : certificate540.NumericValid := by decide +kernel
theorem sound540 : certificate540.Sound := rat_failure_budget_sound certificate540 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1350,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1351,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1352,List.forall_mem_nil _⟩⟩⟩) numericValid540

def certificate541 : RatFailureBudget := ⟨(29508253281651770749/100000000000000000),(502468286236711/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1353),(2,CutFailureCertificates.Decay067.certificate1354)]⟩
theorem numericValid541 : certificate541.NumericValid := by decide +kernel
theorem sound541 : certificate541.Sound := rat_failure_budget_sound certificate541 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1353,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1354,List.forall_mem_nil _⟩⟩) numericValid541

def certificate542 : RatFailureBudget := ⟨(274952852136900303297/1000000000000000000),(867612489067847/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1355),(2,CutFailureCertificates.Decay067.certificate1356),(2,CutFailureCertificates.Decay067.certificate1357)]⟩
theorem numericValid542 : certificate542.NumericValid := by decide +kernel
theorem sound542 : certificate542.Sound := rat_failure_budget_sound certificate542 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1355,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1356,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1357,List.forall_mem_nil _⟩⟩⟩) numericValid542

def certificate543 : RatFailureBudget := ⟨(274952852136900303297/1000000000000000000),(531445879390719/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay067.certificate1358),(2,CutFailureCertificates.Decay067.certificate1359)]⟩
theorem numericValid543 : certificate543.NumericValid := by decide +kernel
theorem sound543 : certificate543.Sound := rat_failure_budget_sound certificate543 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1358,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay067.sound1359,List.forall_mem_nil _⟩⟩) numericValid543

def certificate544 : RatFailureBudget := ⟨(256722563520525037319/1000000000000000000),(28718047058317/15625000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1360),(2,CutFailureCertificates.Decay068.certificate1361),(2,CutFailureCertificates.Decay068.certificate1362)]⟩
theorem numericValid544 : certificate544.NumericValid := by decide +kernel
theorem sound544 : certificate544.Sound := rat_failure_budget_sound certificate544 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1360,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1361,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1362,List.forall_mem_nil _⟩⟩⟩) numericValid544

def certificate545 : RatFailureBudget := ⟨(256722563520525037319/1000000000000000000),(11295294722529/5000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1363),(2,CutFailureCertificates.Decay068.certificate1364)]⟩
theorem numericValid545 : certificate545.NumericValid := by decide +kernel
theorem sound545 : certificate545.Sound := rat_failure_budget_sound certificate545 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1363,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1364,List.forall_mem_nil _⟩⟩) numericValid545

def certificate546 : RatFailureBudget := ⟨(9606499003605273279/40000000000000000),(1939030146639717/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1365),(2,CutFailureCertificates.Decay068.certificate1366),(2,CutFailureCertificates.Decay068.certificate1367)]⟩
theorem numericValid546 : certificate546.NumericValid := by decide +kernel
theorem sound546 : certificate546.Sound := rat_failure_budget_sound certificate546 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1365,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1366,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1367,List.forall_mem_nil _⟩⟩⟩) numericValid546

def certificate547 : RatFailureBudget := ⟨(9606499003605273279/40000000000000000),(1189665438616043/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1368),(2,CutFailureCertificates.Decay068.certificate1369)]⟩
theorem numericValid547 : certificate547.NumericValid := by decide +kernel
theorem sound547 : certificate547.Sound := rat_failure_budget_sound certificate547 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1368,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1369,List.forall_mem_nil _⟩⟩) numericValid547

def certificate548 : RatFailureBudget := ⟨(225076812372183446073/1000000000000000000),(1020913561117687/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1370),(2,CutFailureCertificates.Decay068.certificate1371),(2,CutFailureCertificates.Decay068.certificate1372)]⟩
theorem numericValid548 : certificate548.NumericValid := by decide +kernel
theorem sound548 : certificate548.Sound := rat_failure_budget_sound certificate548 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1370,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1371,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1372,List.forall_mem_nil _⟩⟩⟩) numericValid548

def certificate549 : RatFailureBudget := ⟨(225076812372183446073/1000000000000000000),(314807936684959/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1373),(2,CutFailureCertificates.Decay068.certificate1374)]⟩
theorem numericValid549 : certificate549.NumericValid := by decide +kernel
theorem sound549 : certificate549.Sound := rat_failure_budget_sound certificate549 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1373,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1374,List.forall_mem_nil _⟩⟩) numericValid549

def certificate550 : RatFailureBudget := ⟨(211297548776017505963/1000000000000000000),(107559396561899/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1375),(2,CutFailureCertificates.Decay068.certificate1376),(2,CutFailureCertificates.Decay068.certificate1377)]⟩
theorem numericValid550 : certificate550.NumericValid := by decide +kernel
theorem sound550 : certificate550.Sound := rat_failure_budget_sound certificate550 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1375,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1376,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1377,List.forall_mem_nil _⟩⟩⟩) numericValid550

def certificate551 : RatFailureBudget := ⟨(211297548776017505963/1000000000000000000),(1321579537701799/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay068.certificate1378),(2,CutFailureCertificates.Decay068.certificate1379)]⟩
theorem numericValid551 : certificate551.NumericValid := by decide +kernel
theorem sound551 : certificate551.Sound := rat_failure_budget_sound certificate551 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1378,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay068.sound1379,List.forall_mem_nil _⟩⟩) numericValid551

def certificate552 : RatFailureBudget := ⟨(39735965222884822823/200000000000000000),(2257696832119587/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1380),(2,CutFailureCertificates.Decay069.certificate1381),(2,CutFailureCertificates.Decay069.certificate1382)]⟩
theorem numericValid552 : certificate552.NumericValid := by decide +kernel
theorem sound552 : certificate552.Sound := rat_failure_budget_sound certificate552 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1380,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1381,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1382,List.forall_mem_nil _⟩⟩⟩) numericValid552

def certificate553 : RatFailureBudget := ⟨(39735965222884822823/200000000000000000),(346198269471967/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1383),(2,CutFailureCertificates.Decay069.certificate1384)]⟩
theorem numericValid553 : certificate553.NumericValid := by decide +kernel
theorem sound553 : certificate553.Sound := rat_failure_budget_sound certificate553 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1383,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1384,List.forall_mem_nil _⟩⟩) numericValid553

def certificate554 : RatFailureBudget := ⟨(46774558057064058789/250000000000000000),(473150024642369/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1385),(2,CutFailureCertificates.Decay069.certificate1386),(2,CutFailureCertificates.Decay069.certificate1387)]⟩
theorem numericValid554 : certificate554.NumericValid := by decide +kernel
theorem sound554 : certificate554.Sound := rat_failure_budget_sound certificate554 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1385,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1386,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1387,List.forall_mem_nil _⟩⟩⟩) numericValid554

def certificate555 : RatFailureBudget := ⟨(46774558057064058789/250000000000000000),(2897669900417069/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1388),(2,CutFailureCertificates.Decay069.certificate1389)]⟩
theorem numericValid555 : certificate555.NumericValid := by decide +kernel
theorem sound555 : certificate555.Sound := rat_failure_budget_sound certificate555 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1388,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1389,List.forall_mem_nil _⟩⟩) numericValid555

def certificate556 : RatFailureBudget := ⟨(88221878646497850223/500000000000000000),(62037471769821/25000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1390),(2,CutFailureCertificates.Decay069.certificate1391),(2,CutFailureCertificates.Decay069.certificate1392)]⟩
theorem numericValid556 : certificate556.NumericValid := by decide +kernel
theorem sound556 : certificate556.Sound := rat_failure_budget_sound certificate556 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1390,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1391,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1392,List.forall_mem_nil _⟩⟩⟩) numericValid556

def certificate557 : RatFailureBudget := ⟨(88221878646497850223/500000000000000000),(761469849235919/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1393),(2,CutFailureCertificates.Decay069.certificate1394)]⟩
theorem numericValid557 : certificate557.NumericValid := by decide +kernel
theorem sound557 : certificate557.Sound := rat_failure_budget_sound certificate557 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1393,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1394,List.forall_mem_nil _⟩⟩) numericValid557

def certificate558 : RatFailureBudget := ⟨(83310645544398190007/500000000000000000),(1288528820457829/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1395),(2,CutFailureCertificates.Decay069.certificate1396),(2,CutFailureCertificates.Decay069.certificate1397)]⟩
theorem numericValid558 : certificate558.NumericValid := by decide +kernel
theorem sound558 : certificate558.Sound := rat_failure_budget_sound certificate558 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1395,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1396,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1397,List.forall_mem_nil _⟩⟩⟩) numericValid558

def certificate559 : RatFailureBudget := ⟨(83310645544398190007/500000000000000000),(635425325087003/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay069.certificate1398),(2,CutFailureCertificates.Decay069.certificate1399)]⟩
theorem numericValid559 : certificate559.NumericValid := by decide +kernel
theorem sound559 : certificate559.Sound := rat_failure_budget_sound certificate559 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1398,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay069.sound1399,List.forall_mem_nil _⟩⟩) numericValid559

end Cycle12.CutFailureCertificates.Budget027
