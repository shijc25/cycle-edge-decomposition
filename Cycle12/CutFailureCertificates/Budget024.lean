import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay060
import Cycle12.CutFailureCertificates.Decay061
import Cycle12.CutFailureCertificates.Decay062

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget024

def certificate480 : RatFailureBudget := ⟨(9412525033197477019/500000000000000000),(8101151577567/488281250000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1200),(2,CutFailureCertificates.Decay060.certificate1201),(2,CutFailureCertificates.Decay060.certificate1202)]⟩
theorem numericValid480 : certificate480.NumericValid := by decide +kernel
theorem sound480 : certificate480.Sound := rat_failure_budget_sound certificate480 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1200,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1201,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1202,List.forall_mem_nil _⟩⟩⟩) numericValid480

def certificate481 : RatFailureBudget := ⟨(9412525033197477019/500000000000000000),(15775090388640293/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1203),(2,CutFailureCertificates.Decay060.certificate1204)]⟩
theorem numericValid481 : certificate481.NumericValid := by decide +kernel
theorem sound481 : certificate481.Sound := rat_failure_budget_sound certificate481 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1203,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1204,List.forall_mem_nil _⟩⟩) numericValid481

def certificate482 : RatFailureBudget := ⟨(9244737841268092559/500000000000000000),(1673145273748633/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1205),(2,CutFailureCertificates.Decay060.certificate1206),(2,CutFailureCertificates.Decay060.certificate1207)]⟩
theorem numericValid482 : certificate482.NumericValid := by decide +kernel
theorem sound482 : certificate482.Sound := rat_failure_budget_sound certificate482 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1205,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1206,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1207,List.forall_mem_nil _⟩⟩⟩) numericValid482

def certificate483 : RatFailureBudget := ⟨(9244737841268092559/500000000000000000),(15919991077256263/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1208),(2,CutFailureCertificates.Decay060.certificate1209)]⟩
theorem numericValid483 : certificate483.NumericValid := by decide +kernel
theorem sound483 : certificate483.Sound := rat_failure_budget_sound certificate483 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1208,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1209,List.forall_mem_nil _⟩⟩) numericValid483

def certificate484 : RatFailureBudget := ⟨(18754004729170961038089/1000000000000000000),(2196581116551/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1210),(2,CutFailureCertificates.Decay060.certificate1211),(2,CutFailureCertificates.Decay060.certificate1212)]⟩
theorem numericValid484 : certificate484.NumericValid := by decide +kernel
theorem sound484 : certificate484.Sound := rat_failure_budget_sound certificate484 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1210,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1211,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1212,List.forall_mem_nil _⟩⟩⟩) numericValid484

def certificate485 : RatFailureBudget := ⟨(18754004729170961038089/1000000000000000000),(10039673111939/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1213),(2,CutFailureCertificates.Decay060.certificate1214)]⟩
theorem numericValid485 : certificate485.NumericValid := by decide +kernel
theorem sound485 : certificate485.Sound := rat_failure_budget_sound certificate485 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1213,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1214,List.forall_mem_nil _⟩⟩) numericValid485

def certificate486 : RatFailureBudget := ⟨(597512157261602792499/50000000000000000),(86307575911093/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1215),(2,CutFailureCertificates.Decay060.certificate1216),(2,CutFailureCertificates.Decay060.certificate1217)]⟩
theorem numericValid486 : certificate486.NumericValid := by decide +kernel
theorem sound486 : certificate486.Sound := rat_failure_budget_sound certificate486 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1215,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1216,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1217,List.forall_mem_nil _⟩⟩⟩) numericValid486

def certificate487 : RatFailureBudget := ⟨(597512157261602792499/50000000000000000),(10290569353659/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay060.certificate1218),(2,CutFailureCertificates.Decay060.certificate1219)]⟩
theorem numericValid487 : certificate487.NumericValid := by decide +kernel
theorem sound487 : certificate487.Sound := rat_failure_budget_sound certificate487 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1218,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay060.sound1219,List.forall_mem_nil _⟩⟩) numericValid487

def certificate488 : RatFailureBudget := ⟨(4131200709807438311641/500000000000000000),(476886284343/5000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1220),(2,CutFailureCertificates.Decay061.certificate1221),(2,CutFailureCertificates.Decay061.certificate1222)]⟩
theorem numericValid488 : certificate488.NumericValid := by decide +kernel
theorem sound488 : certificate488.Sound := rat_failure_budget_sound certificate488 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1220,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1221,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1222,List.forall_mem_nil _⟩⟩⟩) numericValid488

def certificate489 : RatFailureBudget := ⟨(4131200709807438311641/500000000000000000),(48927442923493/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1223),(2,CutFailureCertificates.Decay061.certificate1224)]⟩
theorem numericValid489 : certificate489.NumericValid := by decide +kernel
theorem sound489 : certificate489.Sound := rat_failure_budget_sound certificate489 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1223,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1224,List.forall_mem_nil _⟩⟩) numericValid489

def certificate490 : RatFailureBudget := ⟨(60435757821562209223/10000000000000000),(105470953369893/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1225),(2,CutFailureCertificates.Decay061.certificate1226),(2,CutFailureCertificates.Decay061.certificate1227)]⟩
theorem numericValid490 : certificate490.NumericValid := by decide +kernel
theorem sound490 : certificate490.Sound := rat_failure_budget_sound certificate490 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1225,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1226,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1227,List.forall_mem_nil _⟩⟩⟩) numericValid490

def certificate491 : RatFailureBudget := ⟨(60435757821562209223/10000000000000000),(23208630031949/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1228),(2,CutFailureCertificates.Decay061.certificate1229)]⟩
theorem numericValid491 : certificate491.NumericValid := by decide +kernel
theorem sound491 : certificate491.Sound := rat_failure_budget_sound certificate491 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1228,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1229,List.forall_mem_nil _⟩⟩) numericValid491

def certificate492 : RatFailureBudget := ⟨(1313239985870766615451/250000000000000000),(119974155436543/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1230),(2,CutFailureCertificates.Decay061.certificate1231),(2,CutFailureCertificates.Decay061.certificate1232)]⟩
theorem numericValid492 : certificate492.NumericValid := by decide +kernel
theorem sound492 : certificate492.Sound := rat_failure_budget_sound certificate492 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1230,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1231,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1232,List.forall_mem_nil _⟩⟩⟩) numericValid492

def certificate493 : RatFailureBudget := ⟨(1313239985870766615451/250000000000000000),(140216702201301/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1233),(2,CutFailureCertificates.Decay061.certificate1234)]⟩
theorem numericValid493 : certificate493.NumericValid := by decide +kernel
theorem sound493 : certificate493.Sound := rat_failure_budget_sound certificate493 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1233,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1234,List.forall_mem_nil _⟩⟩) numericValid493

def certificate494 : RatFailureBudget := ⟨(575824971072054274113/125000000000000000),(135974691782569/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1235),(2,CutFailureCertificates.Decay061.certificate1236),(2,CutFailureCertificates.Decay061.certificate1237)]⟩
theorem numericValid494 : certificate494.NumericValid := by decide +kernel
theorem sound494 : certificate494.Sound := rat_failure_budget_sound certificate494 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1235,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1236,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1237,List.forall_mem_nil _⟩⟩⟩) numericValid494

def certificate495 : RatFailureBudget := ⟨(575824971072054274113/125000000000000000),(15629349254077/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay061.certificate1238),(2,CutFailureCertificates.Decay061.certificate1239)]⟩
theorem numericValid495 : certificate495.NumericValid := by decide +kernel
theorem sound495 : certificate495.Sound := rat_failure_budget_sound certificate495 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1238,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay061.sound1239,List.forall_mem_nil _⟩⟩) numericValid495

def certificate496 : RatFailureBudget := ⟨(1811777693017488293139/500000000000000000),(171874052847573/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1240),(2,CutFailureCertificates.Decay062.certificate1241),(2,CutFailureCertificates.Decay062.certificate1242)]⟩
theorem numericValid496 : certificate496.NumericValid := by decide +kernel
theorem sound496 : certificate496.Sound := rat_failure_budget_sound certificate496 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1240,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1241,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1242,List.forall_mem_nil _⟩⟩⟩) numericValid496

def certificate497 : RatFailureBudget := ⟨(1811777693017488293139/500000000000000000),(201201942201773/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1243),(2,CutFailureCertificates.Decay062.certificate1244)]⟩
theorem numericValid497 : certificate497.NumericValid := by decide +kernel
theorem sound497 : certificate497.Sound := rat_failure_budget_sound certificate497 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1243,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1244,List.forall_mem_nil _⟩⟩) numericValid497

def certificate498 : RatFailureBudget := ⟨(1460960179092951431811/500000000000000000),(210788635479573/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1245),(2,CutFailureCertificates.Decay062.certificate1246),(2,CutFailureCertificates.Decay062.certificate1247)]⟩
theorem numericValid498 : certificate498.NumericValid := by decide +kernel
theorem sound498 : certificate498.Sound := rat_failure_budget_sound certificate498 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1245,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1246,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1247,List.forall_mem_nil _⟩⟩⟩) numericValid498

def certificate499 : RatFailureBudget := ⟨(1460960179092951431811/500000000000000000),(246614885723987/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1248),(2,CutFailureCertificates.Decay062.certificate1249)]⟩
theorem numericValid499 : certificate499.NumericValid := by decide +kernel
theorem sound499 : certificate499.Sound := rat_failure_budget_sound certificate499 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1248,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1249,List.forall_mem_nil _⟩⟩) numericValid499

end Cycle12.CutFailureCertificates.Budget024
