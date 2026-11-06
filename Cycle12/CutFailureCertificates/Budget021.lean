import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay052
import Cycle12.CutFailureCertificates.Decay053
import Cycle12.CutFailureCertificates.Decay054

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget021

def certificate420 : RatFailureBudget := ⟨(43922520259805796461/1000000000000000000),(9204522776505381/1000000000000000000),(13599743/250000000000000000),[(2,CutFailureCertificates.Decay052.certificate1050),(2,CutFailureCertificates.Decay052.certificate1051),(2,CutFailureCertificates.Decay052.certificate1052)]⟩
theorem numericValid420 : certificate420.NumericValid := by decide +kernel
theorem sound420 : certificate420.Sound := rat_failure_budget_sound certificate420 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1050,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1051,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1052,List.forall_mem_nil _⟩⟩⟩) numericValid420

def certificate421 : RatFailureBudget := ⟨(43922520259805796461/1000000000000000000),(1742641969003349/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay052.certificate1053),(2,CutFailureCertificates.Decay052.certificate1054)]⟩
theorem numericValid421 : certificate421.NumericValid := by decide +kernel
theorem sound421 : certificate421.Sound := rat_failure_budget_sound certificate421 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1053,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1054,List.forall_mem_nil _⟩⟩) numericValid421

def certificate422 : RatFailureBudget := ⟨(10468701106791427219/250000000000000000),(9487181862614769/1000000000000000000),(29439/976562500000000),[(2,CutFailureCertificates.Decay052.certificate1055),(2,CutFailureCertificates.Decay052.certificate1056),(2,CutFailureCertificates.Decay052.certificate1057)]⟩
theorem numericValid422 : certificate422.NumericValid := by decide +kernel
theorem sound422 : certificate422.Sound := rat_failure_budget_sound certificate422 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1055,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1056,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1057,List.forall_mem_nil _⟩⟩⟩) numericValid422

def certificate423 : RatFailureBudget := ⟨(10468701106791427219/250000000000000000),(9006669916131303/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay052.certificate1058),(2,CutFailureCertificates.Decay052.certificate1059)]⟩
theorem numericValid423 : certificate423.NumericValid := by decide +kernel
theorem sound423 : certificate423.Sound := rat_failure_budget_sound certificate423 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1058,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1059,List.forall_mem_nil _⟩⟩) numericValid423

def certificate424 : RatFailureBudget := ⟨(1598231635868585481/40000000000000000),(9783089665309481/1000000000000000000),(31117807/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1060),(2,CutFailureCertificates.Decay053.certificate1061),(2,CutFailureCertificates.Decay053.certificate1062)]⟩
theorem numericValid424 : certificate424.NumericValid := by decide +kernel
theorem sound424 : certificate424.Sound := rat_failure_budget_sound certificate424 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1060,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1061,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1062,List.forall_mem_nil _⟩⟩⟩) numericValid424

def certificate425 : RatFailureBudget := ⟨(1598231635868585481/40000000000000000),(585264862804759/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1063),(2,CutFailureCertificates.Decay053.certificate1064)]⟩
theorem numericValid425 : certificate425.NumericValid := by decide +kernel
theorem sound425 : certificate425.Sound := rat_failure_budget_sound certificate425 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1063,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1064,List.forall_mem_nil _⟩⟩) numericValid425

def certificate426 : RatFailureBudget := ⟨(38155106028494393599/1000000000000000000),(517657277575271/50000000000000000),(4358769/250000000000000000),[(2,CutFailureCertificates.Decay053.certificate1065),(2,CutFailureCertificates.Decay053.certificate1066),(2,CutFailureCertificates.Decay053.certificate1067)]⟩
theorem numericValid426 : certificate426.NumericValid := by decide +kernel
theorem sound426 : certificate426.Sound := rat_failure_budget_sound certificate426 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1065,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1066,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1067,List.forall_mem_nil _⟩⟩⟩) numericValid426

def certificate427 : RatFailureBudget := ⟨(38155106028494393599/1000000000000000000),(4835040733720163/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1068),(2,CutFailureCertificates.Decay053.certificate1069)]⟩
theorem numericValid427 : certificate427.NumericValid := by decide +kernel
theorem sound427 : certificate427.Sound := rat_failure_budget_sound certificate427 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1068,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1069,List.forall_mem_nil _⟩⟩) numericValid427

def certificate428 : RatFailureBudget := ⟨(4557924207760763037/125000000000000000),(544385342372263/50000000000000000),(10726567/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1070),(2,CutFailureCertificates.Decay053.certificate1071),(2,CutFailureCertificates.Decay053.certificate1072)]⟩
theorem numericValid428 : certificate428.NumericValid := by decide +kernel
theorem sound428 : certificate428.Sound := rat_failure_budget_sound certificate428 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1070,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1071,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1072,List.forall_mem_nil _⟩⟩⟩) numericValid428

def certificate429 : RatFailureBudget := ⟨(4557924207760763037/125000000000000000),(5020085104204799/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1073),(2,CutFailureCertificates.Decay053.certificate1074)]⟩
theorem numericValid429 : certificate429.NumericValid := by decide +kernel
theorem sound429 : certificate429.Sound := rat_failure_budget_sound certificate429 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1073,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1074,List.forall_mem_nil _⟩⟩) numericValid429

def certificate430 : RatFailureBudget := ⟨(34872198057386390293/1000000000000000000),(679718358087351/62500000000000000),(425243/125000000000000000),[(2,CutFailureCertificates.Decay053.certificate1075),(2,CutFailureCertificates.Decay053.certificate1076),(2,CutFailureCertificates.Decay053.certificate1077)]⟩
theorem numericValid430 : certificate430.NumericValid := by decide +kernel
theorem sound430 : certificate430.Sound := rat_failure_budget_sound certificate430 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1075,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1076,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1077,List.forall_mem_nil _⟩⟩⟩) numericValid430

def certificate431 : RatFailureBudget := ⟨(34872198057386390293/1000000000000000000),(517169692074823/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay053.certificate1078),(2,CutFailureCertificates.Decay053.certificate1079)]⟩
theorem numericValid431 : certificate431.NumericValid := by decide +kernel
theorem sound431 : certificate431.Sound := rat_failure_budget_sound certificate431 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1078,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay053.sound1079,List.forall_mem_nil _⟩⟩) numericValid431

def certificate432 : RatFailureBudget := ⟨(33373862222675650447/1000000000000000000),(11137948627442567/1000000000000000000),(2009257/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1080),(2,CutFailureCertificates.Decay054.certificate1081),(2,CutFailureCertificates.Decay054.certificate1082)]⟩
theorem numericValid432 : certificate432.NumericValid := by decide +kernel
theorem sound432 : certificate432.Sound := rat_failure_budget_sound certificate432 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1080,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1081,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1082,List.forall_mem_nil _⟩⟩⟩) numericValid432

def certificate433 : RatFailureBudget := ⟨(33373862222675650447/1000000000000000000),(107231026545569/10000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1083),(2,CutFailureCertificates.Decay054.certificate1084)]⟩
theorem numericValid433 : certificate433.NumericValid := by decide +kernel
theorem sound433 : certificate433.Sound := rat_failure_budget_sound certificate433 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1083,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1084,List.forall_mem_nil _⟩⟩) numericValid433

def certificate434 : RatFailureBudget := ⟨(7990359840914203949/250000000000000000),(11465544587861279/1000000000000000000),(1247031/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1085),(2,CutFailureCertificates.Decay054.certificate1086),(2,CutFailureCertificates.Decay054.certificate1087)]⟩
theorem numericValid434 : certificate434.NumericValid := by decide +kernel
theorem sound434 : certificate434.Sound := rat_failure_budget_sound certificate434 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1085,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1086,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1087,List.forall_mem_nil _⟩⟩⟩) numericValid434

def certificate435 : RatFailureBudget := ⟨(7990359840914203949/250000000000000000),(2207189647778413/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1088),(2,CutFailureCertificates.Decay054.certificate1089)]⟩
theorem numericValid435 : certificate435.NumericValid := by decide +kernel
theorem sound435 : certificate435.Sound := rat_failure_budget_sound certificate435 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1088,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1089,List.forall_mem_nil _⟩⟩) numericValid435

def certificate436 : RatFailureBudget := ⟨(3828576944448409413/125000000000000000),(5915825525788253/500000000000000000),(456167/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1090),(2,CutFailureCertificates.Decay054.certificate1091),(2,CutFailureCertificates.Decay054.certificate1092)]⟩
theorem numericValid436 : certificate436.NumericValid := by decide +kernel
theorem sound436 : certificate436.Sound := rat_failure_budget_sound certificate436 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1090,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1091,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1092,List.forall_mem_nil _⟩⟩⟩) numericValid436

def certificate437 : RatFailureBudget := ⟨(3828576944448409413/125000000000000000),(457142912121679/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1093),(2,CutFailureCertificates.Decay054.certificate1094)]⟩
theorem numericValid437 : certificate437.NumericValid := by decide +kernel
theorem sound437 : certificate437.Sound := rat_failure_budget_sound certificate437 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1093,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1094,List.forall_mem_nil _⟩⟩) numericValid437

def certificate438 : RatFailureBudget := ⟨(29990236408876285893/1000000000000000000),(5953163392491853/500000000000000000),(39121/500000000000000000),[(2,CutFailureCertificates.Decay054.certificate1095),(2,CutFailureCertificates.Decay054.certificate1096),(2,CutFailureCertificates.Decay054.certificate1097)]⟩
theorem numericValid438 : certificate438.NumericValid := by decide +kernel
theorem sound438 : certificate438.Sound := rat_failure_budget_sound certificate438 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1095,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1096,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1097,List.forall_mem_nil _⟩⟩⟩) numericValid438

def certificate439 : RatFailureBudget := ⟨(29990236408876285893/1000000000000000000),(11511169512991139/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay054.certificate1098),(2,CutFailureCertificates.Decay054.certificate1099)]⟩
theorem numericValid439 : certificate439.NumericValid := by decide +kernel
theorem sound439 : certificate439.Sound := rat_failure_budget_sound certificate439 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1098,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay054.sound1099,List.forall_mem_nil _⟩⟩) numericValid439

end Cycle12.CutFailureCertificates.Budget021
