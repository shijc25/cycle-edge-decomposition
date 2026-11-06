import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay062
import Cycle12.CutFailureCertificates.Decay063
import Cycle12.CutFailureCertificates.Decay064

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget025

def certificate500 : RatFailureBudget := ⟨(300490240473045089439/125000000000000000),(252937015721341/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1250),(2,CutFailureCertificates.Decay062.certificate1251),(2,CutFailureCertificates.Decay062.certificate1252)]⟩
theorem numericValid500 : certificate500.NumericValid := by decide +kernel
theorem sound500 : certificate500.Sound := rat_failure_budget_sound certificate500 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1250,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1251,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1252,List.forall_mem_nil _⟩⟩⟩) numericValid500

def certificate501 : RatFailureBudget := ⟨(300490240473045089439/125000000000000000),(297399178473507/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1253),(2,CutFailureCertificates.Decay062.certificate1254)]⟩
theorem numericValid501 : certificate501.NumericValid := by decide +kernel
theorem sound501 : certificate501.Sound := rat_failure_budget_sound certificate501 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1253,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1254,List.forall_mem_nil _⟩⟩) numericValid501

def certificate502 : RatFailureBudget := ⟨(2194444176716075134529/1000000000000000000),(17128193322719/62500000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1255),(2,CutFailureCertificates.Decay062.certificate1256),(2,CutFailureCertificates.Decay062.certificate1257)]⟩
theorem numericValid502 : certificate502.NumericValid := by decide +kernel
theorem sound502 : certificate502.Sound := rat_failure_budget_sound certificate502 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1255,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1256,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1257,List.forall_mem_nil _⟩⟩⟩) numericValid502

def certificate503 : RatFailureBudget := ⟨(2194444176716075134529/1000000000000000000),(77242331974489/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay062.certificate1258),(2,CutFailureCertificates.Decay062.certificate1259)]⟩
theorem numericValid503 : certificate503.NumericValid := by decide +kernel
theorem sound503 : certificate503.Sound := rat_failure_budget_sound certificate503 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1258,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay062.sound1259,List.forall_mem_nil _⟩⟩) numericValid503

def certificate504 : RatFailureBudget := ⟨(251350308836381925977/125000000000000000),(297289647835091/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1260),(2,CutFailureCertificates.Decay063.certificate1261),(2,CutFailureCertificates.Decay063.certificate1262)]⟩
theorem numericValid504 : certificate504.NumericValid := by decide +kernel
theorem sound504 : certificate504.Sound := rat_failure_budget_sound certificate504 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1260,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1261,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1262,List.forall_mem_nil _⟩⟩⟩) numericValid504

def certificate505 : RatFailureBudget := ⟨(251350308836381925977/125000000000000000),(350165888951479/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1263),(2,CutFailureCertificates.Decay063.certificate1264)]⟩
theorem numericValid505 : certificate505.NumericValid := by decide +kernel
theorem sound505 : certificate505.Sound := rat_failure_budget_sound certificate505 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1263,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1264,List.forall_mem_nil _⟩⟩) numericValid505

def certificate506 : RatFailureBudget := ⟨(852766459039374206461/500000000000000000),(87099234409761/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1265),(2,CutFailureCertificates.Decay063.certificate1266),(2,CutFailureCertificates.Decay063.certificate1267)]⟩
theorem numericValid506 : certificate506.NumericValid := by decide +kernel
theorem sound506 : certificate506.Sound := rat_failure_budget_sound certificate506 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1265,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1266,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1267,List.forall_mem_nil _⟩⟩⟩) numericValid506

def certificate507 : RatFailureBudget := ⟨(852766459039374206461/500000000000000000),(418572847478011/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1268),(2,CutFailureCertificates.Decay063.certificate1269)]⟩
theorem numericValid507 : certificate507.NumericValid := by decide +kernel
theorem sound507 : certificate507.Sound := rat_failure_budget_sound certificate507 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1268,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1269,List.forall_mem_nil _⟩⟩) numericValid507

def certificate508 : RatFailureBudget := ⟨(365960577732687798351/250000000000000000),(401042486355189/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1270),(2,CutFailureCertificates.Decay063.certificate1271),(2,CutFailureCertificates.Decay063.certificate1272)]⟩
theorem numericValid508 : certificate508.NumericValid := by decide +kernel
theorem sound508 : certificate508.Sound := rat_failure_budget_sound certificate508 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1270,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1271,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1272,List.forall_mem_nil _⟩⟩⟩) numericValid508

def certificate509 : RatFailureBudget := ⟨(365960577732687798351/250000000000000000),(95184799412647/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1273),(2,CutFailureCertificates.Decay063.certificate1274)]⟩
theorem numericValid509 : certificate509.NumericValid := by decide +kernel
theorem sound509 : certificate509.Sound := rat_failure_budget_sound certificate509 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1273,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1274,List.forall_mem_nil _⟩⟩) numericValid509

def certificate510 : RatFailureBudget := ⟨(317321847654582679029/250000000000000000),(45607371564731/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1275),(2,CutFailureCertificates.Decay063.certificate1276),(2,CutFailureCertificates.Decay063.certificate1277)]⟩
theorem numericValid510 : certificate510.NumericValid := by decide +kernel
theorem sound510 : certificate510.Sound := rat_failure_budget_sound certificate510 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1275,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1276,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1277,List.forall_mem_nil _⟩⟩⟩) numericValid510

def certificate511 : RatFailureBudget := ⟨(317321847654582679029/250000000000000000),(16883759583789/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay063.certificate1278),(2,CutFailureCertificates.Decay063.certificate1279)]⟩
theorem numericValid511 : certificate511.NumericValid := by decide +kernel
theorem sound511 : certificate511.Sound := rat_failure_budget_sound certificate511 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1278,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay063.sound1279,List.forall_mem_nil _⟩⟩) numericValid511

def certificate512 : RatFailureBudget := ⟨(555204668868246689109/500000000000000000),(258055280903953/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1280),(2,CutFailureCertificates.Decay064.certificate1281),(2,CutFailureCertificates.Decay064.certificate1282)]⟩
theorem numericValid512 : certificate512.NumericValid := by decide +kernel
theorem sound512 : certificate512.Sound := rat_failure_budget_sound certificate512 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1280,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1281,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1282,List.forall_mem_nil _⟩⟩⟩) numericValid512

def certificate513 : RatFailureBudget := ⟨(555204668868246689109/500000000000000000),(6145002159917/10000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1283),(2,CutFailureCertificates.Decay064.certificate1284)]⟩
theorem numericValid513 : certificate513.NumericValid := by decide +kernel
theorem sound513 : certificate513.Sound := rat_failure_budget_sound certificate513 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1283,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1284,List.forall_mem_nil _⟩⟩) numericValid513

def certificate514 : RatFailureBudget := ⟨(979025926796996761319/1000000000000000000),(289244442196573/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1285),(2,CutFailureCertificates.Decay064.certificate1286),(2,CutFailureCertificates.Decay064.certificate1287)]⟩
theorem numericValid514 : certificate514.NumericValid := by decide +kernel
theorem sound514 : certificate514.Sound := rat_failure_budget_sound certificate514 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1285,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1286,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1287,List.forall_mem_nil _⟩⟩⟩) numericValid514

def certificate515 : RatFailureBudget := ⟨(979025926796996761319/1000000000000000000),(395000950175737/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1288),(2,CutFailureCertificates.Decay064.certificate1289)]⟩
theorem numericValid515 : certificate515.NumericValid := by decide +kernel
theorem sound515 : certificate515.Sound := rat_failure_budget_sound certificate515 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1288,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1289,List.forall_mem_nil _⟩⟩) numericValid515

def certificate516 : RatFailureBudget := ⟨(173833819108730224839/200000000000000000),(643686999672567/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1290),(2,CutFailureCertificates.Decay064.certificate1291),(2,CutFailureCertificates.Decay064.certificate1292)]⟩
theorem numericValid516 : certificate516.NumericValid := by decide +kernel
theorem sound516 : certificate516.Sound := rat_failure_budget_sound certificate516 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1290,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1291,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1292,List.forall_mem_nil _⟩⟩⟩) numericValid516

def certificate517 : RatFailureBudget := ⟨(173833819108730224839/200000000000000000),(30798111126737/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1293),(2,CutFailureCertificates.Decay064.certificate1294)]⟩
theorem numericValid517 : certificate517.NumericValid := by decide +kernel
theorem sound517 : certificate517.Sound := rat_failure_budget_sound certificate517 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1293,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1294,List.forall_mem_nil _⟩⟩) numericValid517

def certificate518 : RatFailureBudget := ⟨(776403571869755913701/1000000000000000000),(71274531141571/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1295),(2,CutFailureCertificates.Decay064.certificate1296),(2,CutFailureCertificates.Decay064.certificate1297)]⟩
theorem numericValid518 : certificate518.NumericValid := by decide +kernel
theorem sound518 : certificate518.Sound := rat_failure_budget_sound certificate518 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1295,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1296,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1297,List.forall_mem_nil _⟩⟩⟩) numericValid518

def certificate519 : RatFailureBudget := ⟨(776403571869755913701/1000000000000000000),(171254361321583/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay064.certificate1298),(2,CutFailureCertificates.Decay064.certificate1299)]⟩
theorem numericValid519 : certificate519.NumericValid := by decide +kernel
theorem sound519 : certificate519.Sound := rat_failure_budget_sound certificate519 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1298,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay064.sound1299,List.forall_mem_nil _⟩⟩) numericValid519

end Cycle12.CutFailureCertificates.Budget025
