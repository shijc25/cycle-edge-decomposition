import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay050
import Cycle12.CutFailureCertificates.Decay051
import Cycle12.CutFailureCertificates.Decay052

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget020

def certificate400 : RatFailureBudget := ⟨(37419646445651247031/500000000000000000),(6053000679515833/1000000000000000000),(11491501/500000000000000000),[(2,CutFailureCertificates.Decay050.certificate1000),(2,CutFailureCertificates.Decay050.certificate1001),(2,CutFailureCertificates.Decay050.certificate1002)]⟩
theorem numericValid400 : certificate400.NumericValid := by decide +kernel
theorem sound400 : certificate400.Sound := rat_failure_budget_sound certificate400 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1000,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1001,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1002,List.forall_mem_nil _⟩⟩⟩) numericValid400

def certificate401 : RatFailureBudget := ⟨(37419646445651247031/500000000000000000),(1417643042661023/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay050.certificate1003),(2,CutFailureCertificates.Decay050.certificate1004)]⟩
theorem numericValid401 : certificate401.NumericValid := by decide +kernel
theorem sound401 : certificate401.Sound := rat_failure_budget_sound certificate401 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1003,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1004,List.forall_mem_nil _⟩⟩) numericValid401

def certificate402 : RatFailureBudget := ⟨(35288751458599140089/500000000000000000),(6352520547490979/1000000000000000000),(17022851/250000000000000000),[(2,CutFailureCertificates.Decay050.certificate1005),(2,CutFailureCertificates.Decay050.certificate1006),(2,CutFailureCertificates.Decay050.certificate1007)]⟩
theorem numericValid402 : certificate402.NumericValid := by decide +kernel
theorem sound402 : certificate402.Sound := rat_failure_budget_sound certificate402 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1005,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1006,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1007,List.forall_mem_nil _⟩⟩⟩) numericValid402

def certificate403 : RatFailureBudget := ⟨(35288751458599140089/500000000000000000),(186623868691587/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay050.certificate1008),(2,CutFailureCertificates.Decay050.certificate1009)]⟩
theorem numericValid403 : certificate403.NumericValid := by decide +kernel
theorem sound403 : certificate403.Sound := rat_failure_budget_sound certificate403 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1008,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1009,List.forall_mem_nil _⟩⟩) numericValid403

def certificate404 : RatFailureBudget := ⟨(13329703287103710401/200000000000000000),(3364914711391747/500000000000000000),(66349469/1000000000000000000),[(2,CutFailureCertificates.Decay050.certificate1010),(2,CutFailureCertificates.Decay050.certificate1011),(2,CutFailureCertificates.Decay050.certificate1012)]⟩
theorem numericValid404 : certificate404.NumericValid := by decide +kernel
theorem sound404 : certificate404.Sound := rat_failure_budget_sound certificate404 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1010,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1011,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1012,List.forall_mem_nil _⟩⟩⟩) numericValid404

def certificate405 : RatFailureBudget := ⟨(13329703287103710401/200000000000000000),(6276580602573149/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay050.certificate1013),(2,CutFailureCertificates.Decay050.certificate1014)]⟩
theorem numericValid405 : certificate405.NumericValid := by decide +kernel
theorem sound405 : certificate405.Sound := rat_failure_budget_sound certificate405 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1013,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1014,List.forall_mem_nil _⟩⟩) numericValid405

def certificate406 : RatFailureBudget := ⟨(12603804332836526079/200000000000000000),(6930608814795809/1000000000000000000),(87253621/500000000000000000),[(2,CutFailureCertificates.Decay050.certificate1015),(2,CutFailureCertificates.Decay050.certificate1016),(2,CutFailureCertificates.Decay050.certificate1017)]⟩
theorem numericValid406 : certificate406.NumericValid := by decide +kernel
theorem sound406 : certificate406.Sound := rat_failure_budget_sound certificate406 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1015,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1016,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1017,List.forall_mem_nil _⟩⟩⟩) numericValid406

def certificate407 : RatFailureBudget := ⟨(12603804332836526079/200000000000000000),(3268929478856079/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay050.certificate1018),(2,CutFailureCertificates.Decay050.certificate1019)]⟩
theorem numericValid407 : certificate407.NumericValid := by decide +kernel
theorem sound407 : certificate407.Sound := rat_failure_budget_sound certificate407 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1018,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay050.sound1019,List.forall_mem_nil _⟩⟩) numericValid407

def certificate408 : RatFailureBudget := ⟨(59659751619044898567/1000000000000000000),(3621740236894439/500000000000000000),(34973297/200000000000000000),[(2,CutFailureCertificates.Decay051.certificate1020),(2,CutFailureCertificates.Decay051.certificate1021),(2,CutFailureCertificates.Decay051.certificate1022)]⟩
theorem numericValid408 : certificate408.NumericValid := by decide +kernel
theorem sound408 : certificate408.Sound := rat_failure_budget_sound certificate408 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1020,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1021,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1022,List.forall_mem_nil _⟩⟩⟩) numericValid408

def certificate409 : RatFailureBudget := ⟨(59659751619044898567/1000000000000000000),(6858830485224067/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay051.certificate1023),(2,CutFailureCertificates.Decay051.certificate1024)]⟩
theorem numericValid409 : certificate409.NumericValid := by decide +kernel
theorem sound409 : certificate409.Sound := rat_failure_budget_sound certificate409 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1023,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1024,List.forall_mem_nil _⟩⟩) numericValid409

def certificate410 : RatFailureBudget := ⟨(56544910216936768259/1000000000000000000),(842132795817753/100000000000000000),(96916951/500000000000000000),[(2,CutFailureCertificates.Decay051.certificate1025),(2,CutFailureCertificates.Decay051.certificate1026),(2,CutFailureCertificates.Decay051.certificate1027)]⟩
theorem numericValid410 : certificate410.NumericValid := by decide +kernel
theorem sound410 : certificate410.Sound := rat_failure_budget_sound certificate410 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1025,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1026,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1027,List.forall_mem_nil _⟩⟩⟩) numericValid410

def certificate411 : RatFailureBudget := ⟨(56544910216936768259/1000000000000000000),(7130160566592387/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay051.certificate1028),(2,CutFailureCertificates.Decay051.certificate1029)]⟩
theorem numericValid411 : certificate411.NumericValid := by decide +kernel
theorem sound411 : certificate411.Sound := rat_failure_budget_sound certificate411 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1028,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1029,List.forall_mem_nil _⟩⟩) numericValid411

def certificate412 : RatFailureBudget := ⟨(53651691046898568089/1000000000000000000),(3928973055132921/500000000000000000),(96010871/500000000000000000),[(2,CutFailureCertificates.Decay051.certificate1030),(2,CutFailureCertificates.Decay051.certificate1031),(2,CutFailureCertificates.Decay051.certificate1032)]⟩
theorem numericValid412 : certificate412.NumericValid := by decide +kernel
theorem sound412 : certificate412.Sound := rat_failure_budget_sound certificate412 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1030,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1031,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1032,List.forall_mem_nil _⟩⟩⟩) numericValid412

def certificate413 : RatFailureBudget := ⟨(53651691046898568089/1000000000000000000),(7457019935744193/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay051.certificate1033),(2,CutFailureCertificates.Decay051.certificate1034)]⟩
theorem numericValid413 : certificate413.NumericValid := by decide +kernel
theorem sound413 : certificate413.Sound := rat_failure_budget_sound certificate413 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1033,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1034,List.forall_mem_nil _⟩⟩) numericValid413

def certificate414 : RatFailureBudget := ⟨(6369984013696635067/125000000000000000),(1639636973067571/200000000000000000),(89334071/1000000000000000000),[(2,CutFailureCertificates.Decay051.certificate1035),(2,CutFailureCertificates.Decay051.certificate1036),(2,CutFailureCertificates.Decay051.certificate1037)]⟩
theorem numericValid414 : certificate414.NumericValid := by decide +kernel
theorem sound414 : certificate414.Sound := rat_failure_budget_sound certificate414 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1035,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1036,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1037,List.forall_mem_nil _⟩⟩⟩) numericValid414

def certificate415 : RatFailureBudget := ⟨(6369984013696635067/125000000000000000),(7735385326507821/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay051.certificate1038),(2,CutFailureCertificates.Decay051.certificate1039)]⟩
theorem numericValid415 : certificate415.NumericValid := by decide +kernel
theorem sound415 : certificate415.Sound := rat_failure_budget_sound certificate415 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1038,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay051.sound1039,List.forall_mem_nil _⟩⟩) numericValid415

def certificate416 : RatFailureBudget := ⟨(48451473133868985059/1000000000000000000),(4244201433068081/500000000000000000),(18934081/200000000000000000),[(2,CutFailureCertificates.Decay052.certificate1040),(2,CutFailureCertificates.Decay052.certificate1041),(2,CutFailureCertificates.Decay052.certificate1042)]⟩
theorem numericValid416 : certificate416.NumericValid := by decide +kernel
theorem sound416 : certificate416.Sound := rat_failure_budget_sound certificate416 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1040,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1041,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1042,List.forall_mem_nil _⟩⟩⟩) numericValid416

def certificate417 : RatFailureBudget := ⟨(48451473133868985059/1000000000000000000),(8075643332682643/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay052.certificate1043),(2,CutFailureCertificates.Decay052.certificate1044)]⟩
theorem numericValid417 : certificate417.NumericValid := by decide +kernel
theorem sound417 : certificate417.Sound := rat_failure_budget_sound certificate417 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1043,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1044,List.forall_mem_nil _⟩⟩) numericValid417

def certificate418 : RatFailureBudget := ⟨(1844418587063087577/40000000000000000),(4403285351691487/500000000000000000),(102257347/1000000000000000000),[(2,CutFailureCertificates.Decay052.certificate1045),(2,CutFailureCertificates.Decay052.certificate1046),(2,CutFailureCertificates.Decay052.certificate1047)]⟩
theorem numericValid418 : certificate418.NumericValid := by decide +kernel
theorem sound418 : certificate418.Sound := rat_failure_budget_sound certificate418 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1045,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1046,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1047,List.forall_mem_nil _⟩⟩⟩) numericValid418

def certificate419 : RatFailureBudget := ⟨(1844418587063087577/40000000000000000),(334399614480949/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay052.certificate1048),(2,CutFailureCertificates.Decay052.certificate1049)]⟩
theorem numericValid419 : certificate419.NumericValid := by decide +kernel
theorem sound419 : certificate419.Sound := rat_failure_budget_sound certificate419 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1048,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay052.sound1049,List.forall_mem_nil _⟩⟩) numericValid419

end Cycle12.CutFailureCertificates.Budget020
