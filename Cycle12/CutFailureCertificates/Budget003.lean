import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay007
import Cycle12.CutFailureCertificates.Decay008
import Cycle12.CutFailureCertificates.Decay009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget003

def certificate60 : RatFailureBudget := ⟨(51344512704105007463/1000000000000000000),(9605812279967447/1000000000000000000),(139089640572453837/500000000000000000),[(2,CutFailureCertificates.Decay007.certificate150),(2,CutFailureCertificates.Decay007.certificate151),(2,CutFailureCertificates.Decay007.certificate152)]⟩
theorem numericValid60 : certificate60.NumericValid := by decide +kernel
theorem sound60 : certificate60.Sound := rat_failure_budget_sound certificate60 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound150,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound151,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound152,List.forall_mem_nil _⟩⟩⟩) numericValid60

def certificate61 : RatFailureBudget := ⟨(51344512704105007463/1000000000000000000),(8197100169990267/1000000000000000000),(8393451417/1000000000000000000),[(2,CutFailureCertificates.Decay007.certificate153),(2,CutFailureCertificates.Decay007.certificate154)]⟩
theorem numericValid61 : certificate61.NumericValid := by decide +kernel
theorem sound61 : certificate61.Sound := rat_failure_budget_sound certificate61 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound153,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound154,List.forall_mem_nil _⟩⟩) numericValid61

def certificate62 : RatFailureBudget := ⟨(49649338197438694597/1000000000000000000),(10070743108901181/1000000000000000000),(38713564319600693/200000000000000000),[(2,CutFailureCertificates.Decay007.certificate155),(2,CutFailureCertificates.Decay007.certificate156),(2,CutFailureCertificates.Decay007.certificate157)]⟩
theorem numericValid62 : certificate62.NumericValid := by decide +kernel
theorem sound62 : certificate62.Sound := rat_failure_budget_sound certificate62 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound155,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound156,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound157,List.forall_mem_nil _⟩⟩⟩) numericValid62

def certificate63 : RatFailureBudget := ⟨(49649338197438694597/1000000000000000000),(8388060871840057/1000000000000000000),(45914976217/125000000000000000),[(2,CutFailureCertificates.Decay007.certificate158),(2,CutFailureCertificates.Decay007.certificate159)]⟩
theorem numericValid63 : certificate63.NumericValid := by decide +kernel
theorem sound63 : certificate63.Sound := rat_failure_budget_sound certificate63 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound158,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay007.sound159,List.forall_mem_nil _⟩⟩) numericValid63

def certificate64 : RatFailureBudget := ⟨(9606499003605273279/200000000000000000),(1008460487112929/100000000000000000),(31103463181443909/125000000000000000),[(2,CutFailureCertificates.Decay008.certificate160),(2,CutFailureCertificates.Decay008.certificate161),(2,CutFailureCertificates.Decay008.certificate162)]⟩
theorem numericValid64 : certificate64.NumericValid := by decide +kernel
theorem sound64 : certificate64.Sound := rat_failure_budget_sound certificate64 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound160,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound161,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound162,List.forall_mem_nil _⟩⟩⟩) numericValid64

def certificate65 : RatFailureBudget := ⟨(9606499003605273279/200000000000000000),(431776796750911/50000000000000000),(63620393277/250000000000000000),[(2,CutFailureCertificates.Decay008.certificate163),(2,CutFailureCertificates.Decay008.certificate164)]⟩
theorem numericValid65 : certificate65.NumericValid := by decide +kernel
theorem sound65 : certificate65.Sound := rat_failure_budget_sound certificate65 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound163,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound164,List.forall_mem_nil _⟩⟩) numericValid65

def certificate66 : RatFailureBudget := ⟨(23244643416741734281/500000000000000000),(5194884691351533/500000000000000000),(278312345544986887/500000000000000000),[(2,CutFailureCertificates.Decay008.certificate165),(2,CutFailureCertificates.Decay008.certificate166),(2,CutFailureCertificates.Decay008.certificate167)]⟩
theorem numericValid66 : certificate66.NumericValid := by decide +kernel
theorem sound66 : certificate66.Sound := rat_failure_budget_sound certificate66 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound165,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound166,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound167,List.forall_mem_nil _⟩⟩⟩) numericValid66

def certificate67 : RatFailureBudget := ⟨(23244643416741734281/500000000000000000),(138959405234877/15625000000000000),(47563554231/250000000000000000),[(2,CutFailureCertificates.Decay008.certificate168),(2,CutFailureCertificates.Decay008.certificate169)]⟩
theorem numericValid67 : certificate67.NumericValid := by decide +kernel
theorem sound67 : certificate67.Sound := rat_failure_budget_sound certificate67 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound168,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound169,List.forall_mem_nil _⟩⟩) numericValid67

def certificate68 : RatFailureBudget := ⟨(22507681237218344607/500000000000000000),(10628256664544447/1000000000000000000),(79519613615452161/200000000000000000),[(2,CutFailureCertificates.Decay008.certificate170),(2,CutFailureCertificates.Decay008.certificate171),(2,CutFailureCertificates.Decay008.certificate172)]⟩
theorem numericValid68 : certificate68.NumericValid := by decide +kernel
theorem sound68 : certificate68.Sound := rat_failure_budget_sound certificate68 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound170,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound171,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound172,List.forall_mem_nil _⟩⟩⟩) numericValid68

def certificate69 : RatFailureBudget := ⟨(22507681237218344607/500000000000000000),(4574592505782367/500000000000000000),(146196758521/1000000000000000000),[(2,CutFailureCertificates.Decay008.certificate173),(2,CutFailureCertificates.Decay008.certificate174)]⟩
theorem numericValid69 : certificate69.NumericValid := by decide +kernel
theorem sound69 : certificate69.Sound := rat_failure_budget_sound certificate69 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound173,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound174,List.forall_mem_nil _⟩⟩) numericValid69

def certificate70 : RatFailureBudget := ⟨(21803343000876340869/500000000000000000),(1367220121503219/125000000000000000),(262662843287521237/500000000000000000),[(2,CutFailureCertificates.Decay008.certificate175),(2,CutFailureCertificates.Decay008.certificate176),(2,CutFailureCertificates.Decay008.certificate177)]⟩
theorem numericValid70 : certificate70.NumericValid := by decide +kernel
theorem sound70 : certificate70.Sound := rat_failure_budget_sound certificate70 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound175,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound176,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound177,List.forall_mem_nil _⟩⟩⟩) numericValid70

def certificate71 : RatFailureBudget := ⟨(21803343000876340869/500000000000000000),(4705133427593887/500000000000000000),(11422478217/100000000000000000),[(2,CutFailureCertificates.Decay008.certificate178),(2,CutFailureCertificates.Decay008.certificate179)]⟩
theorem numericValid71 : certificate71.NumericValid := by decide +kernel
theorem sound71 : certificate71.Sound := rat_failure_budget_sound certificate71 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound178,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay008.sound179,List.forall_mem_nil _⟩⟩) numericValid71

def certificate72 : RatFailureBudget := ⟨(21462816999703401623/500000000000000000),(5534459729669281/500000000000000000),(103975541737719477/250000000000000000),[(2,CutFailureCertificates.Decay009.certificate180),(2,CutFailureCertificates.Decay009.certificate181),(2,CutFailureCertificates.Decay009.certificate182)]⟩
theorem numericValid72 : certificate72.NumericValid := by decide +kernel
theorem sound72 : certificate72.Sound := rat_failure_budget_sound certificate72 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound180,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound181,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound182,List.forall_mem_nil _⟩⟩⟩) numericValid72

def certificate73 : RatFailureBudget := ⟨(21462816999703401623/500000000000000000),(1189354531640119/125000000000000000),(34107804891/1000000000000000000),[(2,CutFailureCertificates.Decay009.certificate183),(2,CutFailureCertificates.Decay009.certificate184)]⟩
theorem numericValid73 : certificate73.NumericValid := by decide +kernel
theorem sound73 : certificate73.Sound := rat_failure_budget_sound certificate73 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound183,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound184,List.forall_mem_nil _⟩⟩) numericValid73

def certificate74 : RatFailureBudget := ⟨(5282438719400437649/125000000000000000),(11172193388873873/1000000000000000000),(498160218578193729/1000000000000000000),[(2,CutFailureCertificates.Decay009.certificate185),(2,CutFailureCertificates.Decay009.certificate186),(2,CutFailureCertificates.Decay009.certificate187)]⟩
theorem numericValid74 : certificate74.NumericValid := by decide +kernel
theorem sound74 : certificate74.Sound := rat_failure_budget_sound certificate74 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound185,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound186,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound187,List.forall_mem_nil _⟩⟩⟩) numericValid74

def certificate75 : RatFailureBudget := ⟨(5282438719400437649/125000000000000000),(965052571766121/100000000000000000),(30831321071/1000000000000000000),[(2,CutFailureCertificates.Decay009.certificate188),(2,CutFailureCertificates.Decay009.certificate189)]⟩
theorem numericValid75 : certificate75.NumericValid := by decide +kernel
theorem sound75 : certificate75.Sound := rat_failure_budget_sound certificate75 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound188,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound189,List.forall_mem_nil _⟩⟩) numericValid75

def certificate76 : RatFailureBudget := ⟨(10242587512302542181/250000000000000000),(11540937509016013/1000000000000000000),(37964993200799683/200000000000000000),[(2,CutFailureCertificates.Decay009.certificate190),(2,CutFailureCertificates.Decay009.certificate191),(2,CutFailureCertificates.Decay009.certificate192)]⟩
theorem numericValid76 : certificate76.NumericValid := by decide +kernel
theorem sound76 : certificate76.Sound := rat_failure_budget_sound certificate76 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound190,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound191,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound192,List.forall_mem_nil _⟩⟩⟩) numericValid76

def certificate77 : RatFailureBudget := ⟨(10242587512302542181/250000000000000000),(9951363609584957/1000000000000000000),(15334268247/200000000000000000),[(2,CutFailureCertificates.Decay009.certificate193),(2,CutFailureCertificates.Decay009.certificate194)]⟩
theorem numericValid77 : certificate77.NumericValid := by decide +kernel
theorem sound77 : certificate77.Sound := rat_failure_budget_sound certificate77 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound193,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound194,List.forall_mem_nil _⟩⟩) numericValid77

def certificate78 : RatFailureBudget := ⟨(39735965222884822823/1000000000000000000),(11859976839516811/1000000000000000000),(58947977403732881/250000000000000000),[(2,CutFailureCertificates.Decay009.certificate195),(2,CutFailureCertificates.Decay009.certificate196),(2,CutFailureCertificates.Decay009.certificate197)]⟩
theorem numericValid78 : certificate78.NumericValid := by decide +kernel
theorem sound78 : certificate78.Sound := rat_failure_budget_sound certificate78 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound195,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound196,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound197,List.forall_mem_nil _⟩⟩⟩) numericValid78

def certificate79 : RatFailureBudget := ⟨(39735965222884822823/1000000000000000000),(5109454940492403/500000000000000000),(59675548671/1000000000000000000),[(2,CutFailureCertificates.Decay009.certificate198),(2,CutFailureCertificates.Decay009.certificate199)]⟩
theorem numericValid79 : certificate79.NumericValid := by decide +kernel
theorem sound79 : certificate79.Sound := rat_failure_budget_sound certificate79 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound198,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay009.sound199,List.forall_mem_nil _⟩⟩) numericValid79

end Cycle12.CutFailureCertificates.Budget003
