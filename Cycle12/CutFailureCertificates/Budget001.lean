import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay002
import Cycle12.CutFailureCertificates.Decay003
import Cycle12.CutFailureCertificates.Decay004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget001

def certificate20 : RatFailureBudget := ⟨(402160494138211081563/1000000000000000000),(150250332660399/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate50),(2,CutFailureCertificates.Decay002.certificate51),(2,CutFailureCertificates.Decay002.certificate52)]⟩
theorem numericValid20 : certificate20.NumericValid := by decide +kernel
theorem sound20 : certificate20.Sound := rat_failure_budget_sound certificate20 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound50,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound51,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound52,List.forall_mem_nil _⟩⟩⟩) numericValid20

def certificate21 : RatFailureBudget := ⟨(402160494138211081563/1000000000000000000),(1233979456706409/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate53),(2,CutFailureCertificates.Decay002.certificate54)]⟩
theorem numericValid21 : certificate21.NumericValid := by decide +kernel
theorem sound21 : certificate21.Sound := rat_failure_budget_sound certificate21 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound53,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound54,List.forall_mem_nil _⟩⟩) numericValid21

def certificate22 : RatFailureBudget := ⟨(42638322951968710323/125000000000000000),(1754943304028229/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate55),(2,CutFailureCertificates.Decay002.certificate56),(2,CutFailureCertificates.Decay002.certificate57)]⟩
theorem numericValid22 : certificate22.NumericValid := by decide +kernel
theorem sound22 : certificate22.Sound := rat_failure_budget_sound certificate22 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound55,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound56,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound57,List.forall_mem_nil _⟩⟩⟩) numericValid22

def certificate23 : RatFailureBudget := ⟨(42638322951968710323/125000000000000000),(176737251157081/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay002.certificate58),(2,CutFailureCertificates.Decay002.certificate59)]⟩
theorem numericValid23 : certificate23.NumericValid := by decide +kernel
theorem sound23 : certificate23.Sound := rat_failure_budget_sound certificate23 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound58,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay002.sound59,List.forall_mem_nil _⟩⟩) numericValid23

def certificate24 : RatFailureBudget := ⟨(7319211554653755967/25000000000000000),(505516488775153/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate60),(2,CutFailureCertificates.Decay003.certificate61),(2,CutFailureCertificates.Decay003.certificate62)]⟩
theorem numericValid24 : certificate24.NumericValid := by decide +kernel
theorem sound24 : certificate24.Sound := rat_failure_budget_sound certificate24 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound60,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound61,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound62,List.forall_mem_nil _⟩⟩⟩) numericValid24

def certificate25 : RatFailureBudget := ⟨(7319211554653755967/25000000000000000),(1635947489286017/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate63),(2,CutFailureCertificates.Decay003.certificate64)]⟩
theorem numericValid25 : certificate25.NumericValid := by decide +kernel
theorem sound25 : certificate25.Sound := rat_failure_budget_sound certificate25 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound63,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound64,List.forall_mem_nil _⟩⟩) numericValid25

def certificate26 : RatFailureBudget := ⟨(253857478123666143223/1000000000000000000),(2311319861256907/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate65),(2,CutFailureCertificates.Decay003.certificate66),(2,CutFailureCertificates.Decay003.certificate67)]⟩
theorem numericValid26 : certificate26.NumericValid := by decide +kernel
theorem sound26 : certificate26.Sound := rat_failure_budget_sound certificate26 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound65,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound66,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound67,List.forall_mem_nil _⟩⟩⟩) numericValid26

def certificate27 : RatFailureBudget := ⟨(253857478123666143223/1000000000000000000),(936740503969243/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate68),(2,CutFailureCertificates.Decay003.certificate69)]⟩
theorem numericValid27 : certificate27.NumericValid := by decide +kernel
theorem sound27 : certificate27.Sound := rat_failure_budget_sound certificate27 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound68,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound69,List.forall_mem_nil _⟩⟩) numericValid27

def certificate28 : RatFailureBudget := ⟨(222081867547298675643/1000000000000000000),(2613094495914267/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate70),(2,CutFailureCertificates.Decay003.certificate71),(2,CutFailureCertificates.Decay003.certificate72)]⟩
theorem numericValid28 : certificate28.NumericValid := by decide +kernel
theorem sound28 : certificate28.Sound := rat_failure_budget_sound certificate28 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound70,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound71,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound72,List.forall_mem_nil _⟩⟩⟩) numericValid28

def certificate29 : RatFailureBudget := ⟨(222081867547298675643/1000000000000000000),(1063146094232823/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate73),(2,CutFailureCertificates.Decay003.certificate74)]⟩
theorem numericValid29 : certificate29.NumericValid := by decide +kernel
theorem sound29 : certificate29.Sound := rat_failure_budget_sound certificate29 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound73,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound74,List.forall_mem_nil _⟩⟩) numericValid29

def certificate30 : RatFailureBudget := ⟨(195805185359399352263/1000000000000000000),(365095348420713/125000000000000000),(169/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate75),(2,CutFailureCertificates.Decay003.certificate76),(2,CutFailureCertificates.Decay003.certificate77)]⟩
theorem numericValid30 : certificate30.NumericValid := by decide +kernel
theorem sound30 : certificate30.Sound := rat_failure_budget_sound certificate30 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound75,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound76,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound77,List.forall_mem_nil _⟩⟩⟩) numericValid30

def certificate31 : RatFailureBudget := ⟨(195805185359399352263/1000000000000000000),(2394194563464213/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay003.certificate78),(2,CutFailureCertificates.Decay003.certificate79)]⟩
theorem numericValid31 : certificate31.NumericValid := by decide +kernel
theorem sound31 : certificate31.Sound := rat_failure_budget_sound certificate31 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound78,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay003.sound79,List.forall_mem_nil _⟩⟩) numericValid31

def certificate32 : RatFailureBudget := ⟨(173833819108730224839/1000000000000000000),(327519952716519/100000000000000000),(21207/500000000000000000),[(2,CutFailureCertificates.Decay004.certificate80),(2,CutFailureCertificates.Decay004.certificate81),(2,CutFailureCertificates.Decay004.certificate82)]⟩
theorem numericValid32 : certificate32.NumericValid := by decide +kernel
theorem sound32 : certificate32.Sound := rat_failure_budget_sound certificate32 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound80,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound81,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound82,List.forall_mem_nil _⟩⟩⟩) numericValid32

def certificate33 : RatFailureBudget := ⟨(173833819108730224839/1000000000000000000),(4283206528999/1600000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay004.certificate83),(2,CutFailureCertificates.Decay004.certificate84)]⟩
theorem numericValid33 : certificate33.NumericValid := by decide +kernel
theorem sound33 : certificate33.Sound := rat_failure_budget_sound certificate33 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound83,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound84,List.forall_mem_nil _⟩⟩) numericValid33

def certificate34 : RatFailureBudget := ⟨(7764035718697559137/50000000000000000),(1813591908765723/500000000000000000),(4235601/1000000000000000000),[(2,CutFailureCertificates.Decay004.certificate85),(2,CutFailureCertificates.Decay004.certificate86),(2,CutFailureCertificates.Decay004.certificate87)]⟩
theorem numericValid34 : certificate34.NumericValid := by decide +kernel
theorem sound34 : certificate34.Sound := rat_failure_budget_sound certificate34 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound85,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound86,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound87,List.forall_mem_nil _⟩⟩⟩) numericValid34

def certificate35 : RatFailureBudget := ⟨(7764035718697559137/50000000000000000),(2966130210430157/1000000000000000000),(57/250000000000000000),[(2,CutFailureCertificates.Decay004.certificate88),(2,CutFailureCertificates.Decay004.certificate89)]⟩
theorem numericValid35 : certificate35.NumericValid := by decide +kernel
theorem sound35 : certificate35.Sound := rat_failure_budget_sound certificate35 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound88,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound89,List.forall_mem_nil _⟩⟩) numericValid35

def certificate36 : RatFailureBudget := ⟨(139475608349223280593/1000000000000000000),(2003923153499129/500000000000000000),(105037001/500000000000000000),[(2,CutFailureCertificates.Decay004.certificate90),(2,CutFailureCertificates.Decay004.certificate91),(2,CutFailureCertificates.Decay004.certificate92)]⟩
theorem numericValid36 : certificate36.NumericValid := by decide +kernel
theorem sound36 : certificate36.Sound := rat_failure_budget_sound certificate36 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound90,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound91,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound92,List.forall_mem_nil _⟩⟩⟩) numericValid36

def certificate37 : RatFailureBudget := ⟨(139475608349223280593/1000000000000000000),(3276802490365389/1000000000000000000),(121/1000000000000000000),[(2,CutFailureCertificates.Decay004.certificate93),(2,CutFailureCertificates.Decay004.certificate94)]⟩
theorem numericValid37 : certificate37.NumericValid := by decide +kernel
theorem sound37 : certificate37.Sound := rat_failure_budget_sound certificate37 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound93,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound94,List.forall_mem_nil _⟩⟩) numericValid37

def certificate38 : RatFailureBudget := ⟨(125904482924188692167/1000000000000000000),(4394258692189677/1000000000000000000),(58442267/25000000000000000),[(2,CutFailureCertificates.Decay004.certificate95),(2,CutFailureCertificates.Decay004.certificate96),(2,CutFailureCertificates.Decay004.certificate97)]⟩
theorem numericValid38 : certificate38.NumericValid := by decide +kernel
theorem sound38 : certificate38.Sound := rat_failure_budget_sound certificate38 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound95,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound96,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound97,List.forall_mem_nil _⟩⟩⟩) numericValid38

def certificate39 : RatFailureBudget := ⟨(125904482924188692167/1000000000000000000),(1794941850755013/500000000000000000),(169/1000000000000000000),[(2,CutFailureCertificates.Decay004.certificate98),(2,CutFailureCertificates.Decay004.certificate99)]⟩
theorem numericValid39 : certificate39.NumericValid := by decide +kernel
theorem sound39 : certificate39.Sound := rat_failure_budget_sound certificate39 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound98,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay004.sound99,List.forall_mem_nil _⟩⟩) numericValid39

end Cycle12.CutFailureCertificates.Budget001
