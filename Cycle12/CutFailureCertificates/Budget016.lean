import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay040
import Cycle12.CutFailureCertificates.Decay041
import Cycle12.CutFailureCertificates.Decay042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget016

def certificate320 : RatFailureBudget := ⟨(9760188529515390503/1000000000000000000),(6669582467472849/200000000000000000),(113102384910159/200000000000000000),[(2,CutFailureCertificates.Decay040.certificate800),(2,CutFailureCertificates.Decay040.certificate801),(2,CutFailureCertificates.Decay040.certificate802)]⟩
theorem numericValid320 : certificate320.NumericValid := by decide +kernel
theorem sound320 : certificate320.Sound := rat_failure_budget_sound certificate320 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound800,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound801,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound802,List.forall_mem_nil _⟩⟩⟩) numericValid320

def certificate321 : RatFailureBudget := ⟨(9760188529515390503/1000000000000000000),(15623004630048303/500000000000000000),(1347075362153897/1000000000000000000),[(2,CutFailureCertificates.Decay040.certificate803),(2,CutFailureCertificates.Decay040.certificate804)]⟩
theorem numericValid321 : certificate321.NumericValid := by decide +kernel
theorem sound321 : certificate321.Sound := rat_failure_budget_sound certificate321 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound803,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound804,List.forall_mem_nil _⟩⟩) numericValid321

def certificate322 : RatFailureBudget := ⟨(9715824122799784559/1000000000000000000),(33407149535615837/1000000000000000000),(553750396928651/1000000000000000000),[(2,CutFailureCertificates.Decay040.certificate805),(2,CutFailureCertificates.Decay040.certificate806),(2,CutFailureCertificates.Decay040.certificate807)]⟩
theorem numericValid322 : certificate322.NumericValid := by decide +kernel
theorem sound322 : certificate322.Sound := rat_failure_budget_sound certificate322 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound805,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound806,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound807,List.forall_mem_nil _⟩⟩⟩) numericValid322

def certificate323 : RatFailureBudget := ⟨(9715824122799784559/1000000000000000000),(31328614918046771/1000000000000000000),(1183186981740523/1000000000000000000),[(2,CutFailureCertificates.Decay040.certificate808),(2,CutFailureCertificates.Decay040.certificate809)]⟩
theorem numericValid323 : certificate323.NumericValid := by decide +kernel
theorem sound323 : certificate323.Sound := rat_failure_budget_sound certificate323 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound808,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound809,List.forall_mem_nil _⟩⟩) numericValid323

def certificate324 : RatFailureBudget := ⟨(967172269176527221/100000000000000000),(6717575555026817/200000000000000000),(260251207092133/500000000000000000),[(2,CutFailureCertificates.Decay040.certificate810),(2,CutFailureCertificates.Decay040.certificate811),(2,CutFailureCertificates.Decay040.certificate812)]⟩
theorem numericValid324 : certificate324.NumericValid := by decide +kernel
theorem sound324 : certificate324.Sound := rat_failure_budget_sound certificate324 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound810,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound811,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound812,List.forall_mem_nil _⟩⟩⟩) numericValid324

def certificate325 : RatFailureBudget := ⟨(967172269176527221/100000000000000000),(785281847294857/25000000000000000),(519800714555547/500000000000000000),[(2,CutFailureCertificates.Decay040.certificate813),(2,CutFailureCertificates.Decay040.certificate814)]⟩
theorem numericValid325 : certificate325.NumericValid := by decide +kernel
theorem sound325 : certificate325.Sound := rat_failure_budget_sound certificate325 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound813,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound814,List.forall_mem_nil _⟩⟩) numericValid325

def certificate326 : RatFailureBudget := ⟨(2406970555152869089/250000000000000000),(6756149031340643/200000000000000000),(494430466961307/1000000000000000000),[(2,CutFailureCertificates.Decay040.certificate815),(2,CutFailureCertificates.Decay040.certificate816),(2,CutFailureCertificates.Decay040.certificate817)]⟩
theorem numericValid326 : certificate326.NumericValid := by decide +kernel
theorem sound326 : certificate326.Sound := rat_failure_budget_sound certificate326 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound815,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound816,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound817,List.forall_mem_nil _⟩⟩⟩) numericValid326

def certificate327 : RatFailureBudget := ⟨(2406970555152869089/250000000000000000),(15756023773931779/500000000000000000),(453344511376791/500000000000000000),[(2,CutFailureCertificates.Decay040.certificate818),(2,CutFailureCertificates.Decay040.certificate819)]⟩
theorem numericValid327 : certificate327.NumericValid := by decide +kernel
theorem sound327 : certificate327.Sound := rat_failure_budget_sound certificate327 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound818,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay040.sound819,List.forall_mem_nil _⟩⟩) numericValid327

def certificate328 : RatFailureBudget := ⟨(1198037589076397431/125000000000000000),(1355778226088041/40000000000000000),(456408836368353/1000000000000000000),[(2,CutFailureCertificates.Decay041.certificate820),(2,CutFailureCertificates.Decay041.certificate821),(2,CutFailureCertificates.Decay041.certificate822)]⟩
theorem numericValid328 : certificate328.NumericValid := by decide +kernel
theorem sound328 : certificate328.Sound := rat_failure_budget_sound certificate328 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound820,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound821,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound822,List.forall_mem_nil _⟩⟩⟩) numericValid328

def certificate329 : RatFailureBudget := ⟨(1198037589076397431/125000000000000000),(7898754021968899/250000000000000000),(783228897272867/1000000000000000000),[(2,CutFailureCertificates.Decay041.certificate823),(2,CutFailureCertificates.Decay041.certificate824)]⟩
theorem numericValid329 : certificate329.NumericValid := by decide +kernel
theorem sound329 : certificate329.Sound := rat_failure_budget_sound certificate329 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound823,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound824,List.forall_mem_nil _⟩⟩) numericValid329

def certificate330 : RatFailureBudget := ⟨(9412525033197477019/1000000000000000000),(34470580413748877/1000000000000000000),(423348144618769/200000000000000000),[(2,CutFailureCertificates.Decay041.certificate825),(2,CutFailureCertificates.Decay041.certificate826),(2,CutFailureCertificates.Decay041.certificate827)]⟩
theorem numericValid330 : certificate330.NumericValid := by decide +kernel
theorem sound330 : certificate330.Sound := rat_failure_budget_sound certificate330 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound825,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound826,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound827,List.forall_mem_nil _⟩⟩⟩) numericValid330

def certificate331 : RatFailureBudget := ⟨(9412525033197477019/1000000000000000000),(8019979966146033/250000000000000000),(587683901412177/500000000000000000),[(2,CutFailureCertificates.Decay041.certificate828),(2,CutFailureCertificates.Decay041.certificate829)]⟩
theorem numericValid331 : certificate331.NumericValid := by decide +kernel
theorem sound331 : certificate331.Sound := rat_failure_budget_sound certificate331 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound828,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound829,List.forall_mem_nil _⟩⟩) numericValid331

def certificate332 : RatFailureBudget := ⟨(9244737841268092559/1000000000000000000),(34969325268687839/1000000000000000000),(393044378254811/250000000000000000),[(2,CutFailureCertificates.Decay041.certificate830),(2,CutFailureCertificates.Decay041.certificate831),(2,CutFailureCertificates.Decay041.certificate832)]⟩
theorem numericValid332 : certificate332.NumericValid := by decide +kernel
theorem sound332 : certificate332.Sound := rat_failure_budget_sound certificate332 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound830,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound831,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound832,List.forall_mem_nil _⟩⟩⟩) numericValid332

def certificate333 : RatFailureBudget := ⟨(9244737841268092559/1000000000000000000),(8106078504879763/250000000000000000),(712051733450833/1000000000000000000),[(2,CutFailureCertificates.Decay041.certificate833),(2,CutFailureCertificates.Decay041.certificate834)]⟩
theorem numericValid333 : certificate333.NumericValid := by decide +kernel
theorem sound333 : certificate333.Sound := rat_failure_budget_sound certificate333 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound833,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound834,List.forall_mem_nil _⟩⟩) numericValid333

def certificate334 : RatFailureBudget := ⟨(1500320378333676883047/200000000000000000),(79584512371023/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay041.certificate835),(2,CutFailureCertificates.Decay041.certificate836),(2,CutFailureCertificates.Decay041.certificate837)]⟩
theorem numericValid334 : certificate334.NumericValid := by decide +kernel
theorem sound334 : certificate334.Sound := rat_failure_budget_sound certificate334 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound835,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound836,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound837,List.forall_mem_nil _⟩⟩⟩) numericValid334

def certificate335 : RatFailureBudget := ⟨(1500320378333676883047/200000000000000000),(81665809385729/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay041.certificate838),(2,CutFailureCertificates.Decay041.certificate839)]⟩
theorem numericValid335 : certificate335.NumericValid := by decide +kernel
theorem sound335 : certificate335.Sound := rat_failure_budget_sound certificate335 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound838,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay041.sound839,List.forall_mem_nil _⟩⟩) numericValid335

def certificate336 : RatFailureBudget := ⟨(597512157261602792499/125000000000000000),(67218927550033/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate840),(2,CutFailureCertificates.Decay042.certificate841),(2,CutFailureCertificates.Decay042.certificate842)]⟩
theorem numericValid336 : certificate336.NumericValid := by decide +kernel
theorem sound336 : certificate336.Sound := rat_failure_budget_sound certificate336 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound840,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound841,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound842,List.forall_mem_nil _⟩⟩⟩) numericValid336

def certificate337 : RatFailureBudget := ⟨(597512157261602792499/125000000000000000),(31553589229627/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate843),(2,CutFailureCertificates.Decay042.certificate844)]⟩
theorem numericValid337 : certificate337.NumericValid := by decide +kernel
theorem sound337 : certificate337.Sound := rat_failure_budget_sound certificate337 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound843,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound844,List.forall_mem_nil _⟩⟩) numericValid337

def certificate338 : RatFailureBudget := ⟨(3304960567845950649313/1000000000000000000),(48781211855081/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate845),(2,CutFailureCertificates.Decay042.certificate846),(2,CutFailureCertificates.Decay042.certificate847)]⟩
theorem numericValid338 : certificate338.NumericValid := by decide +kernel
theorem sound338 : certificate338.Sound := rat_failure_budget_sound certificate338 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound845,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound846,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound847,List.forall_mem_nil _⟩⟩⟩) numericValid338

def certificate339 : RatFailureBudget := ⟨(3304960567845950649313/1000000000000000000),(36087822717983/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate848),(2,CutFailureCertificates.Decay042.certificate849)]⟩
theorem numericValid339 : certificate339.NumericValid := by decide +kernel
theorem sound339 : certificate339.Sound := rat_failure_budget_sound certificate339 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound848,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound849,List.forall_mem_nil _⟩⟩) numericValid339

end Cycle12.CutFailureCertificates.Budget016
