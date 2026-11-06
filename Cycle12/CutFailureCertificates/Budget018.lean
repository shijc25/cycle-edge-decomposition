import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay045
import Cycle12.CutFailureCertificates.Decay046
import Cycle12.CutFailureCertificates.Decay047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget018

def certificate360 : RatFailureBudget := ⟨(391610370718798704527/1000000000000000000),(727767221363309/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate900),(2,CutFailureCertificates.Decay045.certificate901),(2,CutFailureCertificates.Decay045.certificate902)]⟩
theorem numericValid360 : certificate360.NumericValid := by decide +kernel
theorem sound360 : certificate360.Sound := rat_failure_budget_sound certificate360 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound900,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound901,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound902,List.forall_mem_nil _⟩⟩⟩) numericValid360

def certificate361 : RatFailureBudget := ⟨(391610370718798704527/1000000000000000000),(1357800913501989/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate903),(2,CutFailureCertificates.Decay045.certificate904)]⟩
theorem numericValid361 : certificate361.NumericValid := by decide +kernel
theorem sound361 : certificate361.Sound := rat_failure_budget_sound certificate361 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound903,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound904,List.forall_mem_nil _⟩⟩) numericValid361

def certificate362 : RatFailureBudget := ⟨(173833819108730224839/500000000000000000),(405059610110771/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate905),(2,CutFailureCertificates.Decay045.certificate906),(2,CutFailureCertificates.Decay045.certificate907)]⟩
theorem numericValid362 : certificate362.NumericValid := by decide +kernel
theorem sound362 : certificate362.Sound := rat_failure_budget_sound certificate362 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound905,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound906,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound907,List.forall_mem_nil _⟩⟩⟩) numericValid362

def certificate363 : RatFailureBudget := ⟨(173833819108730224839/500000000000000000),(1497668160271301/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate908),(2,CutFailureCertificates.Decay045.certificate909)]⟩
theorem numericValid363 : certificate363.NumericValid := by decide +kernel
theorem sound363 : certificate363.Sound := rat_failure_budget_sound certificate363 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound908,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound909,List.forall_mem_nil _⟩⟩) numericValid363

def certificate364 : RatFailureBudget := ⟨(7764035718697559137/25000000000000000),(1796296622404671/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate910),(2,CutFailureCertificates.Decay045.certificate911),(2,CutFailureCertificates.Decay045.certificate912)]⟩
theorem numericValid364 : certificate364.NumericValid := by decide +kernel
theorem sound364 : certificate364.Sound := rat_failure_budget_sound certificate364 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound910,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound911,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound912,List.forall_mem_nil _⟩⟩⟩) numericValid364

def certificate365 : RatFailureBudget := ⟨(7764035718697559137/25000000000000000),(415689848236303/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate913),(2,CutFailureCertificates.Decay045.certificate914)]⟩
theorem numericValid365 : certificate365.NumericValid := by decide +kernel
theorem sound365 : certificate365.Sound := rat_failure_budget_sound certificate365 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound913,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound914,List.forall_mem_nil _⟩⟩) numericValid365

def certificate366 : RatFailureBudget := ⟨(278951216698446561187/1000000000000000000),(1976345993730849/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate915),(2,CutFailureCertificates.Decay045.certificate916),(2,CutFailureCertificates.Decay045.certificate917)]⟩
theorem numericValid366 : certificate366.NumericValid := by decide +kernel
theorem sound366 : certificate366.Sound := rat_failure_budget_sound certificate366 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound915,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound916,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound917,List.forall_mem_nil _⟩⟩⟩) numericValid366

def certificate367 : RatFailureBudget := ⟨(278951216698446561187/1000000000000000000),(1836244558700953/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay045.certificate918),(2,CutFailureCertificates.Decay045.certificate919)]⟩
theorem numericValid367 : certificate367.NumericValid := by decide +kernel
theorem sound367 : certificate367.Sound := rat_failure_budget_sound certificate367 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound918,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay045.sound919,List.forall_mem_nil _⟩⟩) numericValid367

def certificate368 : RatFailureBudget := ⟨(125904482924188692167/500000000000000000),(426462755302329/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate920),(2,CutFailureCertificates.Decay046.certificate921),(2,CutFailureCertificates.Decay046.certificate922)]⟩
theorem numericValid368 : certificate368.NumericValid := by decide +kernel
theorem sound368 : certificate368.Sound := rat_failure_budget_sound certificate368 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound920,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound921,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound922,List.forall_mem_nil _⟩⟩⟩) numericValid368

def certificate369 : RatFailureBudget := ⟨(125904482924188692167/500000000000000000),(201470382034871/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate923),(2,CutFailureCertificates.Decay046.certificate924)]⟩
theorem numericValid369 : certificate369.NumericValid := by decide +kernel
theorem sound369 : certificate369.Sound := rat_failure_budget_sound certificate369 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound923,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound924,List.forall_mem_nil _⟩⟩) numericValid369

def certificate370 : RatFailureBudget := ⟨(114167855278157797031/500000000000000000),(590864358938283/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate925),(2,CutFailureCertificates.Decay046.certificate926),(2,CutFailureCertificates.Decay046.certificate927)]⟩
theorem numericValid370 : certificate370.NumericValid := by decide +kernel
theorem sound370 : certificate370.Sound := rat_failure_budget_sound certificate370 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound925,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound926,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound927,List.forall_mem_nil _⟩⟩⟩) numericValid370

def certificate371 : RatFailureBudget := ⟨(114167855278157797031/500000000000000000),(544461218706903/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate928),(2,CutFailureCertificates.Decay046.certificate929)]⟩
theorem numericValid371 : certificate371.NumericValid := by decide +kernel
theorem sound371 : certificate371.Sound := rat_failure_budget_sound certificate371 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound928,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound929,List.forall_mem_nil _⟩⟩) numericValid371

def certificate372 : RatFailureBudget := ⟨(207902992142096568441/1000000000000000000),(2565216566953133/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate930),(2,CutFailureCertificates.Decay046.certificate931),(2,CutFailureCertificates.Decay046.certificate932)]⟩
theorem numericValid372 : certificate372.NumericValid := by decide +kernel
theorem sound372 : certificate372.Sound := rat_failure_budget_sound certificate372 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound930,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound931,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound932,List.forall_mem_nil _⟩⟩⟩) numericValid372

def certificate373 : RatFailureBudget := ⟨(207902992142096568441/1000000000000000000),(1184121088716761/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate933),(2,CutFailureCertificates.Decay046.certificate934)]⟩
theorem numericValid373 : certificate373.NumericValid := by decide +kernel
theorem sound373 : certificate373.Sound := rat_failure_budget_sound certificate373 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound933,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound934,List.forall_mem_nil _⟩⟩) numericValid373

def certificate374 : RatFailureBudget := ⟨(95005518140300851637/500000000000000000),(688391051145989/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate935),(2,CutFailureCertificates.Decay046.certificate936),(2,CutFailureCertificates.Decay046.certificate937)]⟩
theorem numericValid374 : certificate374.NumericValid := by decide +kernel
theorem sound374 : certificate374.Sound := rat_failure_budget_sound certificate374 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound935,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound936,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound937,List.forall_mem_nil _⟩⟩⟩) numericValid374

def certificate375 : RatFailureBudget := ⟨(95005518140300851637/500000000000000000),(2564913245129367/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay046.certificate938),(2,CutFailureCertificates.Decay046.certificate939)]⟩
theorem numericValid375 : certificate375.NumericValid := by decide +kernel
theorem sound375 : certificate375.Sound := rat_failure_budget_sound certificate375 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound938,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay046.sound939,List.forall_mem_nil _⟩⟩) numericValid375

def certificate376 : RatFailureBudget := ⟨(87129209707661412453/500000000000000000),(2998532062456109/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate940),(2,CutFailureCertificates.Decay047.certificate941),(2,CutFailureCertificates.Decay047.certificate942)]⟩
theorem numericValid376 : certificate376.NumericValid := by decide +kernel
theorem sound376 : certificate376.Sound := rat_failure_budget_sound certificate376 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound940,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound941,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound942,List.forall_mem_nil _⟩⟩⟩) numericValid376

def certificate377 : RatFailureBudget := ⟨(87129209707661412453/500000000000000000),(2748847391843093/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate943),(2,CutFailureCertificates.Decay047.certificate944)]⟩
theorem numericValid377 : certificate377.NumericValid := by decide +kernel
theorem sound377 : certificate377.Sound := rat_failure_budget_sound certificate377 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound943,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound944,List.forall_mem_nil _⟩⟩) numericValid377

def certificate378 : RatFailureBudget := ⟨(40079938802876286037/250000000000000000),(3222842874954319/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate945),(2,CutFailureCertificates.Decay047.certificate946),(2,CutFailureCertificates.Decay047.certificate947)]⟩
theorem numericValid378 : certificate378.NumericValid := by decide +kernel
theorem sound378 : certificate378.Sound := rat_failure_budget_sound certificate378 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound945,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound946,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound947,List.forall_mem_nil _⟩⟩⟩) numericValid378

def certificate379 : RatFailureBudget := ⟨(40079938802876286037/250000000000000000),(741271309535393/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay047.certificate948),(2,CutFailureCertificates.Decay047.certificate949)]⟩
theorem numericValid379 : certificate379.NumericValid := by decide +kernel
theorem sound379 : certificate379.Sound := rat_failure_budget_sound certificate379 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound948,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay047.sound949,List.forall_mem_nil _⟩⟩) numericValid379

end Cycle12.CutFailureCertificates.Budget018
