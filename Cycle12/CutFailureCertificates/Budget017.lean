import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay042
import Cycle12.CutFailureCertificates.Decay043
import Cycle12.CutFailureCertificates.Decay044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget017

def certificate340 : RatFailureBudget := ⟨(60435757821562209223/25000000000000000),(263947624182981/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate850),(2,CutFailureCertificates.Decay042.certificate851),(2,CutFailureCertificates.Decay042.certificate852)]⟩
theorem numericValid340 : certificate340.NumericValid := by decide +kernel
theorem sound340 : certificate340.Sound := rat_failure_budget_sound certificate340 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound850,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound851,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound852,List.forall_mem_nil _⟩⟩⟩) numericValid340

def certificate341 : RatFailureBudget := ⟨(60435757821562209223/25000000000000000),(61187322877371/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate853),(2,CutFailureCertificates.Decay042.certificate854)]⟩
theorem numericValid341 : certificate341.NumericValid := by decide +kernel
theorem sound341 : certificate341.Sound := rat_failure_budget_sound certificate341 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound853,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound854,List.forall_mem_nil _⟩⟩) numericValid341

def certificate342 : RatFailureBudget := ⟨(1842639907430573677161/1000000000000000000),(68529944380277/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate855),(2,CutFailureCertificates.Decay042.certificate856),(2,CutFailureCertificates.Decay042.certificate857)]⟩
theorem numericValid342 : certificate342.NumericValid := by decide +kernel
theorem sound342 : certificate342.Sound := rat_failure_budget_sound certificate342 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound855,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound856,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound857,List.forall_mem_nil _⟩⟩⟩) numericValid342

def certificate343 : RatFailureBudget := ⟨(1842639907430573677161/1000000000000000000),(31853284876239/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay042.certificate858),(2,CutFailureCertificates.Decay042.certificate859)]⟩
theorem numericValid343 : certificate343.NumericValid := by decide +kernel
theorem sound343 : certificate343.Sound := rat_failure_budget_sound certificate343 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound858,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay042.sound859,List.forall_mem_nil _⟩⟩) numericValid343

def certificate344 : RatFailureBudget := ⟨(1449422154413990634511/1000000000000000000),(17216851186599/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate860),(2,CutFailureCertificates.Decay043.certificate861),(2,CutFailureCertificates.Decay043.certificate862)]⟩
theorem numericValid344 : certificate344.NumericValid := by decide +kernel
theorem sound344 : certificate344.Sound := rat_failure_budget_sound certificate344 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound860,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound861,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound862,List.forall_mem_nil _⟩⟩⟩) numericValid344

def certificate345 : RatFailureBudget := ⟨(1449422154413990634511/1000000000000000000),(50209655366393/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate863),(2,CutFailureCertificates.Decay043.certificate864)]⟩
theorem numericValid345 : certificate345.NumericValid := by decide +kernel
theorem sound345 : certificate345.Sound := rat_failure_budget_sound certificate345 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound863,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound864,List.forall_mem_nil _⟩⟩) numericValid345

def certificate346 : RatFailureBudget := ⟨(146096017909295143181/125000000000000000),(527653903631431/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate865),(2,CutFailureCertificates.Decay043.certificate866),(2,CutFailureCertificates.Decay043.certificate867)]⟩
theorem numericValid346 : certificate346.NumericValid := by decide +kernel
theorem sound346 : certificate346.Sound := rat_failure_budget_sound certificate346 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound865,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound866,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound867,List.forall_mem_nil _⟩⟩⟩) numericValid346

def certificate347 : RatFailureBudget := ⟨(146096017909295143181/125000000000000000),(48985206477709/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate868),(2,CutFailureCertificates.Decay043.certificate869)]⟩
theorem numericValid347 : certificate347.NumericValid := by decide +kernel
theorem sound347 : certificate347.Sound := rat_failure_budget_sound certificate347 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound868,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound869,List.forall_mem_nil _⟩⟩) numericValid347

def certificate348 : RatFailureBudget := ⟨(240392192378436071551/250000000000000000),(317031609759859/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate870),(2,CutFailureCertificates.Decay043.certificate871),(2,CutFailureCertificates.Decay043.certificate872)]⟩
theorem numericValid348 : certificate348.NumericValid := by decide +kernel
theorem sound348 : certificate348.Sound := rat_failure_budget_sound certificate348 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound870,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound871,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound872,List.forall_mem_nil _⟩⟩⟩) numericValid348

def certificate349 : RatFailureBudget := ⟨(240392192378436071551/250000000000000000),(294647973872701/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate873),(2,CutFailureCertificates.Decay043.certificate874)]⟩
theorem numericValid349 : certificate349.NumericValid := by decide +kernel
theorem sound349 : certificate349.Sound := rat_failure_budget_sound certificate349 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound873,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound874,List.forall_mem_nil _⟩⟩) numericValid349

def certificate350 : RatFailureBudget := ⟨(402160494138211081563/500000000000000000),(749101259634027/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate875),(2,CutFailureCertificates.Decay043.certificate876),(2,CutFailureCertificates.Decay043.certificate877)]⟩
theorem numericValid350 : certificate350.NumericValid := by decide +kernel
theorem sound350 : certificate350.Sound := rat_failure_budget_sound certificate350 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound875,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound876,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound877,List.forall_mem_nil _⟩⟩⟩) numericValid350

def certificate351 : RatFailureBudget := ⟨(402160494138211081563/500000000000000000),(697926283997461/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay043.certificate878),(2,CutFailureCertificates.Decay043.certificate879)]⟩
theorem numericValid351 : certificate351.NumericValid := by decide +kernel
theorem sound351 : certificate351.Sound := rat_failure_budget_sound certificate351 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound878,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay043.sound879,List.forall_mem_nil _⟩⟩) numericValid351

def certificate352 : RatFailureBudget := ⟨(682213167231499365169/1000000000000000000),(174801136037507/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate880),(2,CutFailureCertificates.Decay044.certificate881),(2,CutFailureCertificates.Decay044.certificate882)]⟩
theorem numericValid352 : certificate352.NumericValid := by decide +kernel
theorem sound352 : certificate352.Sound := rat_failure_budget_sound certificate352 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound880,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound881,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound882,List.forall_mem_nil _⟩⟩⟩) numericValid352

def certificate353 : RatFailureBudget := ⟨(682213167231499365169/1000000000000000000),(816683519209887/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate883),(2,CutFailureCertificates.Decay044.certificate884)]⟩
theorem numericValid353 : certificate353.NumericValid := by decide +kernel
theorem sound353 : certificate353.Sound := rat_failure_budget_sound certificate353 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound883,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound884,List.forall_mem_nil _⟩⟩) numericValid353

def certificate354 : RatFailureBudget := ⟨(585536924372300477361/1000000000000000000),(503234152124859/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate885),(2,CutFailureCertificates.Decay044.certificate886),(2,CutFailureCertificates.Decay044.certificate887)]⟩
theorem numericValid354 : certificate354.NumericValid := by decide +kernel
theorem sound354 : certificate354.Sound := rat_failure_budget_sound certificate354 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound885,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound886,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound887,List.forall_mem_nil _⟩⟩⟩) numericValid354

def certificate355 : RatFailureBudget := ⟨(585536924372300477361/1000000000000000000),(233380972513611/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate888),(2,CutFailureCertificates.Decay044.certificate889)]⟩
theorem numericValid355 : certificate355.NumericValid := by decide +kernel
theorem sound355 : certificate355.Sound := rat_failure_budget_sound certificate355 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound888,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound889,List.forall_mem_nil _⟩⟩) numericValid355

def certificate356 : RatFailureBudget := ⟨(253857478123666143223/500000000000000000),(1147358094030663/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate890),(2,CutFailureCertificates.Decay044.certificate891),(2,CutFailureCertificates.Decay044.certificate892)]⟩
theorem numericValid356 : certificate356.NumericValid := by decide +kernel
theorem sound356 : certificate356.Sound := rat_failure_budget_sound certificate356 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound890,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound891,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound892,List.forall_mem_nil _⟩⟩⟩) numericValid356

def certificate357 : RatFailureBudget := ⟨(253857478123666143223/500000000000000000),(133401300721507/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate893),(2,CutFailureCertificates.Decay044.certificate894)]⟩
theorem numericValid357 : certificate357.NumericValid := by decide +kernel
theorem sound357 : certificate357.Sound := rat_failure_budget_sound certificate357 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound893,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound894,List.forall_mem_nil _⟩⟩) numericValid357

def certificate358 : RatFailureBudget := ⟨(444163735094597351287/1000000000000000000),(162302859744549/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate895),(2,CutFailureCertificates.Decay044.certificate896),(2,CutFailureCertificates.Decay044.certificate897)]⟩
theorem numericValid358 : certificate358.NumericValid := by decide +kernel
theorem sound358 : certificate358.Sound := rat_failure_budget_sound certificate358 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound895,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound896,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound897,List.forall_mem_nil _⟩⟩⟩) numericValid358

def certificate359 : RatFailureBudget := ⟨(444163735094597351287/1000000000000000000),(1207765410772213/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay044.certificate898),(2,CutFailureCertificates.Decay044.certificate899)]⟩
theorem numericValid359 : certificate359.NumericValid := by decide +kernel
theorem sound359 : certificate359.Sound := rat_failure_budget_sound certificate359 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound898,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay044.sound899,List.forall_mem_nil _⟩⟩) numericValid359

end Cycle12.CutFailureCertificates.Budget017
