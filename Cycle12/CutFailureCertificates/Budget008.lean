import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay020
import Cycle12.CutFailureCertificates.Decay021
import Cycle12.CutFailureCertificates.Decay022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget008

def certificate160 : RatFailureBudget := ⟨(93240441523214477/5000000000000000),(10714934582421327/500000000000000000),(31936631794816127/62500000000000000),[(2,CutFailureCertificates.Decay020.certificate400),(2,CutFailureCertificates.Decay020.certificate401),(2,CutFailureCertificates.Decay020.certificate402)]⟩
theorem numericValid160 : certificate160.NumericValid := by decide +kernel
theorem sound160 : certificate160.Sound := rat_failure_budget_sound certificate160 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound400,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound401,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound402,List.forall_mem_nil _⟩⟩⟩) numericValid160

def certificate161 : RatFailureBudget := ⟨(93240441523214477/5000000000000000),(973036207989147/50000000000000000),(224229148777243/1000000000000000000),[(2,CutFailureCertificates.Decay020.certificate403),(2,CutFailureCertificates.Decay020.certificate404)]⟩
theorem numericValid161 : certificate161.NumericValid := by decide +kernel
theorem sound161 : certificate161.Sound := rat_failure_budget_sound certificate161 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound403,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound404,List.forall_mem_nil _⟩⟩) numericValid161

def certificate162 : RatFailureBudget := ⟨(9219145596916937319/500000000000000000),(10788061528761201/500000000000000000),(62043796835958441/125000000000000000),[(2,CutFailureCertificates.Decay020.certificate405),(2,CutFailureCertificates.Decay020.certificate406),(2,CutFailureCertificates.Decay020.certificate407)]⟩
theorem numericValid162 : certificate162.NumericValid := by decide +kernel
theorem sound162 : certificate162.Sound := rat_failure_budget_sound certificate162 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound405,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound406,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound407,List.forall_mem_nil _⟩⟩⟩) numericValid162

def certificate163 : RatFailureBudget := ⟨(9219145596916937319/500000000000000000),(9818351610857493/500000000000000000),(98642364292657/500000000000000000),[(2,CutFailureCertificates.Decay020.certificate408),(2,CutFailureCertificates.Decay020.certificate409)]⟩
theorem numericValid163 : certificate163.NumericValid := by decide +kernel
theorem sound163 : certificate163.Sound := rat_failure_budget_sound certificate163 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound408,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound409,List.forall_mem_nil _⟩⟩) numericValid163

def certificate164 : RatFailureBudget := ⟨(4557924207760763037/250000000000000000),(11604381727118023/500000000000000000),(268896424125679123/500000000000000000),[(2,CutFailureCertificates.Decay020.certificate410),(2,CutFailureCertificates.Decay020.certificate411),(2,CutFailureCertificates.Decay020.certificate412)]⟩
theorem numericValid164 : certificate164.NumericValid := by decide +kernel
theorem sound164 : certificate164.Sound := rat_failure_budget_sound certificate164 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound410,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound411,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound412,List.forall_mem_nil _⟩⟩⟩) numericValid164

def certificate165 : RatFailureBudget := ⟨(4557924207760763037/250000000000000000),(19806692518299793/1000000000000000000),(1492688956796773/1000000000000000000),[(2,CutFailureCertificates.Decay020.certificate413),(2,CutFailureCertificates.Decay020.certificate414)]⟩
theorem numericValid165 : certificate165.NumericValid := by decide +kernel
theorem sound165 : certificate165.Sound := rat_failure_budget_sound certificate165 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound413,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound414,List.forall_mem_nil _⟩⟩) numericValid165

def certificate166 : RatFailureBudget := ⟨(18028241671172037989/1000000000000000000),(21943312110361101/1000000000000000000),(13040728183568079/125000000000000000),[(2,CutFailureCertificates.Decay020.certificate415),(2,CutFailureCertificates.Decay020.certificate416),(2,CutFailureCertificates.Decay020.certificate417)]⟩
theorem numericValid166 : certificate166.NumericValid := by decide +kernel
theorem sound166 : certificate166.Sound := rat_failure_budget_sound certificate166 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound415,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound416,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound417,List.forall_mem_nil _⟩⟩⟩) numericValid166

def certificate167 : RatFailureBudget := ⟨(18028241671172037989/1000000000000000000),(10009383080984223/500000000000000000),(210421727134549/200000000000000000),[(2,CutFailureCertificates.Decay020.certificate418),(2,CutFailureCertificates.Decay020.certificate419)]⟩
theorem numericValid167 : certificate167.NumericValid := by decide +kernel
theorem sound167 : certificate167.Sound := rat_failure_budget_sound certificate167 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound418,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay020.sound419,List.forall_mem_nil _⟩⟩) numericValid167

def certificate168 : RatFailureBudget := ⟨(17827863725192677929/1000000000000000000),(21862032108312281/1000000000000000000),(101828306612187319/1000000000000000000),[(2,CutFailureCertificates.Decay021.certificate420),(2,CutFailureCertificates.Decay021.certificate421),(2,CutFailureCertificates.Decay021.certificate422)]⟩
theorem numericValid168 : certificate168.NumericValid := by decide +kernel
theorem sound168 : certificate168.Sound := rat_failure_budget_sound certificate168 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound420,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound421,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound422,List.forall_mem_nil _⟩⟩⟩) numericValid168

def certificate169 : RatFailureBudget := ⟨(17827863725192677929/1000000000000000000),(101076542275439/5000000000000000),(231100019048611/250000000000000000),[(2,CutFailureCertificates.Decay021.certificate423),(2,CutFailureCertificates.Decay021.certificate424)]⟩
theorem numericValid169 : certificate169.NumericValid := by decide +kernel
theorem sound169 : certificate169.Sound := rat_failure_budget_sound certificate169 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound423,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound424,List.forall_mem_nil _⟩⟩) numericValid169

def certificate170 : RatFailureBudget := ⟨(8815251257408174541/500000000000000000),(22248624116552599/1000000000000000000),(94033727072941809/1000000000000000000),[(2,CutFailureCertificates.Decay021.certificate425),(2,CutFailureCertificates.Decay021.certificate426),(2,CutFailureCertificates.Decay021.certificate427)]⟩
theorem numericValid170 : certificate170.NumericValid := by decide +kernel
theorem sound170 : certificate170.Sound := rat_failure_budget_sound certificate170 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound425,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound426,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound427,List.forall_mem_nil _⟩⟩⟩) numericValid170

def certificate171 : RatFailureBudget := ⟨(8815251257408174541/500000000000000000),(20369535996052981/1000000000000000000),(781826470684977/1000000000000000000),[(2,CutFailureCertificates.Decay021.certificate428),(2,CutFailureCertificates.Decay021.certificate429)]⟩
theorem numericValid171 : certificate171.NumericValid := by decide +kernel
theorem sound171 : certificate171.Sound := rat_failure_budget_sound certificate171 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound428,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound429,List.forall_mem_nil _⟩⟩) numericValid171

def certificate172 : RatFailureBudget := ⟨(8718049514346597573/500000000000000000),(22217202743553787/1000000000000000000),(47159066816094467/500000000000000000),[(2,CutFailureCertificates.Decay021.certificate430),(2,CutFailureCertificates.Decay021.certificate431),(2,CutFailureCertificates.Decay021.certificate432)]⟩
theorem numericValid172 : certificate172.NumericValid := by decide +kernel
theorem sound172 : certificate172.Sound := rat_failure_budget_sound certificate172 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound430,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound431,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound432,List.forall_mem_nil _⟩⟩⟩) numericValid172

def certificate173 : RatFailureBudget := ⟨(8718049514346597573/500000000000000000),(20567961194126517/1000000000000000000),(329114028077497/500000000000000000),[(2,CutFailureCertificates.Decay021.certificate433),(2,CutFailureCertificates.Decay021.certificate434)]⟩
theorem numericValid173 : certificate173.NumericValid := by decide +kernel
theorem sound173 : certificate173.Sound := rat_failure_budget_sound certificate173 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound433,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound434,List.forall_mem_nil _⟩⟩) numericValid173

def certificate174 : RatFailureBudget := ⟨(17244595680082648633/1000000000000000000),(2817171309854231/125000000000000000),(16177704355535347/200000000000000000),[(2,CutFailureCertificates.Decay021.certificate435),(2,CutFailureCertificates.Decay021.certificate436),(2,CutFailureCertificates.Decay021.certificate437)]⟩
theorem numericValid174 : certificate174.NumericValid := by decide +kernel
theorem sound174 : certificate174.Sound := rat_failure_budget_sound certificate174 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound435,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound436,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound437,List.forall_mem_nil _⟩⟩⟩) numericValid174

def certificate175 : RatFailureBudget := ⟨(17244595680082648633/1000000000000000000),(2590354959540331/125000000000000000),(111346678827003/200000000000000000),[(2,CutFailureCertificates.Decay021.certificate438),(2,CutFailureCertificates.Decay021.certificate439)]⟩
theorem numericValid175 : certificate175.NumericValid := by decide +kernel
theorem sound175 : certificate175.Sound := rat_failure_budget_sound certificate175 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound438,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay021.sound439,List.forall_mem_nil _⟩⟩) numericValid175

def certificate176 : RatFailureBudget := ⟨(17055936265939102859/1000000000000000000),(564287668909131/25000000000000000),(81154755691330971/1000000000000000000),[(2,CutFailureCertificates.Decay022.certificate440),(2,CutFailureCertificates.Decay022.certificate441),(2,CutFailureCertificates.Decay022.certificate442)]⟩
theorem numericValid176 : certificate176.NumericValid := by decide +kernel
theorem sound176 : certificate176.Sound := rat_failure_budget_sound certificate176 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound440,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound441,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound442,List.forall_mem_nil _⟩⟩⟩) numericValid176

def certificate177 : RatFailureBudget := ⟨(17055936265939102859/1000000000000000000),(2092331710884129/100000000000000000),(61954569214311/125000000000000000),[(2,CutFailureCertificates.Decay022.certificate443),(2,CutFailureCertificates.Decay022.certificate444)]⟩
theorem numericValid177 : certificate177.NumericValid := by decide +kernel
theorem sound177 : certificate177.Sound := rat_failure_budget_sound certificate177 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound443,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound444,List.forall_mem_nil _⟩⟩) numericValid177

def certificate178 : RatFailureBudget := ⟨(4217516481839748143/250000000000000000),(11422313947957031/500000000000000000),(452920054551799/6250000000000000),[(2,CutFailureCertificates.Decay022.certificate445),(2,CutFailureCertificates.Decay022.certificate446),(2,CutFailureCertificates.Decay022.certificate447)]⟩
theorem numericValid178 : certificate178.NumericValid := by decide +kernel
theorem sound178 : certificate178.Sound := rat_failure_budget_sound certificate178 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound445,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound446,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound447,List.forall_mem_nil _⟩⟩⟩) numericValid178

def certificate179 : RatFailureBudget := ⟨(4217516481839748143/250000000000000000),(10539312312111913/500000000000000000),(3290345236189/7812500000000000),[(2,CutFailureCertificates.Decay022.certificate448),(2,CutFailureCertificates.Decay022.certificate449)]⟩
theorem numericValid179 : certificate179.NumericValid := by decide +kernel
theorem sound179 : certificate179.Sound := rat_failure_budget_sound certificate179 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound448,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay022.sound449,List.forall_mem_nil _⟩⟩) numericValid179

end Cycle12.CutFailureCertificates.Budget008
