import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch309
import Cycle12.MergedCutProfiles.Batch644
import Cycle12.MergedCutProfiles.Batch645

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch362

def retention4344 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(680532334989028916/120871515643124418446001),(673794391078246451/1000000000000000000),4,(318855556851922912478260614089245551/134758878215649290200000000000000000),false,MergedCutProfiles.Batch644.profile25796,(fun _ => MergedCutProfiles.Batch644.profile25796)⟩
theorem profilesValid4344 : retention4344.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25796
theorem numericValid4344 : retention4344.NumericValid := by decide +kernel
def certificate4344 : RatCutBinCertificate := ⟨⟨retention4344,(217193557780974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(2364208365776652311/1000000000000000000)⟩,(499999003160335623/500000000000000000),(748627126255204817/1000000000000000000),(34634654113914439/1000000000000000000),(16789009215495047/1000000000000000000)⟩
theorem valid4344 : certificate4344.Valid := by decide +kernel
theorem sound4344 : certificate4344.Sound := rat_cut_bin_certificate_sound certificate4344 profilesValid4344 numericValid4344 valid4344

def retention4345 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(6845536379408885257/120871515643124418446001),(170133083747257229/250000000000000000),4,(25164703437708792148428411860820841/10633317734203576812500000000000000),false,MergedCutProfiles.Batch644.profile25797,(fun _ => MergedCutProfiles.Batch644.profile25797)⟩
theorem profilesValid4345 : retention4345.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25797
theorem numericValid4345 : retention4345.NumericValid := by decide +kernel
def certificate4345 : RatCutBinCertificate := ⟨⟨retention4345,(217193557780974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(1182339629387108591/500000000000000000)⟩,(499999003160335623/500000000000000000),(746033360374395509/1000000000000000000),(35390084797087091/1000000000000000000),(8594308686312013/500000000000000000)⟩
theorem valid4345 : certificate4345.Valid := by decide +kernel
theorem sound4345 : certificate4345.Sound := rat_cut_bin_certificate_sound certificate4345 profilesValid4345 numericValid4345 valid4345

def retention4346 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/40),(6845536379408885257/1000000000000000000),(5/4),(947921899345172640835708078690117174471/438114328282168656448000000000000000000),false,MergedCutProfiles.Batch644.profile25798,(fun _ => MergedCutProfiles.Batch644.profile25798)⟩
theorem profilesValid4346 : retention4346.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25798
theorem numericValid4346 : retention4346.NumericValid := by decide +kernel
def certificate4346 : RatCutBinCertificate := ⟨⟨retention4346,(217193557780974093/125000000000000000),(1970684370264843/1000000000000000000),(1433645119237357817/200000000000000000),(87027072012813190743797/100000000000000000),(135190211339594467/62500000000000000)⟩,(499999003160335623/500000000000000000),(574888573449290731/1000000000000000000),(106865157784268237/1000000000000000000),(153816949726621917/1000000000000000000)⟩
theorem valid4346 : certificate4346.Valid := by decide +kernel
theorem sound4346 : certificate4346.Sound := rat_cut_bin_certificate_sound certificate4346 profilesValid4346 numericValid4346 valid4346

def retention4347 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(200268739784696450/23032998842882170964523),(113098037643674347/200000000000000000),4,(4957416206248293460149532354708220919/2261960752873486940000000000000000000),true,MergedCutProfiles.Batch644.profile25799,![MergedCutProfiles.Batch644.profile25799,MergedCutProfiles.Batch645.profile25800,MergedCutProfiles.Batch645.profile25800,MergedCutProfiles.Batch645.profile25801,MergedCutProfiles.Batch645.profile25801,MergedCutProfiles.Batch645.profile25801,MergedCutProfiles.Batch645.profile25801,MergedCutProfiles.Batch645.profile25802,MergedCutProfiles.Batch645.profile25802,MergedCutProfiles.Batch645.profile25802,MergedCutProfiles.Batch645.profile25803,MergedCutProfiles.Batch645.profile25803,MergedCutProfiles.Batch645.profile25803,MergedCutProfiles.Batch645.profile25803,MergedCutProfiles.Batch645.profile25803,MergedCutProfiles.Batch645.profile25804]⟩
theorem profilesValid4347 : retention4347.ProfilesValid := by
  change ∀ j : Fin 16, (retention4347.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25799
  · exact MergedCutProfiles.Batch645.valid25800
  · exact MergedCutProfiles.Batch645.valid25800
  · exact MergedCutProfiles.Batch645.valid25801
  · exact MergedCutProfiles.Batch645.valid25801
  · exact MergedCutProfiles.Batch645.valid25801
  · exact MergedCutProfiles.Batch645.valid25801
  · exact MergedCutProfiles.Batch645.valid25802
  · exact MergedCutProfiles.Batch645.valid25802
  · exact MergedCutProfiles.Batch645.valid25802
  · exact MergedCutProfiles.Batch645.valid25803
  · exact MergedCutProfiles.Batch645.valid25803
  · exact MergedCutProfiles.Batch645.valid25803
  · exact MergedCutProfiles.Batch645.valid25803
  · exact MergedCutProfiles.Batch645.valid25803
  · exact MergedCutProfiles.Batch645.valid25804
theorem numericValid4347 : retention4347.NumericValid := by decide +kernel
def certificate4347 : RatCutBinCertificate := ⟨⟨retention4347,(1827170890992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(87561766598395563/40000000000000000)⟩,(999997283859443801/1000000000000000000),(591033347930089867/1000000000000000000),(98152356914104003/1000000000000000000),(43250675108487041/1000000000000000000)⟩
theorem valid4347 : certificate4347.Valid := by decide +kernel
theorem sound4347 : certificate4347.Sound := rat_cut_bin_certificate_sound certificate4347 profilesValid4347 numericValid4347 valid4347

def retention4348 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(326626070500000000/23032998842882170964523),(4005374795693929/5000000000000000),(73/20),(274319780022613258731453506415464137/114439279876969400000000000000000000),false,MergedCutProfiles.Batch645.profile25805,(fun _ => MergedCutProfiles.Batch645.profile25805)⟩
theorem profilesValid4348 : retention4348.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25805
theorem numericValid4348 : retention4348.NumericValid := by decide +kernel
def certificate4348 : RatCutBinCertificate := ⟨⟨retention4348,(1827170890992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(95788134650509559/40000000000000000)⟩,(999997283859443801/1000000000000000000),(430999183419887881/1000000000000000000),(103125117282235043/500000000000000000),(27629570813084603/250000000000000000)⟩
theorem valid4348 : certificate4348.Valid := by decide +kernel
theorem sound4348 : certificate4348.Sound := rat_cut_bin_certificate_sound certificate4348 profilesValid4348 numericValid4348 valid4348

def retention4349 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(16000000000000000000/23032998842882170964523),(653252141/500000000),(49/20),(37506521532361930307/16000000000000000000),true,MergedCutProfiles.Batch007.profile297,![MergedCutProfiles.Batch007.profile297,MergedCutProfiles.Batch007.profile313,MergedCutProfiles.Batch309.profile12387,MergedCutProfiles.Batch007.profile300,MergedCutProfiles.Batch309.profile12385,MergedCutProfiles.Batch309.profile12386,MergedCutProfiles.Batch008.profile329,MergedCutProfiles.Batch007.profile315,MergedCutProfiles.Batch008.profile330,MergedCutProfiles.Batch007.profile316,MergedCutProfiles.Batch309.profile12389,MergedCutProfiles.Batch007.profile317,MergedCutProfiles.Batch007.profile310,MergedCutProfiles.Batch007.profile311,MergedCutProfiles.Batch007.profile312,MergedCutProfiles.Batch007.profile318]⟩
theorem profilesValid4349 : retention4349.ProfilesValid := by
  change ∀ j : Fin 16, (retention4349.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch007.valid297
  · exact MergedCutProfiles.Batch007.valid313
  · exact MergedCutProfiles.Batch309.valid12387
  · exact MergedCutProfiles.Batch007.valid300
  · exact MergedCutProfiles.Batch309.valid12385
  · exact MergedCutProfiles.Batch309.valid12386
  · exact MergedCutProfiles.Batch008.valid329
  · exact MergedCutProfiles.Batch007.valid315
  · exact MergedCutProfiles.Batch008.valid330
  · exact MergedCutProfiles.Batch007.valid316
  · exact MergedCutProfiles.Batch309.valid12389
  · exact MergedCutProfiles.Batch007.valid317
  · exact MergedCutProfiles.Batch007.valid310
  · exact MergedCutProfiles.Batch007.valid311
  · exact MergedCutProfiles.Batch007.valid312
  · exact MergedCutProfiles.Batch007.valid318
theorem numericValid4349 : retention4349.NumericValid := by decide +kernel
def certificate4349 : RatCutBinCertificate := ⟨⟨retention4349,(1827170890992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(468512850140480603/200000000000000000)⟩,(999997283859443801/1000000000000000000),(336860400637869477/1000000000000000000),(74149469199266723/250000000000000000),(54590898494353177/250000000000000000)⟩
theorem valid4349 : certificate4349.Valid := by decide +kernel
theorem sound4349 : certificate4349.Sound := rat_cut_bin_certificate_sound certificate4349 profilesValid4349 numericValid4349 valid4349

def retention4350 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid4350 : retention4350.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid4350 : retention4350.NumericValid := by decide +kernel
def certificate4350 : RatCutBinCertificate := ⟨⟨retention4350,(1827170890992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(498442207759129409/500000000000000000)⟩,(999997283859443801/1000000000000000000),(413129254593256971/1000000000000000000),(22166574541193969/100000000000000000),(43517068613454057/200000000000000000)⟩
theorem valid4350 : certificate4350.Valid := by decide +kernel
theorem sound4350 : certificate4350.Sound := rat_cut_bin_certificate_sound certificate4350 profilesValid4350 numericValid4350 valid4350

def retention4351 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(16000000000000000000/23032998842882170964523),(7772958745101689589/500000000000000000),1,(35713057605598882255422391345256220659/15545917490203379178000000000000000000),false,MergedCutProfiles.Batch645.profile25806,(fun _ => MergedCutProfiles.Batch645.profile25806)⟩
theorem profilesValid4351 : retention4351.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25806
theorem numericValid4351 : retention4351.NumericValid := by decide +kernel
def certificate4351 : RatCutBinCertificate := ⟨⟨retention4351,(1623557164992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(287085613207495917/125000000000000000)⟩,(999997586536935189/1000000000000000000),(17244645366554369/500000000000000000),(831310505764964479/1000000000000000000),(207937000126569417/125000000000000000)⟩
theorem valid4351 : certificate4351.Valid := by decide +kernel
theorem sound4351 : certificate4351.Sound := rat_cut_bin_certificate_sound certificate4351 profilesValid4351 numericValid4351 valid4351

def retention4352 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid4352 : retention4352.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid4352 : retention4352.NumericValid := by decide +kernel
def certificate4352 : RatCutBinCertificate := ⟨⟨retention4352,(1623557164992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(249239221937677907/250000000000000000)⟩,(999997586536935189/1000000000000000000),(39726408637569737/500000000000000000),(713743467862232111/1000000000000000000),(87581913584213437/125000000000000000)⟩
theorem valid4352 : certificate4352.Valid := by decide +kernel
theorem sound4352 : certificate4352.Sound := rat_cut_bin_certificate_sound certificate4352 profilesValid4352 numericValid4352 valid4352

def retention4353 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(170775387020713724/23032998842882170964523),(676338166418668213/1000000000000000000),4,(1281649279788953553539239569022868691/541070533134934570400000000000000000),false,MergedCutProfiles.Batch645.profile25807,(fun _ => MergedCutProfiles.Batch645.profile25807)⟩
theorem profilesValid4353 : retention4353.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25807
theorem numericValid4353 : retention4353.NumericValid := by decide +kernel
def certificate4353 : RatCutBinCertificate := ⟨⟨retention4353,(1743873266992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(236624587439396439/100000000000000000)⟩,(999997407683688733/1000000000000000000),(148841583457196561/200000000000000000),(35927147299074551/1000000000000000000),(3487928204372697/200000000000000000)⟩
theorem valid4353 : certificate4353.Valid := by decide +kernel
theorem sound4353 : certificate4353.Sound := rat_cut_bin_certificate_sound certificate4353 profilesValid4353 numericValid4353 valid4353

def retention4354 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(5575645297244474047/92131995371528683858092),(42693846755178431/62500000000000000),4,(80917502760522611408655230751481491/34155077404142744800000000000000000),false,MergedCutProfiles.Batch645.profile25808,(fun _ => MergedCutProfiles.Batch645.profile25808)⟩
theorem profilesValid4354 : retention4354.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25808
theorem numericValid4354 : retention4354.NumericValid := by decide +kernel
def certificate4354 : RatCutBinCertificate := ⟨⟨retention4354,(1743873266992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(118331898380064891/50000000000000000)⟩,(999997407683688733/1000000000000000000),(741665284385474199/1000000000000000000),(3668267809095043/100000000000000000),(17840507891685301/1000000000000000000)⟩
theorem valid4354 : certificate4354.Valid := by decide +kernel
theorem sound4354 : certificate4354.Sound := rat_cut_bin_certificate_sound certificate4354 profilesValid4354 numericValid4354 valid4354

def retention4355 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/40),(5575645297244474047/1000000000000000000),(13/10),(4819080075528869508383415602768138705199/2230258118897789618800000000000000000000),false,MergedCutProfiles.Batch645.profile25809,(fun _ => MergedCutProfiles.Batch645.profile25809)⟩
theorem profilesValid4355 : retention4355.ProfilesValid := by
  exact MergedCutProfiles.Batch645.valid25809
theorem numericValid4355 : retention4355.NumericValid := by decide +kernel
def certificate4355 : RatCutBinCertificate := ⟨⟨retention4355,(1743873266992643571/1000000000000000000),(1291114465089419/500000000000000000),(3627439338457358533/500000000000000000),(167845706612490950672187/250000000000000000),(1079982721820386141/500000000000000000)⟩,(999997407683688733/1000000000000000000),(2265719870963839/3906250000000000),(52022503334305819/500000000000000000),(5625375869720953/40000000000000000)⟩
theorem valid4355 : certificate4355.Valid := by decide +kernel
theorem sound4355 : certificate4355.Sound := rat_cut_bin_certificate_sound certificate4355 profilesValid4355 numericValid4355 valid4355

def certificates : List RatCutBinCertificate := [certificate4344,certificate4345,certificate4346,certificate4347,certificate4348,certificate4349,certificate4350,certificate4351,certificate4352,certificate4353,certificate4354,certificate4355]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4344,List.forall_mem_cons.mpr ⟨sound4345,List.forall_mem_cons.mpr ⟨sound4346,List.forall_mem_cons.mpr ⟨sound4347,List.forall_mem_cons.mpr ⟨sound4348,List.forall_mem_cons.mpr ⟨sound4349,List.forall_mem_cons.mpr ⟨sound4350,List.forall_mem_cons.mpr ⟨sound4351,List.forall_mem_cons.mpr ⟨sound4352,List.forall_mem_cons.mpr ⟨sound4353,List.forall_mem_cons.mpr ⟨sound4354,List.forall_mem_cons.mpr ⟨sound4355,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch362
