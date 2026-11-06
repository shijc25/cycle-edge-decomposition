import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch004
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch644

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch360

def retention4320 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(12800000000000000000/47800972580928223399921),(3634329688298576097/250000000000000000),1,(33491973948913207225561185447773754383/14537318753194304388000000000000000000),false,MergedCutProfiles.Batch644.profile25781,(fun _ => MergedCutProfiles.Batch644.profile25781)⟩
theorem profilesValid4320 : retention4320.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25781
theorem numericValid4320 : retention4320.NumericValid := by decide +kernel
def certificate4320 : RatCutBinCertificate := ⟨⟨retention4320,(446171425503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(460721420303718501/200000000000000000)⟩,(249999734634674439/250000000000000000),(24083535012275429/125000000000000000),(489692905986975167/1000000000000000000),(48687794122303161/50000000000000000)⟩
theorem valid4320 : certificate4320.Valid := by decide +kernel
theorem sound4320 : certificate4320.Sound := rat_cut_bin_certificate_sound certificate4320 profilesValid4320 numericValid4320 valid4320

def retention4321 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid4321 : retention4321.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid4321 : retention4321.NumericValid := by decide +kernel
def certificate4321 : RatCutBinCertificate := ⟨⟨retention4321,(446171425503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(498639927319630317/500000000000000000)⟩,(249999734634674439/250000000000000000),(41772896282728887/100000000000000000),(108812629271632579/500000000000000000),(213703026912706303/1000000000000000000)⟩
theorem valid4321 : certificate4321.Valid := by decide +kernel
theorem sound4321 : certificate4321.Sound := rat_cut_bin_certificate_sound certificate4321 profilesValid4321 numericValid4321 valid4321

def retention4322 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(12800000000000000000/47800972580928223399921),(15055199854349967157/1000000000000000000),1,(34736535406821014447357655711288740149/15055199854349967157000000000000000000),false,MergedCutProfiles.Batch644.profile25781,(fun _ => MergedCutProfiles.Batch644.profile25781)⟩
theorem profilesValid4322 : retention4322.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25781
theorem numericValid4322 : retention4322.NumericValid := by decide +kernel
def certificate4322 : RatCutBinCertificate := ⟨⟨retention4322,(405125280253821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(46140939218895287/20000000000000000)⟩,(124999879523658693/125000000000000000),(35577093709350543/1000000000000000000),(207052258951884851/250000000000000000),(207103089737453437/125000000000000000)⟩
theorem valid4322 : certificate4322.Valid := by decide +kernel
theorem sound4322 : certificate4322.Sound := rat_cut_bin_certificate_sound certificate4322 profilesValid4322 numericValid4322 valid4322

def retention4323 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid4323 : retention4323.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid4323 : retention4323.NumericValid := by decide +kernel
def certificate4323 : RatCutBinCertificate := ⟨⟨retention4323,(405125280253821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(997303289762079117/1000000000000000000)⟩,(124999879523658693/125000000000000000),(20574991269953883/250000000000000000),(141392878628709837/200000000000000000),(694238997212702123/1000000000000000000)⟩
theorem valid4323 : certificate4323.Valid := by decide +kernel
theorem sound4323 : certificate4323.Sound := rat_cut_bin_certificate_sound certificate4323 profilesValid4323 numericValid4323 valid4323

def retention4324 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(703060577861258238/239004862904641116999605),(34804979102042487/50000000000000000),4,(810893073466091586921538751483533/339892374043383662109375000000000),false,MergedCutProfiles.Batch644.profile25782,(fun _ => MergedCutProfiles.Batch644.profile25782)⟩
theorem profilesValid4324 : retention4324.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25782
theorem numericValid4324 : retention4324.NumericValid := by decide +kernel
def certificate4324 : RatCutBinCertificate := ⟨⟨retention4324,(441829058503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(1192362891579375381/500000000000000000)⟩,(499999474434689227/500000000000000000),(333568423420623933/500000000000000000),(62832785329472179/1000000000000000000),(30853498102946169/1000000000000000000)⟩
theorem valid4324 : certificate4324.Valid := by decide +kernel
theorem sound4324 : certificate4324.Sound := rat_cut_bin_certificate_sound certificate4324 profilesValid4324 numericValid4324 valid4324

def retention4325 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(12346628938005746127/239004862904641116999605),(351530288930629119/500000000000000000),4,(587362437599094719182413508198329/246363759215508800000000000000000),false,MergedCutProfiles.Batch644.profile25783,(fun _ => MergedCutProfiles.Batch644.profile25783)⟩
theorem profilesValid4325 : retention4325.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25783
theorem numericValid4325 : retention4325.NumericValid := by decide +kernel
def certificate4325 : RatCutBinCertificate := ⟨⟨retention4325,(441829058503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(59577943622595911/25000000000000000)⟩,(499999474434689227/500000000000000000),(665351823475928727/1000000000000000000),(15889420429261781/250000000000000000),(31246645852806743/1000000000000000000)⟩
theorem valid4325 : certificate4325.Valid := by decide +kernel
theorem sound4325 : certificate4325.Sound := rat_cut_bin_certificate_sound certificate4325 profilesValid4325 numericValid4325 valid4325

def retention4326 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/40),(12346628938005746127/1000000000000000000),(11/10),(10630620941521427136808924390308029733551/4938651575202298450800000000000000000000),false,MergedCutProfiles.Batch644.profile25784,(fun _ => MergedCutProfiles.Batch644.profile25784)⟩
theorem profilesValid4326 : retention4326.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25784
theorem numericValid4326 : retention4326.NumericValid := by decide +kernel
def certificate4326 : RatCutBinCertificate := ⟨⟨retention4326,(441829058503821687/250000000000000000),(249776479000013/250000000000000000),(6999655494241419451/1000000000000000000),(210034515586513729646543/125000000000000000),(1076128814784729543/500000000000000000)⟩,(499999474434689227/500000000000000000),(100663935480924117/200000000000000000),(37784083904269271/250000000000000000),(32309411442163473/125000000000000000)⟩
theorem valid4326 : certificate4326.Valid := by decide +kernel
theorem sound4326 : certificate4326.Sound := rat_cut_bin_certificate_sound certificate4326 profilesValid4326 numericValid4326 valid4326

def retention4327 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(469879277107253903/82624014196148766232829),(560150658558941171/1000000000000000000),4,(762711913092357456357530176455747/350094161599338231875000000000000),true,MergedCutProfiles.Batch644.profile25785,![MergedCutProfiles.Batch644.profile25785,MergedCutProfiles.Batch644.profile25785,MergedCutProfiles.Batch644.profile25786,MergedCutProfiles.Batch644.profile25786,MergedCutProfiles.Batch644.profile25786,MergedCutProfiles.Batch644.profile25786,MergedCutProfiles.Batch644.profile25787,MergedCutProfiles.Batch644.profile25787,MergedCutProfiles.Batch644.profile25787,MergedCutProfiles.Batch644.profile25787,MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch441.profile17658,MergedCutProfiles.Batch441.profile17658]⟩
theorem profilesValid4327 : retention4327.ProfilesValid := by
  change ∀ j : Fin 16, (retention4327.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25785
  · exact MergedCutProfiles.Batch644.valid25785
  · exact MergedCutProfiles.Batch644.valid25786
  · exact MergedCutProfiles.Batch644.valid25786
  · exact MergedCutProfiles.Batch644.valid25786
  · exact MergedCutProfiles.Batch644.valid25786
  · exact MergedCutProfiles.Batch644.valid25787
  · exact MergedCutProfiles.Batch644.valid25787
  · exact MergedCutProfiles.Batch644.valid25787
  · exact MergedCutProfiles.Batch644.valid25787
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch441.valid17658
  · exact MergedCutProfiles.Batch441.valid17658
theorem numericValid4327 : retention4327.NumericValid := by decide +kernel
def certificate4327 : RatCutBinCertificate := ⟨⟨retention4327,(1839271295509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(2177091714651079163/1000000000000000000)⟩,(3906243894796107/3906250000000000),(299107687675041677/500000000000000000),(23604728346211857/250000000000000000),(41346044534290283/1000000000000000000)⟩
theorem valid4327 : certificate4327.Valid := by decide +kernel
theorem sound4327 : certificate4327.Sound := rat_cut_bin_certificate_sound certificate4327 profilesValid4327 numericValid4327 valid4327

def retention4328 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(648171963000000000/82624014196148766232829),(469879277107253903/500000000000000000),(63/20),(895448978228104242798638938820560668279/375903421685803122400000000000000000000),false,MergedCutProfiles.Batch644.profile25788,(fun _ => MergedCutProfiles.Batch644.profile25788)⟩
theorem profilesValid4328 : retention4328.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25788
theorem numericValid4328 : retention4328.NumericValid := by decide +kernel
def certificate4328 : RatCutBinCertificate := ⟨⟨retention4328,(1839271295509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(1190472295455090549/500000000000000000)⟩,(3906243894796107/3906250000000000),(78873181158341459/200000000000000000),(238684448703844197/1000000000000000000),(143715009789746429/1000000000000000000)⟩
theorem valid4328 : certificate4328.Valid := by decide +kernel
theorem sound4328 : certificate4328.Sound := rat_cut_bin_certificate_sound certificate4328 profilesValid4328 numericValid4328 valid4328

def retention4329 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(21448346863995491271/82624014196148766232829),(648171963/500000000),(49/20),(37644254921238081749/16000000000000000000),true,MergedCutProfiles.Batch644.profile25789,![MergedCutProfiles.Batch644.profile25789,MergedCutProfiles.Batch308.profile12338,MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch308.profile12340,MergedCutProfiles.Batch308.profile12346,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch004.profile187,MergedCutProfiles.Batch308.profile12342,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch004.profile190,MergedCutProfiles.Batch005.profile201,MergedCutProfiles.Batch004.profile191,MergedCutProfiles.Batch005.profile212,MergedCutProfiles.Batch004.profile192,MergedCutProfiles.Batch004.profile193]⟩
theorem profilesValid4329 : retention4329.ProfilesValid := by
  change ∀ j : Fin 16, (retention4329.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch644.valid25789
  · exact MergedCutProfiles.Batch308.valid12338
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch308.valid12340
  · exact MergedCutProfiles.Batch308.valid12346
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch004.valid187
  · exact MergedCutProfiles.Batch308.valid12342
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch004.valid190
  · exact MergedCutProfiles.Batch005.valid201
  · exact MergedCutProfiles.Batch004.valid191
  · exact MergedCutProfiles.Batch005.valid212
  · exact MergedCutProfiles.Batch004.valid192
  · exact MergedCutProfiles.Batch004.valid193
theorem numericValid4329 : retention4329.NumericValid := by decide +kernel
def certificate4329 : RatCutBinCertificate := ⟨⟨retention4329,(1839271295509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(146990484636011483/62500000000000000)⟩,(3906243894796107/3906250000000000),(336526381752747169/1000000000000000000),(59392281053276027/200000000000000000),(54725559652087087/250000000000000000)⟩
theorem valid4329 : certificate4329.Valid := by decide +kernel
theorem sound4329 : certificate4329.Sound := rat_cut_bin_certificate_sound certificate4329 profilesValid4329 numericValid4329 valid4329

def retention4330 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(32000000000000000000/82624014196148766232829),(21448346863995491271/500000000000000000),1,(33816184696058223092763988283342364513/14298897909330327514000000000000000000),false,MergedCutProfiles.Batch644.profile25790,(fun _ => MergedCutProfiles.Batch644.profile25790)⟩
theorem profilesValid4330 : retention4330.ProfilesValid := by
  exact MergedCutProfiles.Batch644.valid25790
theorem numericValid4330 : retention4330.NumericValid := by decide +kernel
def certificate4330 : RatCutBinCertificate := ⟨⟨retention4330,(1839271295509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(94583026355605549/40000000000000000)⟩,(3906243894796107/3906250000000000),(43820493414809081/250000000000000000),(51894548705289157/100000000000000000),(116297762008203949/100000000000000000)⟩
theorem valid4330 : certificate4330.Valid := by decide +kernel
theorem sound4330 : certificate4330.Sound := rat_cut_bin_certificate_sound certificate4330 profilesValid4330 numericValid4330 valid4330

def retention4331 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid4331 : retention4331.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid4331 : retention4331.NumericValid := by decide +kernel
def certificate4331 : RatCutBinCertificate := ⟨⟨retention4331,(1839271295509417263/1000000000000000000),(721626522366223/500000000000000000),(110674435016275059/15625000000000000),(587816181513631838837573/500000000000000000),(99715978948011591/100000000000000000)⟩,(3906243894796107/3906250000000000),(411763290298049283/1000000000000000000),(222875472684542243/1000000000000000000),(109416280898270277/500000000000000000)⟩
theorem valid4331 : certificate4331.Valid := by decide +kernel
theorem sound4331 : certificate4331.Sound := rat_cut_bin_certificate_sound certificate4331 profilesValid4331 numericValid4331 valid4331

def certificates : List RatCutBinCertificate := [certificate4320,certificate4321,certificate4322,certificate4323,certificate4324,certificate4325,certificate4326,certificate4327,certificate4328,certificate4329,certificate4330,certificate4331]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4320,List.forall_mem_cons.mpr ⟨sound4321,List.forall_mem_cons.mpr ⟨sound4322,List.forall_mem_cons.mpr ⟨sound4323,List.forall_mem_cons.mpr ⟨sound4324,List.forall_mem_cons.mpr ⟨sound4325,List.forall_mem_cons.mpr ⟨sound4326,List.forall_mem_cons.mpr ⟨sound4327,List.forall_mem_cons.mpr ⟨sound4328,List.forall_mem_cons.mpr ⟨sound4329,List.forall_mem_cons.mpr ⟨sound4330,List.forall_mem_cons.mpr ⟨sound4331,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch360
