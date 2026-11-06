import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch360
import Cycle12.MergedCutProfiles.Batch361

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch194

def retention2328 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(26801960862699818157/53651691046898568089),(26536594913564176393/1000000000000000000),1,(105397497615568115521576425691516616571/106146379654256705572000000000000000000),false,MergedCutProfiles.Batch359.profile14368,(fun _ => MergedCutProfiles.Batch359.profile14368)⟩
theorem profilesValid2328 : retention2328.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14368
theorem numericValid2328 : retention2328.NumericValid := by decide +kernel
def certificate2328 : RatCutBinCertificate := ⟨⟨retention2328,(1181585897745703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(195137454719837907/200000000000000000)⟩,(4982807043823873/5000000000000000),(244788509645552133/1000000000000000000),(410608836195105483/1000000000000000000),(15402611179787409/40000000000000000)⟩
theorem valid2328 : certificate2328.Valid := by decide +kernel
theorem sound2328 : certificate2328.Sound := rat_cut_bin_certificate_sound certificate2328 profilesValid2328 numericValid2328 valid2328

def retention2329 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),(26801960862699818157/1000000000000000000),1,(8863975371459811955952990994835341683/8933986954233272719000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid2329 : retention2329.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid2329 : retention2329.NumericValid := by decide +kernel
def certificate2329 : RatCutBinCertificate := ⟨⟨retention2329,(1181585897745703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(974905912477995169/1000000000000000000)⟩,(4982807043823873/5000000000000000),(61246175278957629/250000000000000000),(205166642329268379/500000000000000000),(192322404184378161/500000000000000000)⟩
theorem valid2329 : certificate2329.Valid := by decide +kernel
theorem sound2329 : certificate2329.Sound := rat_cut_bin_certificate_sound certificate2329 profilesValid2329 numericValid2329 valid2329

def retention2330 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(99541498056396314/6369984013696635067),(394223754678797283/500000000000000000),(67/20),(1424303061987744557867/640000000000000000000),true,MergedCutProfiles.Batch359.profile14369,![MergedCutProfiles.Batch359.profile14369,MergedCutProfiles.Batch359.profile14370,MergedCutProfiles.Batch359.profile14371,MergedCutProfiles.Batch359.profile14372,MergedCutProfiles.Batch359.profile14373,MergedCutProfiles.Batch359.profile14374,MergedCutProfiles.Batch359.profile14375,MergedCutProfiles.Batch359.profile14376,MergedCutProfiles.Batch359.profile14377,MergedCutProfiles.Batch359.profile14378,MergedCutProfiles.Batch359.profile14379,MergedCutProfiles.Batch359.profile14380,MergedCutProfiles.Batch359.profile14381,MergedCutProfiles.Batch359.profile14382,MergedCutProfiles.Batch359.profile14383,MergedCutProfiles.Batch359.profile14384]⟩
theorem profilesValid2330 : retention2330.ProfilesValid := by
  change ∀ j : Fin 16, (retention2330.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch359.valid14369
  · exact MergedCutProfiles.Batch359.valid14370
  · exact MergedCutProfiles.Batch359.valid14371
  · exact MergedCutProfiles.Batch359.valid14372
  · exact MergedCutProfiles.Batch359.valid14373
  · exact MergedCutProfiles.Batch359.valid14374
  · exact MergedCutProfiles.Batch359.valid14375
  · exact MergedCutProfiles.Batch359.valid14376
  · exact MergedCutProfiles.Batch359.valid14377
  · exact MergedCutProfiles.Batch359.valid14378
  · exact MergedCutProfiles.Batch359.valid14379
  · exact MergedCutProfiles.Batch359.valid14380
  · exact MergedCutProfiles.Batch359.valid14381
  · exact MergedCutProfiles.Batch359.valid14382
  · exact MergedCutProfiles.Batch359.valid14383
  · exact MergedCutProfiles.Batch359.valid14384
theorem numericValid2330 : retention2330.NumericValid := by decide +kernel
def certificate2330 : RatCutBinCertificate := ⟨⟨retention2330,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(543172029220100877/250000000000000000)⟩,(24921832515678473/25000000000000000),(199207506861033617/500000000000000000),(23493774966326249/100000000000000000),(30471123010759787/250000000000000000)⟩
theorem valid2330 : certificate2330.Valid := by decide +kernel
theorem sound2330 : certificate2330.Sound := rat_cut_bin_certificate_sound certificate2330 profilesValid2330 numericValid2330 valid2330

def retention2331 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(933761879237153289/50959872109573080536),(49770749028198157/62500000000000000),(33/10),(176643924816628916389/80000000000000000000),true,MergedCutProfiles.Batch359.profile14385,![MergedCutProfiles.Batch359.profile14385,MergedCutProfiles.Batch359.profile14386,MergedCutProfiles.Batch359.profile14387,MergedCutProfiles.Batch359.profile14388,MergedCutProfiles.Batch359.profile14389,MergedCutProfiles.Batch359.profile14375,MergedCutProfiles.Batch359.profile14390,MergedCutProfiles.Batch359.profile14391,MergedCutProfiles.Batch359.profile14392,MergedCutProfiles.Batch359.profile14393,MergedCutProfiles.Batch359.profile14394,MergedCutProfiles.Batch359.profile14395,MergedCutProfiles.Batch359.profile14396,MergedCutProfiles.Batch359.profile14397,MergedCutProfiles.Batch359.profile14398,MergedCutProfiles.Batch359.profile14399]⟩
theorem profilesValid2331 : retention2331.ProfilesValid := by
  change ∀ j : Fin 16, (retention2331.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch359.valid14385
  · exact MergedCutProfiles.Batch359.valid14386
  · exact MergedCutProfiles.Batch359.valid14387
  · exact MergedCutProfiles.Batch359.valid14388
  · exact MergedCutProfiles.Batch359.valid14389
  · exact MergedCutProfiles.Batch359.valid14375
  · exact MergedCutProfiles.Batch359.valid14390
  · exact MergedCutProfiles.Batch359.valid14391
  · exact MergedCutProfiles.Batch359.valid14392
  · exact MergedCutProfiles.Batch359.valid14393
  · exact MergedCutProfiles.Batch359.valid14394
  · exact MergedCutProfiles.Batch359.valid14395
  · exact MergedCutProfiles.Batch359.valid14396
  · exact MergedCutProfiles.Batch359.valid14397
  · exact MergedCutProfiles.Batch359.valid14398
  · exact MergedCutProfiles.Batch359.valid14399
theorem numericValid2331 : retention2331.NumericValid := by decide +kernel
def certificate2331 : RatCutBinCertificate := ⟨⟨retention2331,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(2156051469963370659/1000000000000000000)⟩,(24921832515678473/25000000000000000),(399527673880831961/1000000000000000000),(116957705368700727/500000000000000000),(121948415668114771/1000000000000000000)⟩
theorem valid2331 : certificate2331.Valid := by decide +kernel
theorem sound2331 : certificate2331.Sound := rat_cut_bin_certificate_sound certificate2331 profilesValid2331 numericValid2331 valid2331

def retention2332 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(129128073125000000/6369984013696635067),(933761879237153289/1000000000000000000),(29/10),(2807256169067988624349/1280000000000000000000),true,MergedCutProfiles.Batch360.profile14400,![MergedCutProfiles.Batch360.profile14400,MergedCutProfiles.Batch360.profile14401,MergedCutProfiles.Batch360.profile14402,MergedCutProfiles.Batch360.profile14403,MergedCutProfiles.Batch360.profile14404,MergedCutProfiles.Batch360.profile14405,MergedCutProfiles.Batch359.profile14377,MergedCutProfiles.Batch360.profile14406,MergedCutProfiles.Batch360.profile14407,MergedCutProfiles.Batch359.profile14381,MergedCutProfiles.Batch360.profile14408,MergedCutProfiles.Batch360.profile14409,MergedCutProfiles.Batch360.profile14410,MergedCutProfiles.Batch360.profile14411,MergedCutProfiles.Batch360.profile14412,MergedCutProfiles.Batch360.profile14413]⟩
theorem profilesValid2332 : retention2332.ProfilesValid := by
  change ∀ j : Fin 16, (retention2332.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch360.valid14400
  · exact MergedCutProfiles.Batch360.valid14401
  · exact MergedCutProfiles.Batch360.valid14402
  · exact MergedCutProfiles.Batch360.valid14403
  · exact MergedCutProfiles.Batch360.valid14404
  · exact MergedCutProfiles.Batch360.valid14405
  · exact MergedCutProfiles.Batch359.valid14377
  · exact MergedCutProfiles.Batch360.valid14406
  · exact MergedCutProfiles.Batch360.valid14407
  · exact MergedCutProfiles.Batch359.valid14381
  · exact MergedCutProfiles.Batch360.valid14408
  · exact MergedCutProfiles.Batch360.valid14409
  · exact MergedCutProfiles.Batch360.valid14410
  · exact MergedCutProfiles.Batch360.valid14411
  · exact MergedCutProfiles.Batch360.valid14412
  · exact MergedCutProfiles.Batch360.valid14413
theorem numericValid2332 : retention2332.NumericValid := by decide +kernel
def certificate2332 : RatCutBinCertificate := ⟨⟨retention2332,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(2147474105889227307/1000000000000000000)⟩,(24921832515678473/25000000000000000),(372137374437454323/1000000000000000000),(130002327477045529/500000000000000000),(75319853461410261/500000000000000000)⟩
theorem valid2332 : certificate2332.Valid := by decide +kernel
theorem sound2332 : certificate2332.Sound := rat_cut_bin_certificate_sound certificate2332 profilesValid2332 numericValid2332 valid2332

def retention2333 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(145283527539663612/6369984013696635067),(206604917/200000000),(53/20),(17374853488888579491/8000000000000000000),true,MergedCutProfiles.Batch360.profile14414,![MergedCutProfiles.Batch360.profile14414,MergedCutProfiles.Batch360.profile14415,MergedCutProfiles.Batch360.profile14416,MergedCutProfiles.Batch359.profile14389,MergedCutProfiles.Batch360.profile14417,MergedCutProfiles.Batch360.profile14418,MergedCutProfiles.Batch360.profile14419,MergedCutProfiles.Batch360.profile14407,MergedCutProfiles.Batch360.profile14420,MergedCutProfiles.Batch360.profile14421,MergedCutProfiles.Batch359.profile14384,MergedCutProfiles.Batch360.profile14422,MergedCutProfiles.Batch360.profile14423,MergedCutProfiles.Batch360.profile14424,MergedCutProfiles.Batch360.profile14425,MergedCutProfiles.Batch360.profile14426]⟩
theorem profilesValid2333 : retention2333.ProfilesValid := by
  change ∀ j : Fin 16, (retention2333.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch360.valid14414
  · exact MergedCutProfiles.Batch360.valid14415
  · exact MergedCutProfiles.Batch360.valid14416
  · exact MergedCutProfiles.Batch359.valid14389
  · exact MergedCutProfiles.Batch360.valid14417
  · exact MergedCutProfiles.Batch360.valid14418
  · exact MergedCutProfiles.Batch360.valid14419
  · exact MergedCutProfiles.Batch360.valid14407
  · exact MergedCutProfiles.Batch360.valid14420
  · exact MergedCutProfiles.Batch360.valid14421
  · exact MergedCutProfiles.Batch359.valid14384
  · exact MergedCutProfiles.Batch360.valid14422
  · exact MergedCutProfiles.Batch360.valid14423
  · exact MergedCutProfiles.Batch360.valid14424
  · exact MergedCutProfiles.Batch360.valid14425
  · exact MergedCutProfiles.Batch360.valid14426
theorem numericValid2333 : retention2333.NumericValid := by decide +kernel
def certificate2333 : RatCutBinCertificate := ⟨⟨retention2333,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(2130101139375103531/1000000000000000000)⟩,(24921832515678473/25000000000000000),(358901827579178291/1000000000000000000),(273324667050798903/1000000000000000000),(169216906366342839/1000000000000000000)⟩
theorem valid2333 : certificate2333.Valid := by decide +kernel
theorem sound2333 : certificate2333.Sound := rat_cut_bin_certificate_sound certificate2333 profilesValid2333 numericValid2333 valid2333

def retention2334 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(3051262840481958505/50959872109573080536),(36320881884915903/31250000000000000),(12/5),(20271910479111028573/10000000000000000000),true,MergedCutProfiles.Batch360.profile14427,![MergedCutProfiles.Batch360.profile14427,MergedCutProfiles.Batch360.profile14428,MergedCutProfiles.Batch360.profile14429,MergedCutProfiles.Batch360.profile14430,MergedCutProfiles.Batch360.profile14431,MergedCutProfiles.Batch360.profile14432,MergedCutProfiles.Batch360.profile14433,MergedCutProfiles.Batch360.profile14434,MergedCutProfiles.Batch360.profile14435,MergedCutProfiles.Batch360.profile14436,MergedCutProfiles.Batch360.profile14437,MergedCutProfiles.Batch360.profile14438,MergedCutProfiles.Batch360.profile14439,MergedCutProfiles.Batch361.profile14440,MergedCutProfiles.Batch361.profile14441,MergedCutProfiles.Batch361.profile14442]⟩
theorem profilesValid2334 : retention2334.ProfilesValid := by
  change ∀ j : Fin 16, (retention2334.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch360.valid14427
  · exact MergedCutProfiles.Batch360.valid14428
  · exact MergedCutProfiles.Batch360.valid14429
  · exact MergedCutProfiles.Batch360.valid14430
  · exact MergedCutProfiles.Batch360.valid14431
  · exact MergedCutProfiles.Batch360.valid14432
  · exact MergedCutProfiles.Batch360.valid14433
  · exact MergedCutProfiles.Batch360.valid14434
  · exact MergedCutProfiles.Batch360.valid14435
  · exact MergedCutProfiles.Batch360.valid14436
  · exact MergedCutProfiles.Batch360.valid14437
  · exact MergedCutProfiles.Batch360.valid14438
  · exact MergedCutProfiles.Batch360.valid14439
  · exact MergedCutProfiles.Batch361.valid14440
  · exact MergedCutProfiles.Batch361.valid14441
  · exact MergedCutProfiles.Batch361.valid14442
theorem numericValid2334 : retention2334.NumericValid := by decide +kernel
def certificate2334 : RatCutBinCertificate := ⟨⟨retention2334,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(62167960676745583/31250000000000000)⟩,(24921832515678473/25000000000000000),(36606625750103573/100000000000000000),(266055107847464657/1000000000000000000),(1355185456531647/8000000000000000)⟩
theorem valid2334 : certificate2334.Valid := by decide +kernel
theorem sound2334 : certificate2334.Sound := rat_cut_bin_certificate_sound certificate2334 profilesValid2334 numericValid2334 valid2334

def retention2335 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(2154312350539773545/6369984013696635067),(610252568096391701/200000000000000000),(13/10),(4956250914271565761184078384684105787/3755400419054718160000000000000000000),false,MergedCutProfiles.Batch361.profile14443,(fun _ => MergedCutProfiles.Batch361.profile14443)⟩
theorem profilesValid2335 : retention2335.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14443
theorem numericValid2335 : retention2335.NumericValid := by decide +kernel
def certificate2335 : RatCutBinCertificate := ⟨⟨retention2335,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(162410348580009783/125000000000000000)⟩,(24921832515678473/25000000000000000),(422423512314727963/1000000000000000000),(26694208515345033/125000000000000000),(10617906866981241/62500000000000000)⟩
theorem valid2335 : certificate2335.Valid := by decide +kernel
theorem sound2335 : certificate2335.Sound := rat_cut_bin_certificate_sound certificate2335 profilesValid2335 numericValid2335 valid2335

def retention2336 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(6226292179741382963/12739968027393270134),(430862470107954709/25000000000000000),1,(69553639524427759484171655037947398031/68937995217272753440000000000000000000),false,MergedCutProfiles.Batch361.profile14444,(fun _ => MergedCutProfiles.Batch361.profile14444)⟩
theorem profilesValid2336 : retention2336.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14444
theorem numericValid2336 : retention2336.NumericValid := by decide +kernel
def certificate2336 : RatCutBinCertificate := ⟨⟨retention2336,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(496587155428252621/500000000000000000)⟩,(24921832515678473/25000000000000000),(46115816379607603/100000000000000000),(181898673007587273/1000000000000000000),(21282844898299361/125000000000000000)⟩
theorem valid2336 : certificate2336.Valid := by decide +kernel
theorem sound2336 : certificate2336.Sound := rat_cut_bin_certificate_sound certificate2336 profilesValid2336 numericValid2336 valid2336

def retention2337 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(25405762610216739043/50959872109573080536),(6226292179741382963/250000000000000000),1,(99054021448791760274312546458411568991/99620674875862127408000000000000000000),false,MergedCutProfiles.Batch361.profile14445,(fun _ => MergedCutProfiles.Batch361.profile14445)⟩
theorem profilesValid2337 : retention2337.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14445
theorem numericValid2337 : retention2337.NumericValid := by decide +kernel
def certificate2337 : RatCutBinCertificate := ⟨⟨retention2337,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(195711167082190177/200000000000000000)⟩,(24921832515678473/25000000000000000),(461896604471725103/1000000000000000000),(9066385251635529/50000000000000000),(6807417036063451/40000000000000000)⟩
theorem valid2337 : certificate2337.Valid := by decide +kernel
theorem sound2337 : certificate2337.Sound := rat_cut_bin_certificate_sound certificate2337 profilesValid2337 numericValid2337 valid2337

def retention2338 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),(25405762610216739043/1000000000000000000),1,(4030992210420334679445833248881865347/4064922017634678246880000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid2338 : retention2338.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid2338 : retention2338.NumericValid := by decide +kernel
def certificate2338 : RatCutBinCertificate := ⟨⟨retention2338,(416619606831201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(121987121473078837/125000000000000000)⟩,(24921832515678473/25000000000000000),(462882017032021523/1000000000000000000),(180567614852394179/1000000000000000000),(8457741335887513/50000000000000000)⟩
theorem valid2338 : certificate2338.Valid := by decide +kernel
theorem sound2338 : certificate2338.Sound := rat_cut_bin_certificate_sound certificate2338 profilesValid2338 numericValid2338 valid2338

def retention2339 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(22309152587930886475/50959872109573080536),(1107951475107982289/200000000000000000),(21/20),(388063918744648704829690498258607118431/354544472034554332480000000000000000000),false,MergedCutProfiles.Batch361.profile14447,(fun _ => MergedCutProfiles.Batch361.profile14447)⟩
theorem profilesValid2339 : retention2339.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14447
theorem numericValid2339 : retention2339.NumericValid := by decide +kernel
def certificate2339 : RatCutBinCertificate := ⟨⟨retention2339,(474839029431201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(107568618967581581/100000000000000000)⟩,(498218111286115099/500000000000000000),(224473525558926037/1000000000000000000),(440001828892345381/1000000000000000000),(95449493646908333/250000000000000000)⟩
theorem valid2339 : certificate2339.Valid := by decide +kernel
theorem sound2339 : certificate2339.Sound := rat_cut_bin_certificate_sound certificate2339 profilesValid2339 numericValid2339 valid2339

def certificates : List RatCutBinCertificate := [certificate2328,certificate2329,certificate2330,certificate2331,certificate2332,certificate2333,certificate2334,certificate2335,certificate2336,certificate2337,certificate2338,certificate2339]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2328,List.forall_mem_cons.mpr ⟨sound2329,List.forall_mem_cons.mpr ⟨sound2330,List.forall_mem_cons.mpr ⟨sound2331,List.forall_mem_cons.mpr ⟨sound2332,List.forall_mem_cons.mpr ⟨sound2333,List.forall_mem_cons.mpr ⟨sound2334,List.forall_mem_cons.mpr ⟨sound2335,List.forall_mem_cons.mpr ⟨sound2336,List.forall_mem_cons.mpr ⟨sound2337,List.forall_mem_cons.mpr ⟨sound2338,List.forall_mem_cons.mpr ⟨sound2339,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch194
