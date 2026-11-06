import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch234
import Cycle12.MergedCutProfiles.Batch235

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch120

def retention1440 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(1/2),(2916590884329612967/500000000000000000),(11/10),(579885854681596607850188559039915429991/583318176865922593400000000000000000000),false,MergedCutProfiles.Batch234.profile9383,(fun _ => MergedCutProfiles.Batch234.profile9383)⟩
theorem profilesValid1440 : retention1440.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9383
theorem numericValid1440 : retention1440.NumericValid := by decide +kernel
def certificate1440 : RatCutBinCertificate := ⟨⟨retention1440,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(963602225036876247/1000000000000000000)⟩,(990148156725830789/1000000000000000000),(55371886588544207/125000000000000000),(196335748895054449/1000000000000000000),(74855221689824107/500000000000000000)⟩
theorem valid1440 : certificate1440.Valid := by decide +kernel
theorem sound1440 : certificate1440.Sound := rat_cut_bin_certificate_sound certificate1440 profilesValid1440 numericValid1440 valid1440

def retention1441 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(1/2),64,1,(15963135838381215498156476997853162519/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch234.profile9383,(fun _ => MergedCutProfiles.Batch234.profile9383)⟩
theorem profilesValid1441 : retention1441.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9383
theorem numericValid1441 : retention1441.NumericValid := by decide +kernel
def certificate1441 : RatCutBinCertificate := ⟨⟨retention1441,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(193992049219385361/200000000000000000)⟩,(990148156725830789/1000000000000000000),(101324694847992409/250000000000000000),(4573245660892039/20000000000000000),(108154354833648301/500000000000000000)⟩
theorem valid1441 : certificate1441.Valid := by decide +kernel
theorem sound1441 : certificate1441.Sound := rat_cut_bin_certificate_sound certificate1441 profilesValid1441 numericValid1441 valid1441

def retention1442 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(2763058751942193919/5888079509208700464),(1765746277517712801/500000000000000000),(6/5),(372375993690594887840557184982194280311/353149255503542560200000000000000000000),false,MergedCutProfiles.Batch234.profile9384,(fun _ => MergedCutProfiles.Batch234.profile9384)⟩
theorem profilesValid1442 : retention1442.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9384
theorem numericValid1442 : retention1442.NumericValid := by decide +kernel
def certificate1442 : RatCutBinCertificate := ⟨⟨retention1442,(1329926824285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(31762294947048127/31250000000000000)⟩,(247183940275378823/250000000000000000),(12081886211611641/31250000000000000),(245967646230558659/1000000000000000000),(85731119273092791/500000000000000000)⟩
theorem valid1442 : certificate1442.Valid := by decide +kernel
theorem sound1442 : certificate1442.Sound := rat_cut_bin_certificate_sound certificate1442 profilesValid1442 numericValid1442 valid1442

def retention1443 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(5808005034616017409/11776159018417400928),(2763058751942193919/500000000000000000),(11/10),(138922008900161525278202131741161080821/138152937597109695950000000000000000000),false,MergedCutProfiles.Batch234.profile9385,(fun _ => MergedCutProfiles.Batch234.profile9385)⟩
theorem profilesValid1443 : retention1443.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9385
theorem numericValid1443 : retention1443.NumericValid := by decide +kernel
def certificate1443 : RatCutBinCertificate := ⟨⟨retention1443,(1329926824285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(485344979452870429/500000000000000000)⟩,(247183940275378823/250000000000000000),(404823797923841917/1000000000000000000),(229091515145075977/1000000000000000000),(43596827210582099/250000000000000000)⟩
theorem valid1443 : certificate1443.Valid := by decide +kernel
theorem sound1443 : certificate1443.Sound := rat_cut_bin_certificate_sound certificate1443 profilesValid1443 numericValid1443 valid1443

def retention1444 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(40736701978904011/81778882072343062),(5808005034616017409/1000000000000000000),(21/20),(9138127110009630230941007847656607290279/9292808055385627854400000000000000000000),false,MergedCutProfiles.Batch234.profile9386,(fun _ => MergedCutProfiles.Batch234.profile9386)⟩
theorem profilesValid1444 : retention1444.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9386
theorem numericValid1444 : retention1444.NumericValid := by decide +kernel
def certificate1444 : RatCutBinCertificate := ⟨⟨retention1444,(1329926824285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(237515811303650059/250000000000000000)⟩,(247183940275378823/250000000000000000),(10340322019351423/25000000000000000),(55309629675612893/250000000000000000),(172199592338506197/1000000000000000000)⟩
theorem valid1444 : certificate1444.Valid := by decide +kernel
theorem sound1444 : certificate1444.Sound := rat_cut_bin_certificate_sound certificate1444 profilesValid1444 numericValid1444 valid1444

def retention1445 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(1/2),(366630317810136099/62500000000000000),(21/20),(140384083176152339504287682514463019/143214967894584413671875000000000000),false,MergedCutProfiles.Batch234.profile9383,(fun _ => MergedCutProfiles.Batch234.profile9383)⟩
theorem profilesValid1445 : retention1445.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9383
theorem numericValid1445 : retention1445.NumericValid := by decide +kernel
def certificate1445 : RatCutBinCertificate := ⟨⟨retention1445,(1329926824285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(946941849821962623/1000000000000000000)⟩,(247183940275378823/250000000000000000),(82995253794019419/200000000000000000),(2750464587090303/12500000000000000),(170993707423581919/1000000000000000000)⟩
theorem valid1445 : certificate1445.Valid := by decide +kernel
theorem sound1445 : certificate1445.Sound := rat_cut_bin_certificate_sound certificate1445 profilesValid1445 numericValid1445 valid1445

def retention1446 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(266499314423326043/2343874737817172533),(894975505182909117/1000000000000000000),(51/20),(595105827681413079039/320000000000000000000),true,MergedCutProfiles.Batch234.profile9387,![MergedCutProfiles.Batch234.profile9387,MergedCutProfiles.Batch234.profile9388,MergedCutProfiles.Batch234.profile9389,MergedCutProfiles.Batch234.profile9390,MergedCutProfiles.Batch234.profile9391,MergedCutProfiles.Batch234.profile9392,MergedCutProfiles.Batch234.profile9393,MergedCutProfiles.Batch234.profile9394,MergedCutProfiles.Batch234.profile9395,MergedCutProfiles.Batch234.profile9396,MergedCutProfiles.Batch234.profile9397,MergedCutProfiles.Batch234.profile9398,MergedCutProfiles.Batch234.profile9399,MergedCutProfiles.Batch235.profile9400,MergedCutProfiles.Batch235.profile9401,MergedCutProfiles.Batch235.profile9402]⟩
theorem profilesValid1446 : retention1446.ProfilesValid := by
  change ∀ j : Fin 16, (retention1446.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch234.valid9387
  · exact MergedCutProfiles.Batch234.valid9388
  · exact MergedCutProfiles.Batch234.valid9389
  · exact MergedCutProfiles.Batch234.valid9390
  · exact MergedCutProfiles.Batch234.valid9391
  · exact MergedCutProfiles.Batch234.valid9392
  · exact MergedCutProfiles.Batch234.valid9393
  · exact MergedCutProfiles.Batch234.valid9394
  · exact MergedCutProfiles.Batch234.valid9395
  · exact MergedCutProfiles.Batch234.valid9396
  · exact MergedCutProfiles.Batch234.valid9397
  · exact MergedCutProfiles.Batch234.valid9398
  · exact MergedCutProfiles.Batch234.valid9399
  · exact MergedCutProfiles.Batch235.valid9400
  · exact MergedCutProfiles.Batch235.valid9401
  · exact MergedCutProfiles.Batch235.valid9402
theorem numericValid1446 : retention1446.NumericValid := by decide +kernel
def certificate1446 : RatCutBinCertificate := ⟨⟨retention1446,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(894443444633576733/500000000000000000)⟩,(247538605046464387/250000000000000000),(174418885105618977/500000000000000000),(283778316342049783/1000000000000000000),(150453965589180487/1000000000000000000)⟩
theorem valid1446 : certificate1446.Valid := by decide +kernel
theorem sound1446 : certificate1446.Sound := rat_cut_bin_certificate_sound certificate1446 profilesValid1446 numericValid1446 valid1446

def retention1447 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(3013136113378347986/11719373689085862665),(266499314423326043/200000000000000000),(9/5),(382332913100449616247/256000000000000000000),true,MergedCutProfiles.Batch235.profile9403,![MergedCutProfiles.Batch235.profile9403,MergedCutProfiles.Batch235.profile9404,MergedCutProfiles.Batch235.profile9405,MergedCutProfiles.Batch235.profile9406,MergedCutProfiles.Batch235.profile9407,MergedCutProfiles.Batch235.profile9408,MergedCutProfiles.Batch235.profile9409,MergedCutProfiles.Batch235.profile9410,MergedCutProfiles.Batch235.profile9411,MergedCutProfiles.Batch235.profile9412,MergedCutProfiles.Batch235.profile9413,MergedCutProfiles.Batch235.profile9414,MergedCutProfiles.Batch235.profile9415,MergedCutProfiles.Batch235.profile9416,MergedCutProfiles.Batch235.profile9417,MergedCutProfiles.Batch235.profile9418]⟩
theorem profilesValid1447 : retention1447.ProfilesValid := by
  change ∀ j : Fin 16, (retention1447.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch235.valid9403
  · exact MergedCutProfiles.Batch235.valid9404
  · exact MergedCutProfiles.Batch235.valid9405
  · exact MergedCutProfiles.Batch235.valid9406
  · exact MergedCutProfiles.Batch235.valid9407
  · exact MergedCutProfiles.Batch235.valid9408
  · exact MergedCutProfiles.Batch235.valid9409
  · exact MergedCutProfiles.Batch235.valid9410
  · exact MergedCutProfiles.Batch235.valid9411
  · exact MergedCutProfiles.Batch235.valid9412
  · exact MergedCutProfiles.Batch235.valid9413
  · exact MergedCutProfiles.Batch235.valid9414
  · exact MergedCutProfiles.Batch235.valid9415
  · exact MergedCutProfiles.Batch235.valid9416
  · exact MergedCutProfiles.Batch235.valid9417
  · exact MergedCutProfiles.Batch235.valid9418
theorem numericValid1447 : retention1447.NumericValid := by decide +kernel
def certificate1447 : RatCutBinCertificate := ⟨⟨retention1447,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(1443499264031539461/1000000000000000000)⟩,(247538605046464387/250000000000000000),(379068002153763277/1000000000000000000),(253218489122037463/1000000000000000000),(75194816543340019/500000000000000000)⟩
theorem valid1447 : certificate1447.Valid := by decide +kernel
theorem sound1447 : certificate1447.Sound := rat_cut_bin_certificate_sound certificate1447 profilesValid1447 numericValid1447 valid1447

def retention1448 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(5105656127037515068/11719373689085862665),(1506568056689173993/500000000000000000),(23/20),(704545210273060734881/640000000000000000000),true,MergedCutProfiles.Batch235.profile9419,![MergedCutProfiles.Batch235.profile9419,MergedCutProfiles.Batch235.profile9420,MergedCutProfiles.Batch235.profile9421,MergedCutProfiles.Batch235.profile9422,MergedCutProfiles.Batch235.profile9423,MergedCutProfiles.Batch235.profile9424,MergedCutProfiles.Batch235.profile9425,MergedCutProfiles.Batch235.profile9426,MergedCutProfiles.Batch235.profile9427,MergedCutProfiles.Batch235.profile9428,MergedCutProfiles.Batch235.profile9429,MergedCutProfiles.Batch235.profile9430,MergedCutProfiles.Batch235.profile9431,MergedCutProfiles.Batch235.profile9432,MergedCutProfiles.Batch235.profile9433,MergedCutProfiles.Batch235.profile9434]⟩
theorem profilesValid1448 : retention1448.ProfilesValid := by
  change ∀ j : Fin 16, (retention1448.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch235.valid9419
  · exact MergedCutProfiles.Batch235.valid9420
  · exact MergedCutProfiles.Batch235.valid9421
  · exact MergedCutProfiles.Batch235.valid9422
  · exact MergedCutProfiles.Batch235.valid9423
  · exact MergedCutProfiles.Batch235.valid9424
  · exact MergedCutProfiles.Batch235.valid9425
  · exact MergedCutProfiles.Batch235.valid9426
  · exact MergedCutProfiles.Batch235.valid9427
  · exact MergedCutProfiles.Batch235.valid9428
  · exact MergedCutProfiles.Batch235.valid9429
  · exact MergedCutProfiles.Batch235.valid9430
  · exact MergedCutProfiles.Batch235.valid9431
  · exact MergedCutProfiles.Batch235.valid9432
  · exact MergedCutProfiles.Batch235.valid9433
  · exact MergedCutProfiles.Batch235.valid9434
theorem numericValid1448 : retention1448.NumericValid := by decide +kernel
def certificate1448 : RatCutBinCertificate := ⟨⟨retention1448,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(1068918844420078781/1000000000000000000)⟩,(247538605046464387/250000000000000000),(26867427582294549/62500000000000000),(103597304127643527/500000000000000000),(150142451270027973/1000000000000000000)⟩
theorem valid1448 : certificate1448.Valid := by decide +kernel
theorem sound1448 : certificate1448.Sound := rat_cut_bin_certificate_sound certificate1448 profilesValid1448 numericValid1448 valid1448

def retention1449 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(5696218929893587868/11719373689085862665),(1276414031759378767/250000000000000000),(11/10),(518951158072439185774349765847017475199/510565612703751506800000000000000000000),false,MergedCutProfiles.Batch235.profile9435,(fun _ => MergedCutProfiles.Batch235.profile9435)⟩
theorem profilesValid1449 : retention1449.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9435
theorem numericValid1449 : retention1449.NumericValid := by decide +kernel
def certificate1449 : RatCutBinCertificate := ⟨⟨retention1449,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(98588280817042661/100000000000000000)⟩,(247538605046464387/250000000000000000),(437186676891780847/1000000000000000000),(100543415852045999/500000000000000000),(38435926112249591/250000000000000000)⟩
theorem valid1449 : certificate1449.Valid := by decide +kernel
theorem sound1449 : certificate1449.Sound := rat_cut_bin_certificate_sound certificate1449 profilesValid1449 numericValid1449 valid1449

def retention1450 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(1162142586076889797/2343874737817172533),(1424054732473396967/250000000000000000),(11/10),(35654115093087442378074761768740710349/35601368311834924175000000000000000000),false,MergedCutProfiles.Batch235.profile9436,(fun _ => MergedCutProfiles.Batch235.profile9436)⟩
theorem profilesValid1450 : retention1450.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9436
theorem numericValid1450 : retention1450.NumericValid := by decide +kernel
def certificate1450 : RatCutBinCertificate := ⟨⟨retention1450,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(485470472239845623/500000000000000000)⟩,(247538605046464387/250000000000000000),(87906780738254961/200000000000000000),(99575534217012683/500000000000000000),(76214367075923323/500000000000000000)⟩
theorem valid1450 : certificate1450.Valid := by decide +kernel
theorem sound1450 : certificate1450.Sound := rat_cut_bin_certificate_sound certificate1450 profilesValid1450 numericValid1450 valid1450

def retention1451 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(1/2),(1162142586076889797/200000000000000000),(11/10),(92414258790948140676833473711291890199/92971406886151183760000000000000000000),false,MergedCutProfiles.Batch235.profile9437,(fun _ => MergedCutProfiles.Batch235.profile9437)⟩
theorem profilesValid1451 : retention1451.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9437
theorem numericValid1451 : retention1451.NumericValid := by decide +kernel
def certificate1451 : RatCutBinCertificate := ⟨⟨retention1451,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(481733382832742563/500000000000000000)⟩,(247538605046464387/250000000000000000),(442191597689419029/1000000000000000000),(49243596887982857/250000000000000000),(150109406628292599/1000000000000000000)⟩
theorem valid1451 : certificate1451.Valid := by decide +kernel
theorem sound1451 : certificate1451.Sound := rat_cut_bin_certificate_sound certificate1451 profilesValid1451 numericValid1451 valid1451

def certificates : List RatCutBinCertificate := [certificate1440,certificate1441,certificate1442,certificate1443,certificate1444,certificate1445,certificate1446,certificate1447,certificate1448,certificate1449,certificate1450,certificate1451]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1440,List.forall_mem_cons.mpr ⟨sound1441,List.forall_mem_cons.mpr ⟨sound1442,List.forall_mem_cons.mpr ⟨sound1443,List.forall_mem_cons.mpr ⟨sound1444,List.forall_mem_cons.mpr ⟨sound1445,List.forall_mem_cons.mpr ⟨sound1446,List.forall_mem_cons.mpr ⟨sound1447,List.forall_mem_cons.mpr ⟨sound1448,List.forall_mem_cons.mpr ⟨sound1449,List.forall_mem_cons.mpr ⟨sound1450,List.forall_mem_cons.mpr ⟨sound1451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch120
