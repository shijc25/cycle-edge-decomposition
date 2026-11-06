import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch235
import Cycle12.MergedCutProfiles.Batch236
import Cycle12.MergedCutProfiles.Batch237

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch121

def retention1452 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(1/2),64,1,(255410579061100590607878480423416511319/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch235.profile9437,(fun _ => MergedCutProfiles.Batch235.profile9437)⟩
theorem profilesValid1452 : retention1452.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9437
theorem numericValid1452 : retention1452.NumericValid := by decide +kernel
def certificate1452 : RatCutBinCertificate := ⟨⟨retention1452,(232869078000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(969937409540015551/1000000000000000000)⟩,(247538605046464387/250000000000000000),(101362785140685749/250000000000000000),(114262357464454731/500000000000000000),(13510930685925801/62500000000000000)⟩
theorem valid1452 : certificate1452.Valid := by decide +kernel
theorem sound1452 : certificate1452.Sound := rat_cut_bin_certificate_sound certificate1452 profilesValid1452 numericValid1452 valid1452

def retention1453 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(5471011068728845643/11719373689085862665),(3461659917592212391/1000000000000000000),(6/5),(45788141446335264695352634957546902493/43270748969902654887500000000000000000),false,MergedCutProfiles.Batch235.profile9438,(fun _ => MergedCutProfiles.Batch235.profile9438)⟩
theorem profilesValid1453 : retention1453.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9438
theorem numericValid1453 : retention1453.NumericValid := by decide +kernel
def certificate1453 : RatCutBinCertificate := ⟨⟨retention1453,(266388146000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(204012367375003207/200000000000000000)⟩,(988733424797865107/1000000000000000000),(196464353801193673/500000000000000000),(120012139512444161/500000000000000000),(83627162904290521/500000000000000000)⟩
theorem valid1453 : certificate1453.Valid := by decide +kernel
theorem sound1453 : certificate1453.Sound := rat_cut_bin_certificate_sound certificate1453 profilesValid1453 numericValid1453 valid1453

def retention1454 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(5807588493616782191/11719373689085862665),(5471011068728845643/1000000000000000000),(11/10),(2189966510974015172347007232833931173911/2188404427491538257200000000000000000000),false,MergedCutProfiles.Batch235.profile9439,(fun _ => MergedCutProfiles.Batch235.profile9439)⟩
theorem profilesValid1454 : retention1454.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9439
theorem numericValid1454 : retention1454.NumericValid := by decide +kernel
def certificate1454 : RatCutBinCertificate := ⟨⟨retention1454,(266388146000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(193155382025710759/200000000000000000)⟩,(988733424797865107/1000000000000000000),(415014663359952977/1000000000000000000),(1760027204669597/8000000000000000),(166514913824699599/1000000000000000000)⟩
theorem valid1454 : certificate1454.Valid := by decide +kernel
theorem sound1454 : certificate1454.Sound := rat_cut_bin_certificate_sound certificate1454 profilesValid1454 numericValid1454 valid1454

def retention1455 : RatCutRetentionCertificate := ⟨(123/2000),(493/8000),(1/2),(5807588493616782191/1000000000000000000),(21/20),(9104818745461262277202373632157073654279/9292141589786851505600000000000000000000),false,MergedCutProfiles.Batch235.profile9437,(fun _ => MergedCutProfiles.Batch235.profile9437)⟩
theorem profilesValid1455 : retention1455.ProfilesValid := by
  exact MergedCutProfiles.Batch235.valid9437
theorem numericValid1455 : retention1455.NumericValid := by decide +kernel
def certificate1455 : RatCutBinCertificate := ⟨⟨retention1455,(266388146000970357/100000000000000000),(97187835786062329/500000000000000000),(16305667638307781521/1000000000000000000),(191239946813617779739/1000000000000000000),(473245974213994973/500000000000000000)⟩,(988733424797865107/1000000000000000000),(423470669669739361/1000000000000000000),(212652602127968533/1000000000000000000),(8248624388482703/50000000000000000)⟩
theorem valid1455 : certificate1455.Valid := by decide +kernel
theorem sound1455 : certificate1455.Sound := rat_cut_bin_certificate_sound certificate1455 profilesValid1455 numericValid1455 valid1455

def retention1456 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(1095516670847313521/11662950475584323812),(174283948041443991/200000000000000000),(53/20),(490971418384443878287/256000000000000000000),true,MergedCutProfiles.Batch236.profile9440,![MergedCutProfiles.Batch236.profile9440,MergedCutProfiles.Batch236.profile9441,MergedCutProfiles.Batch236.profile9442,MergedCutProfiles.Batch236.profile9443,MergedCutProfiles.Batch236.profile9444,MergedCutProfiles.Batch236.profile9445,MergedCutProfiles.Batch236.profile9446,MergedCutProfiles.Batch236.profile9447,MergedCutProfiles.Batch236.profile9448,MergedCutProfiles.Batch236.profile9449,MergedCutProfiles.Batch236.profile9450,MergedCutProfiles.Batch236.profile9451,MergedCutProfiles.Batch236.profile9452,MergedCutProfiles.Batch236.profile9453,MergedCutProfiles.Batch236.profile9454,MergedCutProfiles.Batch236.profile9455]⟩
theorem profilesValid1456 : retention1456.ProfilesValid := by
  change ∀ j : Fin 16, (retention1456.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch236.valid9440
  · exact MergedCutProfiles.Batch236.valid9441
  · exact MergedCutProfiles.Batch236.valid9442
  · exact MergedCutProfiles.Batch236.valid9443
  · exact MergedCutProfiles.Batch236.valid9444
  · exact MergedCutProfiles.Batch236.valid9445
  · exact MergedCutProfiles.Batch236.valid9446
  · exact MergedCutProfiles.Batch236.valid9447
  · exact MergedCutProfiles.Batch236.valid9448
  · exact MergedCutProfiles.Batch236.valid9449
  · exact MergedCutProfiles.Batch236.valid9450
  · exact MergedCutProfiles.Batch236.valid9451
  · exact MergedCutProfiles.Batch236.valid9452
  · exact MergedCutProfiles.Batch236.valid9453
  · exact MergedCutProfiles.Batch236.valid9454
  · exact MergedCutProfiles.Batch236.valid9455
theorem numericValid1456 : retention1456.NumericValid := by decide +kernel
def certificate1456 : RatCutBinCertificate := ⟨⟨retention1456,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(921954758570470753/500000000000000000)⟩,(990118689933135889/1000000000000000000),(43340047026598737/125000000000000000),(286014315023329533/1000000000000000000),(37775848562749201/250000000000000000)⟩
theorem valid1456 : certificate1456.Valid := by decide +kernel
theorem sound1456 : certificate1456.Sound := rat_cut_bin_certificate_sound certificate1456 profilesValid1456 numericValid1456 valid1456

def retention1457 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(528165061684427824/2915737618896080953),(1095516670847313521/1000000000000000000),(43/20),(2148248147882165247137/1280000000000000000000),true,MergedCutProfiles.Batch236.profile9456,![MergedCutProfiles.Batch236.profile9456,MergedCutProfiles.Batch236.profile9457,MergedCutProfiles.Batch236.profile9458,MergedCutProfiles.Batch236.profile9459,MergedCutProfiles.Batch236.profile9460,MergedCutProfiles.Batch236.profile9461,MergedCutProfiles.Batch236.profile9462,MergedCutProfiles.Batch236.profile9463,MergedCutProfiles.Batch236.profile9464,MergedCutProfiles.Batch236.profile9465,MergedCutProfiles.Batch236.profile9466,MergedCutProfiles.Batch236.profile9467,MergedCutProfiles.Batch236.profile9468,MergedCutProfiles.Batch236.profile9469,MergedCutProfiles.Batch236.profile9470,MergedCutProfiles.Batch236.profile9471]⟩
theorem profilesValid1457 : retention1457.ProfilesValid := by
  change ∀ j : Fin 16, (retention1457.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch236.valid9456
  · exact MergedCutProfiles.Batch236.valid9457
  · exact MergedCutProfiles.Batch236.valid9458
  · exact MergedCutProfiles.Batch236.valid9459
  · exact MergedCutProfiles.Batch236.valid9460
  · exact MergedCutProfiles.Batch236.valid9461
  · exact MergedCutProfiles.Batch236.valid9462
  · exact MergedCutProfiles.Batch236.valid9463
  · exact MergedCutProfiles.Batch236.valid9464
  · exact MergedCutProfiles.Batch236.valid9465
  · exact MergedCutProfiles.Batch236.valid9466
  · exact MergedCutProfiles.Batch236.valid9467
  · exact MergedCutProfiles.Batch236.valid9468
  · exact MergedCutProfiles.Batch236.valid9469
  · exact MergedCutProfiles.Batch236.valid9470
  · exact MergedCutProfiles.Batch236.valid9471
theorem numericValid1457 : retention1457.NumericValid := by decide +kernel
def certificate1457 : RatCutBinCertificate := ⟨⟨retention1457,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(1618324174703759083/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(72616938543505577/200000000000000000),(269063249871183639/1000000000000000000),(7582692169737923/50000000000000000)⟩
theorem valid1457 : certificate1457.Valid := by decide +kernel
theorem sound1457 : certificate1457.Sound := rat_cut_bin_certificate_sound certificate1457 profilesValid1457 numericValid1457 valid1457

def retention1458 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(1081206334449515429/2915737618896080953),(33010316355276739/15625000000000000),(27/20),(99274140904182897123/80000000000000000000),true,MergedCutProfiles.Batch236.profile9472,![MergedCutProfiles.Batch236.profile9472,MergedCutProfiles.Batch236.profile9473,MergedCutProfiles.Batch236.profile9474,MergedCutProfiles.Batch236.profile9475,MergedCutProfiles.Batch236.profile9476,MergedCutProfiles.Batch236.profile9477,MergedCutProfiles.Batch236.profile9478,MergedCutProfiles.Batch236.profile9479,MergedCutProfiles.Batch237.profile9480,MergedCutProfiles.Batch237.profile9481,MergedCutProfiles.Batch237.profile9482,MergedCutProfiles.Batch237.profile9483,MergedCutProfiles.Batch237.profile9484,MergedCutProfiles.Batch237.profile9485,MergedCutProfiles.Batch237.profile9486,MergedCutProfiles.Batch237.profile9487]⟩
theorem profilesValid1458 : retention1458.ProfilesValid := by
  change ∀ j : Fin 16, (retention1458.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch236.valid9472
  · exact MergedCutProfiles.Batch236.valid9473
  · exact MergedCutProfiles.Batch236.valid9474
  · exact MergedCutProfiles.Batch236.valid9475
  · exact MergedCutProfiles.Batch236.valid9476
  · exact MergedCutProfiles.Batch236.valid9477
  · exact MergedCutProfiles.Batch236.valid9478
  · exact MergedCutProfiles.Batch236.valid9479
  · exact MergedCutProfiles.Batch237.valid9480
  · exact MergedCutProfiles.Batch237.valid9481
  · exact MergedCutProfiles.Batch237.valid9482
  · exact MergedCutProfiles.Batch237.valid9483
  · exact MergedCutProfiles.Batch237.valid9484
  · exact MergedCutProfiles.Batch237.valid9485
  · exact MergedCutProfiles.Batch237.valid9486
  · exact MergedCutProfiles.Batch237.valid9487
theorem numericValid1458 : retention1458.NumericValid := by decide +kernel
def certificate1458 : RatCutBinCertificate := ⟨⟨retention1458,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(1203258527178862231/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(16313614914696103/40000000000000000),(113187464907346171/500000000000000000),(30390387944935629/200000000000000000)⟩
theorem valid1458 : certificate1458.Valid := by decide +kernel
theorem sound1458 : certificate1458.Sound := rat_cut_bin_certificate_sound certificate1458 profilesValid1458 numericValid1458 valid1458

def retention1459 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(80755596768396179/171513977582122409),(1081206334449515429/250000000000000000),1,(64641086044933875809/64000000000000000000),true,MergedCutProfiles.Batch237.profile9488,![MergedCutProfiles.Batch237.profile9488,MergedCutProfiles.Batch236.profile9449,MergedCutProfiles.Batch237.profile9489,MergedCutProfiles.Batch237.profile9490,MergedCutProfiles.Batch236.profile9468,MergedCutProfiles.Batch237.profile9491,MergedCutProfiles.Batch237.profile9492,MergedCutProfiles.Batch237.profile9493,MergedCutProfiles.Batch237.profile9494,MergedCutProfiles.Batch237.profile9495,MergedCutProfiles.Batch237.profile9496,MergedCutProfiles.Batch237.profile9497,MergedCutProfiles.Batch237.profile9498,MergedCutProfiles.Batch237.profile9499,MergedCutProfiles.Batch237.profile9500,MergedCutProfiles.Batch237.profile9501]⟩
theorem profilesValid1459 : retention1459.ProfilesValid := by
  change ∀ j : Fin 16, (retention1459.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch237.valid9488
  · exact MergedCutProfiles.Batch236.valid9449
  · exact MergedCutProfiles.Batch237.valid9489
  · exact MergedCutProfiles.Batch237.valid9490
  · exact MergedCutProfiles.Batch236.valid9468
  · exact MergedCutProfiles.Batch237.valid9491
  · exact MergedCutProfiles.Batch237.valid9492
  · exact MergedCutProfiles.Batch237.valid9493
  · exact MergedCutProfiles.Batch237.valid9494
  · exact MergedCutProfiles.Batch237.valid9495
  · exact MergedCutProfiles.Batch237.valid9496
  · exact MergedCutProfiles.Batch237.valid9497
  · exact MergedCutProfiles.Batch237.valid9498
  · exact MergedCutProfiles.Batch237.valid9499
  · exact MergedCutProfiles.Batch237.valid9500
  · exact MergedCutProfiles.Batch237.valid9501
theorem numericValid1459 : retention1459.NumericValid := by decide +kernel
def certificate1459 : RatCutBinCertificate := ⟨⟨retention1459,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(982117983596162041/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(445344071771048209/1000000000000000000),(194413176405733007/1000000000000000000),(153880640606778687/1000000000000000000)⟩
theorem valid1459 : certificate1459.Valid := by decide +kernel
theorem sound1459 : certificate1459.Sound := rat_cut_bin_certificate_sound certificate1459 profilesValid1459 numericValid1459 valid1459

def retention1460 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(5771496178767707703/11662950475584323812),(1372845145062735043/250000000000000000),(11/10),(550333261787205726787429052733602402119/549138058025094017200000000000000000000),false,MergedCutProfiles.Batch237.profile9502,(fun _ => MergedCutProfiles.Batch237.profile9502)⟩
theorem profilesValid1460 : retention1460.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9502
theorem numericValid1460 : retention1460.NumericValid := by decide +kernel
def certificate1460 : RatCutBinCertificate := ⟨⟨retention1460,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(971489687383271811/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(54884195585863141/125000000000000000),(99764860508358383/500000000000000000),(7604151671201073/50000000000000000)⟩
theorem valid1460 : certificate1460.Valid := by decide +kernel
theorem sound1460 : certificate1460.Sound := rat_cut_bin_certificate_sound certificate1460 profilesValid1460 numericValid1460 valid1460

def retention1461 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(5829211140555384781/11662950475584323812),(5771496178767707703/1000000000000000000),(11/10),(2295179537391705870685750741884602644151/2308598471507083081200000000000000000000),false,MergedCutProfiles.Batch237.profile9503,(fun _ => MergedCutProfiles.Batch237.profile9503)⟩
theorem profilesValid1461 : retention1461.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9503
theorem numericValid1461 : retention1461.NumericValid := by decide +kernel
def certificate1461 : RatCutBinCertificate := ⟨⟨retention1461,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(481750421036873329/500000000000000000)⟩,(990118689933135889/1000000000000000000),(110173142614762109/250000000000000000),(198200137699957911/1000000000000000000),(150917960355605817/1000000000000000000)⟩
theorem valid1461 : certificate1461.Valid := by decide +kernel
theorem sound1461 : certificate1461.Sound := rat_cut_bin_certificate_sound certificate1461 profilesValid1461 numericValid1461 valid1461

def retention1462 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(1/2),(5829211140555384781/1000000000000000000),(11/10),(2317924720544839151418254901247483885039/2331684456222153912400000000000000000000),false,MergedCutProfiles.Batch237.profile9504,(fun _ => MergedCutProfiles.Batch237.profile9504)⟩
theorem profilesValid1462 : retention1462.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9504
theorem numericValid1462 : retention1462.NumericValid := by decide +kernel
def certificate1462 : RatCutBinCertificate := ⟨⟨retention1462,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(963412280353391767/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(440340662157739077/1000000000000000000),(19848863033893327/100000000000000000),(37827046969685271/250000000000000000)⟩
theorem valid1462 : certificate1462.Valid := by decide +kernel
theorem sound1462 : certificate1462.Sound := rat_cut_bin_certificate_sound certificate1462 profilesValid1462 numericValid1462 valid1462

def retention1463 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(1/2),64,1,(408657244960798517062391201646044439/409600000000000000000000000000000000),false,MergedCutProfiles.Batch237.profile9504,(fun _ => MergedCutProfiles.Batch237.profile9504)⟩
theorem profilesValid1463 : retention1463.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9504
theorem numericValid1463 : retention1463.NumericValid := by decide +kernel
def certificate1463 : RatCutBinCertificate := ⟨⟨retention1463,(2333949347042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(969805523261504537/1000000000000000000)⟩,(990118689933135889/1000000000000000000),(201002624178093127/500000000000000000),(231650069828098371/1000000000000000000),(54773504626048359/250000000000000000)⟩
theorem valid1463 : certificate1463.Valid := by decide +kernel
theorem sound1463 : certificate1463.Sound := rat_cut_bin_certificate_sound certificate1463 profilesValid1463 numericValid1463 valid1463

def certificates : List RatCutBinCertificate := [certificate1452,certificate1453,certificate1454,certificate1455,certificate1456,certificate1457,certificate1458,certificate1459,certificate1460,certificate1461,certificate1462,certificate1463]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1452,List.forall_mem_cons.mpr ⟨sound1453,List.forall_mem_cons.mpr ⟨sound1454,List.forall_mem_cons.mpr ⟨sound1455,List.forall_mem_cons.mpr ⟨sound1456,List.forall_mem_cons.mpr ⟨sound1457,List.forall_mem_cons.mpr ⟨sound1458,List.forall_mem_cons.mpr ⟨sound1459,List.forall_mem_cons.mpr ⟨sound1460,List.forall_mem_cons.mpr ⟨sound1461,List.forall_mem_cons.mpr ⟨sound1462,List.forall_mem_cons.mpr ⟨sound1463,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch121
