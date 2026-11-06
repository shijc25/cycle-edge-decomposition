import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch006
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch309
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch562
import Cycle12.MergedCutProfiles.Batch563

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch306

def retention3672 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(645180659981642543/33049605678459506493131),(28628253842838461/50000000000000000),4,(1263613880383309457150096319455776191/572565076856769220000000000000000000),true,MergedCutProfiles.Batch562.profile22487,![MergedCutProfiles.Batch562.profile22487,MergedCutProfiles.Batch562.profile22488,MergedCutProfiles.Batch562.profile22488,MergedCutProfiles.Batch562.profile22489,MergedCutProfiles.Batch562.profile22490,MergedCutProfiles.Batch562.profile22490,MergedCutProfiles.Batch562.profile22490,MergedCutProfiles.Batch562.profile22491,MergedCutProfiles.Batch562.profile22491,MergedCutProfiles.Batch562.profile22492,MergedCutProfiles.Batch562.profile22492,MergedCutProfiles.Batch562.profile22492,MergedCutProfiles.Batch562.profile22493,MergedCutProfiles.Batch562.profile22493,MergedCutProfiles.Batch562.profile22493,MergedCutProfiles.Batch562.profile22494]⟩
theorem profilesValid3672 : retention3672.ProfilesValid := by
  change ∀ j : Fin 16, (retention3672.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22487
  · exact MergedCutProfiles.Batch562.valid22488
  · exact MergedCutProfiles.Batch562.valid22488
  · exact MergedCutProfiles.Batch562.valid22489
  · exact MergedCutProfiles.Batch562.valid22490
  · exact MergedCutProfiles.Batch562.valid22490
  · exact MergedCutProfiles.Batch562.valid22490
  · exact MergedCutProfiles.Batch562.valid22491
  · exact MergedCutProfiles.Batch562.valid22491
  · exact MergedCutProfiles.Batch562.valid22492
  · exact MergedCutProfiles.Batch562.valid22492
  · exact MergedCutProfiles.Batch562.valid22492
  · exact MergedCutProfiles.Batch562.valid22493
  · exact MergedCutProfiles.Batch562.valid22493
  · exact MergedCutProfiles.Batch562.valid22493
  · exact MergedCutProfiles.Batch562.valid22494
theorem numericValid3672 : retention3672.NumericValid := by decide +kernel
def certificate3672 : RatCutBinCertificate := ⟨⟨retention3672,(224137433318385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(1102741099743633777/500000000000000000)⟩,(499996205877231567/500000000000000000),(600256434291788633/1000000000000000000),(93373686353352957/1000000000000000000),(41493618792744523/1000000000000000000)⟩
theorem valid3672 : certificate3672.Valid := by decide +kernel
theorem sound3672 : certificate3672.Sound := rat_cut_bin_certificate_sound certificate3672 profilesValid3672 numericValid3672 valid3672

def retention3673 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(1319940661000000000/33049605678459506493131),(645180659981642543/1000000000000000000),4,(6013901024901185903104710240608350359/2580722639926570172000000000000000000),true,MergedCutProfiles.Batch562.profile22488,![MergedCutProfiles.Batch562.profile22488,MergedCutProfiles.Batch562.profile22489,MergedCutProfiles.Batch562.profile22490,MergedCutProfiles.Batch562.profile22491,MergedCutProfiles.Batch562.profile22492,MergedCutProfiles.Batch562.profile22492,MergedCutProfiles.Batch562.profile22493,MergedCutProfiles.Batch562.profile22494,MergedCutProfiles.Batch562.profile22494,MergedCutProfiles.Batch562.profile22495,MergedCutProfiles.Batch562.profile22495,MergedCutProfiles.Batch562.profile22496,MergedCutProfiles.Batch562.profile22496,MergedCutProfiles.Batch562.profile22497,MergedCutProfiles.Batch562.profile22497,MergedCutProfiles.Batch562.profile22497]⟩
theorem profilesValid3673 : retention3673.ProfilesValid := by
  change ∀ j : Fin 16, (retention3673.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22488
  · exact MergedCutProfiles.Batch562.valid22489
  · exact MergedCutProfiles.Batch562.valid22490
  · exact MergedCutProfiles.Batch562.valid22491
  · exact MergedCutProfiles.Batch562.valid22492
  · exact MergedCutProfiles.Batch562.valid22492
  · exact MergedCutProfiles.Batch562.valid22493
  · exact MergedCutProfiles.Batch562.valid22494
  · exact MergedCutProfiles.Batch562.valid22494
  · exact MergedCutProfiles.Batch562.valid22495
  · exact MergedCutProfiles.Batch562.valid22495
  · exact MergedCutProfiles.Batch562.valid22496
  · exact MergedCutProfiles.Batch562.valid22496
  · exact MergedCutProfiles.Batch562.valid22497
  · exact MergedCutProfiles.Batch562.valid22497
  · exact MergedCutProfiles.Batch562.valid22497
theorem numericValid3673 : retention3673.NumericValid := by decide +kernel
def certificate3673 : RatCutBinCertificate := ⟨⟨retention3673,(224137433318385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(232886393165162791/100000000000000000)⟩,(499996205877231567/500000000000000000),(524120298498050587/1000000000000000000),(137280124619836053/1000000000000000000),(32606822676205341/500000000000000000)⟩
theorem valid3673 : certificate3673.Valid := by decide +kernel
theorem sound3673 : certificate3673.Sound := rat_cut_bin_certificate_sound certificate3673 profilesValid3673 numericValid3673 valid3673

def retention3674 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(16536713169122914573/33049605678459506493131),(1319940661/1000000000),(49/20),(776304024392103975450243432621144391/329985165250000000000000000000000000),true,MergedCutProfiles.Batch562.profile22496,![MergedCutProfiles.Batch562.profile22496,MergedCutProfiles.Batch562.profile22498,MergedCutProfiles.Batch562.profile22499,MergedCutProfiles.Batch562.profile22500,MergedCutProfiles.Batch562.profile22501,MergedCutProfiles.Batch562.profile22502,MergedCutProfiles.Batch562.profile22503,MergedCutProfiles.Batch562.profile22504,MergedCutProfiles.Batch562.profile22505,MergedCutProfiles.Batch562.profile22506,MergedCutProfiles.Batch562.profile22507,MergedCutProfiles.Batch562.profile22508,MergedCutProfiles.Batch562.profile22509,MergedCutProfiles.Batch562.profile22510,MergedCutProfiles.Batch562.profile22511,MergedCutProfiles.Batch562.profile22512]⟩
theorem profilesValid3674 : retention3674.ProfilesValid := by
  change ∀ j : Fin 16, (retention3674.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22496
  · exact MergedCutProfiles.Batch562.valid22498
  · exact MergedCutProfiles.Batch562.valid22499
  · exact MergedCutProfiles.Batch562.valid22500
  · exact MergedCutProfiles.Batch562.valid22501
  · exact MergedCutProfiles.Batch562.valid22502
  · exact MergedCutProfiles.Batch562.valid22503
  · exact MergedCutProfiles.Batch562.valid22504
  · exact MergedCutProfiles.Batch562.valid22505
  · exact MergedCutProfiles.Batch562.valid22506
  · exact MergedCutProfiles.Batch562.valid22507
  · exact MergedCutProfiles.Batch562.valid22508
  · exact MergedCutProfiles.Batch562.valid22509
  · exact MergedCutProfiles.Batch562.valid22510
  · exact MergedCutProfiles.Batch562.valid22511
  · exact MergedCutProfiles.Batch562.valid22512
theorem numericValid3674 : retention3674.NumericValid := by decide +kernel
def certificate3674 : RatCutBinCertificate := ⟨⟨retention3674,(224137433318385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(293956547793688977/125000000000000000)⟩,(499996205877231567/500000000000000000),(171034189358007769/500000000000000000),(290972338056238557/1000000000000000000),(215365842022459913/1000000000000000000)⟩
theorem valid3674 : certificate3674.Valid := by decide +kernel
theorem sound3674 : certificate3674.Sound := rat_cut_bin_certificate_sound certificate3674 profilesValid3674 numericValid3674 valid3674

def retention3675 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(64000000000000000000/33049605678459506493131),(16536713169122914573/1000000000000000000),1,(240791907520834173314961733510250059/105834964282386653267200000000000000),false,MergedCutProfiles.Batch562.profile22513,(fun _ => MergedCutProfiles.Batch562.profile22513)⟩
theorem profilesValid3675 : retention3675.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22513
theorem numericValid3675 : retention3675.NumericValid := by decide +kernel
def certificate3675 : RatCutBinCertificate := ⟨⟨retention3675,(224137433318385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(18198407012427229/8000000000000000)⟩,(499996205877231567/500000000000000000),(192655823658746073/1000000000000000000),(489713310827977033/1000000000000000000),(122410129538252107/125000000000000000)⟩
theorem valid3675 : certificate3675.Valid := by decide +kernel
theorem sound3675 : certificate3675.Sound := rat_cut_bin_certificate_sound certificate3675 profilesValid3675 numericValid3675 valid3675

def retention3676 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(1/2),64,1,(255368906635207693109493206474999528679/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch562.profile22514,(fun _ => MergedCutProfiles.Batch562.profile22514)⟩
theorem profilesValid3676 : retention3676.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22514
theorem numericValid3676 : retention3676.NumericValid := by decide +kernel
def certificate3676 : RatCutBinCertificate := ⟨⟨retention3676,(224137433318385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(498585801714042803/500000000000000000)⟩,(499996205877231567/500000000000000000),(103968560024920881/250000000000000000),(109624182527947887/500000000000000000),(107636226038073529/500000000000000000)⟩
theorem valid3676 : certificate3676.Valid := by decide +kernel
theorem sound3676 : certificate3676.Sound := rat_cut_bin_certificate_sound certificate3676 profilesValid3676 numericValid3676 valid3676

def retention3677 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(64000000000000000000/33049605678459506493131),(3784903387793341031/250000000000000000),1,(219696232825993195475914541569213167/96893526727509530393600000000000000),false,MergedCutProfiles.Batch562.profile22513,(fun _ => MergedCutProfiles.Batch562.profile22513)⟩
theorem profilesValid3677 : retention3677.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22513
theorem numericValid3677 : retention3677.NumericValid := by decide +kernel
def certificate3677 : RatCutBinCertificate := ⟨⟨retention3677,(219835122693385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(226704223852130891/100000000000000000)⟩,(124999069676323343/125000000000000000),(208599637400183/6250000000000000),(834499352983431933/1000000000000000000),(1645438770743280191/1000000000000000000)⟩
theorem valid3677 : certificate3677.Valid := by decide +kernel
theorem sound3677 : certificate3677.Sound := rat_cut_bin_certificate_sound certificate3677 profilesValid3677 numericValid3677 valid3677

def retention3678 : RatCutRetentionCertificate := ⟨(11/2000),(3/500),(1/2),64,1,(255368906635207693109493206474999528679/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch562.profile22514,(fun _ => MergedCutProfiles.Batch562.profile22514)⟩
theorem profilesValid3678 : retention3678.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22514
theorem numericValid3678 : retention3678.NumericValid := by decide +kernel
def certificate3678 : RatCutBinCertificate := ⟨⟨retention3678,(219835122693385789/125000000000000000),(721626522366223/500000000000000000),(1781374550142707921/250000000000000000),(236013496621874441686089/1000000000000000000),(997178574811963311/1000000000000000000)⟩,(124999069676323343/125000000000000000),(1517575129259051/20000000000000000),(722356184905962307/1000000000000000000),(709261755623939771/1000000000000000000)⟩
theorem valid3678 : certificate3678.Valid := by decide +kernel
theorem sound3678 : certificate3678.Sound := rat_cut_bin_certificate_sound certificate3678 profilesValid3678 numericValid3678 valid3678

def retention3679 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(40259023713787059/1510893945539055230575),(279123745349467/488281250000000),4,(1008247497700955505507395102937965379/457316344380566732800000000000000000),true,MergedCutProfiles.Batch562.profile22515,![MergedCutProfiles.Batch562.profile22515,MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch562.profile22517,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch308.profile12358,MergedCutProfiles.Batch308.profile12358,MergedCutProfiles.Batch441.profile17672,MergedCutProfiles.Batch441.profile17672,MergedCutProfiles.Batch441.profile17672,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch441.profile17673]⟩
theorem profilesValid3679 : retention3679.ProfilesValid := by
  change ∀ j : Fin 16, (retention3679.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22515
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch562.valid22517
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch308.valid12358
  · exact MergedCutProfiles.Batch308.valid12358
  · exact MergedCutProfiles.Batch441.valid17672
  · exact MergedCutProfiles.Batch441.valid17672
  · exact MergedCutProfiles.Batch441.valid17672
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch441.valid17673
theorem numericValid3679 : retention3679.NumericValid := by decide +kernel
def certificate3679 : RatCutBinCertificate := ⟨⟨retention3679,(443281683309740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(88110193623475517/40000000000000000)⟩,(249997456872258013/250000000000000000),(60892233107477341/100000000000000000),(11126610415231191/125000000000000000),(4937984829054761/125000000000000000)⟩
theorem valid3679 : certificate3679.Valid := by decide +kernel
theorem sound3679 : certificate3679.Sound := rat_cut_bin_certificate_sound certificate3679 profilesValid3679 numericValid3679 valid3679

def retention3680 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3295489430000000/60435757821562209223),(40259023713787059/62500000000000000),4,(9312957786296032209/4000000000000000000),true,MergedCutProfiles.Batch562.profile22516,![MergedCutProfiles.Batch562.profile22516,MergedCutProfiles.Batch441.profile17670,MergedCutProfiles.Batch562.profile22518,MergedCutProfiles.Batch441.profile17671,MergedCutProfiles.Batch308.profile12358,MergedCutProfiles.Batch441.profile17672,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch441.profile17673,MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch441.profile17674,MergedCutProfiles.Batch441.profile17675,MergedCutProfiles.Batch441.profile17675,MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch005.profile239]⟩
theorem profilesValid3680 : retention3680.ProfilesValid := by
  change ∀ j : Fin 16, (retention3680.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch562.valid22516
  · exact MergedCutProfiles.Batch441.valid17670
  · exact MergedCutProfiles.Batch562.valid22518
  · exact MergedCutProfiles.Batch441.valid17671
  · exact MergedCutProfiles.Batch308.valid12358
  · exact MergedCutProfiles.Batch441.valid17672
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch441.valid17673
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch441.valid17674
  · exact MergedCutProfiles.Batch441.valid17675
  · exact MergedCutProfiles.Batch441.valid17675
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch005.valid239
theorem numericValid3680 : retention3680.NumericValid := by decide +kernel
def certificate3680 : RatCutBinCertificate := ⟨⟨retention3680,(443281683309740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(290786197340643757/125000000000000000)⟩,(249997456872258013/250000000000000000),(531640235892556863/1000000000000000000),(26495137017313437/200000000000000000),(6285577998027121/100000000000000000)⟩
theorem valid3680 : certificate3680.Valid := by decide +kernel
theorem sound3680 : certificate3680.Sound := rat_cut_bin_certificate_sound certificate3680 profilesValid3680 numericValid3680 valid3680

def retention3681 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(3949715356605586393/4834860625724976737840),(329548943/250000000),(49/20),(494487811196333486331506996001837071/210911323520000000000000000000000000),true,MergedCutProfiles.Batch308.profile12359,![MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch309.profile12367,MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch309.profile12366,MergedCutProfiles.Batch006.profile247,MergedCutProfiles.Batch562.profile22519,MergedCutProfiles.Batch006.profile256,MergedCutProfiles.Batch006.profile252,MergedCutProfiles.Batch563.profile22520,MergedCutProfiles.Batch309.profile12368,MergedCutProfiles.Batch006.profile259,MergedCutProfiles.Batch563.profile22521,MergedCutProfiles.Batch563.profile22522,MergedCutProfiles.Batch309.profile12369,MergedCutProfiles.Batch006.profile262]⟩
theorem profilesValid3681 : retention3681.ProfilesValid := by
  change ∀ j : Fin 16, (retention3681.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch309.valid12367
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch309.valid12366
  · exact MergedCutProfiles.Batch006.valid247
  · exact MergedCutProfiles.Batch562.valid22519
  · exact MergedCutProfiles.Batch006.valid256
  · exact MergedCutProfiles.Batch006.valid252
  · exact MergedCutProfiles.Batch563.valid22520
  · exact MergedCutProfiles.Batch309.valid12368
  · exact MergedCutProfiles.Batch006.valid259
  · exact MergedCutProfiles.Batch563.valid22521
  · exact MergedCutProfiles.Batch563.valid22522
  · exact MergedCutProfiles.Batch309.valid12369
  · exact MergedCutProfiles.Batch006.valid262
theorem numericValid3681 : retention3681.NumericValid := by decide +kernel
def certificate3681 : RatCutBinCertificate := ⟨⟨retention3681,(443281683309740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(2343335164787237703/1000000000000000000)⟩,(249997456872258013/250000000000000000),(17393701595257633/50000000000000000),(2847944422381127/10000000000000000),(13134609140134391/62500000000000000)⟩
theorem valid3681 : certificate3681.Valid := by decide +kernel
theorem sound3681 : certificate3681.Sound := rat_cut_bin_certificate_sound certificate3681 profilesValid3681 numericValid3681 valid3681

def retention3682 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(160000000000000000/60435757821562209223),(3949715356605586393/200000000000000000),1,(25704417554033768476149159669807552093/11284901018873103980000000000000000000),false,MergedCutProfiles.Batch563.profile22523,(fun _ => MergedCutProfiles.Batch563.profile22523)⟩
theorem profilesValid3682 : retention3682.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22523
theorem numericValid3682 : retention3682.NumericValid := by decide +kernel
def certificate3682 : RatCutBinCertificate := ⟨⟨retention3682,(443281683309740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(569320822899926681/250000000000000000)⟩,(249997456872258013/250000000000000000),(48217162636447317/250000000000000000),(122341196543553/250000000000000),(999190210406648361/1000000000000000000)⟩
theorem valid3682 : certificate3682.Valid := by decide +kernel
theorem sound3682 : certificate3682.Sound := rat_cut_bin_certificate_sound certificate3682 profilesValid3682 numericValid3682 valid3682

def retention3683 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid3683 : retention3683.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid3683 : retention3683.NumericValid := by decide +kernel
def certificate3683 : RatCutBinCertificate := ⟨⟨retention3683,(443281683309740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(498523572280314169/500000000000000000)⟩,(249997456872258013/250000000000000000),(105467368841198231/250000000000000000),(53507864859991893/250000000000000000),(52530944132886321/250000000000000000)⟩
theorem valid3683 : certificate3683.Valid := by decide +kernel
theorem sound3683 : certificate3683.Sound := rat_cut_bin_certificate_sound certificate3683 profilesValid3683 numericValid3683 valid3683

def certificates : List RatCutBinCertificate := [certificate3672,certificate3673,certificate3674,certificate3675,certificate3676,certificate3677,certificate3678,certificate3679,certificate3680,certificate3681,certificate3682,certificate3683]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3672,List.forall_mem_cons.mpr ⟨sound3673,List.forall_mem_cons.mpr ⟨sound3674,List.forall_mem_cons.mpr ⟨sound3675,List.forall_mem_cons.mpr ⟨sound3676,List.forall_mem_cons.mpr ⟨sound3677,List.forall_mem_cons.mpr ⟨sound3678,List.forall_mem_cons.mpr ⟨sound3679,List.forall_mem_cons.mpr ⟨sound3680,List.forall_mem_cons.mpr ⟨sound3681,List.forall_mem_cons.mpr ⟨sound3682,List.forall_mem_cons.mpr ⟨sound3683,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch306
