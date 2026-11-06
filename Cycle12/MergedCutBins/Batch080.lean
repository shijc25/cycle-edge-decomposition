import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch161
import Cycle12.MergedCutProfiles.Batch162

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch080

def retention960 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(922687343839345284/18028241671172037989),(1331384815050631/1562500000000000),(57/20),(32771555903121750049/16000000000000000000),true,MergedCutProfiles.Batch161.profile6451,![MergedCutProfiles.Batch161.profile6451,MergedCutProfiles.Batch161.profile6452,MergedCutProfiles.Batch161.profile6453,MergedCutProfiles.Batch161.profile6454,MergedCutProfiles.Batch161.profile6455,MergedCutProfiles.Batch161.profile6456,MergedCutProfiles.Batch161.profile6457,MergedCutProfiles.Batch161.profile6458,MergedCutProfiles.Batch161.profile6459,MergedCutProfiles.Batch161.profile6460,MergedCutProfiles.Batch161.profile6461,MergedCutProfiles.Batch161.profile6447,MergedCutProfiles.Batch161.profile6462,MergedCutProfiles.Batch161.profile6463,MergedCutProfiles.Batch161.profile6464,MergedCutProfiles.Batch161.profile6465]⟩
theorem profilesValid960 : retention960.ProfilesValid := by
  change ∀ j : Fin 16, (retention960.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch161.valid6451
  · exact MergedCutProfiles.Batch161.valid6452
  · exact MergedCutProfiles.Batch161.valid6453
  · exact MergedCutProfiles.Batch161.valid6454
  · exact MergedCutProfiles.Batch161.valid6455
  · exact MergedCutProfiles.Batch161.valid6456
  · exact MergedCutProfiles.Batch161.valid6457
  · exact MergedCutProfiles.Batch161.valid6458
  · exact MergedCutProfiles.Batch161.valid6459
  · exact MergedCutProfiles.Batch161.valid6460
  · exact MergedCutProfiles.Batch161.valid6461
  · exact MergedCutProfiles.Batch161.valid6447
  · exact MergedCutProfiles.Batch161.valid6462
  · exact MergedCutProfiles.Batch161.valid6463
  · exact MergedCutProfiles.Batch161.valid6464
  · exact MergedCutProfiles.Batch161.valid6465
theorem numericValid960 : retention960.NumericValid := by decide +kernel
def certificate960 : RatCutBinCertificate := ⟨⟨retention960,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(497515893578939341/250000000000000000)⟩,(12402305880691687/12500000000000000),(370797339950929319/1000000000000000000),(65332890431676827/250000000000000000),(140411531989608973/1000000000000000000)⟩
theorem valid960 : certificate960.Valid := by decide +kernel
theorem sound960 : certificate960.Sound := rat_cut_bin_certificate_sound certificate960 profilesValid960 numericValid960 valid960

def retention961 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(1472852076520157455/18028241671172037989),(230671835959836321/250000000000000000),(53/20),(156241318547785003681/80000000000000000000),true,MergedCutProfiles.Batch161.profile6466,![MergedCutProfiles.Batch161.profile6466,MergedCutProfiles.Batch161.profile6467,MergedCutProfiles.Batch161.profile6468,MergedCutProfiles.Batch161.profile6469,MergedCutProfiles.Batch161.profile6458,MergedCutProfiles.Batch161.profile6470,MergedCutProfiles.Batch161.profile6471,MergedCutProfiles.Batch161.profile6472,MergedCutProfiles.Batch161.profile6473,MergedCutProfiles.Batch161.profile6474,MergedCutProfiles.Batch161.profile6475,MergedCutProfiles.Batch161.profile6476,MergedCutProfiles.Batch161.profile6477,MergedCutProfiles.Batch161.profile6478,MergedCutProfiles.Batch161.profile6479,MergedCutProfiles.Batch162.profile6480]⟩
theorem profilesValid961 : retention961.ProfilesValid := by
  change ∀ j : Fin 16, (retention961.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch161.valid6466
  · exact MergedCutProfiles.Batch161.valid6467
  · exact MergedCutProfiles.Batch161.valid6468
  · exact MergedCutProfiles.Batch161.valid6469
  · exact MergedCutProfiles.Batch161.valid6458
  · exact MergedCutProfiles.Batch161.valid6470
  · exact MergedCutProfiles.Batch161.valid6471
  · exact MergedCutProfiles.Batch161.valid6472
  · exact MergedCutProfiles.Batch161.valid6473
  · exact MergedCutProfiles.Batch161.valid6474
  · exact MergedCutProfiles.Batch161.valid6475
  · exact MergedCutProfiles.Batch161.valid6476
  · exact MergedCutProfiles.Batch161.valid6477
  · exact MergedCutProfiles.Batch161.valid6478
  · exact MergedCutProfiles.Batch161.valid6479
  · exact MergedCutProfiles.Batch162.valid6480
theorem numericValid961 : retention961.NumericValid := by decide +kernel
def certificate961 : RatCutBinCertificate := ⟨⟨retention961,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(474734800247410651/250000000000000000)⟩,(12402305880691687/12500000000000000),(376493273186401469/1000000000000000000),(255724645045472429/1000000000000000000),(70200932753997777/500000000000000000)⟩
theorem valid961 : certificate961.Valid := by decide +kernel
theorem sound961 : certificate961.Sound := rat_cut_bin_certificate_sound certificate961 profilesValid961 numericValid961 valid961

def retention962 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(4313874435699600891/18028241671172037989),(294570415304031491/200000000000000000),(37/20),(394637597285433975323/256000000000000000000),true,MergedCutProfiles.Batch162.profile6481,![MergedCutProfiles.Batch162.profile6481,MergedCutProfiles.Batch162.profile6482,MergedCutProfiles.Batch161.profile6463,MergedCutProfiles.Batch162.profile6483,MergedCutProfiles.Batch162.profile6484,MergedCutProfiles.Batch162.profile6485,MergedCutProfiles.Batch162.profile6486,MergedCutProfiles.Batch162.profile6487,MergedCutProfiles.Batch162.profile6488,MergedCutProfiles.Batch162.profile6489,MergedCutProfiles.Batch162.profile6490,MergedCutProfiles.Batch162.profile6491,MergedCutProfiles.Batch162.profile6492,MergedCutProfiles.Batch162.profile6493,MergedCutProfiles.Batch162.profile6494,MergedCutProfiles.Batch162.profile6495]⟩
theorem profilesValid962 : retention962.ProfilesValid := by
  change ∀ j : Fin 16, (retention962.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch162.valid6481
  · exact MergedCutProfiles.Batch162.valid6482
  · exact MergedCutProfiles.Batch161.valid6463
  · exact MergedCutProfiles.Batch162.valid6483
  · exact MergedCutProfiles.Batch162.valid6484
  · exact MergedCutProfiles.Batch162.valid6485
  · exact MergedCutProfiles.Batch162.valid6486
  · exact MergedCutProfiles.Batch162.valid6487
  · exact MergedCutProfiles.Batch162.valid6488
  · exact MergedCutProfiles.Batch162.valid6489
  · exact MergedCutProfiles.Batch162.valid6490
  · exact MergedCutProfiles.Batch162.valid6491
  · exact MergedCutProfiles.Batch162.valid6492
  · exact MergedCutProfiles.Batch162.valid6493
  · exact MergedCutProfiles.Batch162.valid6494
  · exact MergedCutProfiles.Batch162.valid6495
theorem numericValid962 : retention962.NumericValid := by decide +kernel
def certificate962 : RatCutBinCertificate := ⟨⟨retention962,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(1503801870773442837/1000000000000000000)⟩,(12402305880691687/12500000000000000),(203275714351628077/500000000000000000),(28441619207857221/125000000000000000),(28231464910271299/200000000000000000)⟩
theorem valid962 : certificate962.Valid := by decide +kernel
theorem sound962 : certificate962.Sound := rat_cut_bin_certificate_sound certificate962 profilesValid962 numericValid962 valid962

def retention963 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(7994525174407138276/18028241671172037989),(4313874435699600891/1000000000000000000),(21/20),(1377398461794486578019/1280000000000000000000),true,MergedCutProfiles.Batch162.profile6496,![MergedCutProfiles.Batch162.profile6496,MergedCutProfiles.Batch162.profile6497,MergedCutProfiles.Batch162.profile6498,MergedCutProfiles.Batch162.profile6499,MergedCutProfiles.Batch162.profile6500,MergedCutProfiles.Batch162.profile6501,MergedCutProfiles.Batch162.profile6502,MergedCutProfiles.Batch162.profile6503,MergedCutProfiles.Batch162.profile6504,MergedCutProfiles.Batch162.profile6505,MergedCutProfiles.Batch162.profile6506,MergedCutProfiles.Batch162.profile6507,MergedCutProfiles.Batch162.profile6508,MergedCutProfiles.Batch162.profile6509,MergedCutProfiles.Batch162.profile6510,MergedCutProfiles.Batch162.profile6511]⟩
theorem profilesValid963 : retention963.ProfilesValid := by
  change ∀ j : Fin 16, (retention963.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch162.valid6496
  · exact MergedCutProfiles.Batch162.valid6497
  · exact MergedCutProfiles.Batch162.valid6498
  · exact MergedCutProfiles.Batch162.valid6499
  · exact MergedCutProfiles.Batch162.valid6500
  · exact MergedCutProfiles.Batch162.valid6501
  · exact MergedCutProfiles.Batch162.valid6502
  · exact MergedCutProfiles.Batch162.valid6503
  · exact MergedCutProfiles.Batch162.valid6504
  · exact MergedCutProfiles.Batch162.valid6505
  · exact MergedCutProfiles.Batch162.valid6506
  · exact MergedCutProfiles.Batch162.valid6507
  · exact MergedCutProfiles.Batch162.valid6508
  · exact MergedCutProfiles.Batch162.valid6509
  · exact MergedCutProfiles.Batch162.valid6510
  · exact MergedCutProfiles.Batch162.valid6511
theorem numericValid963 : retention963.NumericValid := by decide +kernel
def certificate963 : RatCutBinCertificate := ⟨⟨retention963,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(26366694721460501/25000000000000000)⟩,(12402305880691687/12500000000000000),(14725737758285879/31250000000000000),(174216987226218287/1000000000000000000),(70995686336469043/500000000000000000)⟩
theorem valid963 : certificate963.Valid := by decide +kernel
theorem sound963 : certificate963.Sound := rat_cut_bin_certificate_sound certificate963 profilesValid963 numericValid963 valid963

def retention964 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(8830929389806993510/18028241671172037989),(1998631293601784569/250000000000000000),(21/20),(807313157656573856785806830511050779319/799452517440713827600000000000000000000),false,MergedCutProfiles.Batch162.profile6512,(fun _ => MergedCutProfiles.Batch162.profile6512)⟩
theorem profilesValid964 : retention964.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6512
theorem numericValid964 : retention964.NumericValid := by decide +kernel
def certificate964 : RatCutBinCertificate := ⟨⟨retention964,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(988408897263677967/1000000000000000000)⟩,(12402305880691687/12500000000000000),(118797520363511739/250000000000000000),(171249187767148367/1000000000000000000),(71872472471269933/500000000000000000)⟩
theorem valid964 : certificate964.Valid := by decide +kernel
theorem sound964 : certificate964.Sound := rat_cut_bin_certificate_sound certificate964 profilesValid964 numericValid964 valid964

def retention965 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(8919238683705063446/18028241671172037989),(883092938980699351/100000000000000000),(21/20),(141703468693118420534645728080976903239/141294870236911896160000000000000000000),false,MergedCutProfiles.Batch162.profile6513,(fun _ => MergedCutProfiles.Batch162.profile6513)⟩
theorem profilesValid965 : retention965.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6513
theorem numericValid965 : retention965.NumericValid := by decide +kernel
def certificate965 : RatCutBinCertificate := ⟨⟨retention965,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(981468307035098233/1000000000000000000)⟩,(12402305880691687/12500000000000000),(237731235551020527/500000000000000000),(42761649509134507/250000000000000000),(144040714716698099/1000000000000000000)⟩
theorem valid965 : certificate965.Valid := by decide +kernel
theorem sound965 : certificate965.Sound := rat_cut_bin_certificate_sound certificate965 profilesValid965 numericValid965 valid965

def retention966 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(9008431070542114081/18028241671172037989),(4459619341852531723/500000000000000000),(21/20),(3544571657710749162595696654409253465911/3567695473482025378400000000000000000000),false,MergedCutProfiles.Batch162.profile6514,(fun _ => MergedCutProfiles.Batch162.profile6514)⟩
theorem profilesValid966 : retention966.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6514
theorem numericValid966 : retention966.NumericValid := by decide +kernel
def certificate966 : RatCutBinCertificate := ⟨⟨retention966,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(60755941363630339/62500000000000000)⟩,(12402305880691687/12500000000000000),(95950395582018849/200000000000000000),(41969199420523319/250000000000000000),(17533801773570769/125000000000000000)⟩
theorem valid966 : certificate966.Valid := by decide +kernel
theorem sound966 : certificate966.Sound := rat_cut_bin_certificate_sound certificate966 profilesValid966 numericValid966 valid966

def retention967 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(1/2),(9008431070542114081/1000000000000000000),(21/20),(14314450049899514112771936283182383973359/14413489712867382529600000000000000000000),false,MergedCutProfiles.Batch162.profile6515,(fun _ => MergedCutProfiles.Batch162.profile6515)⟩
theorem profilesValid967 : retention967.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6515
theorem numericValid967 : retention967.NumericValid := by decide +kernel
def certificate967 : RatCutBinCertificate := ⟨⟨retention967,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(194341039876284933/200000000000000000)⟩,(12402305880691687/12500000000000000),(11991305355647921/25000000000000000),(167950082733672761/1000000000000000000),(28081202603508321/200000000000000000)⟩
theorem valid967 : certificate967.Valid := by decide +kernel
theorem sound967 : certificate967.Sound := rat_cut_bin_certificate_sound certificate967 profilesValid967 numericValid967 valid967

def retention968 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(1/2),64,1,(63848953630392859927501808078909239479/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch162.profile6515,(fun _ => MergedCutProfiles.Batch162.profile6515)⟩
theorem profilesValid968 : retention968.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6515
theorem numericValid968 : retention968.NumericValid := by decide +kernel
def certificate968 : RatCutBinCertificate := ⟨⟨retention968,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(977237534962336019/1000000000000000000)⟩,(12402305880691687/12500000000000000),(225983909765625299/500000000000000000),(189104252428635117/1000000000000000000),(90292481315409581/500000000000000000)⟩
theorem valid968 : certificate968.Valid := by decide +kernel
theorem sound968 : certificate968.Sound := rat_cut_bin_certificate_sound certificate968 profilesValid968 numericValid968 valid968

def retention969 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(8134703036147165949/18028241671172037989),(917427616891112347/250000000000000000),(6/5),(100073500893723426396865103747381246279/91742761689111234700000000000000000000),false,MergedCutProfiles.Batch162.profile6516,(fun _ => MergedCutProfiles.Batch162.profile6516)⟩
theorem profilesValid969 : retention969.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6516
theorem numericValid969 : retention969.NumericValid := by decide +kernel
def certificate969 : RatCutBinCertificate := ⟨⟨retention969,(2550378879450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(212438160603108493/200000000000000000)⟩,(198172956800622417/200000000000000000),(383908564408896421/1000000000000000000),(248554061514431611/1000000000000000000),(181355305423560731/1000000000000000000)⟩
theorem valid969 : certificate969.Valid := by decide +kernel
theorem sound969 : certificate969.Sound := rat_cut_bin_certificate_sound certificate969 profilesValid969 numericValid969 valid969

def retention970 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(8896804908294911727/18028241671172037989),(8134703036147165949/1000000000000000000),(21/20),(1450866982901172568012454694501941982671/1446169428648385057600000000000000000000),false,MergedCutProfiles.Batch162.profile6517,(fun _ => MergedCutProfiles.Batch162.profile6517)⟩
theorem profilesValid970 : retention970.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6517
theorem numericValid970 : retention970.NumericValid := by decide +kernel
def certificate970 : RatCutBinCertificate := ⟨⟨retention970,(2550378879450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(978211917650619471/1000000000000000000)⟩,(198172956800622417/200000000000000000),(104216719035024823/250000000000000000),(218378662383962213/1000000000000000000),(22709401773729069/125000000000000000)⟩
theorem valid970 : certificate970.Valid := by decide +kernel
theorem sound970 : certificate970.Sound := rat_cut_bin_certificate_sound certificate970 profilesValid970 numericValid970 valid970

def retention971 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(152301236565726455/305563418155458271),(8896804908294911727/1000000000000000000),(21/20),(4725511480492534596119581819652322427917/4744962617757286254400000000000000000000),false,MergedCutProfiles.Batch162.profile6518,(fun _ => MergedCutProfiles.Batch162.profile6518)⟩
theorem profilesValid971 : retention971.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6518
theorem numericValid971 : retention971.NumericValid := by decide +kernel
def certificate971 : RatCutBinCertificate := ⟨⟨retention971,(2550378879450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(485432225130151719/500000000000000000)⟩,(198172956800622417/200000000000000000),(820354901815643/1953125000000000),(43126040503299777/200000000000000000),(22460385398636137/125000000000000000)⟩
theorem valid971 : certificate971.Valid := by decide +kernel
theorem sound971 : certificate971.Sound := rat_cut_bin_certificate_sound certificate971 profilesValid971 numericValid971 valid971

def certificates : List RatCutBinCertificate := [certificate960,certificate961,certificate962,certificate963,certificate964,certificate965,certificate966,certificate967,certificate968,certificate969,certificate970,certificate971]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound960,List.forall_mem_cons.mpr ⟨sound961,List.forall_mem_cons.mpr ⟨sound962,List.forall_mem_cons.mpr ⟨sound963,List.forall_mem_cons.mpr ⟨sound964,List.forall_mem_cons.mpr ⟨sound965,List.forall_mem_cons.mpr ⟨sound966,List.forall_mem_cons.mpr ⟨sound967,List.forall_mem_cons.mpr ⟨sound968,List.forall_mem_cons.mpr ⟨sound969,List.forall_mem_cons.mpr ⟨sound970,List.forall_mem_cons.mpr ⟨sound971,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch080
