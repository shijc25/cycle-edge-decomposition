import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch378
import Cycle12.MergedCutProfiles.Batch379
import Cycle12.MergedCutProfiles.Batch380
import Cycle12.MergedCutProfiles.Batch381
import Cycle12.MergedCutProfiles.Batch499
import Cycle12.MergedCutProfiles.Batch612
import Cycle12.MergedCutProfiles.Batch613
import Cycle12.MergedCutProfiles.Batch614

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch339

def retention4068 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(800000000000000000/4557924207760763037),(6283691172935282869/250000000000000000),1,(168949041344228746116673030036484203279/100539058766964525904000000000000000000),false,MergedCutProfiles.Batch612.profile24495,(fun _ => MergedCutProfiles.Batch612.profile24495)⟩
theorem profilesValid4068 : retention4068.ProfilesValid := by
  exact MergedCutProfiles.Batch612.valid24495
theorem numericValid4068 : retention4068.NumericValid := by decide +kernel
def certificate4068 : RatCutBinCertificate := ⟨⟨retention4068,(1866890838493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(20786046561572883/12500000000000000)⟩,(249915909336849289/250000000000000000),(16620633158652999/500000000000000000),(834886092817603283/1000000000000000000),(1301719497870024153/1000000000000000000)⟩
theorem valid4068 : certificate4068.Valid := by decide +kernel
theorem sound4068 : certificate4068.Sound := rat_cut_bin_certificate_sound certificate4068 profilesValid4068 numericValid4068 valid4068

def retention4069 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(1/2),64,1,(63848635416822846544693585750381821951/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch378.profile15126,(fun _ => MergedCutProfiles.Batch378.profile15126)⟩
theorem profilesValid4069 : retention4069.ProfilesValid := by
  exact MergedCutProfiles.Batch378.valid15126
theorem numericValid4069 : retention4069.NumericValid := by decide +kernel
def certificate4069 : RatCutBinCertificate := ⟨⟨retention4069,(1866890838493732891/1000000000000000000),(31307344283847009/250000000000000000),(6661371946043031087/500000000000000000),(4885916049529217336309/1000000000000000000),(980086766207006913/1000000000000000000)⟩,(249915909336849289/250000000000000000),(451195650514871/8000000000000000),(96427328346643093/125000000000000000),(372200277854302473/500000000000000000)⟩
theorem valid4069 : certificate4069.Valid := by decide +kernel
theorem sound4069 : certificate4069.Sound := rat_cut_bin_certificate_sound certificate4069 profilesValid4069 numericValid4069 valid4069

def retention4070 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(134561077590136580/69744396114772780587),(163254570254392381/250000000000000000),4,(149993626610198875653/64000000000000000000),true,MergedCutProfiles.Batch612.profile24496,![MergedCutProfiles.Batch612.profile24496,MergedCutProfiles.Batch612.profile24497,MergedCutProfiles.Batch612.profile24498,MergedCutProfiles.Batch612.profile24499,MergedCutProfiles.Batch612.profile24500,MergedCutProfiles.Batch612.profile24501,MergedCutProfiles.Batch612.profile24502,MergedCutProfiles.Batch612.profile24503,MergedCutProfiles.Batch612.profile24504,MergedCutProfiles.Batch612.profile24505,MergedCutProfiles.Batch612.profile24506,MergedCutProfiles.Batch612.profile24507,MergedCutProfiles.Batch612.profile24508,MergedCutProfiles.Batch612.profile24509,MergedCutProfiles.Batch379.profile15162,MergedCutProfiles.Batch612.profile24510]⟩
theorem profilesValid4070 : retention4070.ProfilesValid := by
  change ∀ j : Fin 16, (retention4070.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch612.valid24496
  · exact MergedCutProfiles.Batch612.valid24497
  · exact MergedCutProfiles.Batch612.valid24498
  · exact MergedCutProfiles.Batch612.valid24499
  · exact MergedCutProfiles.Batch612.valid24500
  · exact MergedCutProfiles.Batch612.valid24501
  · exact MergedCutProfiles.Batch612.valid24502
  · exact MergedCutProfiles.Batch612.valid24503
  · exact MergedCutProfiles.Batch612.valid24504
  · exact MergedCutProfiles.Batch612.valid24505
  · exact MergedCutProfiles.Batch612.valid24506
  · exact MergedCutProfiles.Batch612.valid24507
  · exact MergedCutProfiles.Batch612.valid24508
  · exact MergedCutProfiles.Batch612.valid24509
  · exact MergedCutProfiles.Batch379.valid15162
  · exact MergedCutProfiles.Batch612.valid24510
theorem numericValid4070 : retention4070.NumericValid := by decide +kernel
def certificate4070 : RatCutBinCertificate := ⟨⟨retention4070,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(566961302146736173/250000000000000000)⟩,(124954859210987149/125000000000000000),(30028448774620419/50000000000000000),(93214247214209939/1000000000000000000),(43404667063227739/1000000000000000000)⟩
theorem valid4070 : certificate4070.Valid := by decide +kernel
theorem sound4070 : certificate4070.Sound := rat_cut_bin_certificate_sound certificate4070 profilesValid4070 numericValid4070 valid4070

def retention4071 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(73055539400000000/23248132038257593529),(6728053879506829/10000000000000000),4,(587463930720884779/250000000000000000),true,MergedCutProfiles.Batch612.profile24511,![MergedCutProfiles.Batch612.profile24511,MergedCutProfiles.Batch612.profile24512,MergedCutProfiles.Batch612.profile24513,MergedCutProfiles.Batch612.profile24514,MergedCutProfiles.Batch612.profile24515,MergedCutProfiles.Batch612.profile24516,MergedCutProfiles.Batch612.profile24517,MergedCutProfiles.Batch612.profile24508,MergedCutProfiles.Batch612.profile24518,MergedCutProfiles.Batch612.profile24519,MergedCutProfiles.Batch613.profile24520,MergedCutProfiles.Batch613.profile24521,MergedCutProfiles.Batch613.profile24522,MergedCutProfiles.Batch613.profile24523,MergedCutProfiles.Batch613.profile24524,MergedCutProfiles.Batch613.profile24525]⟩
theorem profilesValid4071 : retention4071.ProfilesValid := by
  change ∀ j : Fin 16, (retention4071.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch612.valid24511
  · exact MergedCutProfiles.Batch612.valid24512
  · exact MergedCutProfiles.Batch612.valid24513
  · exact MergedCutProfiles.Batch612.valid24514
  · exact MergedCutProfiles.Batch612.valid24515
  · exact MergedCutProfiles.Batch612.valid24516
  · exact MergedCutProfiles.Batch612.valid24517
  · exact MergedCutProfiles.Batch612.valid24508
  · exact MergedCutProfiles.Batch612.valid24518
  · exact MergedCutProfiles.Batch612.valid24519
  · exact MergedCutProfiles.Batch613.valid24520
  · exact MergedCutProfiles.Batch613.valid24521
  · exact MergedCutProfiles.Batch613.valid24522
  · exact MergedCutProfiles.Batch613.valid24523
  · exact MergedCutProfiles.Batch613.valid24524
  · exact MergedCutProfiles.Batch613.valid24525
theorem numericValid4071 : retention4071.NumericValid := by decide +kernel
def certificate4071 : RatCutBinCertificate := ⟨⟨retention4071,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(568512634798759191/250000000000000000)⟩,(124954859210987149/125000000000000000),(293969688398600949/500000000000000000),(49893767715706467/500000000000000000),(11704021525949809/250000000000000000)⟩
theorem valid4071 : certificate4071.Valid := by decide +kernel
theorem sound4071 : certificate4071.Sound := rat_cut_bin_certificate_sound certificate4071 profilesValid4071 numericValid4071 valid4071

def retention4072 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1246851221940166987/348721980573863902935),(1095833091/1000000000),(14/5),(7534204019449033881/3200000000000000000),true,MergedCutProfiles.Batch613.profile24526,![MergedCutProfiles.Batch613.profile24526,MergedCutProfiles.Batch613.profile24527,MergedCutProfiles.Batch613.profile24528,MergedCutProfiles.Batch613.profile24529,MergedCutProfiles.Batch613.profile24530,MergedCutProfiles.Batch612.profile24506,MergedCutProfiles.Batch612.profile24508,MergedCutProfiles.Batch612.profile24518,MergedCutProfiles.Batch613.profile24531,MergedCutProfiles.Batch379.profile15178,MergedCutProfiles.Batch613.profile24532,MergedCutProfiles.Batch613.profile24533,MergedCutProfiles.Batch613.profile24534,MergedCutProfiles.Batch613.profile24525,MergedCutProfiles.Batch613.profile24535,MergedCutProfiles.Batch613.profile24536]⟩
theorem profilesValid4072 : retention4072.ProfilesValid := by
  change ∀ j : Fin 16, (retention4072.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch613.valid24526
  · exact MergedCutProfiles.Batch613.valid24527
  · exact MergedCutProfiles.Batch613.valid24528
  · exact MergedCutProfiles.Batch613.valid24529
  · exact MergedCutProfiles.Batch613.valid24530
  · exact MergedCutProfiles.Batch612.valid24506
  · exact MergedCutProfiles.Batch612.valid24508
  · exact MergedCutProfiles.Batch612.valid24518
  · exact MergedCutProfiles.Batch613.valid24531
  · exact MergedCutProfiles.Batch379.valid15178
  · exact MergedCutProfiles.Batch613.valid24532
  · exact MergedCutProfiles.Batch613.valid24533
  · exact MergedCutProfiles.Batch613.valid24534
  · exact MergedCutProfiles.Batch613.valid24525
  · exact MergedCutProfiles.Batch613.valid24535
  · exact MergedCutProfiles.Batch613.valid24536
theorem numericValid4072 : retention4072.NumericValid := by decide +kernel
def certificate4072 : RatCutBinCertificate := ⟨⟨retention4072,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(1150687597122104703/500000000000000000)⟩,(124954859210987149/125000000000000000),(88519824377154487/200000000000000000),(49160508835469199/250000000000000000),(63711376595566377/500000000000000000)⟩
theorem valid4072 : certificate4072.Valid := by decide +kernel
theorem sound4072 : certificate4072.Sound := rat_cut_bin_certificate_sound certificate4072 profilesValid4072 numericValid4072 valid4072

def retention4073 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(9976581525225925543/348721980573863902935),(1246851221940166987/1000000000000000000),(51/20),(2797891007141346099723/1280000000000000000000),true,MergedCutProfiles.Batch612.profile24518,![MergedCutProfiles.Batch612.profile24518,MergedCutProfiles.Batch613.profile24536,MergedCutProfiles.Batch613.profile24537,MergedCutProfiles.Batch613.profile24538,MergedCutProfiles.Batch379.profile15181,MergedCutProfiles.Batch378.profile15136,MergedCutProfiles.Batch613.profile24539,MergedCutProfiles.Batch613.profile24540,MergedCutProfiles.Batch613.profile24541,MergedCutProfiles.Batch613.profile24542,MergedCutProfiles.Batch613.profile24543,MergedCutProfiles.Batch613.profile24544,MergedCutProfiles.Batch613.profile24545,MergedCutProfiles.Batch613.profile24546,MergedCutProfiles.Batch379.profile15187,MergedCutProfiles.Batch613.profile24547]⟩
theorem profilesValid4073 : retention4073.ProfilesValid := by
  change ∀ j : Fin 16, (retention4073.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch612.valid24518
  · exact MergedCutProfiles.Batch613.valid24536
  · exact MergedCutProfiles.Batch613.valid24537
  · exact MergedCutProfiles.Batch613.valid24538
  · exact MergedCutProfiles.Batch379.valid15181
  · exact MergedCutProfiles.Batch378.valid15136
  · exact MergedCutProfiles.Batch613.valid24539
  · exact MergedCutProfiles.Batch613.valid24540
  · exact MergedCutProfiles.Batch613.valid24541
  · exact MergedCutProfiles.Batch613.valid24542
  · exact MergedCutProfiles.Batch613.valid24543
  · exact MergedCutProfiles.Batch613.valid24544
  · exact MergedCutProfiles.Batch613.valid24545
  · exact MergedCutProfiles.Batch613.valid24546
  · exact MergedCutProfiles.Batch379.valid15187
  · exact MergedCutProfiles.Batch613.valid24547
theorem numericValid4073 : retention4073.NumericValid := by decide +kernel
def certificate4073 : RatCutBinCertificate := ⟨⟨retention4073,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(2137526620680301631/1000000000000000000)⟩,(124954859210987149/125000000000000000),(2239149545577477/5000000000000000),(24051164067060291/125000000000000000),(127582288215960107/1000000000000000000)⟩
theorem valid4073 : certificate4073.Valid := by decide +kernel
theorem sound4073 : certificate4073.Sound := rat_cut_bin_certificate_sound certificate4073 profilesValid4073 numericValid4073 valid4073

def retention4074 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(12800000000000000000/69744396114772780587),(9976581525225925543/1000000000000000000),(21/20),(26404936784129951174260819984524620100671/15962530440361480868800000000000000000000),false,MergedCutProfiles.Batch613.profile24548,(fun _ => MergedCutProfiles.Batch613.profile24548)⟩
theorem profilesValid4074 : retention4074.ProfilesValid := by
  exact MergedCutProfiles.Batch613.valid24548
theorem numericValid4074 : retention4074.NumericValid := by decide +kernel
def certificate4074 : RatCutBinCertificate := ⟨⟨retention4074,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(817141841244587489/500000000000000000)⟩,(124954859210987149/125000000000000000),(173710814807742261/500000000000000000),(142636177708293503/500000000000000000),(386429484831369131/1000000000000000000)⟩
theorem valid4074 : certificate4074.Valid := by decide +kernel
theorem sound4074 : certificate4074.Sound := rat_cut_bin_certificate_sound certificate4074 profilesValid4074 numericValid4074 valid4074

def retention4075 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),64,1,(63848938712576751324224913430591766799/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid4075 : retention4075.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid4075 : retention4075.NumericValid := by decide +kernel
def certificate4075 : RatCutBinCertificate := ⟨⟨retention4075,(196161234290364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(978688557267245621/1000000000000000000)⟩,(124954859210987149/125000000000000000),(532171840045930719/1000000000000000000),(132140089831588281/1000000000000000000),(25465938240560879/200000000000000000)⟩
theorem valid4075 : certificate4075.Valid := by decide +kernel
theorem sound4075 : certificate4075.Sound := rat_cut_bin_certificate_sound certificate4075 profilesValid4075 numericValid4075 valid4075

def retention4076 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(12800000000000000000/69744396114772780587),(25170479803529277087/1000000000000000000),1,(13939101470977134238204494405342892191/8390159934509759029000000000000000000),false,MergedCutProfiles.Batch613.profile24548,(fun _ => MergedCutProfiles.Batch613.profile24548)⟩
theorem profilesValid4076 : retention4076.ProfilesValid := by
  exact MergedCutProfiles.Batch613.valid24548
theorem numericValid4076 : retention4076.NumericValid := by decide +kernel
def certificate4076 : RatCutBinCertificate := ⟨⟨retention4076,(187103356190364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(821643490549663749/500000000000000000)⟩,(999655549762666239/1000000000000000000),(4181106037125573/125000000000000000),(417145041441426223/500000000000000000),(10292021266194711/8000000000000000)⟩
theorem valid4076 : certificate4076.Valid := by decide +kernel
theorem sound4076 : certificate4076.Sound := rat_cut_bin_certificate_sound certificate4076 profilesValid4076 numericValid4076 valid4076

def retention4077 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/2),64,1,(63848938712576751324224913430591766799/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch380.profile15211,(fun _ => MergedCutProfiles.Batch380.profile15211)⟩
theorem profilesValid4077 : retention4077.ProfilesValid := by
  exact MergedCutProfiles.Batch380.valid15211
theorem numericValid4077 : retention4077.NumericValid := by decide +kernel
def certificate4077 : RatCutBinCertificate := ⟨⟨retention4077,(187103356190364433/100000000000000000),(65444215677591123/500000000000000000),(846759343543568017/62500000000000000),(2375968812101934089673/500000000000000000),(195912727527260377/200000000000000000)⟩,(999655549762666239/1000000000000000000),(7014099802625861/125000000000000000),(154433741391582819/200000000000000000),(744726531827050929/1000000000000000000)⟩
theorem valid4077 : certificate4077.Valid := by decide +kernel
theorem sound4077 : certificate4077.Sound := rat_cut_bin_certificate_sound certificate4077 profilesValid4077 numericValid4077 valid4077

def retention4078 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(338152903382543747/166869311113378252238),(662979910562775701/1000000000000000000),4,(4821332996564556113/2048000000000000000),true,MergedCutProfiles.Batch613.profile24549,![MergedCutProfiles.Batch613.profile24549,MergedCutProfiles.Batch613.profile24550,MergedCutProfiles.Batch613.profile24551,MergedCutProfiles.Batch613.profile24552,MergedCutProfiles.Batch613.profile24553,MergedCutProfiles.Batch499.profile19969,MergedCutProfiles.Batch613.profile24554,MergedCutProfiles.Batch613.profile24555,MergedCutProfiles.Batch499.profile19994,MergedCutProfiles.Batch613.profile24556,MergedCutProfiles.Batch613.profile24557,MergedCutProfiles.Batch499.profile19970,MergedCutProfiles.Batch499.profile19982,MergedCutProfiles.Batch613.profile24558,MergedCutProfiles.Batch613.profile24559,MergedCutProfiles.Batch381.profile15262]⟩
theorem profilesValid4078 : retention4078.ProfilesValid := by
  change ∀ j : Fin 16, (retention4078.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch613.valid24549
  · exact MergedCutProfiles.Batch613.valid24550
  · exact MergedCutProfiles.Batch613.valid24551
  · exact MergedCutProfiles.Batch613.valid24552
  · exact MergedCutProfiles.Batch613.valid24553
  · exact MergedCutProfiles.Batch499.valid19969
  · exact MergedCutProfiles.Batch613.valid24554
  · exact MergedCutProfiles.Batch613.valid24555
  · exact MergedCutProfiles.Batch499.valid19994
  · exact MergedCutProfiles.Batch613.valid24556
  · exact MergedCutProfiles.Batch613.valid24557
  · exact MergedCutProfiles.Batch499.valid19970
  · exact MergedCutProfiles.Batch499.valid19982
  · exact MergedCutProfiles.Batch613.valid24558
  · exact MergedCutProfiles.Batch613.valid24559
  · exact MergedCutProfiles.Batch381.valid15262
theorem numericValid4078 : retention4078.NumericValid := by decide +kernel
def certificate4078 : RatCutBinCertificate := ⟨⟨retention4078,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(2275886732307338703/1000000000000000000)⟩,(124953671131530317/125000000000000000),(117001016944046851/200000000000000000),(101353364433906333/1000000000000000000),(47459042606171619/1000000000000000000)⟩
theorem valid4078 : certificate4078.Valid := by decide +kernel
theorem sound4078 : certificate4078.Sound := rat_cut_bin_certificate_sound certificate4078 profilesValid4078 numericValid4078 valid4078

def retention4079 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(277662421750000000/83434655556689126119),(338152903382543747/500000000000000000),4,(18818192610375460523/8000000000000000000),true,MergedCutProfiles.Batch614.profile24560,![MergedCutProfiles.Batch614.profile24560,MergedCutProfiles.Batch614.profile24561,MergedCutProfiles.Batch613.profile24553,MergedCutProfiles.Batch614.profile24562,MergedCutProfiles.Batch614.profile24563,MergedCutProfiles.Batch613.profile24556,MergedCutProfiles.Batch614.profile24564,MergedCutProfiles.Batch499.profile19982,MergedCutProfiles.Batch381.profile15247,MergedCutProfiles.Batch614.profile24565,MergedCutProfiles.Batch499.profile19971,MergedCutProfiles.Batch499.profile19983,MergedCutProfiles.Batch614.profile24566,MergedCutProfiles.Batch614.profile24567,MergedCutProfiles.Batch614.profile24568,MergedCutProfiles.Batch614.profile24569]⟩
theorem profilesValid4079 : retention4079.ProfilesValid := by
  change ∀ j : Fin 16, (retention4079.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24560
  · exact MergedCutProfiles.Batch614.valid24561
  · exact MergedCutProfiles.Batch613.valid24553
  · exact MergedCutProfiles.Batch614.valid24562
  · exact MergedCutProfiles.Batch614.valid24563
  · exact MergedCutProfiles.Batch613.valid24556
  · exact MergedCutProfiles.Batch614.valid24564
  · exact MergedCutProfiles.Batch499.valid19982
  · exact MergedCutProfiles.Batch381.valid15247
  · exact MergedCutProfiles.Batch614.valid24565
  · exact MergedCutProfiles.Batch499.valid19971
  · exact MergedCutProfiles.Batch499.valid19983
  · exact MergedCutProfiles.Batch614.valid24566
  · exact MergedCutProfiles.Batch614.valid24567
  · exact MergedCutProfiles.Batch614.valid24568
  · exact MergedCutProfiles.Batch614.valid24569
theorem numericValid4079 : retention4079.NumericValid := by decide +kernel
def certificate4079 : RatCutBinCertificate := ⟨⟨retention4079,(197245753882956873/100000000000000000),(136712609017002193/1000000000000000000),(2755887728889418891/200000000000000000),(4625575734360181354019/1000000000000000000),(1136997161782832077/500000000000000000)⟩,(124953671131530317/125000000000000000),(72294431659249157/125000000000000000),(26239099689524917/250000000000000000),(49284010222609161/1000000000000000000)⟩
theorem valid4079 : certificate4079.Valid := by decide +kernel
theorem sound4079 : certificate4079.Sound := rat_cut_bin_certificate_sound certificate4079 profilesValid4079 numericValid4079 valid4079

def certificates : List RatCutBinCertificate := [certificate4068,certificate4069,certificate4070,certificate4071,certificate4072,certificate4073,certificate4074,certificate4075,certificate4076,certificate4077,certificate4078,certificate4079]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4068,List.forall_mem_cons.mpr ⟨sound4069,List.forall_mem_cons.mpr ⟨sound4070,List.forall_mem_cons.mpr ⟨sound4071,List.forall_mem_cons.mpr ⟨sound4072,List.forall_mem_cons.mpr ⟨sound4073,List.forall_mem_cons.mpr ⟨sound4074,List.forall_mem_cons.mpr ⟨sound4075,List.forall_mem_cons.mpr ⟨sound4076,List.forall_mem_cons.mpr ⟨sound4077,List.forall_mem_cons.mpr ⟨sound4078,List.forall_mem_cons.mpr ⟨sound4079,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch339
