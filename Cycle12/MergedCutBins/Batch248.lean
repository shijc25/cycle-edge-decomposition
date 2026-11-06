import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch041
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch331
import Cycle12.MergedCutProfiles.Batch332
import Cycle12.MergedCutProfiles.Batch462
import Cycle12.MergedCutProfiles.Batch463

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch248

def retention2976 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid2976 : retention2976.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid2976 : retention2976.NumericValid := by decide +kernel
def certificate2976 : RatCutBinCertificate := ⟨⟨retention2976,(2053212004901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(495066224117525467/500000000000000000)⟩,(99938435890663907/100000000000000000),(134464790448352599/1000000000000000000),(594277793291737079/1000000000000000000),(57908958624577387/100000000000000000)⟩
theorem valid2976 : certificate2976.Valid := by decide +kernel
theorem sound2976 : certificate2976.Sound := rat_cut_bin_certificate_sound certificate2976 profilesValid2976 numericValid2976 valid2976

def retention2977 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(317295460625403157/158690640500348274084),(157076960705645127/250000000000000000),4,(36640004211771189987/16000000000000000000),true,MergedCutProfiles.Batch462.profile18491,![MergedCutProfiles.Batch462.profile18491,MergedCutProfiles.Batch462.profile18492,MergedCutProfiles.Batch462.profile18493,MergedCutProfiles.Batch462.profile18494,MergedCutProfiles.Batch462.profile18495,MergedCutProfiles.Batch462.profile18496,MergedCutProfiles.Batch462.profile18497,MergedCutProfiles.Batch462.profile18498,MergedCutProfiles.Batch331.profile13246,MergedCutProfiles.Batch462.profile18499,MergedCutProfiles.Batch330.profile13224,MergedCutProfiles.Batch462.profile18500,MergedCutProfiles.Batch462.profile18501,MergedCutProfiles.Batch462.profile18502,MergedCutProfiles.Batch462.profile18503,MergedCutProfiles.Batch331.profile13254]⟩
theorem profilesValid2977 : retention2977.ProfilesValid := by
  change ∀ j : Fin 16, (retention2977.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch462.valid18491
  · exact MergedCutProfiles.Batch462.valid18492
  · exact MergedCutProfiles.Batch462.valid18493
  · exact MergedCutProfiles.Batch462.valid18494
  · exact MergedCutProfiles.Batch462.valid18495
  · exact MergedCutProfiles.Batch462.valid18496
  · exact MergedCutProfiles.Batch462.valid18497
  · exact MergedCutProfiles.Batch462.valid18498
  · exact MergedCutProfiles.Batch331.valid13246
  · exact MergedCutProfiles.Batch462.valid18499
  · exact MergedCutProfiles.Batch330.valid13224
  · exact MergedCutProfiles.Batch462.valid18500
  · exact MergedCutProfiles.Batch462.valid18501
  · exact MergedCutProfiles.Batch462.valid18502
  · exact MergedCutProfiles.Batch462.valid18503
  · exact MergedCutProfiles.Batch331.valid13254
theorem numericValid2977 : retention2977.NumericValid := by decide +kernel
def certificate2977 : RatCutBinCertificate := ⟨⟨retention2977,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(1130332177962841509/500000000000000000)⟩,(124924111913708739/125000000000000000),(69151549859905003/125000000000000000),(59639257471457979/500000000000000000),(27498195980701957/500000000000000000)⟩
theorem valid2977 : certificate2977.Valid := by decide +kernel
theorem sound2977 : certificate2977.Sound := rat_cut_bin_certificate_sound certificate2977 profilesValid2977 numericValid2977 valid2977

def retention2978 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(148862619875000000/39672660125087068521),(317295460625403157/500000000000000000),4,(11688453367060320637/5120000000000000000),true,MergedCutProfiles.Batch462.profile18504,![MergedCutProfiles.Batch462.profile18504,MergedCutProfiles.Batch462.profile18505,MergedCutProfiles.Batch040.profile1624,MergedCutProfiles.Batch330.profile13233,MergedCutProfiles.Batch041.profile1671,MergedCutProfiles.Batch330.profile13234,MergedCutProfiles.Batch462.profile18501,MergedCutProfiles.Batch462.profile18503,MergedCutProfiles.Batch040.profile1626,MergedCutProfiles.Batch041.profile1672,MergedCutProfiles.Batch462.profile18506,MergedCutProfiles.Batch040.profile1627,MergedCutProfiles.Batch330.profile13228,MergedCutProfiles.Batch462.profile18507,MergedCutProfiles.Batch040.profile1628,MergedCutProfiles.Batch042.profile1683]⟩
theorem profilesValid2978 : retention2978.ProfilesValid := by
  change ∀ j : Fin 16, (retention2978.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch462.valid18504
  · exact MergedCutProfiles.Batch462.valid18505
  · exact MergedCutProfiles.Batch040.valid1624
  · exact MergedCutProfiles.Batch330.valid13233
  · exact MergedCutProfiles.Batch041.valid1671
  · exact MergedCutProfiles.Batch330.valid13234
  · exact MergedCutProfiles.Batch462.valid18501
  · exact MergedCutProfiles.Batch462.valid18503
  · exact MergedCutProfiles.Batch040.valid1626
  · exact MergedCutProfiles.Batch041.valid1672
  · exact MergedCutProfiles.Batch462.valid18506
  · exact MergedCutProfiles.Batch040.valid1627
  · exact MergedCutProfiles.Batch330.valid13228
  · exact MergedCutProfiles.Batch462.valid18507
  · exact MergedCutProfiles.Batch040.valid1628
  · exact MergedCutProfiles.Batch042.valid1683
theorem numericValid2978 : retention2978.NumericValid := by decide +kernel
def certificate2978 : RatCutBinCertificate := ⟨⟨retention2978,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(563391285583901853/250000000000000000)⟩,(124924111913708739/125000000000000000),(551482481625006171/1000000000000000000),(3759542375135019/31250000000000000),(6928511179053003/125000000000000000)⟩
theorem valid2978 : certificate2978.Valid := by decide +kernel
theorem sound2978 : certificate2978.Sound := rat_cut_bin_certificate_sound certificate2978 profilesValid2978 numericValid2978 valid2978

def retention2979 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(601335505204245599/105793760333565516056),(1190900959/1000000000),(51/20),(18287501895269696989/8000000000000000000),true,MergedCutProfiles.Batch462.profile18508,![MergedCutProfiles.Batch462.profile18508,MergedCutProfiles.Batch040.profile1624,MergedCutProfiles.Batch462.profile18509,MergedCutProfiles.Batch040.profile1625,MergedCutProfiles.Batch462.profile18510,MergedCutProfiles.Batch040.profile1626,MergedCutProfiles.Batch462.profile18511,MergedCutProfiles.Batch462.profile18512,MergedCutProfiles.Batch462.profile18513,MergedCutProfiles.Batch041.profile1673,MergedCutProfiles.Batch331.profile13248,MergedCutProfiles.Batch040.profile1629,MergedCutProfiles.Batch462.profile18514,MergedCutProfiles.Batch040.profile1630,MergedCutProfiles.Batch331.profile13258,MergedCutProfiles.Batch040.profile1631]⟩
theorem profilesValid2979 : retention2979.ProfilesValid := by
  change ∀ j : Fin 16, (retention2979.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch462.valid18508
  · exact MergedCutProfiles.Batch040.valid1624
  · exact MergedCutProfiles.Batch462.valid18509
  · exact MergedCutProfiles.Batch040.valid1625
  · exact MergedCutProfiles.Batch462.valid18510
  · exact MergedCutProfiles.Batch040.valid1626
  · exact MergedCutProfiles.Batch462.valid18511
  · exact MergedCutProfiles.Batch462.valid18512
  · exact MergedCutProfiles.Batch462.valid18513
  · exact MergedCutProfiles.Batch041.valid1673
  · exact MergedCutProfiles.Batch331.valid13248
  · exact MergedCutProfiles.Batch040.valid1629
  · exact MergedCutProfiles.Batch462.valid18514
  · exact MergedCutProfiles.Batch040.valid1630
  · exact MergedCutProfiles.Batch331.valid13258
  · exact MergedCutProfiles.Batch040.valid1631
theorem numericValid2979 : retention2979.NumericValid := by decide +kernel
def certificate2979 : RatCutBinCertificate := ⟨⟨retention2979,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(2267236111447164513/1000000000000000000)⟩,(124924111913708739/125000000000000000),(386915869120389193/1000000000000000000),(245686949661980677/1000000000000000000),(84427257691289933/500000000000000000)⟩
theorem valid2979 : certificate2979.Valid := by decide +kernel
theorem sound2979 : certificate2979.Sound := rat_cut_bin_certificate_sound certificate2979 profilesValid2979 numericValid2979 valid2979

def retention2980 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(6507157974182893437/52896880166782758028),(1804006515612736797/1000000000000000000),(39/20),(5296159292410576891752049943255066207831/2886410424980378875200000000000000000000),false,MergedCutProfiles.Batch462.profile18515,(fun _ => MergedCutProfiles.Batch462.profile18515)⟩
theorem profilesValid2980 : retention2980.ProfilesValid := by
  exact MergedCutProfiles.Batch462.valid18515
theorem numericValid2980 : retention2980.NumericValid := by decide +kernel
def certificate2980 : RatCutBinCertificate := ⟨⟨retention2980,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(910279427421060649/500000000000000000)⟩,(124924111913708739/125000000000000000),(40399925410346469/100000000000000000),(114918981819324489/500000000000000000),(169460209316354157/1000000000000000000)⟩
theorem valid2980 : certificate2980.Valid := by decide +kernel
theorem sound2980 : certificate2980.Sound := rat_cut_bin_certificate_sound certificate2980 profilesValid2980 numericValid2980 valid2980

def retention2981 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(8000000000000000000/39672660125087068521),(19521473922548680311/500000000000000000),1,(252851106920563985564692324943528693927/156171791380389442488000000000000000000),false,MergedCutProfiles.Batch462.profile18516,(fun _ => MergedCutProfiles.Batch462.profile18516)⟩
theorem profilesValid2981 : retention2981.ProfilesValid := by
  exact MergedCutProfiles.Batch462.valid18516
theorem numericValid2981 : retention2981.NumericValid := by decide +kernel
def certificate2981 : RatCutBinCertificate := ⟨⟨retention2981,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(805861767772453911/500000000000000000)⟩,(124924111913708739/125000000000000000),(293435037827726687/1000000000000000000),(346757144838507473/1000000000000000000),(1676218943764413/3125000000000000)⟩
theorem valid2981 : certificate2981.Valid := by decide +kernel
theorem sound2981 : certificate2981.Sound := rat_cut_bin_certificate_sound certificate2981 profilesValid2981 numericValid2981 valid2981

def retention2982 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid2982 : retention2982.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid2982 : retention2982.NumericValid := by decide +kernel
def certificate2982 : RatCutBinCertificate := ⟨⟨retention2982,(954684532717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(495112979044326617/500000000000000000)⟩,(124924111913708739/125000000000000000),(29537197139331561/62500000000000000),(86593502728513869/500000000000000000),(84388937268196649/500000000000000000)⟩
theorem valid2982 : certificate2982.Valid := by decide +kernel
theorem sound2982 : certificate2982.Sound := rat_cut_bin_certificate_sound certificate2982 profilesValid2982 numericValid2982 valid2982

def retention2983 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(8000000000000000000/39672660125087068521),(4640707306733617823/500000000000000000),1,(58067845790077974145895922460177775463/37125658453868942584000000000000000000),false,MergedCutProfiles.Batch462.profile18516,(fun _ => MergedCutProfiles.Batch462.profile18516)⟩
theorem profilesValid2983 : retention2983.ProfilesValid := by
  exact MergedCutProfiles.Batch462.valid18516
theorem numericValid2983 : retention2983.NumericValid := by decide +kernel
def certificate2983 : RatCutBinCertificate := ⟨⟨retention2983,(1030862965717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(778085079171605833/500000000000000000)⟩,(62459028166748507/62500000000000000),(85768082721864187/1000000000000000000),(698803042495847157/1000000000000000000),(116333574861639327/125000000000000000)⟩
theorem valid2983 : certificate2983.Valid := by decide +kernel
theorem sound2983 : certificate2983.Sound := rat_cut_bin_certificate_sound certificate2983 profilesValid2983 numericValid2983 valid2983

def retention2984 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid2984 : retention2984.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid2984 : retention2984.NumericValid := by decide +kernel
def certificate2984 : RatCutBinCertificate := ⟨⟨retention2984,(1030862965717283611/500000000000000000),(36585906920747501/1000000000000000000),(9525027860197911687/1000000000000000000),(3038266549588119464343/1000000000000000000),(247410187714735429/250000000000000000)⟩,(62459028166748507/62500000000000000),(5394674006875093/40000000000000000),(74185723201877459/125000000000000000),(578011731942295507/1000000000000000000)⟩
theorem valid2984 : certificate2984.Valid := by decide +kernel
theorem sound2984 : certificate2984.Sound := rat_cut_bin_certificate_sound certificate2984 profilesValid2984 numericValid2984 valid2984

def retention2985 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(65154083996137735/29508253281651770749),(158094780059753739/250000000000000000),4,(36702533808302030689/16000000000000000000),true,MergedCutProfiles.Batch462.profile18517,![MergedCutProfiles.Batch462.profile18517,MergedCutProfiles.Batch462.profile18518,MergedCutProfiles.Batch462.profile18519,MergedCutProfiles.Batch463.profile18520,MergedCutProfiles.Batch463.profile18521,MergedCutProfiles.Batch463.profile18522,MergedCutProfiles.Batch332.profile13296,MergedCutProfiles.Batch043.profile1749,MergedCutProfiles.Batch463.profile18523,MergedCutProfiles.Batch463.profile18524,MergedCutProfiles.Batch463.profile18525,MergedCutProfiles.Batch463.profile18526,MergedCutProfiles.Batch332.profile13308,MergedCutProfiles.Batch332.profile13297,MergedCutProfiles.Batch463.profile18527,MergedCutProfiles.Batch043.profile1750]⟩
theorem profilesValid2985 : retention2985.ProfilesValid := by
  change ∀ j : Fin 16, (retention2985.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch462.valid18517
  · exact MergedCutProfiles.Batch462.valid18518
  · exact MergedCutProfiles.Batch462.valid18519
  · exact MergedCutProfiles.Batch463.valid18520
  · exact MergedCutProfiles.Batch463.valid18521
  · exact MergedCutProfiles.Batch463.valid18522
  · exact MergedCutProfiles.Batch332.valid13296
  · exact MergedCutProfiles.Batch043.valid1749
  · exact MergedCutProfiles.Batch463.valid18523
  · exact MergedCutProfiles.Batch463.valid18524
  · exact MergedCutProfiles.Batch463.valid18525
  · exact MergedCutProfiles.Batch463.valid18526
  · exact MergedCutProfiles.Batch332.valid13308
  · exact MergedCutProfiles.Batch332.valid13297
  · exact MergedCutProfiles.Batch463.valid18527
  · exact MergedCutProfiles.Batch043.valid1750
theorem numericValid2985 : retention2985.NumericValid := by decide +kernel
def certificate2985 : RatCutBinCertificate := ⟨⟨retention2985,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(2262737706472813833/1000000000000000000)⟩,(24983900853504023/25000000000000000),(549768515875225503/1000000000000000000),(121328080190180097/1000000000000000000),(11209429751830677/200000000000000000)⟩
theorem valid2985 : certificate2985.Valid := by decide +kernel
theorem sound2985 : certificate2985.Sound := rat_cut_bin_certificate_sound certificate2985 profilesValid2985 numericValid2985 valid2985

def retention2986 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(117233765900000000/29508253281651770749),(13030816799227547/20000000000000000),4,(3678799195765336393/1600000000000000000),true,MergedCutProfiles.Batch463.profile18528,![MergedCutProfiles.Batch463.profile18528,MergedCutProfiles.Batch332.profile13295,MergedCutProfiles.Batch332.profile13286,MergedCutProfiles.Batch463.profile18529,MergedCutProfiles.Batch463.profile18523,MergedCutProfiles.Batch463.profile18525,MergedCutProfiles.Batch463.profile18530,MergedCutProfiles.Batch463.profile18531,MergedCutProfiles.Batch043.profile1750,MergedCutProfiles.Batch463.profile18532,MergedCutProfiles.Batch043.profile1722,MergedCutProfiles.Batch332.profile13290,MergedCutProfiles.Batch463.profile18533,MergedCutProfiles.Batch463.profile18534,MergedCutProfiles.Batch043.profile1723,MergedCutProfiles.Batch463.profile18535]⟩
theorem profilesValid2986 : retention2986.ProfilesValid := by
  change ∀ j : Fin 16, (retention2986.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch463.valid18528
  · exact MergedCutProfiles.Batch332.valid13295
  · exact MergedCutProfiles.Batch332.valid13286
  · exact MergedCutProfiles.Batch463.valid18529
  · exact MergedCutProfiles.Batch463.valid18523
  · exact MergedCutProfiles.Batch463.valid18525
  · exact MergedCutProfiles.Batch463.valid18530
  · exact MergedCutProfiles.Batch463.valid18531
  · exact MergedCutProfiles.Batch043.valid1750
  · exact MergedCutProfiles.Batch463.valid18532
  · exact MergedCutProfiles.Batch043.valid1722
  · exact MergedCutProfiles.Batch332.valid13290
  · exact MergedCutProfiles.Batch463.valid18533
  · exact MergedCutProfiles.Batch463.valid18534
  · exact MergedCutProfiles.Batch043.valid1723
  · exact MergedCutProfiles.Batch463.valid18535
theorem numericValid2986 : retention2986.NumericValid := by decide +kernel
def certificate2986 : RatCutBinCertificate := ⟨⟨retention2986,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(1134039422890154913/500000000000000000)⟩,(24983900853504023/25000000000000000),(269166564927126301/500000000000000000),(16036143748890427/125000000000000000),(59698737687693763/1000000000000000000)⟩
theorem valid2986 : certificate2986.Valid := by decide +kernel
theorem sound2986 : certificate2986.Sound := rat_cut_bin_certificate_sound certificate2986 profilesValid2986 numericValid2986 valid2986

def retention2987 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(129454286202777355/29508253281651770749),(1172337659/1000000000),(51/20),(18341686520289484583/8000000000000000000),true,MergedCutProfiles.Batch463.profile18536,![MergedCutProfiles.Batch463.profile18536,MergedCutProfiles.Batch463.profile18537,MergedCutProfiles.Batch463.profile18522,MergedCutProfiles.Batch043.profile1735,MergedCutProfiles.Batch463.profile18538,MergedCutProfiles.Batch463.profile18526,MergedCutProfiles.Batch463.profile18539,MergedCutProfiles.Batch043.profile1736,MergedCutProfiles.Batch332.profile13298,MergedCutProfiles.Batch043.profile1722,MergedCutProfiles.Batch332.profile13318,MergedCutProfiles.Batch043.profile1737,MergedCutProfiles.Batch332.profile13310,MergedCutProfiles.Batch042.profile1708,MergedCutProfiles.Batch463.profile18540,MergedCutProfiles.Batch043.profile1738]⟩
theorem profilesValid2987 : retention2987.ProfilesValid := by
  change ∀ j : Fin 16, (retention2987.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch463.valid18536
  · exact MergedCutProfiles.Batch463.valid18537
  · exact MergedCutProfiles.Batch463.valid18522
  · exact MergedCutProfiles.Batch043.valid1735
  · exact MergedCutProfiles.Batch463.valid18538
  · exact MergedCutProfiles.Batch463.valid18526
  · exact MergedCutProfiles.Batch463.valid18539
  · exact MergedCutProfiles.Batch043.valid1736
  · exact MergedCutProfiles.Batch332.valid13298
  · exact MergedCutProfiles.Batch043.valid1722
  · exact MergedCutProfiles.Batch332.valid13318
  · exact MergedCutProfiles.Batch043.valid1737
  · exact MergedCutProfiles.Batch332.valid13310
  · exact MergedCutProfiles.Batch042.valid1708
  · exact MergedCutProfiles.Batch463.valid18540
  · exact MergedCutProfiles.Batch043.valid1738
theorem numericValid2987 : retention2987.NumericValid := by decide +kernel
def certificate2987 : RatCutBinCertificate := ⟨⟨retention2987,(957405645196595327/500000000000000000),(39310593322721927/1000000000000000000),(9659440590120051229/1000000000000000000),(2864750281502089248499/1000000000000000000),(2272839538073307201/1000000000000000000)⟩,(24983900853504023/25000000000000000),(194422724594934349/500000000000000000),(243859635445894887/1000000000000000000),(41827610879321297/250000000000000000)⟩
theorem valid2987 : certificate2987.Valid := by decide +kernel
theorem sound2987 : certificate2987.Sound := rat_cut_bin_certificate_sound certificate2987 profilesValid2987 numericValid2987 valid2987

def certificates : List RatCutBinCertificate := [certificate2976,certificate2977,certificate2978,certificate2979,certificate2980,certificate2981,certificate2982,certificate2983,certificate2984,certificate2985,certificate2986,certificate2987]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2976,List.forall_mem_cons.mpr ⟨sound2977,List.forall_mem_cons.mpr ⟨sound2978,List.forall_mem_cons.mpr ⟨sound2979,List.forall_mem_cons.mpr ⟨sound2980,List.forall_mem_cons.mpr ⟨sound2981,List.forall_mem_cons.mpr ⟨sound2982,List.forall_mem_cons.mpr ⟨sound2983,List.forall_mem_cons.mpr ⟨sound2984,List.forall_mem_cons.mpr ⟨sound2985,List.forall_mem_cons.mpr ⟨sound2986,List.forall_mem_cons.mpr ⟨sound2987,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch248
