import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch037
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch327
import Cycle12.MergedCutProfiles.Batch328
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch460
import Cycle12.MergedCutProfiles.Batch461
import Cycle12.MergedCutProfiles.Batch590
import Cycle12.MergedCutProfiles.Batch591
import Cycle12.MergedCutProfiles.Batch592

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch323

def retention3876 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(585537026927141920/1603197552115051441481),(557118389944444469/1000000000000000000),4,(241974042617365143341514511006703319/111423677988888893800000000000000000),true,MergedCutProfiles.Batch590.profile23635,![MergedCutProfiles.Batch590.profile23635,MergedCutProfiles.Batch590.profile23636,MergedCutProfiles.Batch590.profile23637,MergedCutProfiles.Batch590.profile23638,MergedCutProfiles.Batch590.profile23639,MergedCutProfiles.Batch591.profile23640,MergedCutProfiles.Batch591.profile23641,MergedCutProfiles.Batch460.profile18401,MergedCutProfiles.Batch460.profile18410,MergedCutProfiles.Batch591.profile23642,MergedCutProfiles.Batch591.profile23643,MergedCutProfiles.Batch326.profile13065,MergedCutProfiles.Batch459.profile18392,MergedCutProfiles.Batch591.profile23644,MergedCutProfiles.Batch591.profile23645,MergedCutProfiles.Batch460.profile18402]⟩
theorem profilesValid3876 : retention3876.ProfilesValid := by
  change ∀ j : Fin 16, (retention3876.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch590.valid23635
  · exact MergedCutProfiles.Batch590.valid23636
  · exact MergedCutProfiles.Batch590.valid23637
  · exact MergedCutProfiles.Batch590.valid23638
  · exact MergedCutProfiles.Batch590.valid23639
  · exact MergedCutProfiles.Batch591.valid23640
  · exact MergedCutProfiles.Batch591.valid23641
  · exact MergedCutProfiles.Batch460.valid18401
  · exact MergedCutProfiles.Batch460.valid18410
  · exact MergedCutProfiles.Batch591.valid23642
  · exact MergedCutProfiles.Batch591.valid23643
  · exact MergedCutProfiles.Batch326.valid13065
  · exact MergedCutProfiles.Batch459.valid18392
  · exact MergedCutProfiles.Batch591.valid23644
  · exact MergedCutProfiles.Batch591.valid23645
  · exact MergedCutProfiles.Batch460.valid18402
theorem numericValid3876 : retention3876.NumericValid := by decide +kernel
def certificate3876 : RatCutBinCertificate := ⟨⟨retention3876,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(1074237626849787483/500000000000000000)⟩,(15623117794821933/15625000000000000),(726533904609135301/1000000000000000000),(20680107712116431/500000000000000000),(17898192626817403/1000000000000000000)⟩
theorem valid3876 : certificate3876.Valid := by decide +kernel
theorem sound3876 : certificate3876.Sound := rat_cut_bin_certificate_sound certificate3876 profilesValid3876 numericValid3876 valid3876

def retention3877 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1193618840000000000/1603197552115051441481),(3659606418294637/6250000000000000),4,(35692641594294446987/16000000000000000000),true,MergedCutProfiles.Batch590.profile23636,![MergedCutProfiles.Batch590.profile23636,MergedCutProfiles.Batch590.profile23638,MergedCutProfiles.Batch591.profile23646,MergedCutProfiles.Batch460.profile18401,MergedCutProfiles.Batch591.profile23647,MergedCutProfiles.Batch591.profile23648,MergedCutProfiles.Batch591.profile23644,MergedCutProfiles.Batch460.profile18402,MergedCutProfiles.Batch460.profile18411,MergedCutProfiles.Batch591.profile23649,MergedCutProfiles.Batch591.profile23650,MergedCutProfiles.Batch034.profile1390,MergedCutProfiles.Batch460.profile18412,MergedCutProfiles.Batch591.profile23651,MergedCutProfiles.Batch591.profile23652,MergedCutProfiles.Batch460.profile18403]⟩
theorem profilesValid3877 : retention3877.ProfilesValid := by
  change ∀ j : Fin 16, (retention3877.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch590.valid23636
  · exact MergedCutProfiles.Batch590.valid23638
  · exact MergedCutProfiles.Batch591.valid23646
  · exact MergedCutProfiles.Batch460.valid18401
  · exact MergedCutProfiles.Batch591.valid23647
  · exact MergedCutProfiles.Batch591.valid23648
  · exact MergedCutProfiles.Batch591.valid23644
  · exact MergedCutProfiles.Batch460.valid18402
  · exact MergedCutProfiles.Batch460.valid18411
  · exact MergedCutProfiles.Batch591.valid23649
  · exact MergedCutProfiles.Batch591.valid23650
  · exact MergedCutProfiles.Batch034.valid1390
  · exact MergedCutProfiles.Batch460.valid18412
  · exact MergedCutProfiles.Batch591.valid23651
  · exact MergedCutProfiles.Batch591.valid23652
  · exact MergedCutProfiles.Batch460.valid18403
theorem numericValid3877 : retention3877.NumericValid := by decide +kernel
def certificate3877 : RatCutBinCertificate := ⟨⟨retention3877,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(137975504002050333/62500000000000000)⟩,(15623117794821933/15625000000000000),(683474034893229129/1000000000000000000),(5641856724686531/100000000000000000),(1574742499228811/62500000000000000)⟩
theorem valid3877 : certificate3877.Valid := by decide +kernel
theorem sound3877 : certificate3877.Sound := rat_cut_bin_certificate_sound certificate3877 profilesValid3877 numericValid3877 valid3877

def retention3878 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1222745359176845444/1603197552115051441481),(29840471/25000000),(53/20),(18078551352374614332059292970997719/7639160576000000000000000000000000),true,MergedCutProfiles.Batch591.profile23653,![MergedCutProfiles.Batch591.profile23653,MergedCutProfiles.Batch590.profile23638,MergedCutProfiles.Batch591.profile23646,MergedCutProfiles.Batch459.profile18391,MergedCutProfiles.Batch591.profile23647,MergedCutProfiles.Batch591.profile23648,MergedCutProfiles.Batch591.profile23645,MergedCutProfiles.Batch460.profile18402,MergedCutProfiles.Batch591.profile23654,MergedCutProfiles.Batch591.profile23649,MergedCutProfiles.Batch591.profile23650,MergedCutProfiles.Batch034.profile1390,MergedCutProfiles.Batch460.profile18412,MergedCutProfiles.Batch591.profile23651,MergedCutProfiles.Batch591.profile23652,MergedCutProfiles.Batch591.profile23655]⟩
theorem profilesValid3878 : retention3878.ProfilesValid := by
  change ∀ j : Fin 16, (retention3878.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch591.valid23653
  · exact MergedCutProfiles.Batch590.valid23638
  · exact MergedCutProfiles.Batch591.valid23646
  · exact MergedCutProfiles.Batch459.valid18391
  · exact MergedCutProfiles.Batch591.valid23647
  · exact MergedCutProfiles.Batch591.valid23648
  · exact MergedCutProfiles.Batch591.valid23645
  · exact MergedCutProfiles.Batch460.valid18402
  · exact MergedCutProfiles.Batch591.valid23654
  · exact MergedCutProfiles.Batch591.valid23649
  · exact MergedCutProfiles.Batch591.valid23650
  · exact MergedCutProfiles.Batch034.valid1390
  · exact MergedCutProfiles.Batch460.valid18412
  · exact MergedCutProfiles.Batch591.valid23651
  · exact MergedCutProfiles.Batch591.valid23652
  · exact MergedCutProfiles.Batch591.valid23655
theorem numericValid3878 : retention3878.NumericValid := by decide +kernel
def certificate3878 : RatCutBinCertificate := ⟨⟨retention3878,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(1175602228678077457/500000000000000000)⟩,(15623117794821933/15625000000000000),(16817596008330273/40000000000000000),(215267661186514049/1000000000000000000),(149136481355842301/1000000000000000000)⟩
theorem valid3878 : certificate3878.Valid := by decide +kernel
theorem sound3878 : certificate3878.Sound := rat_cut_bin_certificate_sound certificate3878 profilesValid3878 numericValid3878 valid3878

def retention3879 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(4547339322564945490/1603197552115051441481),(305686339794211361/250000000000000000),(13/5),(285153571895969617602272991108196458791/122274535917684544400000000000000000000),true,MergedCutProfiles.Batch460.profile18401,![MergedCutProfiles.Batch460.profile18401,MergedCutProfiles.Batch591.profile23656,MergedCutProfiles.Batch326.profile13066,MergedCutProfiles.Batch591.profile23652,MergedCutProfiles.Batch459.profile18395,MergedCutProfiles.Batch326.profile13068,MergedCutProfiles.Batch459.profile18398,MergedCutProfiles.Batch460.profile18416,MergedCutProfiles.Batch326.profile13070,MergedCutProfiles.Batch591.profile23657,MergedCutProfiles.Batch591.profile23658,MergedCutProfiles.Batch326.profile13072,MergedCutProfiles.Batch591.profile23659,MergedCutProfiles.Batch327.profile13090,MergedCutProfiles.Batch326.profile13074,MergedCutProfiles.Batch460.profile18418]⟩
theorem profilesValid3879 : retention3879.ProfilesValid := by
  change ∀ j : Fin 16, (retention3879.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18401
  · exact MergedCutProfiles.Batch591.valid23656
  · exact MergedCutProfiles.Batch326.valid13066
  · exact MergedCutProfiles.Batch591.valid23652
  · exact MergedCutProfiles.Batch459.valid18395
  · exact MergedCutProfiles.Batch326.valid13068
  · exact MergedCutProfiles.Batch459.valid18398
  · exact MergedCutProfiles.Batch460.valid18416
  · exact MergedCutProfiles.Batch326.valid13070
  · exact MergedCutProfiles.Batch591.valid23657
  · exact MergedCutProfiles.Batch591.valid23658
  · exact MergedCutProfiles.Batch326.valid13072
  · exact MergedCutProfiles.Batch591.valid23659
  · exact MergedCutProfiles.Batch327.valid13090
  · exact MergedCutProfiles.Batch326.valid13074
  · exact MergedCutProfiles.Batch460.valid18418
theorem numericValid3879 : retention3879.NumericValid := by decide +kernel
def certificate3879 : RatCutBinCertificate := ⟨⟨retention3879,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(2317008181291863079/1000000000000000000)⟩,(15623117794821933/15625000000000000),(421494307190529259/1000000000000000000),(53588852650666757/250000000000000000),(29836122428262261/200000000000000000)⟩
theorem valid3879 : certificate3879.Valid := by decide +kernel
theorem sound3879 : certificate3879.Sound := rat_cut_bin_certificate_sound certificate3879 profilesValid3879 numericValid3879 valid3879

def retention3880 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(64000000000000000000/1603197552115051441481),(454733932256494549/100000000000000000),(5/4),(52978352447997590513/25600000000000000000),true,MergedCutProfiles.Batch327.profile13090,![MergedCutProfiles.Batch327.profile13090,MergedCutProfiles.Batch034.profile1398,MergedCutProfiles.Batch035.profile1414,MergedCutProfiles.Batch591.profile23660,MergedCutProfiles.Batch591.profile23661,MergedCutProfiles.Batch591.profile23662,MergedCutProfiles.Batch591.profile23663,MergedCutProfiles.Batch591.profile23664,MergedCutProfiles.Batch591.profile23665,MergedCutProfiles.Batch591.profile23666,MergedCutProfiles.Batch591.profile23667,MergedCutProfiles.Batch591.profile23668,MergedCutProfiles.Batch591.profile23669,MergedCutProfiles.Batch591.profile23670,MergedCutProfiles.Batch591.profile23671,MergedCutProfiles.Batch591.profile23672]⟩
theorem profilesValid3880 : retention3880.ProfilesValid := by
  change ∀ j : Fin 16, (retention3880.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch327.valid13090
  · exact MergedCutProfiles.Batch034.valid1398
  · exact MergedCutProfiles.Batch035.valid1414
  · exact MergedCutProfiles.Batch591.valid23660
  · exact MergedCutProfiles.Batch591.valid23661
  · exact MergedCutProfiles.Batch591.valid23662
  · exact MergedCutProfiles.Batch591.valid23663
  · exact MergedCutProfiles.Batch591.valid23664
  · exact MergedCutProfiles.Batch591.valid23665
  · exact MergedCutProfiles.Batch591.valid23666
  · exact MergedCutProfiles.Batch591.valid23667
  · exact MergedCutProfiles.Batch591.valid23668
  · exact MergedCutProfiles.Batch591.valid23669
  · exact MergedCutProfiles.Batch591.valid23670
  · exact MergedCutProfiles.Batch591.valid23671
  · exact MergedCutProfiles.Batch591.valid23672
theorem numericValid3880 : retention3880.NumericValid := by decide +kernel
def certificate3880 : RatCutBinCertificate := ⟨⟨retention3880,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(1031111254980649809/500000000000000000)⟩,(15623117794821933/15625000000000000),(150089830843217839/500000000000000000),(169284503152895567/500000000000000000),(432858104719231701/1000000000000000000)⟩
theorem valid3880 : certificate3880.Valid := by decide +kernel
theorem sound3880 : certificate3880.Sound := rat_cut_bin_certificate_sound certificate3880 profilesValid3880 numericValid3880 valid3880

def retention3881 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid3881 : retention3881.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid3881 : retention3881.NumericValid := by decide +kernel
def certificate3881 : RatCutBinCertificate := ⟨⟨retention3881,(455590472111850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(247939543216433737/250000000000000000)⟩,(15623117794821933/15625000000000000),(16032034725957/32000000000000),(152733462937104169/1000000000000000000),(149145065468267889/1000000000000000000)⟩
theorem valid3881 : certificate3881.Valid := by decide +kernel
theorem sound3881 : certificate3881.Sound := rat_cut_bin_certificate_sound certificate3881 profilesValid3881 numericValid3881 valid3881

def retention3882 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(64000000000000000000/1603197552115051441481),(5068235283554220991/250000000000000000),1,(166911865506219861609506563660525187559/81091764536867535856000000000000000000),false,MergedCutProfiles.Batch591.profile23673,(fun _ => MergedCutProfiles.Batch591.profile23673)⟩
theorem profilesValid3882 : retention3882.ProfilesValid := by
  exact MergedCutProfiles.Batch591.valid23673
theorem numericValid3882 : retention3882.NumericValid := by decide +kernel
def certificate3882 : RatCutBinCertificate := ⟨⟨retention3882,(449079293611850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(2052595789693275999/1000000000000000000)⟩,(499940630236423799/500000000000000000),(31958924496716243/1000000000000000000),(838579413993335417/1000000000000000000),(390705527523187203/250000000000000000)⟩
theorem valid3882 : certificate3882.Valid := by decide +kernel
theorem sound3882 : certificate3882.Sound := rat_cut_bin_certificate_sound certificate3882 profilesValid3882 numericValid3882 valid3882

def retention3883 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid3883 : retention3883.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid3883 : retention3883.NumericValid := by decide +kernel
def certificate3883 : RatCutBinCertificate := ⟨⟨retention3883,(449079293611850779/250000000000000000),(14531335098101001/500000000000000000),(571161524247938817/62500000000000000),(7361664530051213017487/500000000000000000),(991841000678506327/1000000000000000000)⟩,(499940630236423799/500000000000000000),(66138376836821377/1000000000000000000),(746428863901804481/1000000000000000000),(364476542909915659/500000000000000000)⟩
theorem valid3883 : certificate3883.Valid := by decide +kernel
theorem sound3883 : certificate3883.Sound := rat_cut_bin_certificate_sound certificate3883 profilesValid3883 numericValid3883 valid3883

def retention3884 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(585792490104676525/1479290671338451585612),(278680727196157819/500000000000000000),4,(242160914531951203612995701099608227/111472290878463127600000000000000000),true,MergedCutProfiles.Batch591.profile23674,![MergedCutProfiles.Batch591.profile23674,MergedCutProfiles.Batch591.profile23675,MergedCutProfiles.Batch591.profile23676,MergedCutProfiles.Batch591.profile23677,MergedCutProfiles.Batch591.profile23678,MergedCutProfiles.Batch591.profile23679,MergedCutProfiles.Batch592.profile23680,MergedCutProfiles.Batch592.profile23681,MergedCutProfiles.Batch592.profile23682,MergedCutProfiles.Batch592.profile23683,MergedCutProfiles.Batch592.profile23684,MergedCutProfiles.Batch592.profile23685,MergedCutProfiles.Batch460.profile18434,MergedCutProfiles.Batch592.profile23686,MergedCutProfiles.Batch592.profile23687,MergedCutProfiles.Batch328.profile13124]⟩
theorem profilesValid3884 : retention3884.ProfilesValid := by
  change ∀ j : Fin 16, (retention3884.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch591.valid23674
  · exact MergedCutProfiles.Batch591.valid23675
  · exact MergedCutProfiles.Batch591.valid23676
  · exact MergedCutProfiles.Batch591.valid23677
  · exact MergedCutProfiles.Batch591.valid23678
  · exact MergedCutProfiles.Batch591.valid23679
  · exact MergedCutProfiles.Batch592.valid23680
  · exact MergedCutProfiles.Batch592.valid23681
  · exact MergedCutProfiles.Batch592.valid23682
  · exact MergedCutProfiles.Batch592.valid23683
  · exact MergedCutProfiles.Batch592.valid23684
  · exact MergedCutProfiles.Batch592.valid23685
  · exact MergedCutProfiles.Batch460.valid18434
  · exact MergedCutProfiles.Batch592.valid23686
  · exact MergedCutProfiles.Batch592.valid23687
  · exact MergedCutProfiles.Batch328.valid13124
theorem numericValid3884 : retention3884.NumericValid := by decide +kernel
def certificate3884 : RatCutBinCertificate := ⟨⟨retention3884,(365552146933234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(429511564722048391/200000000000000000)⟩,(39994846106634309/40000000000000000),(182425111359152141/250000000000000000),(40355490775045059/1000000000000000000),(17458699749698839/1000000000000000000)⟩
theorem valid3884 : certificate3884.Valid := by decide +kernel
theorem sound3884 : certificate3884.Sound := rat_cut_bin_certificate_sound certificate3884 profilesValid3884 numericValid3884 valid3884

def retention3885 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(298513985250000000/369822667834612896403),(23431699604187061/40000000000000000),4,(571165043215457712061/256000000000000000000),true,MergedCutProfiles.Batch591.profile23675,![MergedCutProfiles.Batch591.profile23675,MergedCutProfiles.Batch591.profile23677,MergedCutProfiles.Batch592.profile23688,MergedCutProfiles.Batch460.profile18433,MergedCutProfiles.Batch592.profile23683,MergedCutProfiles.Batch592.profile23685,MergedCutProfiles.Batch592.profile23686,MergedCutProfiles.Batch461.profile18442,MergedCutProfiles.Batch592.profile23689,MergedCutProfiles.Batch328.profile13130,MergedCutProfiles.Batch327.profile13111,MergedCutProfiles.Batch461.profile18443,MergedCutProfiles.Batch592.profile23690,MergedCutProfiles.Batch592.profile23691,MergedCutProfiles.Batch592.profile23692,MergedCutProfiles.Batch461.profile18444]⟩
theorem profilesValid3885 : retention3885.ProfilesValid := by
  change ∀ j : Fin 16, (retention3885.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch591.valid23675
  · exact MergedCutProfiles.Batch591.valid23677
  · exact MergedCutProfiles.Batch592.valid23688
  · exact MergedCutProfiles.Batch460.valid18433
  · exact MergedCutProfiles.Batch592.valid23683
  · exact MergedCutProfiles.Batch592.valid23685
  · exact MergedCutProfiles.Batch592.valid23686
  · exact MergedCutProfiles.Batch461.valid18442
  · exact MergedCutProfiles.Batch592.valid23689
  · exact MergedCutProfiles.Batch328.valid13130
  · exact MergedCutProfiles.Batch327.valid13111
  · exact MergedCutProfiles.Batch461.valid18443
  · exact MergedCutProfiles.Batch592.valid23690
  · exact MergedCutProfiles.Batch592.valid23691
  · exact MergedCutProfiles.Batch592.valid23692
  · exact MergedCutProfiles.Batch461.valid18444
theorem numericValid3885 : retention3885.NumericValid := by decide +kernel
def certificate3885 : RatCutBinCertificate := ⟨⟨retention3885,(365552146933234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(2206284643002591293/1000000000000000000)⟩,(39994846106634309/40000000000000000),(343298130324040219/500000000000000000),(55237472967023993/1000000000000000000),(4931649589285731/200000000000000000)⟩
theorem valid3885 : certificate3885.Valid := by decide +kernel
theorem sound3885 : certificate3885.Sound := rat_cut_bin_certificate_sound certificate3885 profilesValid3885 numericValid3885 valid3885

def retention3886 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(412198760750702863/369822667834612896403),(1194055941/1000000000),(53/20),(450960061669931633111988589804712279/191048950560000000000000000000000000),true,MergedCutProfiles.Batch591.profile23676,![MergedCutProfiles.Batch591.profile23676,MergedCutProfiles.Batch591.profile23679,MergedCutProfiles.Batch460.profile18433,MergedCutProfiles.Batch327.profile13110,MergedCutProfiles.Batch592.profile23686,MergedCutProfiles.Batch461.profile18442,MergedCutProfiles.Batch328.profile13130,MergedCutProfiles.Batch327.profile13111,MergedCutProfiles.Batch460.profile18437,MergedCutProfiles.Batch592.profile23691,MergedCutProfiles.Batch592.profile23692,MergedCutProfiles.Batch327.profile13112,MergedCutProfiles.Batch592.profile23693,MergedCutProfiles.Batch328.profile13131,MergedCutProfiles.Batch460.profile18438,MergedCutProfiles.Batch037.profile1512]⟩
theorem profilesValid3886 : retention3886.ProfilesValid := by
  change ∀ j : Fin 16, (retention3886.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch591.valid23676
  · exact MergedCutProfiles.Batch591.valid23679
  · exact MergedCutProfiles.Batch460.valid18433
  · exact MergedCutProfiles.Batch327.valid13110
  · exact MergedCutProfiles.Batch592.valid23686
  · exact MergedCutProfiles.Batch461.valid18442
  · exact MergedCutProfiles.Batch328.valid13130
  · exact MergedCutProfiles.Batch327.valid13111
  · exact MergedCutProfiles.Batch460.valid18437
  · exact MergedCutProfiles.Batch592.valid23691
  · exact MergedCutProfiles.Batch592.valid23692
  · exact MergedCutProfiles.Batch327.valid13112
  · exact MergedCutProfiles.Batch592.valid23693
  · exact MergedCutProfiles.Batch328.valid13131
  · exact MergedCutProfiles.Batch460.valid18438
  · exact MergedCutProfiles.Batch037.valid1512
theorem numericValid3886 : retention3886.NumericValid := by decide +kernel
def certificate3886 : RatCutBinCertificate := ⟨⟨retention3886,(365552146933234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(2343993415233697371/1000000000000000000)⟩,(39994846106634309/40000000000000000),(42366304523532707/100000000000000000),(212487346991112979/1000000000000000000),(36716950736509751/250000000000000000)⟩
theorem valid3886 : certificate3886.Valid := by decide +kernel
theorem sound3886 : certificate3886.Sound := rat_cut_bin_certificate_sound certificate3886 profilesValid3886 numericValid3886 valid3886

def retention3887 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(16000000000000000000/369822667834612896403),(412198760750702863/250000000000000000),(21/10),(668278596854994075459/320000000000000000000),true,MergedCutProfiles.Batch328.profile13151,![MergedCutProfiles.Batch328.profile13151,MergedCutProfiles.Batch328.profile13143,MergedCutProfiles.Batch037.profile1494,MergedCutProfiles.Batch592.profile23694,MergedCutProfiles.Batch592.profile23695,MergedCutProfiles.Batch592.profile23696,MergedCutProfiles.Batch038.profile1527,MergedCutProfiles.Batch592.profile23697,MergedCutProfiles.Batch592.profile23698,MergedCutProfiles.Batch592.profile23699,MergedCutProfiles.Batch592.profile23700,MergedCutProfiles.Batch592.profile23701,MergedCutProfiles.Batch592.profile23702,MergedCutProfiles.Batch592.profile23703,MergedCutProfiles.Batch592.profile23704,MergedCutProfiles.Batch592.profile23705]⟩
theorem profilesValid3887 : retention3887.ProfilesValid := by
  change ∀ j : Fin 16, (retention3887.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch328.valid13151
  · exact MergedCutProfiles.Batch328.valid13143
  · exact MergedCutProfiles.Batch037.valid1494
  · exact MergedCutProfiles.Batch592.valid23694
  · exact MergedCutProfiles.Batch592.valid23695
  · exact MergedCutProfiles.Batch592.valid23696
  · exact MergedCutProfiles.Batch038.valid1527
  · exact MergedCutProfiles.Batch592.valid23697
  · exact MergedCutProfiles.Batch592.valid23698
  · exact MergedCutProfiles.Batch592.valid23699
  · exact MergedCutProfiles.Batch592.valid23700
  · exact MergedCutProfiles.Batch592.valid23701
  · exact MergedCutProfiles.Batch592.valid23702
  · exact MergedCutProfiles.Batch592.valid23703
  · exact MergedCutProfiles.Batch592.valid23704
  · exact MergedCutProfiles.Batch592.valid23705
theorem numericValid3887 : retention3887.NumericValid := by decide +kernel
def certificate3887 : RatCutBinCertificate := ⟨⟨retention3887,(365552146933234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(518833873893654641/250000000000000000)⟩,(39994846106634309/40000000000000000),(51466182604738877/125000000000000000),(8916219607998531/40000000000000000),(42837268523649071/250000000000000000)⟩
theorem valid3887 : certificate3887.Valid := by decide +kernel
theorem sound3887 : certificate3887.Sound := rat_cut_bin_certificate_sound certificate3887 profilesValid3887 numericValid3887 valid3887

def certificates : List RatCutBinCertificate := [certificate3876,certificate3877,certificate3878,certificate3879,certificate3880,certificate3881,certificate3882,certificate3883,certificate3884,certificate3885,certificate3886,certificate3887]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3876,List.forall_mem_cons.mpr ⟨sound3877,List.forall_mem_cons.mpr ⟨sound3878,List.forall_mem_cons.mpr ⟨sound3879,List.forall_mem_cons.mpr ⟨sound3880,List.forall_mem_cons.mpr ⟨sound3881,List.forall_mem_cons.mpr ⟨sound3882,List.forall_mem_cons.mpr ⟨sound3883,List.forall_mem_cons.mpr ⟨sound3884,List.forall_mem_cons.mpr ⟨sound3885,List.forall_mem_cons.mpr ⟨sound3886,List.forall_mem_cons.mpr ⟨sound3887,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch323
