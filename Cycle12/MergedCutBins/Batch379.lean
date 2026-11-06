import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch037
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch327
import Cycle12.MergedCutProfiles.Batch328
import Cycle12.MergedCutProfiles.Batch460
import Cycle12.MergedCutProfiles.Batch461
import Cycle12.MergedCutProfiles.Batch591
import Cycle12.MergedCutProfiles.Batch592
import Cycle12.MergedCutProfiles.Batch652
import Cycle12.MergedCutProfiles.Batch653

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch379

def retention4548 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(27172454421089371296/8015987760575257207405),(540721661238383893/500000000000000000),(31/10),(254334805487338240199649517993004161551/108144332247676778600000000000000000000),false,MergedCutProfiles.Batch652.profile26114,(fun _ => MergedCutProfiles.Batch652.profile26114)⟩
theorem profilesValid4548 : retention4548.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26114
theorem numericValid4548 : retention4548.NumericValid := by decide +kernel
def certificate4548 : RatCutBinCertificate := ⟨⟨retention4548,(110184817168092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(145901781936981889/62500000000000000)⟩,(999976693188231963/1000000000000000000),(782066378187665963/1000000000000000000),(25689459327385463/1000000000000000000),(15796467640286479/1000000000000000000)⟩
theorem valid4548 : certificate4548.Valid := by decide +kernel
theorem sound4548 : certificate4548.Sound := rat_cut_bin_certificate_sound certificate4548 profilesValid4548 numericValid4548 valid4548

def retention4549 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/40),(849139200659042853/31250000000000000),(21/20),(1480429635445591120726397919880412209751/679311360527234282400000000000000000000),false,MergedCutProfiles.Batch652.profile26115,(fun _ => MergedCutProfiles.Batch652.profile26115)⟩
theorem profilesValid4549 : retention4549.ProfilesValid := by
  exact MergedCutProfiles.Batch652.valid26115
theorem numericValid4549 : retention4549.NumericValid := by decide +kernel
def certificate4549 : RatCutBinCertificate := ⟨⟨retention4549,(110184817168092539/62500000000000000),(14531335098101001/500000000000000000),(2284646189452429893/250000000000000000),(73616648279811504845921/1000000000000000000),(1086711244949241993/500000000000000000)⟩,(999976693188231963/1000000000000000000),(677649163913762439/1000000000000000000),(29330105272387537/500000000000000000),(113206315696116841/1000000000000000000)⟩
theorem valid4549 : certificate4549.Valid := by decide +kernel
theorem sound4549 : certificate4549.Sound := rat_cut_bin_certificate_sound certificate4549 profilesValid4549 numericValid4549 valid4549

def retention4550 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(32725735448551384/369822667834612896403),(162008591329462297/250000000000000000),4,(379663866278175356842303640020803583/162008591329462297000000000000000000),true,MergedCutProfiles.Batch652.profile26116,![MergedCutProfiles.Batch652.profile26116,MergedCutProfiles.Batch652.profile26117,MergedCutProfiles.Batch652.profile26118,MergedCutProfiles.Batch652.profile26119,MergedCutProfiles.Batch591.profile23674,MergedCutProfiles.Batch653.profile26120,MergedCutProfiles.Batch653.profile26121,MergedCutProfiles.Batch653.profile26122,MergedCutProfiles.Batch591.profile23675,MergedCutProfiles.Batch653.profile26123,MergedCutProfiles.Batch653.profile26123,MergedCutProfiles.Batch653.profile26124,MergedCutProfiles.Batch591.profile23676,MergedCutProfiles.Batch653.profile26125,MergedCutProfiles.Batch653.profile26125,MergedCutProfiles.Batch653.profile26126]⟩
theorem profilesValid4550 : retention4550.ProfilesValid := by
  change ∀ j : Fin 16, (retention4550.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch652.valid26116
  · exact MergedCutProfiles.Batch652.valid26117
  · exact MergedCutProfiles.Batch652.valid26118
  · exact MergedCutProfiles.Batch652.valid26119
  · exact MergedCutProfiles.Batch591.valid23674
  · exact MergedCutProfiles.Batch653.valid26120
  · exact MergedCutProfiles.Batch653.valid26121
  · exact MergedCutProfiles.Batch653.valid26122
  · exact MergedCutProfiles.Batch591.valid23675
  · exact MergedCutProfiles.Batch653.valid26123
  · exact MergedCutProfiles.Batch653.valid26123
  · exact MergedCutProfiles.Batch653.valid26124
  · exact MergedCutProfiles.Batch591.valid23676
  · exact MergedCutProfiles.Batch653.valid26125
  · exact MergedCutProfiles.Batch653.valid26125
  · exact MergedCutProfiles.Batch653.valid26126
theorem numericValid4550 : retention4550.NumericValid := by decide +kernel
def certificate4550 : RatCutBinCertificate := ⟨⟨retention4550,(1924682053933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(463466888071694387/200000000000000000)⟩,(39998914565216147/40000000000000000),(476993196527460909/1000000000000000000),(10619438823420519/62500000000000000),(40225709896485803/500000000000000000)⟩
theorem valid4550 : certificate4550.Valid := by decide +kernel
theorem sound4550 : certificate4550.Sound := rat_cut_bin_certificate_sound certificate4550 profilesValid4550 numericValid4550 valid4550

def retention4551 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(63110864450000000/369822667834612896403),(4090716931068923/6250000000000000),4,(1536807557201439718936054549758616599/654514708971027680000000000000000000),true,MergedCutProfiles.Batch652.profile26117,![MergedCutProfiles.Batch652.profile26117,MergedCutProfiles.Batch652.profile26119,MergedCutProfiles.Batch653.profile26120,MergedCutProfiles.Batch653.profile26122,MergedCutProfiles.Batch591.profile23675,MergedCutProfiles.Batch653.profile26124,MergedCutProfiles.Batch591.profile23676,MergedCutProfiles.Batch653.profile26125,MergedCutProfiles.Batch591.profile23677,MergedCutProfiles.Batch460.profile18432,MergedCutProfiles.Batch591.profile23678,MergedCutProfiles.Batch653.profile26127,MergedCutProfiles.Batch591.profile23679,MergedCutProfiles.Batch592.profile23688,MergedCutProfiles.Batch592.profile23688,MergedCutProfiles.Batch592.profile23680]⟩
theorem profilesValid4551 : retention4551.ProfilesValid := by
  change ∀ j : Fin 16, (retention4551.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch652.valid26117
  · exact MergedCutProfiles.Batch652.valid26119
  · exact MergedCutProfiles.Batch653.valid26120
  · exact MergedCutProfiles.Batch653.valid26122
  · exact MergedCutProfiles.Batch591.valid23675
  · exact MergedCutProfiles.Batch653.valid26124
  · exact MergedCutProfiles.Batch591.valid23676
  · exact MergedCutProfiles.Batch653.valid26125
  · exact MergedCutProfiles.Batch591.valid23677
  · exact MergedCutProfiles.Batch460.valid18432
  · exact MergedCutProfiles.Batch591.valid23678
  · exact MergedCutProfiles.Batch653.valid26127
  · exact MergedCutProfiles.Batch591.valid23679
  · exact MergedCutProfiles.Batch592.valid23688
  · exact MergedCutProfiles.Batch592.valid23688
  · exact MergedCutProfiles.Batch592.valid23680
theorem numericValid4551 : retention4551.NumericValid := by decide +kernel
def certificate4551 : RatCutBinCertificate := ⟨⟨retention4551,(1924682053933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(2321865335427486573/1000000000000000000)⟩,(39998914565216147/40000000000000000),(473033872964490461/1000000000000000000),(86429192093804063/500000000000000000),(82126496496688637/1000000000000000000)⟩
theorem valid4551 : certificate4551.Valid := by decide +kernel
theorem sound4551 : certificate4551.Sound := rat_cut_bin_certificate_sound certificate4551 profilesValid4551 numericValid4551 valid4551

def retention4552 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(386002496371986583/369822667834612896403),(1262217289/1000000000),(5/2),(37596880881278177841/16000000000000000000),true,MergedCutProfiles.Batch653.profile26124,![MergedCutProfiles.Batch653.profile26124,MergedCutProfiles.Batch653.profile26127,MergedCutProfiles.Batch592.profile23681,MergedCutProfiles.Batch592.profile23684,MergedCutProfiles.Batch460.profile18434,MergedCutProfiles.Batch328.profile13124,MergedCutProfiles.Batch592.profile23689,MergedCutProfiles.Batch653.profile26128,MergedCutProfiles.Batch036.profile1468,MergedCutProfiles.Batch592.profile23690,MergedCutProfiles.Batch592.profile23691,MergedCutProfiles.Batch328.profile13125,MergedCutProfiles.Batch327.profile13112,MergedCutProfiles.Batch592.profile23693,MergedCutProfiles.Batch328.profile13139,MergedCutProfiles.Batch460.profile18438]⟩
theorem profilesValid4552 : retention4552.ProfilesValid := by
  change ∀ j : Fin 16, (retention4552.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch653.valid26124
  · exact MergedCutProfiles.Batch653.valid26127
  · exact MergedCutProfiles.Batch592.valid23681
  · exact MergedCutProfiles.Batch592.valid23684
  · exact MergedCutProfiles.Batch460.valid18434
  · exact MergedCutProfiles.Batch328.valid13124
  · exact MergedCutProfiles.Batch592.valid23689
  · exact MergedCutProfiles.Batch653.valid26128
  · exact MergedCutProfiles.Batch036.valid1468
  · exact MergedCutProfiles.Batch592.valid23690
  · exact MergedCutProfiles.Batch592.valid23691
  · exact MergedCutProfiles.Batch328.valid13125
  · exact MergedCutProfiles.Batch327.valid13112
  · exact MergedCutProfiles.Batch592.valid23693
  · exact MergedCutProfiles.Batch328.valid13139
  · exact MergedCutProfiles.Batch460.valid18438
theorem numericValid4552 : retention4552.NumericValid := by decide +kernel
def certificate4552 : RatCutBinCertificate := ⟨⟨retention4552,(1924682053933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(2333464186254679769/1000000000000000000)⟩,(39998914565216147/40000000000000000),(6511948800743527/20000000000000000),(309040298111706493/1000000000000000000),(222601170581426061/1000000000000000000)⟩
theorem valid4552 : certificate4552.Valid := by decide +kernel
theorem sound4552 : certificate4552.Sound := rat_cut_bin_certificate_sound certificate4552 profilesValid4552 numericValid4552 valid4552

def retention4553 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(3200000000000000000/369822667834612896403),(386002496371986583/50000000000000000),(11/10),(68722465589981579007903997745478306839/30880199709758926640000000000000000000),true,MergedCutProfiles.Batch460.profile18436,![MergedCutProfiles.Batch460.profile18436,MergedCutProfiles.Batch653.profile26129,MergedCutProfiles.Batch461.profile18447,MergedCutProfiles.Batch653.profile26130,MergedCutProfiles.Batch328.profile13151,MergedCutProfiles.Batch461.profile18450,MergedCutProfiles.Batch653.profile26131,MergedCutProfiles.Batch328.profile13123,MergedCutProfiles.Batch328.profile13135,MergedCutProfiles.Batch328.profile13143,MergedCutProfiles.Batch328.profile13144,MergedCutProfiles.Batch037.profile1505,MergedCutProfiles.Batch653.profile26132,MergedCutProfiles.Batch653.profile26133,MergedCutProfiles.Batch037.profile1494,MergedCutProfiles.Batch653.profile26134]⟩
theorem profilesValid4553 : retention4553.ProfilesValid := by
  change ∀ j : Fin 16, (retention4553.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch460.valid18436
  · exact MergedCutProfiles.Batch653.valid26129
  · exact MergedCutProfiles.Batch461.valid18447
  · exact MergedCutProfiles.Batch653.valid26130
  · exact MergedCutProfiles.Batch328.valid13151
  · exact MergedCutProfiles.Batch461.valid18450
  · exact MergedCutProfiles.Batch653.valid26131
  · exact MergedCutProfiles.Batch328.valid13123
  · exact MergedCutProfiles.Batch328.valid13135
  · exact MergedCutProfiles.Batch328.valid13143
  · exact MergedCutProfiles.Batch328.valid13144
  · exact MergedCutProfiles.Batch037.valid1505
  · exact MergedCutProfiles.Batch653.valid26132
  · exact MergedCutProfiles.Batch653.valid26133
  · exact MergedCutProfiles.Batch037.valid1494
  · exact MergedCutProfiles.Batch653.valid26134
theorem numericValid4553 : retention4553.NumericValid := by decide +kernel
def certificate4553 : RatCutBinCertificate := ⟨⟨retention4553,(1924682053933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(2218264070997037019/1000000000000000000)⟩,(39998914565216147/40000000000000000),(205005549504110931/1000000000000000000),(117464000680957211/250000000000000000),(765664383744962883/1000000000000000000)⟩
theorem valid4553 : certificate4553.Valid := by decide +kernel
theorem sound4553 : certificate4553.Sound := rat_cut_bin_certificate_sound certificate4553 profilesValid4553 numericValid4553 valid4553

def retention4554 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid4554 : retention4554.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid4554 : retention4554.NumericValid := by decide +kernel
def certificate4554 : RatCutBinCertificate := ⟨⟨retention4554,(1924682053933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(991019304603829257/1000000000000000000)⟩,(39998914565216147/40000000000000000),(405977194658532821/1000000000000000000),(114025088141727423/500000000000000000),(222549830112448223/1000000000000000000)⟩
theorem valid4554 : certificate4554.Valid := by decide +kernel
theorem sound4554 : certificate4554.Sound := rat_cut_bin_certificate_sound certificate4554 profilesValid4554 numericValid4554 valid4554

def retention4555 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(3200000000000000000/369822667834612896403),(3882587359225456913/200000000000000000),1,(6922685163724071350704850526256659187/3106069887380365530400000000000000000),false,MergedCutProfiles.Batch653.profile26135,(fun _ => MergedCutProfiles.Batch653.profile26135)⟩
theorem profilesValid4555 : retention4555.ProfilesValid := by
  exact MergedCutProfiles.Batch653.valid26135
theorem numericValid4555 : retention4555.NumericValid := by decide +kernel
def certificate4555 : RatCutBinCertificate := ⟨⟨retention4555,(1798710765933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(2222651730964411367/1000000000000000000)⟩,(999974640186366723/1000000000000000000),(2516446425558783/100000000000000000),(429241796635115913/500000000000000000),(1712042851402424777/1000000000000000000)⟩
theorem valid4555 : certificate4555.Valid := by decide +kernel
theorem sound4555 : certificate4555.Sound := rat_cut_bin_certificate_sound certificate4555 profilesValid4555 numericValid4555 valid4555

def retention4556 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid4556 : retention4556.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid4556 : retention4556.NumericValid := by decide +kernel
def certificate4556 : RatCutBinCertificate := ⟨⟨retention4556,(1798710765933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(247861777842297711/250000000000000000)⟩,(999974640186366723/1000000000000000000),(56414345652016013/1000000000000000000),(771379689907830761/1000000000000000000),(376548055271184731/500000000000000000)⟩
theorem valid4556 : certificate4556.Valid := by decide +kernel
theorem sound4556 : certificate4556.Sound := rat_cut_bin_certificate_sound certificate4556 profilesValid4556 numericValid4556 valid4556

def retention4557 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(667654019596632153/7396453356692257928060),(132208716751808347/200000000000000000),4,(48700220456860333354482004398735047/20657611992470054218750000000000000),false,MergedCutProfiles.Batch653.profile26136,(fun _ => MergedCutProfiles.Batch653.profile26136)⟩
theorem profilesValid4557 : retention4557.ProfilesValid := by
  exact MergedCutProfiles.Batch653.valid26136
theorem numericValid4557 : retention4557.NumericValid := by decide +kernel
def certificate4557 : RatCutBinCertificate := ⟨⟨retention4557,(1769874921933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(291681589792740707/125000000000000000)⟩,(499987523369938537/500000000000000000),(10977694193830217/12500000000000000),(7736557677093179/1000000000000000000),(3697368319544831/1000000000000000000)⟩
theorem valid4557 : certificate4557.Valid := by decide +kernel
theorem sound4557 : certificate4557.Sound := rat_cut_bin_certificate_sound certificate4557 profilesValid4557 numericValid4557 valid4557

def retention4558 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(215281844252641897/1479290671338451585612),(667654019596632153/1000000000000000000),4,(6307919190145682497376751566221427303/2670616078386528612000000000000000000),false,MergedCutProfiles.Batch653.profile26137,(fun _ => MergedCutProfiles.Batch653.profile26137)⟩
theorem profilesValid4558 : retention4558.ProfilesValid := by
  exact MergedCutProfiles.Batch653.valid26137
theorem numericValid4558 : retention4558.NumericValid := by decide +kernel
def certificate4558 : RatCutBinCertificate := ⟨⟨retention4558,(1769874921933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(467585819458070757/200000000000000000)⟩,(499987523369938537/500000000000000000),(27312812243723521/31250000000000000),(8292788905079489/1000000000000000000),(994137537052187/250000000000000000)⟩
theorem valid4558 : certificate4558.Valid := by decide +kernel
theorem sound4558 : certificate4558.Sound := rat_cut_bin_certificate_sound certificate4558 profilesValid4558 numericValid4558 valid4558

def retention4559 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(5095704884916536831/1479290671338451585612),(215281844252641897/200000000000000000),(31/10),(40502311344733835878845055054110892671/17222547540211351760000000000000000000),false,MergedCutProfiles.Batch653.profile26138,(fun _ => MergedCutProfiles.Batch653.profile26138)⟩
theorem profilesValid4559 : retention4559.ProfilesValid := by
  exact MergedCutProfiles.Batch653.valid26138
theorem numericValid4559 : retention4559.NumericValid := by decide +kernel
def certificate4559 : RatCutBinCertificate := ⟨⟨retention4559,(1769874921933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(2333069790113291127/1000000000000000000)⟩,(499987523369938537/500000000000000000),(389891387108700299/500000000000000000),(1312707110563507/50000000000000000),(16122163958660399/1000000000000000000)⟩
theorem valid4559 : certificate4559.Valid := by decide +kernel
theorem sound4559 : certificate4559.Sound := rat_cut_bin_certificate_sound certificate4559 profilesValid4559 numericValid4559 valid4559

def certificates : List RatCutBinCertificate := [certificate4548,certificate4549,certificate4550,certificate4551,certificate4552,certificate4553,certificate4554,certificate4555,certificate4556,certificate4557,certificate4558,certificate4559]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4548,List.forall_mem_cons.mpr ⟨sound4549,List.forall_mem_cons.mpr ⟨sound4550,List.forall_mem_cons.mpr ⟨sound4551,List.forall_mem_cons.mpr ⟨sound4552,List.forall_mem_cons.mpr ⟨sound4553,List.forall_mem_cons.mpr ⟨sound4554,List.forall_mem_cons.mpr ⟨sound4555,List.forall_mem_cons.mpr ⟨sound4556,List.forall_mem_cons.mpr ⟨sound4557,List.forall_mem_cons.mpr ⟨sound4558,List.forall_mem_cons.mpr ⟨sound4559,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch379
