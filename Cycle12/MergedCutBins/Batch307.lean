import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch442
import Cycle12.MergedCutProfiles.Batch443
import Cycle12.MergedCutProfiles.Batch444
import Cycle12.MergedCutProfiles.Batch563

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch307

def retention3684 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(160000000000000000/60435757821562209223),(3834366140186863407/250000000000000000),1,(19787139310293557738167846908224743121/8764265463284259216000000000000000000),false,MergedCutProfiles.Batch563.profile22523,(fun _ => MergedCutProfiles.Batch563.profile22523)⟩
theorem profilesValid3684 : retention3684.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22523
theorem numericValid3684 : retention3684.NumericValid := by decide +kernel
def certificate3684 : RatCutBinCertificate := ⟨⟨retention3684,(439810641809740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(70538214799486071/31250000000000000)⟩,(199997981428628537/200000000000000000),(33333120646728431/1000000000000000000),(208655574216196663/250000000000000000),(1642222189531359029/1000000000000000000)⟩
theorem valid3684 : certificate3684.Valid := by decide +kernel
theorem sound3684 : certificate3684.Sound := rat_cut_bin_certificate_sound certificate3684 profilesValid3684 numericValid3684 valid3684

def retention3685 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid3685 : retention3685.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid3685 : retention3685.NumericValid := by decide +kernel
def certificate3685 : RatCutBinCertificate := ⟨⟨retention3685,(439810641809740929/250000000000000000),(1970684370264843/1000000000000000000),(7168225594558521301/1000000000000000000),(174054143986089853018667/1000000000000000000),(997050961587390997/1000000000000000000)⟩,(199997981428628537/200000000000000000),(37731412570891383/500000000000000000),(22605188431803499/31250000000000000),(710161896159244043/1000000000000000000)⟩
theorem valid3685 : certificate3685.Valid := by decide +kernel
theorem sound3685 : certificate3685.Sound := rat_cut_bin_certificate_sound certificate3685 profilesValid3685 numericValid3685 valid3685

def retention3686 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(732265170928795745/21011839773932265847217),(570997272193723913/1000000000000000000),4,(5032124604401565049974077419129248543/2283989088774895652000000000000000000),true,MergedCutProfiles.Batch563.profile22524,![MergedCutProfiles.Batch563.profile22524,MergedCutProfiles.Batch563.profile22525,MergedCutProfiles.Batch442.profile17692,MergedCutProfiles.Batch563.profile22526,MergedCutProfiles.Batch563.profile22526,MergedCutProfiles.Batch563.profile22527,MergedCutProfiles.Batch563.profile22527,MergedCutProfiles.Batch442.profile17693,MergedCutProfiles.Batch442.profile17694,MergedCutProfiles.Batch442.profile17694,MergedCutProfiles.Batch563.profile22528,MergedCutProfiles.Batch563.profile22528,MergedCutProfiles.Batch563.profile22528,MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17696]⟩
theorem profilesValid3686 : retention3686.ProfilesValid := by
  change ∀ j : Fin 16, (retention3686.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22524
  · exact MergedCutProfiles.Batch563.valid22525
  · exact MergedCutProfiles.Batch442.valid17692
  · exact MergedCutProfiles.Batch563.valid22526
  · exact MergedCutProfiles.Batch563.valid22526
  · exact MergedCutProfiles.Batch563.valid22527
  · exact MergedCutProfiles.Batch563.valid22527
  · exact MergedCutProfiles.Batch442.valid17693
  · exact MergedCutProfiles.Batch442.valid17694
  · exact MergedCutProfiles.Batch442.valid17694
  · exact MergedCutProfiles.Batch563.valid22528
  · exact MergedCutProfiles.Batch563.valid22528
  · exact MergedCutProfiles.Batch563.valid22528
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17696
theorem numericValid3686 : retention3686.NumericValid := by decide +kernel
def certificate3686 : RatCutBinCertificate := ⟨⟨retention3686,(1789785505215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(137561341007520119/62500000000000000)⟩,(199997661611752227/200000000000000000),(152973864345391213/250000000000000000),(43772633670806557/500000000000000000),(38818722085254819/1000000000000000000)⟩
theorem valid3686 : certificate3686.Valid := by decide +kernel
theorem sound3686 : certificate3686.Sound := rat_cut_bin_certificate_sound certificate3686 profilesValid3686 numericValid3686 valid3686

def retention3687 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(1316965689000000000/21011839773932265847217),(146453034185759149/200000000000000000),(39/10),(4893620971705403717/2048000000000000000),true,MergedCutProfiles.Batch563.profile22525,![MergedCutProfiles.Batch563.profile22525,MergedCutProfiles.Batch442.profile17692,MergedCutProfiles.Batch563.profile22527,MergedCutProfiles.Batch442.profile17693,MergedCutProfiles.Batch442.profile17694,MergedCutProfiles.Batch442.profile17694,MergedCutProfiles.Batch563.profile22528,MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17696,MergedCutProfiles.Batch442.profile17696,MergedCutProfiles.Batch442.profile17697,MergedCutProfiles.Batch442.profile17698,MergedCutProfiles.Batch442.profile17698,MergedCutProfiles.Batch563.profile22529,MergedCutProfiles.Batch563.profile22529,MergedCutProfiles.Batch442.profile17699]⟩
theorem profilesValid3687 : retention3687.ProfilesValid := by
  change ∀ j : Fin 16, (retention3687.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22525
  · exact MergedCutProfiles.Batch442.valid17692
  · exact MergedCutProfiles.Batch563.valid22527
  · exact MergedCutProfiles.Batch442.valid17693
  · exact MergedCutProfiles.Batch442.valid17694
  · exact MergedCutProfiles.Batch442.valid17694
  · exact MergedCutProfiles.Batch563.valid22528
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17696
  · exact MergedCutProfiles.Batch442.valid17696
  · exact MergedCutProfiles.Batch442.valid17697
  · exact MergedCutProfiles.Batch442.valid17698
  · exact MergedCutProfiles.Batch442.valid17698
  · exact MergedCutProfiles.Batch563.valid22529
  · exact MergedCutProfiles.Batch563.valid22529
  · exact MergedCutProfiles.Batch442.valid17699
theorem numericValid3687 : retention3687.NumericValid := by decide +kernel
def certificate3687 : RatCutBinCertificate := ⟨⟨retention3687,(1789785505215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(2387283276011210149/1000000000000000000)⟩,(199997661611752227/200000000000000000),(119521674097172709/250000000000000000),(42275702795570407/250000000000000000),(8523999629481419/100000000000000000)⟩
theorem valid3687 : certificate3687.Valid := by decide +kernel
theorem sound3687 : certificate3687.Sound := rat_cut_bin_certificate_sound certificate3687 profilesValid3687 numericValid3687 valid3687

def retention3688 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(18582958517881812593/21011839773932265847217),(1316965689/1000000000),(49/20),(21432247394729307902835302053401311/9145595062500000000000000000000000),true,MergedCutProfiles.Batch563.profile22529,![MergedCutProfiles.Batch563.profile22529,MergedCutProfiles.Batch442.profile17704,MergedCutProfiles.Batch442.profile17708,MergedCutProfiles.Batch442.profile17711,MergedCutProfiles.Batch563.profile22530,MergedCutProfiles.Batch442.profile17718,MergedCutProfiles.Batch443.profile17720,MergedCutProfiles.Batch443.profile17722,MergedCutProfiles.Batch443.profile17723,MergedCutProfiles.Batch563.profile22531,MergedCutProfiles.Batch563.profile22532,MergedCutProfiles.Batch563.profile22533,MergedCutProfiles.Batch563.profile22534,MergedCutProfiles.Batch443.profile17725,MergedCutProfiles.Batch563.profile22535,MergedCutProfiles.Batch563.profile22536]⟩
theorem profilesValid3688 : retention3688.ProfilesValid := by
  change ∀ j : Fin 16, (retention3688.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22529
  · exact MergedCutProfiles.Batch442.valid17704
  · exact MergedCutProfiles.Batch442.valid17708
  · exact MergedCutProfiles.Batch442.valid17711
  · exact MergedCutProfiles.Batch563.valid22530
  · exact MergedCutProfiles.Batch442.valid17718
  · exact MergedCutProfiles.Batch443.valid17720
  · exact MergedCutProfiles.Batch443.valid17722
  · exact MergedCutProfiles.Batch443.valid17723
  · exact MergedCutProfiles.Batch563.valid22531
  · exact MergedCutProfiles.Batch563.valid22532
  · exact MergedCutProfiles.Batch563.valid22533
  · exact MergedCutProfiles.Batch563.valid22534
  · exact MergedCutProfiles.Batch443.valid17725
  · exact MergedCutProfiles.Batch563.valid22535
  · exact MergedCutProfiles.Batch563.valid22536
theorem numericValid3688 : retention3688.NumericValid := by decide +kernel
def certificate3688 : RatCutBinCertificate := ⟨⟨retention3688,(1789785505215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(2342080746127680381/1000000000000000000)⟩,(199997661611752227/200000000000000000),(349423812477188351/1000000000000000000),(141580858871329703/500000000000000000),(104408862829873997/500000000000000000)⟩
theorem valid3688 : certificate3688.Valid := by decide +kernel
theorem sound3688 : certificate3688.Sound := rat_cut_bin_certificate_sound certificate3688 profilesValid3688 numericValid3688 valid3688

def retention3689 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(64000000000000000000/21011839773932265847217),(18582958517881812593/1000000000000000000),1,(168609745479265935321495902641026650587/74331834071527250372000000000000000000),false,MergedCutProfiles.Batch563.profile22537,(fun _ => MergedCutProfiles.Batch563.profile22537)⟩
theorem profilesValid3689 : retention3689.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22537
theorem numericValid3689 : retention3689.NumericValid := by decide +kernel
def certificate3689 : RatCutBinCertificate := ⟨⟨retention3689,(1789785505215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(2267779293998540071/1000000000000000000)⟩,(199997661611752227/200000000000000000),(48790882874498179/250000000000000000),(48562097212939913/100000000000000000),(981491257182308289/1000000000000000000)⟩
theorem valid3689 : certificate3689.Valid := by decide +kernel
theorem sound3689 : certificate3689.Sound := rat_cut_bin_certificate_sound certificate3689 profilesValid3689 numericValid3689 valid3689

def retention3690 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(1/2),64,1,(10214758165775650715803726264123871679/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch443.profile17741,(fun _ => MergedCutProfiles.Batch443.profile17741)⟩
theorem profilesValid3690 : retention3690.ProfilesValid := by
  exact MergedCutProfiles.Batch443.valid17741
theorem numericValid3690 : retention3690.NumericValid := by decide +kernel
def certificate3690 : RatCutBinCertificate := ⟨⟨retention3690,(1789785505215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(996975979929476533/1000000000000000000)⟩,(199997661611752227/200000000000000000),(423527768472656327/1000000000000000000),(1660965185914059/7812500000000000),(208706942283825789/1000000000000000000)⟩
theorem valid3690 : certificate3690.Valid := by decide +kernel
theorem sound3690 : certificate3690.Sound := rat_cut_bin_certificate_sound certificate3690 profilesValid3690 numericValid3690 valid3690

def retention3691 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(64000000000000000000/21011839773932265847217),(15519521894573462301/1000000000000000000),1,(27981958051224929947261468227957715567/12415617515658769840800000000000000000),false,MergedCutProfiles.Batch563.profile22537,(fun _ => MergedCutProfiles.Batch563.profile22537)⟩
theorem profilesValid3691 : retention3691.ProfilesValid := by
  exact MergedCutProfiles.Batch563.valid22537
theorem numericValid3691 : retention3691.NumericValid := by decide +kernel
def certificate3691 : RatCutBinCertificate := ⟨⟨retention3691,(1760743341215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(8801644612767303/3906250000000000)⟩,(999988497779418533/1000000000000000000),(519194491772499/15625000000000000),(834922915212477637/1000000000000000000),(821370125450168729/500000000000000000)⟩
theorem valid3691 : certificate3691.Valid := by decide +kernel
theorem sound3691 : certificate3691.Sound := rat_cut_bin_certificate_sound certificate3691 profilesValid3691 numericValid3691 valid3691

def retention3692 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(1/2),64,1,(10214758165775650715803726264123871679/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch443.profile17741,(fun _ => MergedCutProfiles.Batch443.profile17741)⟩
theorem profilesValid3692 : retention3692.ProfilesValid := by
  exact MergedCutProfiles.Batch443.valid17741
theorem numericValid3692 : retention3692.NumericValid := by decide +kernel
def certificate3692 : RatCutBinCertificate := ⟨⟨retention3692,(1760743341215187203/1000000000000000000),(90635594743493/40000000000000000),(3627439337388246101/500000000000000000),(4774277875570401094503/31250000000000000),(996985050562926751/1000000000000000000)⟩,(999988497779418533/1000000000000000000),(75097451356670751/1000000000000000000),(90531804222228577/125000000000000000),(710986789970032229/1000000000000000000)⟩
theorem valid3692 : certificate3692.Valid := by decide +kernel
theorem sound3692 : certificate3692.Sound := rat_cut_bin_certificate_sound certificate3692 profilesValid3692 numericValid3692 valid3692

def retention3693 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(638222505226341105/18426399074305736771618),(36110906760805059/62500000000000000),4,(5126778808963740662029529034276085967/2311098032691523776000000000000000000),true,MergedCutProfiles.Batch563.profile22538,![MergedCutProfiles.Batch563.profile22538,MergedCutProfiles.Batch563.profile22539,MergedCutProfiles.Batch563.profile22540,MergedCutProfiles.Batch443.profile17743,MergedCutProfiles.Batch443.profile17743,MergedCutProfiles.Batch563.profile22541,MergedCutProfiles.Batch563.profile22541,MergedCutProfiles.Batch443.profile17744,MergedCutProfiles.Batch563.profile22542,MergedCutProfiles.Batch563.profile22542,MergedCutProfiles.Batch563.profile22542,MergedCutProfiles.Batch443.profile17745,MergedCutProfiles.Batch443.profile17745,MergedCutProfiles.Batch563.profile22543,MergedCutProfiles.Batch563.profile22543,MergedCutProfiles.Batch443.profile17746]⟩
theorem profilesValid3693 : retention3693.ProfilesValid := by
  change ∀ j : Fin 16, (retention3693.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22538
  · exact MergedCutProfiles.Batch563.valid22539
  · exact MergedCutProfiles.Batch563.valid22540
  · exact MergedCutProfiles.Batch443.valid17743
  · exact MergedCutProfiles.Batch443.valid17743
  · exact MergedCutProfiles.Batch563.valid22541
  · exact MergedCutProfiles.Batch563.valid22541
  · exact MergedCutProfiles.Batch443.valid17744
  · exact MergedCutProfiles.Batch563.valid22542
  · exact MergedCutProfiles.Batch563.valid22542
  · exact MergedCutProfiles.Batch563.valid22542
  · exact MergedCutProfiles.Batch443.valid17745
  · exact MergedCutProfiles.Batch443.valid17745
  · exact MergedCutProfiles.Batch563.valid22543
  · exact MergedCutProfiles.Batch563.valid22543
  · exact MergedCutProfiles.Batch443.valid17746
theorem numericValid3693 : retention3693.NumericValid := by decide +kernel
def certificate3693 : RatCutBinCertificate := ⟨⟨retention3693,(1795108273963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(2215789960039556377/1000000000000000000)⟩,(499993356200043421/500000000000000000),(150464259922537251/250000000000000000),(46279436123704811/500000000000000000),(20679336508493061/500000000000000000)⟩
theorem valid3693 : certificate3693.Valid := by decide +kernel
theorem sound3693 : certificate3693.Sound := rat_cut_bin_certificate_sound certificate3693 profilesValid3693 numericValid3693 valid3693

def retention3694 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(8925451500000000/126208212837710525833),(127644501045268221/200000000000000000),4,(29701611769561089037/12800000000000000000),true,MergedCutProfiles.Batch563.profile22539,![MergedCutProfiles.Batch563.profile22539,MergedCutProfiles.Batch443.profile17743,MergedCutProfiles.Batch563.profile22541,MergedCutProfiles.Batch443.profile17744,MergedCutProfiles.Batch563.profile22542,MergedCutProfiles.Batch443.profile17745,MergedCutProfiles.Batch563.profile22543,MergedCutProfiles.Batch443.profile17746,MergedCutProfiles.Batch443.profile17746,MergedCutProfiles.Batch443.profile17747,MergedCutProfiles.Batch443.profile17748,MergedCutProfiles.Batch443.profile17748,MergedCutProfiles.Batch443.profile17749,MergedCutProfiles.Batch563.profile22544,MergedCutProfiles.Batch563.profile22544,MergedCutProfiles.Batch443.profile17750]⟩
theorem profilesValid3694 : retention3694.ProfilesValid := by
  change ∀ j : Fin 16, (retention3694.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch563.valid22539
  · exact MergedCutProfiles.Batch443.valid17743
  · exact MergedCutProfiles.Batch563.valid22541
  · exact MergedCutProfiles.Batch443.valid17744
  · exact MergedCutProfiles.Batch563.valid22542
  · exact MergedCutProfiles.Batch443.valid17745
  · exact MergedCutProfiles.Batch563.valid22543
  · exact MergedCutProfiles.Batch443.valid17746
  · exact MergedCutProfiles.Batch443.valid17746
  · exact MergedCutProfiles.Batch443.valid17747
  · exact MergedCutProfiles.Batch443.valid17748
  · exact MergedCutProfiles.Batch443.valid17748
  · exact MergedCutProfiles.Batch443.valid17749
  · exact MergedCutProfiles.Batch563.valid22544
  · exact MergedCutProfiles.Batch563.valid22544
  · exact MergedCutProfiles.Batch443.valid17750
theorem numericValid3694 : retention3694.NumericValid := by decide +kernel
def certificate3694 : RatCutBinCertificate := ⟨⟨retention3694,(1795108273963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(579474518070150073/250000000000000000)⟩,(499993356200043421/500000000000000000),(537818900604489317/1000000000000000000),(128607846139093683/1000000000000000000),(60737206412504293/1000000000000000000)⟩
theorem valid3694 : certificate3694.Valid := by decide +kernel
theorem sound3694 : certificate3694.Sound := rat_cut_bin_certificate_sound certificate3694 profilesValid3694 numericValid3694 valid3694

def retention3695 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(10146447812434543091/18426399074305736771618),(1303115919/1000000000),(49/20),(9389115550036126149/4000000000000000000),true,MergedCutProfiles.Batch443.profile17746,![MergedCutProfiles.Batch443.profile17746,MergedCutProfiles.Batch563.profile22544,MergedCutProfiles.Batch443.profile17753,MergedCutProfiles.Batch443.profile17757,MergedCutProfiles.Batch563.profile22545,MergedCutProfiles.Batch444.profile17761,MergedCutProfiles.Batch563.profile22546,MergedCutProfiles.Batch444.profile17764,MergedCutProfiles.Batch563.profile22547,MergedCutProfiles.Batch563.profile22548,MergedCutProfiles.Batch563.profile22549,MergedCutProfiles.Batch563.profile22550,MergedCutProfiles.Batch444.profile17769,MergedCutProfiles.Batch563.profile22551,MergedCutProfiles.Batch563.profile22552,MergedCutProfiles.Batch563.profile22553]⟩
theorem profilesValid3695 : retention3695.ProfilesValid := by
  change ∀ j : Fin 16, (retention3695.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch443.valid17746
  · exact MergedCutProfiles.Batch563.valid22544
  · exact MergedCutProfiles.Batch443.valid17753
  · exact MergedCutProfiles.Batch443.valid17757
  · exact MergedCutProfiles.Batch563.valid22545
  · exact MergedCutProfiles.Batch444.valid17761
  · exact MergedCutProfiles.Batch563.valid22546
  · exact MergedCutProfiles.Batch444.valid17764
  · exact MergedCutProfiles.Batch563.valid22547
  · exact MergedCutProfiles.Batch563.valid22548
  · exact MergedCutProfiles.Batch563.valid22549
  · exact MergedCutProfiles.Batch563.valid22550
  · exact MergedCutProfiles.Batch444.valid17769
  · exact MergedCutProfiles.Batch563.valid22551
  · exact MergedCutProfiles.Batch563.valid22552
  · exact MergedCutProfiles.Batch563.valid22553
theorem numericValid3695 : retention3695.NumericValid := by decide +kernel
def certificate3695 : RatCutBinCertificate := ⟨⟨retention3695,(1795108273963217851/1000000000000000000),(1291114465089419/500000000000000000),(3649407075351135127/500000000000000000),(67395196350995630792803/500000000000000000),(469144584968270173/200000000000000000)⟩,(499993356200043421/500000000000000000),(175301615538218007/500000000000000000),(140961888601769983/500000000000000000),(41529747471245629/200000000000000000)⟩
theorem valid3695 : certificate3695.Valid := by decide +kernel
theorem sound3695 : certificate3695.Sound := rat_cut_bin_certificate_sound certificate3695 profilesValid3695 numericValid3695 valid3695

def certificates : List RatCutBinCertificate := [certificate3684,certificate3685,certificate3686,certificate3687,certificate3688,certificate3689,certificate3690,certificate3691,certificate3692,certificate3693,certificate3694,certificate3695]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3684,List.forall_mem_cons.mpr ⟨sound3685,List.forall_mem_cons.mpr ⟨sound3686,List.forall_mem_cons.mpr ⟨sound3687,List.forall_mem_cons.mpr ⟨sound3688,List.forall_mem_cons.mpr ⟨sound3689,List.forall_mem_cons.mpr ⟨sound3690,List.forall_mem_cons.mpr ⟨sound3691,List.forall_mem_cons.mpr ⟨sound3692,List.forall_mem_cons.mpr ⟨sound3693,List.forall_mem_cons.mpr ⟨sound3694,List.forall_mem_cons.mpr ⟨sound3695,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch307
