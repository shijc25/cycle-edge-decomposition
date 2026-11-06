import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch242
import Cycle12.MergedCutProfiles.Batch243
import Cycle12.MergedCutProfiles.Batch244

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch125

def retention1500 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(5704306088361194678/11440819367386345185),(352989238141163037/62500000000000000),(21/20),(554256906415693930512063186346132835831/564782781025860859200000000000000000000),false,MergedCutProfiles.Batch242.profile9699,(fun _ => MergedCutProfiles.Batch242.profile9699)⟩
theorem profilesValid1500 : retention1500.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9699
theorem numericValid1500 : retention1500.NumericValid := by decide +kernel
def certificate1500 : RatCutBinCertificate := ⟨⟨retention1500,(667721499526796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(236876688460977421/250000000000000000)⟩,(988628179305402093/1000000000000000000),(104642230559210299/250000000000000000),(108446451570068341/500000000000000000),(167783195646357267/1000000000000000000)⟩
theorem valid1500 : certificate1500.Valid := by decide +kernel
theorem sound1500 : certificate1500.Sound := rat_cut_bin_certificate_sound certificate1500 profilesValid1500 numericValid1500 valid1500

def retention1501 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1/2),(2852153044180597339/500000000000000000),(21/20),(2234096121315722519035218810796965924959/2281722435344477871200000000000000000000),false,MergedCutProfiles.Batch242.profile9696,(fun _ => MergedCutProfiles.Batch242.profile9696)⟩
theorem profilesValid1501 : retention1501.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9696
theorem numericValid1501 : retention1501.NumericValid := by decide +kernel
def certificate1501 : RatCutBinCertificate := ⟨⟨retention1501,(667721499526796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(472635439748162841/500000000000000000)⟩,(988628179305402093/1000000000000000000),(419558974439045817/1000000000000000000),(108015923078917933/500000000000000000),(41748485170700441/250000000000000000)⟩
theorem valid1501 : certificate1501.Valid := by decide +kernel
theorem sound1501 : certificate1501.Sound := rat_cut_bin_certificate_sound certificate1501 profilesValid1501 numericValid1501 valid1501

def retention1502 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(357976889543710463/3795387479085849213),(217854935891653033/250000000000000000),(53/20),(613676341110461146233/320000000000000000000),true,MergedCutProfiles.Batch242.profile9700,![MergedCutProfiles.Batch242.profile9700,MergedCutProfiles.Batch242.profile9701,MergedCutProfiles.Batch242.profile9702,MergedCutProfiles.Batch242.profile9703,MergedCutProfiles.Batch242.profile9704,MergedCutProfiles.Batch242.profile9705,MergedCutProfiles.Batch242.profile9706,MergedCutProfiles.Batch242.profile9707,MergedCutProfiles.Batch242.profile9708,MergedCutProfiles.Batch242.profile9709,MergedCutProfiles.Batch242.profile9710,MergedCutProfiles.Batch242.profile9711,MergedCutProfiles.Batch242.profile9712,MergedCutProfiles.Batch242.profile9713,MergedCutProfiles.Batch242.profile9714,MergedCutProfiles.Batch242.profile9715]⟩
theorem profilesValid1502 : retention1502.ProfilesValid := by
  change ∀ j : Fin 16, (retention1502.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch242.valid9700
  · exact MergedCutProfiles.Batch242.valid9701
  · exact MergedCutProfiles.Batch242.valid9702
  · exact MergedCutProfiles.Batch242.valid9703
  · exact MergedCutProfiles.Batch242.valid9704
  · exact MergedCutProfiles.Batch242.valid9705
  · exact MergedCutProfiles.Batch242.valid9706
  · exact MergedCutProfiles.Batch242.valid9707
  · exact MergedCutProfiles.Batch242.valid9708
  · exact MergedCutProfiles.Batch242.valid9709
  · exact MergedCutProfiles.Batch242.valid9710
  · exact MergedCutProfiles.Batch242.valid9711
  · exact MergedCutProfiles.Batch242.valid9712
  · exact MergedCutProfiles.Batch242.valid9713
  · exact MergedCutProfiles.Batch242.valid9714
  · exact MergedCutProfiles.Batch242.valid9715
theorem numericValid1502 : retention1502.NumericValid := by decide +kernel
def certificate1502 : RatCutBinCertificate := ⟨⟨retention1502,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(1842527641721787049/1000000000000000000)⟩,(495004239113238793/500000000000000000),(171943245076226929/500000000000000000),(144513576952148711/500000000000000000),(152584806360523731/1000000000000000000)⟩
theorem valid1502 : certificate1502.Valid := by decide +kernel
theorem sound1502 : certificate1502.Sound := rat_cut_bin_certificate_sound certificate1502 profilesValid1502 numericValid1502 valid1502

def retention1503 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(290032139930262236/1626594633893935377),(1073930668631131389/1000000000000000000),(43/20),(2155652384341887672333/1280000000000000000000),true,MergedCutProfiles.Batch242.profile9716,![MergedCutProfiles.Batch242.profile9716,MergedCutProfiles.Batch242.profile9717,MergedCutProfiles.Batch242.profile9718,MergedCutProfiles.Batch242.profile9719,MergedCutProfiles.Batch243.profile9720,MergedCutProfiles.Batch243.profile9721,MergedCutProfiles.Batch243.profile9722,MergedCutProfiles.Batch243.profile9723,MergedCutProfiles.Batch243.profile9724,MergedCutProfiles.Batch243.profile9725,MergedCutProfiles.Batch243.profile9726,MergedCutProfiles.Batch243.profile9727,MergedCutProfiles.Batch243.profile9728,MergedCutProfiles.Batch243.profile9729,MergedCutProfiles.Batch243.profile9730,MergedCutProfiles.Batch243.profile9731]⟩
theorem profilesValid1503 : retention1503.ProfilesValid := by
  change ∀ j : Fin 16, (retention1503.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch242.valid9716
  · exact MergedCutProfiles.Batch242.valid9717
  · exact MergedCutProfiles.Batch242.valid9718
  · exact MergedCutProfiles.Batch242.valid9719
  · exact MergedCutProfiles.Batch243.valid9720
  · exact MergedCutProfiles.Batch243.valid9721
  · exact MergedCutProfiles.Batch243.valid9722
  · exact MergedCutProfiles.Batch243.valid9723
  · exact MergedCutProfiles.Batch243.valid9724
  · exact MergedCutProfiles.Batch243.valid9725
  · exact MergedCutProfiles.Batch243.valid9726
  · exact MergedCutProfiles.Batch243.valid9727
  · exact MergedCutProfiles.Batch243.valid9728
  · exact MergedCutProfiles.Batch243.valid9729
  · exact MergedCutProfiles.Batch243.valid9730
  · exact MergedCutProfiles.Batch243.valid9731
theorem numericValid1503 : retention1503.NumericValid := by decide +kernel
def certificate1503 : RatCutBinCertificate := ⟨⟨retention1503,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(811541618830325067/500000000000000000)⟩,(495004239113238793/500000000000000000),(180593521531498667/500000000000000000),(270990538300235753/1000000000000000000),(152310483139758103/1000000000000000000)⟩
theorem valid1503 : certificate1503.Valid := by decide +kernel
theorem sound1503 : certificate1503.Sound := rat_cut_bin_certificate_sound certificate1503 profilesValid1503 numericValid1503 valid1503

def retention1504 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(4156072158967181219/11386162437257547639),(507556244877958913/250000000000000000),(27/20),(400197856946634092229/320000000000000000000),true,MergedCutProfiles.Batch243.profile9732,![MergedCutProfiles.Batch243.profile9732,MergedCutProfiles.Batch243.profile9733,MergedCutProfiles.Batch243.profile9734,MergedCutProfiles.Batch243.profile9735,MergedCutProfiles.Batch243.profile9736,MergedCutProfiles.Batch243.profile9737,MergedCutProfiles.Batch243.profile9738,MergedCutProfiles.Batch243.profile9739,MergedCutProfiles.Batch243.profile9740,MergedCutProfiles.Batch243.profile9741,MergedCutProfiles.Batch243.profile9742,MergedCutProfiles.Batch243.profile9743,MergedCutProfiles.Batch243.profile9744,MergedCutProfiles.Batch243.profile9745,MergedCutProfiles.Batch243.profile9746,MergedCutProfiles.Batch243.profile9747]⟩
theorem profilesValid1504 : retention1504.ProfilesValid := by
  change ∀ j : Fin 16, (retention1504.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch243.valid9732
  · exact MergedCutProfiles.Batch243.valid9733
  · exact MergedCutProfiles.Batch243.valid9734
  · exact MergedCutProfiles.Batch243.valid9735
  · exact MergedCutProfiles.Batch243.valid9736
  · exact MergedCutProfiles.Batch243.valid9737
  · exact MergedCutProfiles.Batch243.valid9738
  · exact MergedCutProfiles.Batch243.valid9739
  · exact MergedCutProfiles.Batch243.valid9740
  · exact MergedCutProfiles.Batch243.valid9741
  · exact MergedCutProfiles.Batch243.valid9742
  · exact MergedCutProfiles.Batch243.valid9743
  · exact MergedCutProfiles.Batch243.valid9744
  · exact MergedCutProfiles.Batch243.valid9745
  · exact MergedCutProfiles.Batch243.valid9746
  · exact MergedCutProfiles.Batch243.valid9747
theorem numericValid1504 : retention1504.NumericValid := by decide +kernel
def certificate1504 : RatCutBinCertificate := ⟨⟨retention1504,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(1212306076575106221/1000000000000000000)⟩,(495004239113238793/500000000000000000),(202174965487185489/500000000000000000),(229520295181412339/1000000000000000000),(153423324390231201/1000000000000000000)⟩
theorem valid1504 : certificate1504.Valid := by decide +kernel
theorem sound1504 : certificate1504.Sound := rat_cut_bin_certificate_sound certificate1504 profilesValid1504 numericValid1504 valid1504

def retention1505 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(5329879910259863506/11386162437257547639),(4156072158967181219/1000000000000000000),1,(259696777939614576179/256000000000000000000),true,MergedCutProfiles.Batch243.profile9748,![MergedCutProfiles.Batch243.profile9748,MergedCutProfiles.Batch243.profile9749,MergedCutProfiles.Batch243.profile9750,MergedCutProfiles.Batch243.profile9751,MergedCutProfiles.Batch243.profile9752,MergedCutProfiles.Batch243.profile9753,MergedCutProfiles.Batch243.profile9754,MergedCutProfiles.Batch243.profile9755,MergedCutProfiles.Batch243.profile9756,MergedCutProfiles.Batch243.profile9757,MergedCutProfiles.Batch243.profile9758,MergedCutProfiles.Batch243.profile9759,MergedCutProfiles.Batch244.profile9760,MergedCutProfiles.Batch244.profile9761,MergedCutProfiles.Batch244.profile9762,MergedCutProfiles.Batch244.profile9763]⟩
theorem profilesValid1505 : retention1505.ProfilesValid := by
  change ∀ j : Fin 16, (retention1505.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch243.valid9748
  · exact MergedCutProfiles.Batch243.valid9749
  · exact MergedCutProfiles.Batch243.valid9750
  · exact MergedCutProfiles.Batch243.valid9751
  · exact MergedCutProfiles.Batch243.valid9752
  · exact MergedCutProfiles.Batch243.valid9753
  · exact MergedCutProfiles.Batch243.valid9754
  · exact MergedCutProfiles.Batch243.valid9755
  · exact MergedCutProfiles.Batch243.valid9756
  · exact MergedCutProfiles.Batch243.valid9757
  · exact MergedCutProfiles.Batch243.valid9758
  · exact MergedCutProfiles.Batch243.valid9759
  · exact MergedCutProfiles.Batch244.valid9760
  · exact MergedCutProfiles.Batch244.valid9761
  · exact MergedCutProfiles.Batch244.valid9762
  · exact MergedCutProfiles.Batch244.valid9763
theorem numericValid1505 : retention1505.NumericValid := by decide +kernel
def certificate1505 : RatCutBinCertificate := ⟨⟨retention1505,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(493032427289784767/500000000000000000)⟩,(495004239113238793/500000000000000000),(441175472650564657/1000000000000000000),(24725589274878529/125000000000000000),(38968918215460419/250000000000000000)⟩
theorem valid1505 : certificate1505.Valid := by decide +kernel
theorem sound1505 : certificate1505.Sound := rat_cut_bin_certificate_sound certificate1505 profilesValid1505 numericValid1505 valid1505

def retention1506 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(5601757351509202651/11386162437257547639),(2664939955129931753/500000000000000000),(11/10),(134137989985062683689200030411645202189/133246997756496587650000000000000000000),false,MergedCutProfiles.Batch244.profile9764,(fun _ => MergedCutProfiles.Batch244.profile9764)⟩
theorem profilesValid1506 : retention1506.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9764
theorem numericValid1506 : retention1506.NumericValid := by decide +kernel
def certificate1506 : RatCutBinCertificate := ⟨⟨retention1506,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(195095167982356451/200000000000000000)⟩,(495004239113238793/500000000000000000),(434069536105377751/1000000000000000000),(101838516645088987/500000000000000000),(155174259661717027/1000000000000000000)⟩
theorem valid1506 : certificate1506.Valid := by decide +kernel
theorem sound1506 : certificate1506.Sound := rat_cut_bin_certificate_sound certificate1506 profilesValid1506 numericValid1506 valid1506

def retention1507 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(628641658336032742/1265129159695283071),(5601757351509202651/1000000000000000000),(11/10),(2238220400799566637733136426166778879399/2240702940603681060400000000000000000000),false,MergedCutProfiles.Batch244.profile9765,(fun _ => MergedCutProfiles.Batch244.profile9765)⟩
theorem profilesValid1507 : retention1507.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9765
theorem numericValid1507 : retention1507.NumericValid := by decide +kernel
def certificate1507 : RatCutBinCertificate := ⟨⟨retention1507,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(30240044177901563/31250000000000000)⟩,(495004239113238793/500000000000000000),(435505303677788669/1000000000000000000),(101240602751648369/500000000000000000),(154173716072169981/1000000000000000000)⟩
theorem valid1507 : certificate1507.Valid := by decide +kernel
theorem sound1507 : certificate1507.Sound := rat_cut_bin_certificate_sound certificate1507 profilesValid1507 numericValid1507 valid1507

def retention1508 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(1/2),(2828887462512147339/500000000000000000),(11/10),(62438415238098615744570297800197208231/62864165833603274200000000000000000000),false,MergedCutProfiles.Batch244.profile9766,(fun _ => MergedCutProfiles.Batch244.profile9766)⟩
theorem profilesValid1508 : retention1508.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9766
theorem numericValid1508 : retention1508.NumericValid := by decide +kernel
def certificate1508 : RatCutBinCertificate := ⟨⟨retention1508,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(481008423857244143/500000000000000000)⟩,(495004239113238793/500000000000000000),(437667348733581207/1000000000000000000),(401378793648659/2000000000000000),(152214477871390701/1000000000000000000)⟩
theorem valid1508 : certificate1508.Valid := by decide +kernel
theorem sound1508 : certificate1508.Sound := rat_cut_bin_certificate_sound certificate1508 profilesValid1508 numericValid1508 valid1508

def retention1509 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(1/2),64,1,(4086588511787060117865209394969471/4096000000000000000000000000000000),false,MergedCutProfiles.Batch244.profile9766,(fun _ => MergedCutProfiles.Batch244.profile9766)⟩
theorem profilesValid1509 : retention1509.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9766
theorem numericValid1509 : retention1509.NumericValid := by decide +kernel
def certificate1509 : RatCutBinCertificate := ⟨⟨retention1509,(1172245204598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(484666683281137477/500000000000000000)⟩,(495004239113238793/500000000000000000),(3109113965093461/7812500000000000),(235350652043028013/1000000000000000000),(222462141247374789/1000000000000000000)⟩
theorem valid1509 : certificate1509.Valid := by decide +kernel
theorem sound1509 : certificate1509.Sound := rat_cut_bin_certificate_sound certificate1509 profilesValid1509 numericValid1509 valid1509

def retention1510 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(1782290175648112364/3795387479085849213),(3416943893315611577/1000000000000000000),(6/5),(44944917773188909214834364667489188927/42711798666445144712500000000000000000),false,MergedCutProfiles.Batch244.profile9767,(fun _ => MergedCutProfiles.Batch244.profile9767)⟩
theorem profilesValid1510 : retention1510.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9767
theorem numericValid1510 : retention1510.NumericValid := by decide +kernel
def certificate1510 : RatCutBinCertificate := ⟨⟨retention1510,(1332090844598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(202717869813420689/200000000000000000)⟩,(988642204017253493/1000000000000000000),(391206505066391647/1000000000000000000),(120818363359103781/500000000000000000),(83549171485339559/500000000000000000)⟩
theorem valid1510 : certificate1510.Valid := by decide +kernel
theorem sound1510 : certificate1510.Sound := rat_cut_bin_certificate_sound certificate1510 profilesValid1510 numericValid1510 valid1510

def retention1511 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(5619614660401981129/11386162437257547639),(1336717631736084273/250000000000000000),(11/10),(134178640156990062513008834452035542591/133671763173608427300000000000000000000),false,MergedCutProfiles.Batch244.profile9768,(fun _ => MergedCutProfiles.Batch244.profile9768)⟩
theorem profilesValid1511 : retention1511.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9768
theorem numericValid1511 : retention1511.NumericValid := by decide +kernel
def certificate1511 : RatCutBinCertificate := ⟨⟨retention1511,(1332090844598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(242081291104594777/250000000000000000)⟩,(988642204017253493/1000000000000000000),(204746691189849601/500000000000000000),(224895777305251903/1000000000000000000),(85041869274038767/500000000000000000)⟩
theorem valid1511 : certificate1511.Valid := by decide +kernel
theorem sound1511 : certificate1511.Sound := rat_cut_bin_certificate_sound certificate1511 profilesValid1511 numericValid1511 valid1511

def certificates : List RatCutBinCertificate := [certificate1500,certificate1501,certificate1502,certificate1503,certificate1504,certificate1505,certificate1506,certificate1507,certificate1508,certificate1509,certificate1510,certificate1511]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1500,List.forall_mem_cons.mpr ⟨sound1501,List.forall_mem_cons.mpr ⟨sound1502,List.forall_mem_cons.mpr ⟨sound1503,List.forall_mem_cons.mpr ⟨sound1504,List.forall_mem_cons.mpr ⟨sound1505,List.forall_mem_cons.mpr ⟨sound1506,List.forall_mem_cons.mpr ⟨sound1507,List.forall_mem_cons.mpr ⟨sound1508,List.forall_mem_cons.mpr ⟨sound1509,List.forall_mem_cons.mpr ⟨sound1510,List.forall_mem_cons.mpr ⟨sound1511,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch125
