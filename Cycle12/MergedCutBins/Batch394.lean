import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch667
import Cycle12.MergedCutProfiles.Batch668

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch394

def retention4728 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(1/40),(4175258806770802869/500000000000000000),(6/5),(19062907025384779605637971998464573671/8698455847439172643750000000000000000),false,MergedCutProfiles.Batch667.profile26701,(fun _ => MergedCutProfiles.Batch667.profile26701)⟩
theorem profilesValid4728 : retention4728.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26701
theorem numericValid4728 : retention4728.NumericValid := by decide +kernel
def certificate4728 : RatCutBinCertificate := ⟨⟨retention4728,(1835562192458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(2178150588433550271/1000000000000000000)⟩,(999954835279595917/1000000000000000000),(69818921259037237/100000000000000000),(6371968232945461/125000000000000000),(78333689232588383/1000000000000000000)⟩
theorem valid4728 : certificate4728.Valid := by decide +kernel
theorem sound4728 : certificate4728.Sound := rat_cut_bin_certificate_sound certificate4728 profilesValid4728 numericValid4728 valid4728

def retention4729 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(592448003071932231/3380072921991454528517),(287512097470512127/500000000000000000),4,(71122980068496765847/32000000000000000000),true,MergedCutProfiles.Batch667.profile26702,![MergedCutProfiles.Batch667.profile26702,MergedCutProfiles.Batch667.profile26703,MergedCutProfiles.Batch667.profile26704,MergedCutProfiles.Batch667.profile26705,MergedCutProfiles.Batch667.profile26706,MergedCutProfiles.Batch667.profile26707,MergedCutProfiles.Batch667.profile26708,MergedCutProfiles.Batch667.profile26709,MergedCutProfiles.Batch667.profile26710,MergedCutProfiles.Batch667.profile26711,MergedCutProfiles.Batch667.profile26712,MergedCutProfiles.Batch667.profile26713,MergedCutProfiles.Batch667.profile26714,MergedCutProfiles.Batch667.profile26715,MergedCutProfiles.Batch667.profile26716,MergedCutProfiles.Batch667.profile26717]⟩
theorem profilesValid4729 : retention4729.ProfilesValid := by
  change ∀ j : Fin 16, (retention4729.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch667.valid26702
  · exact MergedCutProfiles.Batch667.valid26703
  · exact MergedCutProfiles.Batch667.valid26704
  · exact MergedCutProfiles.Batch667.valid26705
  · exact MergedCutProfiles.Batch667.valid26706
  · exact MergedCutProfiles.Batch667.valid26707
  · exact MergedCutProfiles.Batch667.valid26708
  · exact MergedCutProfiles.Batch667.valid26709
  · exact MergedCutProfiles.Batch667.valid26710
  · exact MergedCutProfiles.Batch667.valid26711
  · exact MergedCutProfiles.Batch667.valid26712
  · exact MergedCutProfiles.Batch667.valid26713
  · exact MergedCutProfiles.Batch667.valid26714
  · exact MergedCutProfiles.Batch667.valid26715
  · exact MergedCutProfiles.Batch667.valid26716
  · exact MergedCutProfiles.Batch667.valid26717
theorem numericValid4729 : retention4729.NumericValid := by decide +kernel
def certificate4729 : RatCutBinCertificate := ⟨⟨retention4729,(93978129830264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(2176461699472271171/1000000000000000000)⟩,(199990662410385847/200000000000000000),(717508819074446469/1000000000000000000),(44299749532572659/1000000000000000000),(19491793562314043/1000000000000000000)⟩
theorem valid4729 : certificate4729.Valid := by decide +kernel
theorem sound4729 : certificate4729.Sound := rat_cut_bin_certificate_sound certificate4729 profilesValid4729 numericValid4729 valid4729

def retention4730 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(1147349390000000000/3380072921991454528517),(592448003071932231/1000000000000000000),4,(577828846007894176871/256000000000000000000),true,MergedCutProfiles.Batch667.profile26703,![MergedCutProfiles.Batch667.profile26703,MergedCutProfiles.Batch667.profile26705,MergedCutProfiles.Batch667.profile26707,MergedCutProfiles.Batch667.profile26718,MergedCutProfiles.Batch667.profile26711,MergedCutProfiles.Batch667.profile26713,MergedCutProfiles.Batch667.profile26714,MergedCutProfiles.Batch667.profile26716,MergedCutProfiles.Batch667.profile26719,MergedCutProfiles.Batch668.profile26720,MergedCutProfiles.Batch668.profile26721,MergedCutProfiles.Batch668.profile26722,MergedCutProfiles.Batch668.profile26723,MergedCutProfiles.Batch668.profile26724,MergedCutProfiles.Batch668.profile26725,MergedCutProfiles.Batch668.profile26726]⟩
theorem profilesValid4730 : retention4730.ProfilesValid := by
  change ∀ j : Fin 16, (retention4730.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch667.valid26703
  · exact MergedCutProfiles.Batch667.valid26705
  · exact MergedCutProfiles.Batch667.valid26707
  · exact MergedCutProfiles.Batch667.valid26718
  · exact MergedCutProfiles.Batch667.valid26711
  · exact MergedCutProfiles.Batch667.valid26713
  · exact MergedCutProfiles.Batch667.valid26714
  · exact MergedCutProfiles.Batch667.valid26716
  · exact MergedCutProfiles.Batch667.valid26719
  · exact MergedCutProfiles.Batch668.valid26720
  · exact MergedCutProfiles.Batch668.valid26721
  · exact MergedCutProfiles.Batch668.valid26722
  · exact MergedCutProfiles.Batch668.valid26723
  · exact MergedCutProfiles.Batch668.valid26724
  · exact MergedCutProfiles.Batch668.valid26725
  · exact MergedCutProfiles.Batch668.valid26726
theorem numericValid4730 : retention4730.NumericValid := by decide +kernel
def certificate4730 : RatCutBinCertificate := ⟨⟨retention4730,(93978129830264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(1105506251559714741/500000000000000000)⟩,(199990662410385847/200000000000000000),(346130614327616887/500000000000000000),(53130701144913431/1000000000000000000),(11906147520356631/500000000000000000)⟩
theorem valid4730 : certificate4730.Valid := by decide +kernel
theorem sound4730 : certificate4730.Sound := rat_cut_bin_certificate_sound certificate4730 profilesValid4730 numericValid4730 valid4730

def retention4731 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(120430181327903745/146959692260498022979),(114734939/100000000),(11/4),(2736904741757077941167782519566508639/1147349390000000000000000000000000000),true,MergedCutProfiles.Batch668.profile26727,![MergedCutProfiles.Batch668.profile26727,MergedCutProfiles.Batch667.profile26710,MergedCutProfiles.Batch667.profile26715,MergedCutProfiles.Batch668.profile26720,MergedCutProfiles.Batch668.profile26722,MergedCutProfiles.Batch668.profile26724,MergedCutProfiles.Batch668.profile26728,MergedCutProfiles.Batch668.profile26729,MergedCutProfiles.Batch668.profile26730,MergedCutProfiles.Batch668.profile26731,MergedCutProfiles.Batch668.profile26732,MergedCutProfiles.Batch668.profile26733,MergedCutProfiles.Batch668.profile26734,MergedCutProfiles.Batch668.profile26735,MergedCutProfiles.Batch668.profile26736,MergedCutProfiles.Batch668.profile26737]⟩
theorem profilesValid4731 : retention4731.ProfilesValid := by
  change ∀ j : Fin 16, (retention4731.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch668.valid26727
  · exact MergedCutProfiles.Batch667.valid26710
  · exact MergedCutProfiles.Batch667.valid26715
  · exact MergedCutProfiles.Batch668.valid26720
  · exact MergedCutProfiles.Batch668.valid26722
  · exact MergedCutProfiles.Batch668.valid26724
  · exact MergedCutProfiles.Batch668.valid26728
  · exact MergedCutProfiles.Batch668.valid26729
  · exact MergedCutProfiles.Batch668.valid26730
  · exact MergedCutProfiles.Batch668.valid26731
  · exact MergedCutProfiles.Batch668.valid26732
  · exact MergedCutProfiles.Batch668.valid26733
  · exact MergedCutProfiles.Batch668.valid26734
  · exact MergedCutProfiles.Batch668.valid26735
  · exact MergedCutProfiles.Batch668.valid26736
  · exact MergedCutProfiles.Batch668.valid26737
theorem numericValid4731 : retention4731.NumericValid := by decide +kernel
def certificate4731 : RatCutBinCertificate := ⟨⟨retention4731,(93978129830264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(1176849954385310429/500000000000000000)⟩,(199990662410385847/200000000000000000),(439856111001549957/1000000000000000000),(198886323107266499/1000000000000000000),(133895095360138607/1000000000000000000)⟩
theorem valid4731 : certificate4731.Valid := by decide +kernel
theorem sound4731 : certificate4731.Sound := rat_cut_bin_certificate_sound certificate4731 profilesValid4731 numericValid4731 valid4731

def retention4732 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(64000000000000000000/3380072921991454528517),(553978834108357227/200000000000000000),(31/20),(140582699964378277841/64000000000000000000),true,MergedCutProfiles.Batch668.profile26738,![MergedCutProfiles.Batch668.profile26738,MergedCutProfiles.Batch668.profile26739,MergedCutProfiles.Batch668.profile26740,MergedCutProfiles.Batch668.profile26741,MergedCutProfiles.Batch668.profile26742,MergedCutProfiles.Batch668.profile26743,MergedCutProfiles.Batch668.profile26744,MergedCutProfiles.Batch668.profile26745,MergedCutProfiles.Batch668.profile26746,MergedCutProfiles.Batch668.profile26747,MergedCutProfiles.Batch668.profile26748,MergedCutProfiles.Batch668.profile26749,MergedCutProfiles.Batch668.profile26750,MergedCutProfiles.Batch668.profile26751,MergedCutProfiles.Batch668.profile26752,MergedCutProfiles.Batch668.profile26753]⟩
theorem profilesValid4732 : retention4732.ProfilesValid := by
  change ∀ j : Fin 16, (retention4732.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch668.valid26738
  · exact MergedCutProfiles.Batch668.valid26739
  · exact MergedCutProfiles.Batch668.valid26740
  · exact MergedCutProfiles.Batch668.valid26741
  · exact MergedCutProfiles.Batch668.valid26742
  · exact MergedCutProfiles.Batch668.valid26743
  · exact MergedCutProfiles.Batch668.valid26744
  · exact MergedCutProfiles.Batch668.valid26745
  · exact MergedCutProfiles.Batch668.valid26746
  · exact MergedCutProfiles.Batch668.valid26747
  · exact MergedCutProfiles.Batch668.valid26748
  · exact MergedCutProfiles.Batch668.valid26749
  · exact MergedCutProfiles.Batch668.valid26750
  · exact MergedCutProfiles.Batch668.valid26751
  · exact MergedCutProfiles.Batch668.valid26752
  · exact MergedCutProfiles.Batch668.valid26753
theorem numericValid4732 : retention4732.NumericValid := by decide +kernel
def certificate4732 : RatCutBinCertificate := ⟨⟨retention4732,(93978129830264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(544682191315805999/250000000000000000)⟩,(199990662410385847/200000000000000000),(166499819801103959/500000000000000000),(300819974901291647/1000000000000000000),(159266486646526411/500000000000000000)⟩
theorem valid4732 : certificate4732.Valid := by decide +kernel
theorem sound4732 : certificate4732.Sound := rat_cut_bin_certificate_sound certificate4732 profilesValid4732 numericValid4732 valid4732

def retention4733 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(1/2),64,1,(255382853441000253850307765633342734479/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch668.profile26754,(fun _ => MergedCutProfiles.Batch668.profile26754)⟩
theorem profilesValid4733 : retention4733.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26754
theorem numericValid4733 : retention4733.NumericValid := by decide +kernel
def certificate4733 : RatCutBinCertificate := ⟨⟨retention4733,(93978129830264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(493028211550093119/500000000000000000)⟩,(199990662410385847/200000000000000000),(523242227453664413/1000000000000000000),(137848123645066761/1000000000000000000),(66928632815366071/500000000000000000)⟩
theorem valid4733 : certificate4733.Valid := by decide +kernel
theorem sound4733 : certificate4733.Sound := rat_cut_bin_certificate_sound certificate4733 profilesValid4733 numericValid4733 valid4733

def retention4734 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(64000000000000000000/3380072921991454528517),(29801355939048807611/1000000000000000000),1,(13076488896243320453934017566375253637/5960271187809761522200000000000000000),false,MergedCutProfiles.Batch668.profile26755,(fun _ => MergedCutProfiles.Batch668.profile26755)⟩
theorem profilesValid4734 : retention4734.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26755
theorem numericValid4734 : retention4734.NumericValid := by decide +kernel
def certificate4734 : RatCutBinCertificate := ⟨⟨retention4734,(87683557230264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(2183181545418942739/1000000000000000000)⟩,(499978219589745213/500000000000000000),(2659062566991777/125000000000000000),(13596029435104691/15625000000000000),(70797603628576579/40000000000000000)⟩
theorem valid4734 : certificate4734.Valid := by decide +kernel
theorem sound4734 : certificate4734.Sound := rat_cut_bin_certificate_sound certificate4734 profilesValid4734 numericValid4734 valid4734

def retention4735 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(1/2),64,1,(255382853441000253850307765633342734479/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch668.profile26754,(fun _ => MergedCutProfiles.Batch668.profile26754)⟩
theorem profilesValid4735 : retention4735.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26754
theorem numericValid4735 : retention4735.NumericValid := by decide +kernel
def certificate4735 : RatCutBinCertificate := ⟨⟨retention4735,(87683557230264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(197365776628166131/200000000000000000)⟩,(499978219589745213/500000000000000000),(23530792110154743/500000000000000000),(199074261167061581/250000000000000000),(48365144898966631/62500000000000000)⟩
theorem valid4735 : certificate4735.Valid := by decide +kernel
theorem sound4735 : certificate4735.Sound := rat_cut_bin_certificate_sound certificate4735 profilesValid4735 numericValid4735 valid4735

def retention4736 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(694945263987685916/3380072921991454528517),(137612923561918003/200000000000000000),4,(16453953973145773598405627059175833/6880646178095900150000000000000000),false,MergedCutProfiles.Batch668.profile26756,(fun _ => MergedCutProfiles.Batch668.profile26756)⟩
theorem profilesValid4736 : retention4736.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26756
theorem numericValid4736 : retention4736.NumericValid := by decide +kernel
def certificate4736 : RatCutBinCertificate := ⟨⟨retention4736,(91887951930264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(1173116536173674743/500000000000000000)⟩,(499977175223558857/500000000000000000),(426399610710658421/500000000000000000),(11408587607043747/1000000000000000000),(551589705651789/100000000000000000)⟩
theorem valid4736 : certificate4736.Valid := by decide +kernel
theorem sound4736 : certificate4736.Sound := rat_cut_bin_certificate_sound certificate4736 profilesValid4736 numericValid4736 valid4736

def retention4737 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(936681220281542261/3380072921991454528517),(173736315996921479/250000000000000000),4,(266248129742324424339727993918723647/111191242238029746560000000000000000),false,MergedCutProfiles.Batch668.profile26757,(fun _ => MergedCutProfiles.Batch668.profile26757)⟩
theorem profilesValid4737 : retention4737.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26757
theorem numericValid4737 : retention4737.NumericValid := by decide +kernel
def certificate4737 : RatCutBinCertificate := ⟨⟨retention4737,(91887951930264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(2349400889901212011/1000000000000000000)⟩,(499977175223558857/500000000000000000),(42471887435449273/50000000000000000),(186726131290689/15625000000000000),(2897205245746701/500000000000000000)⟩
theorem valid4737 : certificate4737.Valid := by decide +kernel
theorem sound4737 : certificate4737.Sound := rat_cut_bin_certificate_sound certificate4737 profilesValid4737 numericValid4737 valid4737

def retention4738 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(8278900660139031303/3380072921991454528517),(936681220281542261/1000000000000000000),(69/20),(3571610467424220863689997932081629177959/1498689952450467617600000000000000000000),false,MergedCutProfiles.Batch668.profile26758,(fun _ => MergedCutProfiles.Batch668.profile26758)⟩
theorem profilesValid4738 : retention4738.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26758
theorem numericValid4738 : retention4738.NumericValid := by decide +kernel
def certificate4738 : RatCutBinCertificate := ⟨⟨retention4738,(91887951930264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(293031449859747423/125000000000000000)⟩,(499977175223558857/500000000000000000),(49631368454228903/62500000000000000),(22823078889699221/1000000000000000000),(6406556306235751/500000000000000000)⟩
theorem valid4738 : certificate4738.Valid := by decide +kernel
theorem sound4738 : certificate4738.Sound := rat_cut_bin_certificate_sound certificate4738 profilesValid4738 numericValid4738 valid4738

def retention4739 : RatCutRetentionCertificate := ⟨(77/2000),(31/800),(1/40),(8278900660139031303/1000000000000000000),(6/5),(1814147162523801487814030923975685525111/827890066013903130300000000000000000000),false,MergedCutProfiles.Batch668.profile26759,(fun _ => MergedCutProfiles.Batch668.profile26759)⟩
theorem profilesValid4739 : retention4739.ProfilesValid := by
  exact MergedCutProfiles.Batch668.valid26759
theorem numericValid4739 : retention4739.NumericValid := by decide +kernel
def certificate4739 : RatCutBinCertificate := ⟨⟨retention4739,(91887951930264967/50000000000000000),(68084449468112531/1000000000000000000),(2219208760055839659/200000000000000000),(37555462999086581195769/1000000000000000000),(217775831138604571/100000000000000000)⟩,(499977175223558857/500000000000000000),(69782395341014097/100000000000000000),(25553533155870007/500000000000000000),(78419451913462591/1000000000000000000)⟩
theorem valid4739 : certificate4739.Valid := by decide +kernel
theorem sound4739 : certificate4739.Sound := rat_cut_bin_certificate_sound certificate4739 profilesValid4739 numericValid4739 valid4739

def certificates : List RatCutBinCertificate := [certificate4728,certificate4729,certificate4730,certificate4731,certificate4732,certificate4733,certificate4734,certificate4735,certificate4736,certificate4737,certificate4738,certificate4739]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4728,List.forall_mem_cons.mpr ⟨sound4729,List.forall_mem_cons.mpr ⟨sound4730,List.forall_mem_cons.mpr ⟨sound4731,List.forall_mem_cons.mpr ⟨sound4732,List.forall_mem_cons.mpr ⟨sound4733,List.forall_mem_cons.mpr ⟨sound4734,List.forall_mem_cons.mpr ⟨sound4735,List.forall_mem_cons.mpr ⟨sound4736,List.forall_mem_cons.mpr ⟨sound4737,List.forall_mem_cons.mpr ⟨sound4738,List.forall_mem_cons.mpr ⟨sound4739,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch394
