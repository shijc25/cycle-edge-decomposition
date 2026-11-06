import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch417
import Cycle12.MergedCutProfiles.Batch418
import Cycle12.MergedCutProfiles.Batch419

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch221

def retention2652 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(122129847625000000/2727356343157655291),(939431925151892189/1000000000000000000),(13/5),(165460808806043354993/80000000000000000000),true,MergedCutProfiles.Batch417.profile16697,![MergedCutProfiles.Batch417.profile16697,MergedCutProfiles.Batch417.profile16698,MergedCutProfiles.Batch417.profile16699,MergedCutProfiles.Batch417.profile16700,MergedCutProfiles.Batch417.profile16701,MergedCutProfiles.Batch417.profile16702,MergedCutProfiles.Batch417.profile16703,MergedCutProfiles.Batch417.profile16704,MergedCutProfiles.Batch417.profile16705,MergedCutProfiles.Batch417.profile16706,MergedCutProfiles.Batch417.profile16707,MergedCutProfiles.Batch417.profile16708,MergedCutProfiles.Batch417.profile16709,MergedCutProfiles.Batch417.profile16710,MergedCutProfiles.Batch417.profile16711,MergedCutProfiles.Batch417.profile16712]⟩
theorem profilesValid2652 : retention2652.ProfilesValid := by
  change ∀ j : Fin 16, (retention2652.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch417.valid16697
  · exact MergedCutProfiles.Batch417.valid16698
  · exact MergedCutProfiles.Batch417.valid16699
  · exact MergedCutProfiles.Batch417.valid16700
  · exact MergedCutProfiles.Batch417.valid16701
  · exact MergedCutProfiles.Batch417.valid16702
  · exact MergedCutProfiles.Batch417.valid16703
  · exact MergedCutProfiles.Batch417.valid16704
  · exact MergedCutProfiles.Batch417.valid16705
  · exact MergedCutProfiles.Batch417.valid16706
  · exact MergedCutProfiles.Batch417.valid16707
  · exact MergedCutProfiles.Batch417.valid16708
  · exact MergedCutProfiles.Batch417.valid16709
  · exact MergedCutProfiles.Batch417.valid16710
  · exact MergedCutProfiles.Batch417.valid16711
  · exact MergedCutProfiles.Batch417.valid16712
theorem numericValid2652 : retention2652.NumericValid := by decide +kernel
def certificate2652 : RatCutBinCertificate := ⟨⟨retention2652,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(498514946515693407/250000000000000000)⟩,(995030470150701123/1000000000000000000),(72815074726853867/250000000000000000),(174715019935027171/500000000000000000),(202730821681561991/1000000000000000000)⟩
theorem valid2652 : certificate2652.Valid := by decide +kernel
theorem sound2652 : certificate2652.Sound := rat_cut_bin_certificate_sound certificate2652 profilesValid2652 numericValid2652 valid2652

def retention2653 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(997225918666623959/21818850745261242328),(977038781/1000000000),(51/20),(8282792261582477949/4000000000000000000),true,MergedCutProfiles.Batch417.profile16713,![MergedCutProfiles.Batch417.profile16713,MergedCutProfiles.Batch417.profile16714,MergedCutProfiles.Batch417.profile16715,MergedCutProfiles.Batch417.profile16716,MergedCutProfiles.Batch417.profile16717,MergedCutProfiles.Batch417.profile16718,MergedCutProfiles.Batch417.profile16719,MergedCutProfiles.Batch418.profile16720,MergedCutProfiles.Batch418.profile16721,MergedCutProfiles.Batch418.profile16722,MergedCutProfiles.Batch418.profile16723,MergedCutProfiles.Batch418.profile16724,MergedCutProfiles.Batch418.profile16725,MergedCutProfiles.Batch418.profile16726,MergedCutProfiles.Batch418.profile16727,MergedCutProfiles.Batch418.profile16728]⟩
theorem profilesValid2653 : retention2653.ProfilesValid := by
  change ∀ j : Fin 16, (retention2653.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch417.valid16713
  · exact MergedCutProfiles.Batch417.valid16714
  · exact MergedCutProfiles.Batch417.valid16715
  · exact MergedCutProfiles.Batch417.valid16716
  · exact MergedCutProfiles.Batch417.valid16717
  · exact MergedCutProfiles.Batch417.valid16718
  · exact MergedCutProfiles.Batch417.valid16719
  · exact MergedCutProfiles.Batch418.valid16720
  · exact MergedCutProfiles.Batch418.valid16721
  · exact MergedCutProfiles.Batch418.valid16722
  · exact MergedCutProfiles.Batch418.valid16723
  · exact MergedCutProfiles.Batch418.valid16724
  · exact MergedCutProfiles.Batch418.valid16725
  · exact MergedCutProfiles.Batch418.valid16726
  · exact MergedCutProfiles.Batch418.valid16727
  · exact MergedCutProfiles.Batch418.valid16728
theorem numericValid2653 : retention2653.NumericValid := by decide +kernel
def certificate2653 : RatCutBinCertificate := ⟨⟨retention2653,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(1997925003412152449/1000000000000000000)⟩,(995030470150701123/1000000000000000000),(14313816719632789/50000000000000000),(355616744554029277/1000000000000000000),(210701119445066969/1000000000000000000)⟩
theorem valid2653 : certificate2653.Valid := by decide +kernel
theorem sound2653 : certificate2653.Sound := rat_cut_bin_certificate_sound certificate2653 profilesValid2653 numericValid2653 valid2653

def retention2654 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(147627384319603666/2727356343157655291),(997225918666623959/1000000000000000000),(5/2),(32690865282184852817/16000000000000000000),true,MergedCutProfiles.Batch418.profile16729,![MergedCutProfiles.Batch418.profile16729,MergedCutProfiles.Batch418.profile16730,MergedCutProfiles.Batch418.profile16731,MergedCutProfiles.Batch418.profile16732,MergedCutProfiles.Batch418.profile16733,MergedCutProfiles.Batch418.profile16734,MergedCutProfiles.Batch418.profile16735,MergedCutProfiles.Batch418.profile16736,MergedCutProfiles.Batch418.profile16737,MergedCutProfiles.Batch418.profile16738,MergedCutProfiles.Batch418.profile16739,MergedCutProfiles.Batch418.profile16740,MergedCutProfiles.Batch418.profile16741,MergedCutProfiles.Batch418.profile16742,MergedCutProfiles.Batch418.profile16743,MergedCutProfiles.Batch418.profile16744]⟩
theorem profilesValid2654 : retention2654.ProfilesValid := by
  change ∀ j : Fin 16, (retention2654.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch418.valid16729
  · exact MergedCutProfiles.Batch418.valid16730
  · exact MergedCutProfiles.Batch418.valid16731
  · exact MergedCutProfiles.Batch418.valid16732
  · exact MergedCutProfiles.Batch418.valid16733
  · exact MergedCutProfiles.Batch418.valid16734
  · exact MergedCutProfiles.Batch418.valid16735
  · exact MergedCutProfiles.Batch418.valid16736
  · exact MergedCutProfiles.Batch418.valid16737
  · exact MergedCutProfiles.Batch418.valid16738
  · exact MergedCutProfiles.Batch418.valid16739
  · exact MergedCutProfiles.Batch418.valid16740
  · exact MergedCutProfiles.Batch418.valid16741
  · exact MergedCutProfiles.Batch418.valid16742
  · exact MergedCutProfiles.Batch418.valid16743
  · exact MergedCutProfiles.Batch418.valid16744
theorem numericValid2654 : retention2654.NumericValid := by decide +kernel
def certificate2654 : RatCutBinCertificate := ⟨⟨retention2654,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(985916475746092953/500000000000000000)⟩,(995030470150701123/1000000000000000000),(287799502374813927/1000000000000000000),(353716920457401137/1000000000000000000),(52667993870747617/250000000000000000)⟩
theorem valid2654 : certificate2654.Valid := by decide +kernel
theorem sound2654 : certificate2654.Sound := rat_cut_bin_certificate_sound certificate2654 profilesValid2654 numericValid2654 valid2654

def retention2655 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(317623557868865760/2727356343157655291),(73813692159801833/62500000000000000),(11/5),(148663645201655329183/80000000000000000000),true,MergedCutProfiles.Batch418.profile16745,![MergedCutProfiles.Batch418.profile16745,MergedCutProfiles.Batch418.profile16746,MergedCutProfiles.Batch418.profile16747,MergedCutProfiles.Batch418.profile16748,MergedCutProfiles.Batch417.profile16709,MergedCutProfiles.Batch418.profile16749,MergedCutProfiles.Batch418.profile16750,MergedCutProfiles.Batch418.profile16751,MergedCutProfiles.Batch418.profile16752,MergedCutProfiles.Batch418.profile16753,MergedCutProfiles.Batch418.profile16754,MergedCutProfiles.Batch418.profile16755,MergedCutProfiles.Batch418.profile16756,MergedCutProfiles.Batch418.profile16757,MergedCutProfiles.Batch418.profile16758,MergedCutProfiles.Batch418.profile16759]⟩
theorem profilesValid2655 : retention2655.ProfilesValid := by
  change ∀ j : Fin 16, (retention2655.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch418.valid16745
  · exact MergedCutProfiles.Batch418.valid16746
  · exact MergedCutProfiles.Batch418.valid16747
  · exact MergedCutProfiles.Batch418.valid16748
  · exact MergedCutProfiles.Batch417.valid16709
  · exact MergedCutProfiles.Batch418.valid16749
  · exact MergedCutProfiles.Batch418.valid16750
  · exact MergedCutProfiles.Batch418.valid16751
  · exact MergedCutProfiles.Batch418.valid16752
  · exact MergedCutProfiles.Batch418.valid16753
  · exact MergedCutProfiles.Batch418.valid16754
  · exact MergedCutProfiles.Batch418.valid16755
  · exact MergedCutProfiles.Batch418.valid16756
  · exact MergedCutProfiles.Batch418.valid16757
  · exact MergedCutProfiles.Batch418.valid16758
  · exact MergedCutProfiles.Batch418.valid16759
theorem numericValid2655 : retention2655.NumericValid := by decide +kernel
def certificate2655 : RatCutBinCertificate := ⟨⟨retention2655,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(897755775770268189/500000000000000000)⟩,(995030470150701123/1000000000000000000),(74331728684469041/250000000000000000),(342013712902406947/1000000000000000000),(42230127379546593/200000000000000000)⟩
theorem valid2655 : certificate2655.Valid := by decide +kernel
theorem sound2655 : certificate2655.Sound := rat_cut_bin_certificate_sound certificate2655 profilesValid2655 numericValid2655 valid2655

def retention2656 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1897989554406279411/5454712686315310582),(1985147236680411/781250000000000),(13/10),(20636064731493113559/16000000000000000000),true,MergedCutProfiles.Batch418.profile16747,![MergedCutProfiles.Batch418.profile16747,MergedCutProfiles.Batch418.profile16749,MergedCutProfiles.Batch419.profile16760,MergedCutProfiles.Batch419.profile16761,MergedCutProfiles.Batch419.profile16762,MergedCutProfiles.Batch419.profile16763,MergedCutProfiles.Batch419.profile16764,MergedCutProfiles.Batch419.profile16765,MergedCutProfiles.Batch419.profile16766,MergedCutProfiles.Batch419.profile16767,MergedCutProfiles.Batch419.profile16768,MergedCutProfiles.Batch419.profile16769,MergedCutProfiles.Batch419.profile16770,MergedCutProfiles.Batch419.profile16771,MergedCutProfiles.Batch419.profile16772,MergedCutProfiles.Batch419.profile16773]⟩
theorem profilesValid2656 : retention2656.ProfilesValid := by
  change ∀ j : Fin 16, (retention2656.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch418.valid16747
  · exact MergedCutProfiles.Batch418.valid16749
  · exact MergedCutProfiles.Batch419.valid16760
  · exact MergedCutProfiles.Batch419.valid16761
  · exact MergedCutProfiles.Batch419.valid16762
  · exact MergedCutProfiles.Batch419.valid16763
  · exact MergedCutProfiles.Batch419.valid16764
  · exact MergedCutProfiles.Batch419.valid16765
  · exact MergedCutProfiles.Batch419.valid16766
  · exact MergedCutProfiles.Batch419.valid16767
  · exact MergedCutProfiles.Batch419.valid16768
  · exact MergedCutProfiles.Batch419.valid16769
  · exact MergedCutProfiles.Batch419.valid16770
  · exact MergedCutProfiles.Batch419.valid16771
  · exact MergedCutProfiles.Batch419.valid16772
  · exact MergedCutProfiles.Batch419.valid16773
theorem numericValid2656 : retention2656.NumericValid := by decide +kernel
def certificate2656 : RatCutBinCertificate := ⟨⟨retention2656,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(15658201681222551/12500000000000000)⟩,(995030470150701123/1000000000000000000),(17409752298178557/50000000000000000),(284455682559764399/1000000000000000000),(26372429010820979/125000000000000000)⟩
theorem valid2656 : certificate2656.Valid := by decide +kernel
theorem sound2656 : certificate2656.Sound := rat_cut_bin_certificate_sound certificate2656 profilesValid2656 numericValid2656 valid2656

def retention2657 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(2609623045780304367/5454712686315310582),(1897989554406279411/250000000000000000),(21/20),(782294896134773736760411590077337049079/759195821762511764400000000000000000000),false,MergedCutProfiles.Batch419.profile16774,(fun _ => MergedCutProfiles.Batch419.profile16774)⟩
theorem profilesValid2657 : retention2657.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16774
theorem numericValid2657 : retention2657.NumericValid := by decide +kernel
def certificate2657 : RatCutBinCertificate := ⟨⟨retention2657,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(500232518354869823/500000000000000000)⟩,(995030470150701123/1000000000000000000),(15182134385395387/40000000000000000),(126374009662837967/500000000000000000),(213964123266161523/1000000000000000000)⟩
theorem valid2657 : certificate2657.Valid := by decide +kernel
theorem sound2657 : certificate2657.Sound := rat_cut_bin_certificate_sound certificate2657 profilesValid2657 numericValid2657 valid2657

def retention2658 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(10862336824109593215/21818850745261242328),(2609623045780304367/250000000000000000),(21/20),(1044203731678984546926615317842266008471/1043849218312121746800000000000000000000),false,MergedCutProfiles.Batch419.profile16775,(fun _ => MergedCutProfiles.Batch419.profile16775)⟩
theorem profilesValid2658 : retention2658.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16775
theorem numericValid2658 : retention2658.NumericValid := by decide +kernel
def certificate2658 : RatCutBinCertificate := ⟨⟨retention2658,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(485189763816738339/500000000000000000)⟩,(995030470150701123/1000000000000000000),(383342085335483257/1000000000000000000),(124548381036673469/500000000000000000),(211192718825670631/1000000000000000000)⟩
theorem valid2658 : certificate2658.Valid := by decide +kernel
theorem sound2658 : certificate2658.Sound := rat_cut_bin_certificate_sound certificate2658 profilesValid2658 numericValid2658 valid2658

def retention2659 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1/2),(2172467364821918643/200000000000000000),(21/20),(230985394325358389672568722069394791877/231729852247671321920000000000000000000),false,MergedCutProfiles.Batch419.profile16776,(fun _ => MergedCutProfiles.Batch419.profile16776)⟩
theorem profilesValid2659 : retention2659.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16776
theorem numericValid2659 : retention2659.NumericValid := by decide +kernel
def certificate2659 : RatCutBinCertificate := ⟨⟨retention2659,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(966827355841969521/1000000000000000000)⟩,(995030470150701123/1000000000000000000),(383917098046516367/1000000000000000000),(124272946237001801/500000000000000000),(10532659059592473/50000000000000000)⟩
theorem valid2659 : certificate2659.Valid := by decide +kernel
theorem sound2659 : certificate2659.Sound := rat_cut_bin_certificate_sound certificate2659 profilesValid2659 numericValid2659 valid2659

def retention2660 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(9919844249164632281/21818850745261242328),(2471602881882526267/500000000000000000),(21/20),(2089879290367787911366682301811649986311/1977282305506021013600000000000000000000),false,MergedCutProfiles.Batch419.profile16777,(fun _ => MergedCutProfiles.Batch419.profile16777)⟩
theorem profilesValid2660 : retention2660.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16777
theorem numericValid2660 : retention2660.NumericValid := by decide +kernel
def certificate2660 : RatCutBinCertificate := ⟨⟨retention2660,(1280589797582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(1023462044693684487/1000000000000000000)⟩,(248611389425113257/250000000000000000),(1767836398532049/7812500000000000),(87462565619026731/200000000000000000),(22292623750257951/62500000000000000)⟩
theorem valid2660 : certificate2660.Valid := by decide +kernel
theorem sound2660 : certificate2660.Sound := rat_cut_bin_certificate_sound certificate2660 profilesValid2660 numericValid2660 valid2660

def retention2661 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(10741769863994069487/21818850745261242328),(9919844249164632281/1000000000000000000),1,(7864201359725335457746183690930310543/7935875399331705824800000000000000000),false,MergedCutProfiles.Batch419.profile16778,(fun _ => MergedCutProfiles.Batch419.profile16778)⟩
theorem profilesValid2661 : retention2661.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16778
theorem numericValid2661 : retention2661.NumericValid := by decide +kernel
def certificate2661 : RatCutBinCertificate := ⟨⟨retention2661,(1280589797582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(959081178101533097/1000000000000000000)⟩,(248611389425113257/250000000000000000),(120736454610910093/500000000000000000),(415289130740035873/1000000000000000000),(361055341744321933/1000000000000000000)⟩
theorem valid2661 : certificate2661.Valid := by decide +kernel
theorem sound2661 : certificate2661.Sound := rat_cut_bin_certificate_sound certificate2661 profilesValid2661 numericValid2661 valid2661

def retention2662 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(5424593781317005091/10909425372630621164),(10741769863994069487/1000000000000000000),1,(42260301608632617440744315354023588307/42967079455976277948000000000000000000),false,MergedCutProfiles.Batch419.profile16779,(fun _ => MergedCutProfiles.Batch419.profile16779)⟩
theorem profilesValid2662 : retention2662.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16779
theorem numericValid2662 : retention2662.NumericValid := by decide +kernel
def certificate2662 : RatCutBinCertificate := ⟨⟨retention2662,(1280589797582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(951663679206157811/1000000000000000000)⟩,(248611389425113257/250000000000000000),(60838751997253203/250000000000000000),(103156725549206179/250000000000000000),(179309381857315991/500000000000000000)⟩
theorem valid2662 : certificate2662.Valid := by decide +kernel
theorem sound2662 : certificate2662.Sound := rat_cut_bin_certificate_sound certificate2662 profilesValid2662 numericValid2662 valid2662

def retention2663 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1/2),(5424593781317005091/500000000000000000),1,(42464054975226197857409667409828694271/43396750250536040728000000000000000000),false,MergedCutProfiles.Batch419.profile16776,(fun _ => MergedCutProfiles.Batch419.profile16776)⟩
theorem profilesValid2663 : retention2663.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16776
theorem numericValid2663 : retention2663.NumericValid := by decide +kernel
def certificate2663 : RatCutBinCertificate := ⟨⟨retention2663,(1280589797582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(236655174914126401/250000000000000000)⟩,(248611389425113257/250000000000000000),(122325722615248251/500000000000000000),(410801435506637313/1000000000000000000),(177789748552997073/500000000000000000)⟩
theorem valid2663 : certificate2663.Valid := by decide +kernel
theorem sound2663 : certificate2663.Sound := rat_cut_bin_certificate_sound certificate2663 profilesValid2663 numericValid2663 valid2663

def certificates : List RatCutBinCertificate := [certificate2652,certificate2653,certificate2654,certificate2655,certificate2656,certificate2657,certificate2658,certificate2659,certificate2660,certificate2661,certificate2662,certificate2663]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2652,List.forall_mem_cons.mpr ⟨sound2653,List.forall_mem_cons.mpr ⟨sound2654,List.forall_mem_cons.mpr ⟨sound2655,List.forall_mem_cons.mpr ⟨sound2656,List.forall_mem_cons.mpr ⟨sound2657,List.forall_mem_cons.mpr ⟨sound2658,List.forall_mem_cons.mpr ⟨sound2659,List.forall_mem_cons.mpr ⟨sound2660,List.forall_mem_cons.mpr ⟨sound2661,List.forall_mem_cons.mpr ⟨sound2662,List.forall_mem_cons.mpr ⟨sound2663,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch221
