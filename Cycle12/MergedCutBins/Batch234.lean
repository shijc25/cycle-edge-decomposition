import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch442
import Cycle12.MergedCutProfiles.Batch443
import Cycle12.MergedCutProfiles.Batch444

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch234

def retention2808 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(324690688250000000/1313239985870766615451),(642002531642094239/1000000000000000000),4,(148419307118186022479/64000000000000000000),true,MergedCutProfiles.Batch442.profile17693,![MergedCutProfiles.Batch442.profile17693,MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17697,MergedCutProfiles.Batch442.profile17699,MergedCutProfiles.Batch442.profile17701,MergedCutProfiles.Batch442.profile17702,MergedCutProfiles.Batch442.profile17704,MergedCutProfiles.Batch442.profile17705,MergedCutProfiles.Batch442.profile17706,MergedCutProfiles.Batch442.profile17707,MergedCutProfiles.Batch442.profile17708,MergedCutProfiles.Batch442.profile17709,MergedCutProfiles.Batch442.profile17710,MergedCutProfiles.Batch442.profile17711,MergedCutProfiles.Batch442.profile17712,MergedCutProfiles.Batch442.profile17713]⟩
theorem profilesValid2808 : retention2808.ProfilesValid := by
  change ∀ j : Fin 16, (retention2808.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch442.valid17693
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17697
  · exact MergedCutProfiles.Batch442.valid17699
  · exact MergedCutProfiles.Batch442.valid17701
  · exact MergedCutProfiles.Batch442.valid17702
  · exact MergedCutProfiles.Batch442.valid17704
  · exact MergedCutProfiles.Batch442.valid17705
  · exact MergedCutProfiles.Batch442.valid17706
  · exact MergedCutProfiles.Batch442.valid17707
  · exact MergedCutProfiles.Batch442.valid17708
  · exact MergedCutProfiles.Batch442.valid17709
  · exact MergedCutProfiles.Batch442.valid17710
  · exact MergedCutProfiles.Batch442.valid17711
  · exact MergedCutProfiles.Batch442.valid17712
  · exact MergedCutProfiles.Batch442.valid17713
theorem numericValid2808 : retention2808.NumericValid := by decide +kernel
def certificate2808 : RatCutBinCertificate := ⟨⟨retention2808,(180436997786074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(289599683051275751/125000000000000000)⟩,(199990570226759163/200000000000000000),(130416516635767621/250000000000000000),(4339731095407703/31250000000000000),(4101737608342523/62500000000000000)⟩
theorem valid2808 : certificate2808.Valid := by decide +kernel
theorem sound2808 : certificate2808.Sound := rat_cut_bin_certificate_sound certificate2808 profilesValid2808 numericValid2808 valid2808

def retention2809 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(686115643804301133/1313239985870766615451),(1298762753/1000000000),(49/20),(37540627599785683643/16000000000000000000),true,MergedCutProfiles.Batch442.profile17695,![MergedCutProfiles.Batch442.profile17695,MergedCutProfiles.Batch442.profile17699,MergedCutProfiles.Batch442.profile17703,MergedCutProfiles.Batch442.profile17714,MergedCutProfiles.Batch442.profile17708,MergedCutProfiles.Batch442.profile17715,MergedCutProfiles.Batch442.profile17711,MergedCutProfiles.Batch442.profile17716,MergedCutProfiles.Batch442.profile17717,MergedCutProfiles.Batch442.profile17718,MergedCutProfiles.Batch442.profile17719,MergedCutProfiles.Batch443.profile17720,MergedCutProfiles.Batch443.profile17721,MergedCutProfiles.Batch443.profile17722,MergedCutProfiles.Batch443.profile17723,MergedCutProfiles.Batch443.profile17724]⟩
theorem profilesValid2809 : retention2809.ProfilesValid := by
  change ∀ j : Fin 16, (retention2809.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch442.valid17695
  · exact MergedCutProfiles.Batch442.valid17699
  · exact MergedCutProfiles.Batch442.valid17703
  · exact MergedCutProfiles.Batch442.valid17714
  · exact MergedCutProfiles.Batch442.valid17708
  · exact MergedCutProfiles.Batch442.valid17715
  · exact MergedCutProfiles.Batch442.valid17711
  · exact MergedCutProfiles.Batch442.valid17716
  · exact MergedCutProfiles.Batch442.valid17717
  · exact MergedCutProfiles.Batch442.valid17718
  · exact MergedCutProfiles.Batch442.valid17719
  · exact MergedCutProfiles.Batch443.valid17720
  · exact MergedCutProfiles.Batch443.valid17721
  · exact MergedCutProfiles.Batch443.valid17722
  · exact MergedCutProfiles.Batch443.valid17723
  · exact MergedCutProfiles.Batch443.valid17724
theorem numericValid2809 : retention2809.NumericValid := by decide +kernel
def certificate2809 : RatCutBinCertificate := ⟨⟨retention2809,(180436997786074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(234490852178949617/100000000000000000)⟩,(199990570226759163/200000000000000000),(342926743555854139/1000000000000000000),(145026390476678657/500000000000000000),(213405847167998239/1000000000000000000)⟩
theorem valid2809 : certificate2809.Valid := by decide +kernel
theorem sound2809 : certificate2809.Sound := rat_cut_bin_certificate_sound certificate2809 profilesValid2809 numericValid2809 valid2809

def retention2810 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(16000000000000000000/1313239985870766615451),(686115643804301133/250000000000000000),(31/20),(176533823268507224041/80000000000000000000),true,MergedCutProfiles.Batch443.profile17725,![MergedCutProfiles.Batch443.profile17725,MergedCutProfiles.Batch443.profile17726,MergedCutProfiles.Batch443.profile17727,MergedCutProfiles.Batch443.profile17728,MergedCutProfiles.Batch443.profile17729,MergedCutProfiles.Batch443.profile17730,MergedCutProfiles.Batch443.profile17731,MergedCutProfiles.Batch443.profile17732,MergedCutProfiles.Batch443.profile17733,MergedCutProfiles.Batch443.profile17734,MergedCutProfiles.Batch443.profile17735,MergedCutProfiles.Batch443.profile17736,MergedCutProfiles.Batch443.profile17737,MergedCutProfiles.Batch443.profile17738,MergedCutProfiles.Batch443.profile17739,MergedCutProfiles.Batch443.profile17740]⟩
theorem profilesValid2810 : retention2810.ProfilesValid := by
  change ∀ j : Fin 16, (retention2810.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch443.valid17725
  · exact MergedCutProfiles.Batch443.valid17726
  · exact MergedCutProfiles.Batch443.valid17727
  · exact MergedCutProfiles.Batch443.valid17728
  · exact MergedCutProfiles.Batch443.valid17729
  · exact MergedCutProfiles.Batch443.valid17730
  · exact MergedCutProfiles.Batch443.valid17731
  · exact MergedCutProfiles.Batch443.valid17732
  · exact MergedCutProfiles.Batch443.valid17733
  · exact MergedCutProfiles.Batch443.valid17734
  · exact MergedCutProfiles.Batch443.valid17735
  · exact MergedCutProfiles.Batch443.valid17736
  · exact MergedCutProfiles.Batch443.valid17737
  · exact MergedCutProfiles.Batch443.valid17738
  · exact MergedCutProfiles.Batch443.valid17739
  · exact MergedCutProfiles.Batch443.valid17740
theorem numericValid2810 : retention2810.NumericValid := by decide +kernel
def certificate2810 : RatCutBinCertificate := ⟨⟨retention2810,(180436997786074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(2205799284756150707/1000000000000000000)⟩,(199990570226759163/200000000000000000),(1350668261577649/5000000000000000),(18812724327677839/50000000000000000),(401201543526112049/1000000000000000000)⟩
theorem valid2810 : certificate2810.Valid := by decide +kernel
theorem sound2810 : certificate2810.Sound := rat_cut_bin_certificate_sound certificate2810 profilesValid2810 numericValid2810 valid2810

def retention2811 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(1/2),64,1,(10214758165775650715803726264123871679/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch443.profile17741,(fun _ => MergedCutProfiles.Batch443.profile17741)⟩
theorem profilesValid2811 : retention2811.ProfilesValid := by
  exact MergedCutProfiles.Batch443.valid17741
theorem numericValid2811 : retention2811.NumericValid := by decide +kernel
def certificate2811 : RatCutBinCertificate := ⟨⟨retention2811,(180436997786074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(996971424811162381/1000000000000000000)⟩,(199990570226759163/200000000000000000),(83609401278328267/200000000000000000),(217347759889230757/1000000000000000000),(213355616504739831/1000000000000000000)⟩
theorem valid2811 : certificate2811.Valid := by decide +kernel
theorem sound2811 : certificate2811.Sound := rat_cut_bin_certificate_sound certificate2811 profilesValid2811 numericValid2811 valid2811

def retention2812 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(16000000000000000000/1313239985870766615451),(1897604479449345967/250000000000000000),1,(197787265378223072517066960362603001/94880223972467298350000000000000000),false,MergedCutProfiles.Batch443.profile17742,(fun _ => MergedCutProfiles.Batch443.profile17742)⟩
theorem profilesValid2812 : retention2812.ProfilesValid := by
  exact MergedCutProfiles.Batch443.valid17742
theorem numericValid2812 : retention2812.NumericValid := by decide +kernel
def certificate2812 : RatCutBinCertificate := ⟨⟨retention2812,(195425938586074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(16671912891202807/8000000000000000)⟩,(124993616808348941/125000000000000000),(17781047608049729/250000000000000000),(733995158455105081/1000000000000000000),(1200070105772806007/1000000000000000000)⟩
theorem valid2812 : certificate2812.Valid := by decide +kernel
theorem sound2812 : certificate2812.Sound := rat_cut_bin_certificate_sound certificate2812 profilesValid2812 numericValid2812 valid2812

def retention2813 : RatCutRetentionCertificate := ⟨(7/1000),(3/400),(1/2),64,1,(10214758165775650715803726264123871679/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch443.profile17741,(fun _ => MergedCutProfiles.Batch443.profile17741)⟩
theorem profilesValid2813 : retention2813.ProfilesValid := by
  exact MergedCutProfiles.Batch443.valid17741
theorem numericValid2813 : retention2813.NumericValid := by decide +kernel
def certificate2813 : RatCutBinCertificate := ⟨⟨retention2813,(195425938586074881/100000000000000000),(90635594743493/40000000000000000),(181371966023790381/25000000000000000),(38194222826487881556691/1000000000000000000),(996924610397287357/1000000000000000000)⟩,(124993616808348941/125000000000000000),(148679285145542907/1000000000000000000),(566907482901943203/1000000000000000000),(278233438931173013/500000000000000000)⟩
theorem valid2813 : certificate2813.Valid := by decide +kernel
theorem sound2813 : certificate2813.Sound := rat_cut_bin_certificate_sound certificate2813 profilesValid2813 numericValid2813 valid2813

def retention2814 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(106994564955613993/767766628096072365484),(143852649322824329/250000000000000000),4,(1272052782059062990241532808415437783/575410597291297316000000000000000000),true,MergedCutProfiles.Batch443.profile17743,![MergedCutProfiles.Batch443.profile17743,MergedCutProfiles.Batch443.profile17744,MergedCutProfiles.Batch443.profile17745,MergedCutProfiles.Batch443.profile17746,MergedCutProfiles.Batch443.profile17747,MergedCutProfiles.Batch443.profile17748,MergedCutProfiles.Batch443.profile17749,MergedCutProfiles.Batch443.profile17750,MergedCutProfiles.Batch443.profile17751,MergedCutProfiles.Batch443.profile17752,MergedCutProfiles.Batch443.profile17753,MergedCutProfiles.Batch443.profile17753,MergedCutProfiles.Batch443.profile17754,MergedCutProfiles.Batch443.profile17755,MergedCutProfiles.Batch443.profile17756,MergedCutProfiles.Batch443.profile17757]⟩
theorem profilesValid2814 : retention2814.ProfilesValid := by
  change ∀ j : Fin 16, (retention2814.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch443.valid17743
  · exact MergedCutProfiles.Batch443.valid17744
  · exact MergedCutProfiles.Batch443.valid17745
  · exact MergedCutProfiles.Batch443.valid17746
  · exact MergedCutProfiles.Batch443.valid17747
  · exact MergedCutProfiles.Batch443.valid17748
  · exact MergedCutProfiles.Batch443.valid17749
  · exact MergedCutProfiles.Batch443.valid17750
  · exact MergedCutProfiles.Batch443.valid17751
  · exact MergedCutProfiles.Batch443.valid17752
  · exact MergedCutProfiles.Batch443.valid17753
  · exact MergedCutProfiles.Batch443.valid17753
  · exact MergedCutProfiles.Batch443.valid17754
  · exact MergedCutProfiles.Batch443.valid17755
  · exact MergedCutProfiles.Batch443.valid17756
  · exact MergedCutProfiles.Batch443.valid17757
theorem numericValid2814 : retention2814.NumericValid := by decide +kernel
def certificate2814 : RatCutBinCertificate := ⟨⟨retention2814,(1806443732852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(552032676713076207/250000000000000000)⟩,(999946513969609047/1000000000000000000),(295329306924052251/500000000000000000),(49174770967257667/500000000000000000),(43786748494808917/1000000000000000000)⟩
theorem valid2814 : certificate2814.Valid := by decide +kernel
theorem sound2814 : certificate2814.Sound := rat_cut_bin_certificate_sound certificate2814 profilesValid2814 numericValid2814 valid2814

def retention2815 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(162337992875000000/575824971072054274113),(320983694866841979/500000000000000000),4,(74183907399863304799/32000000000000000000),true,MergedCutProfiles.Batch443.profile17744,![MergedCutProfiles.Batch443.profile17744,MergedCutProfiles.Batch443.profile17746,MergedCutProfiles.Batch443.profile17748,MergedCutProfiles.Batch443.profile17750,MergedCutProfiles.Batch443.profile17752,MergedCutProfiles.Batch443.profile17754,MergedCutProfiles.Batch443.profile17755,MergedCutProfiles.Batch443.profile17757,MergedCutProfiles.Batch443.profile17758,MergedCutProfiles.Batch443.profile17759,MergedCutProfiles.Batch444.profile17760,MergedCutProfiles.Batch444.profile17761,MergedCutProfiles.Batch444.profile17762,MergedCutProfiles.Batch444.profile17763,MergedCutProfiles.Batch444.profile17764,MergedCutProfiles.Batch444.profile17765]⟩
theorem profilesValid2815 : retention2815.ProfilesValid := by
  change ∀ j : Fin 16, (retention2815.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch443.valid17744
  · exact MergedCutProfiles.Batch443.valid17746
  · exact MergedCutProfiles.Batch443.valid17748
  · exact MergedCutProfiles.Batch443.valid17750
  · exact MergedCutProfiles.Batch443.valid17752
  · exact MergedCutProfiles.Batch443.valid17754
  · exact MergedCutProfiles.Batch443.valid17755
  · exact MergedCutProfiles.Batch443.valid17757
  · exact MergedCutProfiles.Batch443.valid17758
  · exact MergedCutProfiles.Batch443.valid17759
  · exact MergedCutProfiles.Batch444.valid17760
  · exact MergedCutProfiles.Batch444.valid17761
  · exact MergedCutProfiles.Batch444.valid17762
  · exact MergedCutProfiles.Batch444.valid17763
  · exact MergedCutProfiles.Batch444.valid17764
  · exact MergedCutProfiles.Batch444.valid17765
theorem numericValid2815 : retention2815.NumericValid := by decide +kernel
def certificate2815 : RatCutBinCertificate := ⟨⟨retention2815,(1806443732852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(46313814351676783/20000000000000000)⟩,(999946513969609047/1000000000000000000),(2092844507025139/4000000000000000),(34467067200224571/250000000000000000),(13025440947709329/200000000000000000)⟩
theorem valid2815 : certificate2815.Valid := by decide +kernel
theorem sound2815 : certificate2815.Sound := rat_cut_bin_certificate_sound certificate2815 profilesValid2815 numericValid2815 valid2815

def retention2816 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(3250101275917110025/4606599768576434192904),(1298703943/1000000000),(49/20),(37472943406153782027/16000000000000000000),true,MergedCutProfiles.Batch443.profile17747,![MergedCutProfiles.Batch443.profile17747,MergedCutProfiles.Batch443.profile17752,MergedCutProfiles.Batch443.profile17756,MergedCutProfiles.Batch443.profile17759,MergedCutProfiles.Batch444.profile17762,MergedCutProfiles.Batch444.profile17764,MergedCutProfiles.Batch444.profile17766,MergedCutProfiles.Batch444.profile17767,MergedCutProfiles.Batch444.profile17768,MergedCutProfiles.Batch444.profile17769,MergedCutProfiles.Batch444.profile17770,MergedCutProfiles.Batch444.profile17771,MergedCutProfiles.Batch444.profile17772,MergedCutProfiles.Batch444.profile17773,MergedCutProfiles.Batch444.profile17774,MergedCutProfiles.Batch444.profile17775]⟩
theorem profilesValid2816 : retention2816.ProfilesValid := by
  change ∀ j : Fin 16, (retention2816.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch443.valid17747
  · exact MergedCutProfiles.Batch443.valid17752
  · exact MergedCutProfiles.Batch443.valid17756
  · exact MergedCutProfiles.Batch443.valid17759
  · exact MergedCutProfiles.Batch444.valid17762
  · exact MergedCutProfiles.Batch444.valid17764
  · exact MergedCutProfiles.Batch444.valid17766
  · exact MergedCutProfiles.Batch444.valid17767
  · exact MergedCutProfiles.Batch444.valid17768
  · exact MergedCutProfiles.Batch444.valid17769
  · exact MergedCutProfiles.Batch444.valid17770
  · exact MergedCutProfiles.Batch444.valid17771
  · exact MergedCutProfiles.Batch444.valid17772
  · exact MergedCutProfiles.Batch444.valid17773
  · exact MergedCutProfiles.Batch444.valid17774
  · exact MergedCutProfiles.Batch444.valid17775
theorem numericValid2816 : retention2816.NumericValid := by decide +kernel
def certificate2816 : RatCutBinCertificate := ⟨⟨retention2816,(1806443732852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(1170246587419110167/500000000000000000)⟩,(999946513969609047/1000000000000000000),(21536984860952521/62500000000000000),(144137589446581233/500000000000000000),(211787087583118377/1000000000000000000)⟩
theorem valid2816 : certificate2816.Valid := by decide +kernel
theorem sound2816 : certificate2816.Sound := rat_cut_bin_certificate_sound certificate2816 profilesValid2816 numericValid2816 valid2816

def retention2817 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(8000000000000000000/575824971072054274113),(130004051036684401/40000000000000000),(29/20),(457266417681236694828807549830625264471/208006481658695041600000000000000000000),true,MergedCutProfiles.Batch444.profile17776,![MergedCutProfiles.Batch444.profile17776,MergedCutProfiles.Batch444.profile17777,MergedCutProfiles.Batch444.profile17778,MergedCutProfiles.Batch444.profile17779,MergedCutProfiles.Batch444.profile17780,MergedCutProfiles.Batch444.profile17781,MergedCutProfiles.Batch444.profile17782,MergedCutProfiles.Batch444.profile17783,MergedCutProfiles.Batch444.profile17784,MergedCutProfiles.Batch444.profile17785,MergedCutProfiles.Batch444.profile17786,MergedCutProfiles.Batch444.profile17787,MergedCutProfiles.Batch444.profile17788,MergedCutProfiles.Batch444.profile17789,MergedCutProfiles.Batch444.profile17790,MergedCutProfiles.Batch444.profile17791]⟩
theorem profilesValid2817 : retention2817.ProfilesValid := by
  change ∀ j : Fin 16, (retention2817.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch444.valid17776
  · exact MergedCutProfiles.Batch444.valid17777
  · exact MergedCutProfiles.Batch444.valid17778
  · exact MergedCutProfiles.Batch444.valid17779
  · exact MergedCutProfiles.Batch444.valid17780
  · exact MergedCutProfiles.Batch444.valid17781
  · exact MergedCutProfiles.Batch444.valid17782
  · exact MergedCutProfiles.Batch444.valid17783
  · exact MergedCutProfiles.Batch444.valid17784
  · exact MergedCutProfiles.Batch444.valid17785
  · exact MergedCutProfiles.Batch444.valid17786
  · exact MergedCutProfiles.Batch444.valid17787
  · exact MergedCutProfiles.Batch444.valid17788
  · exact MergedCutProfiles.Batch444.valid17789
  · exact MergedCutProfiles.Batch444.valid17790
  · exact MergedCutProfiles.Batch444.valid17791
theorem numericValid2817 : retention2817.NumericValid := by decide +kernel
def certificate2817 : RatCutBinCertificate := ⟨⟨retention2817,(1806443732852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(1098700522040072663/500000000000000000)⟩,(999946513969609047/1000000000000000000),(258837306693418173/1000000000000000000),(195630997886080323/500000000000000000),(224317573992168233/500000000000000000)⟩
theorem valid2817 : certificate2817.Valid := by decide +kernel
theorem sound2817 : certificate2817.Sound := rat_cut_bin_certificate_sound certificate2817 profilesValid2817 numericValid2817 valid2817

def retention2818 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(1/2),64,1,(63842245492489957688683474884787466679/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch444.profile17792,(fun _ => MergedCutProfiles.Batch444.profile17792)⟩
theorem profilesValid2818 : retention2818.ProfilesValid := by
  exact MergedCutProfiles.Batch444.valid17792
theorem numericValid2818 : retention2818.NumericValid := by decide +kernel
def certificate2818 : RatCutBinCertificate := ⟨⟨retention2818,(1806443732852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(996895988672989807/1000000000000000000)⟩,(999946513969609047/1000000000000000000),(419882362722510789/1000000000000000000),(8630043955002719/40000000000000000),(42354229888892703/200000000000000000)⟩
theorem valid2818 : certificate2818.Valid := by decide +kernel
theorem sound2818 : certificate2818.Sound := rat_cut_bin_certificate_sound certificate2818 profilesValid2818 numericValid2818 valid2818

def retention2819 : RatCutRetentionCertificate := ⟨(3/400),(1/125),(8000000000000000000/575824971072054274113),(7656546719584410081/1000000000000000000),1,(5297652664682315756238026309272848699/2552182239861470027000000000000000000),false,MergedCutProfiles.Batch444.profile17793,(fun _ => MergedCutProfiles.Batch444.profile17793)⟩
theorem profilesValid2819 : retention2819.ProfilesValid := by
  exact MergedCutProfiles.Batch444.valid17793
theorem numericValid2819 : retention2819.NumericValid := by decide +kernel
def certificate2819 : RatCutBinCertificate := ⟨⟨retention2819,(1953702420852871401/1000000000000000000),(1291114465089419/500000000000000000),(3649407053359982287/500000000000000000),(16848798986218848632169/500000000000000000),(83001731228509713/40000000000000000)⟩,(99994215386497187/100000000000000000),(14215463938143981/200000000000000000),(367055472486331563/500000000000000000),(1198426879434882361/1000000000000000000)⟩
theorem valid2819 : certificate2819.Valid := by decide +kernel
theorem sound2819 : certificate2819.Sound := rat_cut_bin_certificate_sound certificate2819 profilesValid2819 numericValid2819 valid2819

def certificates : List RatCutBinCertificate := [certificate2808,certificate2809,certificate2810,certificate2811,certificate2812,certificate2813,certificate2814,certificate2815,certificate2816,certificate2817,certificate2818,certificate2819]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2808,List.forall_mem_cons.mpr ⟨sound2809,List.forall_mem_cons.mpr ⟨sound2810,List.forall_mem_cons.mpr ⟨sound2811,List.forall_mem_cons.mpr ⟨sound2812,List.forall_mem_cons.mpr ⟨sound2813,List.forall_mem_cons.mpr ⟨sound2814,List.forall_mem_cons.mpr ⟨sound2815,List.forall_mem_cons.mpr ⟨sound2816,List.forall_mem_cons.mpr ⟨sound2817,List.forall_mem_cons.mpr ⟨sound2818,List.forall_mem_cons.mpr ⟨sound2819,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch234
