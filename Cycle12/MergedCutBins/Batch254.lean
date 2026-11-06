import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch347
import Cycle12.MergedCutProfiles.Batch348
import Cycle12.MergedCutProfiles.Batch470
import Cycle12.MergedCutProfiles.Batch471

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch254

def retention3048 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(6371909817711404396/46774558057064058789),(357727895482713317/200000000000000000),(39/20),(206440267956113443694141355607384585359/114472926554468261440000000000000000000),false,MergedCutProfiles.Batch470.profile18805,(fun _ => MergedCutProfiles.Batch470.profile18805)⟩
theorem profilesValid3048 : retention3048.ProfilesValid := by
  exact MergedCutProfiles.Batch470.valid18805
theorem numericValid3048 : retention3048.NumericValid := by decide +kernel
def certificate3048 : RatCutBinCertificate := ⟨⟨retention3048,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(1781338199298688403/1000000000000000000)⟩,(999080091205210327/1000000000000000000),(101763542624980381/250000000000000000),(45416158205040157/200000000000000000),(5131702731661227/31250000000000000)⟩
theorem valid3048 : certificate3048.Valid := by decide +kernel
theorem sound3048 : certificate3048.Sound := rat_cut_bin_certificate_sound certificate3048 profilesValid3048 numericValid3048 valid3048

def retention3049 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(16000000000000000000/46774558057064058789),(1592977454427851099/62500000000000000),1,(520932264154220150200985580302440443/398244363606962774750000000000000000),false,MergedCutProfiles.Batch470.profile18806,(fun _ => MergedCutProfiles.Batch470.profile18806)⟩
theorem profilesValid3049 : retention3049.ProfilesValid := by
  exact MergedCutProfiles.Batch470.valid18806
theorem numericValid3049 : retention3049.NumericValid := by decide +kernel
def certificate3049 : RatCutBinCertificate := ⟨⟨retention3049,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(25935183594050553/20000000000000000)⟩,(999080091205210327/1000000000000000000),(93087969671088663/250000000000000000),(64948175041939153/250000000000000000),(160138489815473901/500000000000000000)⟩
theorem valid3049 : certificate3049.Valid := by decide +kernel
theorem sound3049 : certificate3049.Sound := rat_cut_bin_certificate_sound certificate3049 profilesValid3049 numericValid3049 valid3049

def retention3050 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid3050 : retention3050.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid3050 : retention3050.NumericValid := by decide +kernel
def certificate3050 : RatCutBinCertificate := ⟨⟨retention3050,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(493134151183011493/500000000000000000)⟩,(999080091205210327/1000000000000000000),(239209030088793717/500000000000000000),(168858392942695871/1000000000000000000),(163859971324513849/1000000000000000000)⟩
theorem valid3050 : certificate3050.Valid := by decide +kernel
theorem sound3050 : certificate3050.Sound := rat_cut_bin_certificate_sound certificate3050 profilesValid3050 numericValid3050 valid3050

def retention3051 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(16000000000000000000/46774558057064058789),(9814259063221209469/1000000000000000000),1,(785483319051327986567470448020878817/613391191451325591812500000000000000),false,MergedCutProfiles.Batch470.profile18806,(fun _ => MergedCutProfiles.Batch470.profile18806)⟩
theorem profilesValid3051 : retention3051.ProfilesValid := by
  exact MergedCutProfiles.Batch470.valid18806
theorem numericValid3051 : retention3051.NumericValid := by decide +kernel
def certificate3051 : RatCutBinCertificate := ⟨⟨retention3051,(526781370483647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(1268415463530062807/1000000000000000000)⟩,(999012569356170881/1000000000000000000),(25366880074236753/250000000000000000),(663125515371982781/1000000000000000000),(744081392678275279/1000000000000000000)⟩
theorem valid3051 : certificate3051.Valid := by decide +kernel
theorem sound3051 : certificate3051.Sound := rat_cut_bin_certificate_sound certificate3051 profilesValid3051 numericValid3051 valid3051

def retention3052 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid3052 : retention3052.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid3052 : retention3052.NumericValid := by decide +kernel
def certificate3052 : RatCutBinCertificate := ⟨⟨retention3052,(526781370483647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(61589874539237237/62500000000000000)⟩,(999012569356170881/1000000000000000000),(4081401263750981/31250000000000000),(601935902607760363/1000000000000000000),(583594100867140109/1000000000000000000)⟩
theorem valid3052 : certificate3052.Valid := by decide +kernel
theorem sound3052 : certificate3052.Sound := rat_cut_bin_certificate_sound certificate3052 profilesValid3052 numericValid3052 valid3052

def retention3053 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(688129263913419701/176443757292995700446),(681316102884573961/1000000000000000000),4,(596775950375707713809/256000000000000000000),true,MergedCutProfiles.Batch470.profile18807,![MergedCutProfiles.Batch470.profile18807,MergedCutProfiles.Batch470.profile18808,MergedCutProfiles.Batch470.profile18809,MergedCutProfiles.Batch347.profile13897,MergedCutProfiles.Batch470.profile18810,MergedCutProfiles.Batch470.profile18811,MergedCutProfiles.Batch470.profile18812,MergedCutProfiles.Batch470.profile18813,MergedCutProfiles.Batch470.profile18814,MergedCutProfiles.Batch470.profile18815,MergedCutProfiles.Batch470.profile18816,MergedCutProfiles.Batch470.profile18817,MergedCutProfiles.Batch470.profile18818,MergedCutProfiles.Batch470.profile18819,MergedCutProfiles.Batch470.profile18820,MergedCutProfiles.Batch470.profile18821]⟩
theorem profilesValid3053 : retention3053.ProfilesValid := by
  change ∀ j : Fin 16, (retention3053.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch470.valid18807
  · exact MergedCutProfiles.Batch470.valid18808
  · exact MergedCutProfiles.Batch470.valid18809
  · exact MergedCutProfiles.Batch347.valid13897
  · exact MergedCutProfiles.Batch470.valid18810
  · exact MergedCutProfiles.Batch470.valid18811
  · exact MergedCutProfiles.Batch470.valid18812
  · exact MergedCutProfiles.Batch470.valid18813
  · exact MergedCutProfiles.Batch470.valid18814
  · exact MergedCutProfiles.Batch470.valid18815
  · exact MergedCutProfiles.Batch470.valid18816
  · exact MergedCutProfiles.Batch470.valid18817
  · exact MergedCutProfiles.Batch470.valid18818
  · exact MergedCutProfiles.Batch470.valid18819
  · exact MergedCutProfiles.Batch470.valid18820
  · exact MergedCutProfiles.Batch470.valid18821
theorem numericValid3053 : retention3053.NumericValid := by decide +kernel
def certificate3053 : RatCutBinCertificate := ⟨⟨retention3053,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(570933658941761009/250000000000000000)⟩,(999038801668559083/1000000000000000000),(249889288095330373/500000000000000000),(76789943476925181/500000000000000000),(36207179604336307/500000000000000000)⟩
theorem valid3053 : certificate3053.Valid := by decide +kernel
theorem sound3053 : certificate3053.Sound := rat_cut_bin_certificate_sound certificate3053 profilesValid3053 numericValid3053 valid3053

def retention3054 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(974805811765518019/176443757292995700446),(688129263913419701/1000000000000000000),(79/20),(2961287464572726936053/1280000000000000000000),true,MergedCutProfiles.Batch470.profile18822,![MergedCutProfiles.Batch470.profile18822,MergedCutProfiles.Batch470.profile18823,MergedCutProfiles.Batch470.profile18824,MergedCutProfiles.Batch470.profile18825,MergedCutProfiles.Batch470.profile18826,MergedCutProfiles.Batch470.profile18827,MergedCutProfiles.Batch347.profile13885,MergedCutProfiles.Batch470.profile18828,MergedCutProfiles.Batch470.profile18829,MergedCutProfiles.Batch347.profile13913,MergedCutProfiles.Batch347.profile13900,MergedCutProfiles.Batch470.profile18830,MergedCutProfiles.Batch470.profile18831,MergedCutProfiles.Batch347.profile13887,MergedCutProfiles.Batch470.profile18832,MergedCutProfiles.Batch470.profile18833]⟩
theorem profilesValid3054 : retention3054.ProfilesValid := by
  change ∀ j : Fin 16, (retention3054.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch470.valid18822
  · exact MergedCutProfiles.Batch470.valid18823
  · exact MergedCutProfiles.Batch470.valid18824
  · exact MergedCutProfiles.Batch470.valid18825
  · exact MergedCutProfiles.Batch470.valid18826
  · exact MergedCutProfiles.Batch470.valid18827
  · exact MergedCutProfiles.Batch347.valid13885
  · exact MergedCutProfiles.Batch470.valid18828
  · exact MergedCutProfiles.Batch470.valid18829
  · exact MergedCutProfiles.Batch347.valid13913
  · exact MergedCutProfiles.Batch347.valid13900
  · exact MergedCutProfiles.Batch470.valid18830
  · exact MergedCutProfiles.Batch470.valid18831
  · exact MergedCutProfiles.Batch347.valid13887
  · exact MergedCutProfiles.Batch470.valid18832
  · exact MergedCutProfiles.Batch470.valid18833
theorem numericValid3054 : retention3054.NumericValid := by decide +kernel
def certificate3054 : RatCutBinCertificate := ⟨⟨retention3054,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(2266677177530617001/1000000000000000000)⟩,(999038801668559083/1000000000000000000),(125145605022207983/250000000000000000),(38255749077734097/250000000000000000),(4526390994795587/62500000000000000)⟩
theorem valid3054 : certificate3054.Valid := by decide +kernel
theorem sound3054 : certificate3054.Sound := rat_cut_bin_certificate_sound certificate3054 profilesValid3054 numericValid3054 valid3054

def retention3055 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(572108966500000000/88221878646497850223),(974805811765518019/1000000000000000000),(59/20),(2932972403530708562627/1280000000000000000000),true,MergedCutProfiles.Batch470.profile18834,![MergedCutProfiles.Batch470.profile18834,MergedCutProfiles.Batch347.profile13883,MergedCutProfiles.Batch470.profile18810,MergedCutProfiles.Batch347.profile13884,MergedCutProfiles.Batch470.profile18835,MergedCutProfiles.Batch347.profile13885,MergedCutProfiles.Batch347.profile13899,MergedCutProfiles.Batch347.profile13886,MergedCutProfiles.Batch470.profile18820,MergedCutProfiles.Batch470.profile18836,MergedCutProfiles.Batch470.profile18837,MergedCutProfiles.Batch347.profile13887,MergedCutProfiles.Batch470.profile18838,MergedCutProfiles.Batch347.profile13902,MergedCutProfiles.Batch470.profile18839,MergedCutProfiles.Batch347.profile13889]⟩
theorem profilesValid3055 : retention3055.ProfilesValid := by
  change ∀ j : Fin 16, (retention3055.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch470.valid18834
  · exact MergedCutProfiles.Batch347.valid13883
  · exact MergedCutProfiles.Batch470.valid18810
  · exact MergedCutProfiles.Batch347.valid13884
  · exact MergedCutProfiles.Batch470.valid18835
  · exact MergedCutProfiles.Batch347.valid13885
  · exact MergedCutProfiles.Batch347.valid13899
  · exact MergedCutProfiles.Batch347.valid13886
  · exact MergedCutProfiles.Batch470.valid18820
  · exact MergedCutProfiles.Batch470.valid18836
  · exact MergedCutProfiles.Batch470.valid18837
  · exact MergedCutProfiles.Batch347.valid13887
  · exact MergedCutProfiles.Batch470.valid18838
  · exact MergedCutProfiles.Batch347.valid13902
  · exact MergedCutProfiles.Batch470.valid18839
  · exact MergedCutProfiles.Batch347.valid13889
theorem numericValid3055 : retention3055.NumericValid := by decide +kernel
def certificate3055 : RatCutBinCertificate := ⟨⟨retention3055,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(1128205707742183631/500000000000000000)⟩,(999038801668559083/1000000000000000000),(415498716489819291/1000000000000000000),(8783119960675069/40000000000000000),(66258715324411209/500000000000000000)⟩
theorem valid3055 : certificate3055.Valid := by decide +kernel
theorem sound3055 : certificate3055.Sound := rat_cut_bin_certificate_sound certificate3055 profilesValid3055 numericValid3055 valid3055

def retention3056 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(725676510214352814/88221878646497850223),(1144217933/1000000000),(13/5),(36344064463249574343/16000000000000000000),true,MergedCutProfiles.Batch471.profile18840,![MergedCutProfiles.Batch471.profile18840,MergedCutProfiles.Batch470.profile18824,MergedCutProfiles.Batch471.profile18841,MergedCutProfiles.Batch470.profile18835,MergedCutProfiles.Batch471.profile18842,MergedCutProfiles.Batch471.profile18843,MergedCutProfiles.Batch471.profile18844,MergedCutProfiles.Batch470.profile18830,MergedCutProfiles.Batch346.profile13873,MergedCutProfiles.Batch471.profile18845,MergedCutProfiles.Batch347.profile13902,MergedCutProfiles.Batch471.profile18846,MergedCutProfiles.Batch346.profile13876,MergedCutProfiles.Batch471.profile18847,MergedCutProfiles.Batch471.profile18848,MergedCutProfiles.Batch471.profile18849]⟩
theorem profilesValid3056 : retention3056.ProfilesValid := by
  change ∀ j : Fin 16, (retention3056.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch471.valid18840
  · exact MergedCutProfiles.Batch470.valid18824
  · exact MergedCutProfiles.Batch471.valid18841
  · exact MergedCutProfiles.Batch470.valid18835
  · exact MergedCutProfiles.Batch471.valid18842
  · exact MergedCutProfiles.Batch471.valid18843
  · exact MergedCutProfiles.Batch471.valid18844
  · exact MergedCutProfiles.Batch470.valid18830
  · exact MergedCutProfiles.Batch346.valid13873
  · exact MergedCutProfiles.Batch471.valid18845
  · exact MergedCutProfiles.Batch347.valid13902
  · exact MergedCutProfiles.Batch471.valid18846
  · exact MergedCutProfiles.Batch346.valid13876
  · exact MergedCutProfiles.Batch471.valid18847
  · exact MergedCutProfiles.Batch471.valid18848
  · exact MergedCutProfiles.Batch471.valid18849
theorem numericValid3056 : retention3056.NumericValid := by decide +kernel
def certificate3056 : RatCutBinCertificate := ⟨⟨retention3056,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(1120340068946924923/500000000000000000)⟩,(999038801668559083/1000000000000000000),(48393746772120967/125000000000000000),(245464740297562497/1000000000000000000),(163844543581802877/1000000000000000000)⟩
theorem valid3056 : certificate3056.Valid := by decide +kernel
theorem sound3056 : certificate3056.Sound := rat_cut_bin_certificate_sound certificate3056 profilesValid3056 numericValid3056 valid3056

def retention3057 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(12575092024660275869/176443757292995700446),(362838255107176407/250000000000000000),(11/5),(637400713053794585007/320000000000000000000),true,MergedCutProfiles.Batch470.profile18837,![MergedCutProfiles.Batch470.profile18837,MergedCutProfiles.Batch471.profile18850,MergedCutProfiles.Batch347.profile13908,MergedCutProfiles.Batch471.profile18851,MergedCutProfiles.Batch471.profile18852,MergedCutProfiles.Batch471.profile18853,MergedCutProfiles.Batch471.profile18854,MergedCutProfiles.Batch471.profile18855,MergedCutProfiles.Batch471.profile18856,MergedCutProfiles.Batch471.profile18857,MergedCutProfiles.Batch471.profile18858,MergedCutProfiles.Batch471.profile18859,MergedCutProfiles.Batch471.profile18860,MergedCutProfiles.Batch471.profile18861,MergedCutProfiles.Batch471.profile18862,MergedCutProfiles.Batch471.profile18863]⟩
theorem profilesValid3057 : retention3057.ProfilesValid := by
  change ∀ j : Fin 16, (retention3057.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch470.valid18837
  · exact MergedCutProfiles.Batch471.valid18850
  · exact MergedCutProfiles.Batch347.valid13908
  · exact MergedCutProfiles.Batch471.valid18851
  · exact MergedCutProfiles.Batch471.valid18852
  · exact MergedCutProfiles.Batch471.valid18853
  · exact MergedCutProfiles.Batch471.valid18854
  · exact MergedCutProfiles.Batch471.valid18855
  · exact MergedCutProfiles.Batch471.valid18856
  · exact MergedCutProfiles.Batch471.valid18857
  · exact MergedCutProfiles.Batch471.valid18858
  · exact MergedCutProfiles.Batch471.valid18859
  · exact MergedCutProfiles.Batch471.valid18860
  · exact MergedCutProfiles.Batch471.valid18861
  · exact MergedCutProfiles.Batch471.valid18862
  · exact MergedCutProfiles.Batch471.valid18863
theorem numericValid3057 : retention3057.NumericValid := by decide +kernel
def certificate3057 : RatCutBinCertificate := ⟨⟨retention3057,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(393159098923807687/200000000000000000)⟩,(999038801668559083/1000000000000000000),(198945701913098273/500000000000000000),(117709964600900673/500000000000000000),(41045397845886453/250000000000000000)⟩
theorem valid3057 : certificate3057.Valid := by decide +kernel
theorem sound3057 : certificate3057.Sound := rat_cut_bin_certificate_sound certificate3057 profilesValid3057 numericValid3057 valid3057

def retention3058 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(32000000000000000000/88221878646497850223),(12575092024660275869/1000000000000000000),(21/20),(25621144453024290367579750593853794382079/20120147239456441390400000000000000000000),false,MergedCutProfiles.Batch471.profile18864,(fun _ => MergedCutProfiles.Batch471.profile18864)⟩
theorem profilesValid3058 : retention3058.ProfilesValid := by
  exact MergedCutProfiles.Batch471.valid18864
theorem numericValid3058 : retention3058.NumericValid := by decide +kernel
def certificate3058 : RatCutBinCertificate := ⟨⟨retention3058,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(1260959403512687507/1000000000000000000)⟩,(999038801668559083/1000000000000000000),(79470968245962913/200000000000000000),(117957375524124329/500000000000000000),(3242925712868431/12500000000000000)⟩
theorem valid3058 : certificate3058.Valid := by decide +kernel
theorem sound3058 : certificate3058.Sound := rat_cut_bin_certificate_sound certificate3058 profilesValid3058 numericValid3058 valid3058

def retention3059 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),64,1,(255381539274569722621815190999861472551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid3059 : retention3059.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid3059 : retention3059.NumericValid := by decide +kernel
def certificate3059 : RatCutBinCertificate := ⟨⟨retention3059,(1970861142369050987/1000000000000000000),(65254397982896969/1000000000000000000),(10848174231108216483/1000000000000000000),(1924254854081980321927/1000000000000000000),(492864461965750109/500000000000000000)⟩,(999038801668559083/1000000000000000000),(478403288258754381/1000000000000000000),(33773856802715643/200000000000000000),(163775447452518313/1000000000000000000)⟩
theorem valid3059 : certificate3059.Valid := by decide +kernel
theorem sound3059 : certificate3059.Sound := rat_cut_bin_certificate_sound certificate3059 profilesValid3059 numericValid3059 valid3059

def certificates : List RatCutBinCertificate := [certificate3048,certificate3049,certificate3050,certificate3051,certificate3052,certificate3053,certificate3054,certificate3055,certificate3056,certificate3057,certificate3058,certificate3059]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3048,List.forall_mem_cons.mpr ⟨sound3049,List.forall_mem_cons.mpr ⟨sound3050,List.forall_mem_cons.mpr ⟨sound3051,List.forall_mem_cons.mpr ⟨sound3052,List.forall_mem_cons.mpr ⟨sound3053,List.forall_mem_cons.mpr ⟨sound3054,List.forall_mem_cons.mpr ⟨sound3055,List.forall_mem_cons.mpr ⟨sound3056,List.forall_mem_cons.mpr ⟨sound3057,List.forall_mem_cons.mpr ⟨sound3058,List.forall_mem_cons.mpr ⟨sound3059,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch254
