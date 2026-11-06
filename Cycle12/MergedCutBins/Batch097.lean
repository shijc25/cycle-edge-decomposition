import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch193
import Cycle12.MergedCutProfiles.Batch194
import Cycle12.MergedCutProfiles.Batch195

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch097

def retention1164 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(6921184524133004983/14995118204438142946),(933673993516170141/250000000000000000),(6/5),(400215853433806054561834615003107464519/373469597406468056400000000000000000000),false,MergedCutProfiles.Batch193.profile7748,(fun _ => MergedCutProfiles.Batch193.profile7748)⟩
theorem profilesValid1164 : retention1164.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7748
theorem numericValid1164 : retention1164.NumericValid := by decide +kernel
def certificate1164 : RatCutBinCertificate := ⟨⟨retention1164,(2593357413599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(207799562442639883/200000000000000000)⟩,(197972845363416081/200000000000000000),(384918937806417667/1000000000000000000),(247588172273569603/1000000000000000000),(177662135711886119/1000000000000000000)⟩
theorem valid1164 : certificate1164.Valid := by decide +kernel
theorem sound1164 : certificate1164.Sound := rat_cut_bin_certificate_sound certificate1164 profilesValid1164 numericValid1164 valid1164

def retention1165 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(7420446606778927751/14995118204438142946),(6921184524133004983/1000000000000000000),(21/20),(11028199444479043384114377522472146716471/11073895238612807972800000000000000000000),false,MergedCutProfiles.Batch193.profile7749,(fun _ => MergedCutProfiles.Batch193.profile7749)⟩
theorem profilesValid1165 : retention1165.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7749
theorem numericValid1165 : retention1165.NumericValid := by decide +kernel
def certificate1165 : RatCutBinCertificate := ⟨⟨retention1165,(2593357413599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(967334677882232981/1000000000000000000)⟩,(197972845363416081/200000000000000000),(413434919066331173/1000000000000000000),(55348915279510943/250000000000000000),(89533245558877903/500000000000000000)⟩
theorem valid1165 : certificate1165.Valid := by decide +kernel
theorem sound1165 : certificate1165.Sound := rat_cut_bin_certificate_sound certificate1165 profilesValid1165 numericValid1165 valid1165

def retention1166 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(7494651072846717029/14995118204438142946),(7420446606778927751/1000000000000000000),(21/20),(11736833143613269645860672739300895843519/11872714570846284401600000000000000000000),false,MergedCutProfiles.Batch193.profile7750,(fun _ => MergedCutProfiles.Batch193.profile7750)⟩
theorem profilesValid1166 : retention1166.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7750
theorem numericValid1166 : retention1166.NumericValid := by decide +kernel
def certificate1166 : RatCutBinCertificate := ⟨⟨retention1166,(2593357413599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(240004113880521863/250000000000000000)⟩,(197972845363416081/200000000000000000),(416586540740910449/1000000000000000000),(109312019935053107/500000000000000000),(88486983045629947/500000000000000000)⟩
theorem valid1166 : certificate1166.Valid := by decide +kernel
theorem sound1166 : certificate1166.Sound := rat_cut_bin_certificate_sound certificate1166 profilesValid1166 numericValid1166 valid1166

def retention1167 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1/2),(7494651072846717029/1000000000000000000),(21/20),(11853197464045406788674522058771430635679/11991441716554747246400000000000000000000),false,MergedCutProfiles.Batch193.profile7747,(fun _ => MergedCutProfiles.Batch193.profile7747)⟩
theorem profilesValid1167 : retention1167.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7747
theorem numericValid1167 : retention1167.NumericValid := by decide +kernel
def certificate1167 : RatCutBinCertificate := ⟨⟨retention1167,(2593357413599441323/1000000000000000000),(30403935940526677/200000000000000000),(7253142565918527661/500000000000000000),(21816897607164609127/100000000000000000),(959932753492374017/1000000000000000000)⟩,(197972845363416081/200000000000000000),(416622865305193159/1000000000000000000),(218592234358110709/1000000000000000000),(177119530234843097/1000000000000000000)⟩
theorem valid1167 : certificate1167.Valid := by decide +kernel
theorem sound1167 : certificate1167.Sound := rat_cut_bin_certificate_sound certificate1167 profilesValid1167 numericValid1167 valid1167

def retention1168 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(906730481465439172/14684821021866378471),(418675193473321133/500000000000000000),(57/20),(1290174990586728950077/640000000000000000000),true,MergedCutProfiles.Batch193.profile7751,![MergedCutProfiles.Batch193.profile7751,MergedCutProfiles.Batch193.profile7752,MergedCutProfiles.Batch193.profile7753,MergedCutProfiles.Batch193.profile7754,MergedCutProfiles.Batch193.profile7755,MergedCutProfiles.Batch193.profile7756,MergedCutProfiles.Batch193.profile7757,MergedCutProfiles.Batch193.profile7758,MergedCutProfiles.Batch193.profile7759,MergedCutProfiles.Batch194.profile7760,MergedCutProfiles.Batch194.profile7761,MergedCutProfiles.Batch194.profile7762,MergedCutProfiles.Batch194.profile7763,MergedCutProfiles.Batch194.profile7764,MergedCutProfiles.Batch194.profile7765,MergedCutProfiles.Batch194.profile7766]⟩
theorem profilesValid1168 : retention1168.ProfilesValid := by
  change ∀ j : Fin 16, (retention1168.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch193.valid7751
  · exact MergedCutProfiles.Batch193.valid7752
  · exact MergedCutProfiles.Batch193.valid7753
  · exact MergedCutProfiles.Batch193.valid7754
  · exact MergedCutProfiles.Batch193.valid7755
  · exact MergedCutProfiles.Batch193.valid7756
  · exact MergedCutProfiles.Batch193.valid7757
  · exact MergedCutProfiles.Batch193.valid7758
  · exact MergedCutProfiles.Batch193.valid7759
  · exact MergedCutProfiles.Batch194.valid7760
  · exact MergedCutProfiles.Batch194.valid7761
  · exact MergedCutProfiles.Batch194.valid7762
  · exact MergedCutProfiles.Batch194.valid7763
  · exact MergedCutProfiles.Batch194.valid7764
  · exact MergedCutProfiles.Batch194.valid7765
  · exact MergedCutProfiles.Batch194.valid7766
theorem numericValid1168 : retention1168.NumericValid := by decide +kernel
def certificate1168 : RatCutBinCertificate := ⟨⟨retention1168,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(1947968244671854993/1000000000000000000)⟩,(198229369835747023/200000000000000000),(23260558286332203/62500000000000000),(259973464141949767/1000000000000000000),(27333291233960047/200000000000000000)⟩
theorem valid1168 : certificate1168.Valid := by decide +kernel
theorem sound1168 : certificate1168.Sound := rat_cut_bin_certificate_sound certificate1168 profilesValid1168 numericValid1168 valid1168

def retention1169 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(41318124584630536/444994576420193287),(226682620366359793/250000000000000000),(53/20),(153787949909424265133/80000000000000000000),true,MergedCutProfiles.Batch194.profile7767,![MergedCutProfiles.Batch194.profile7767,MergedCutProfiles.Batch193.profile7753,MergedCutProfiles.Batch194.profile7768,MergedCutProfiles.Batch194.profile7769,MergedCutProfiles.Batch194.profile7770,MergedCutProfiles.Batch194.profile7771,MergedCutProfiles.Batch194.profile7772,MergedCutProfiles.Batch194.profile7773,MergedCutProfiles.Batch194.profile7774,MergedCutProfiles.Batch194.profile7775,MergedCutProfiles.Batch194.profile7776,MergedCutProfiles.Batch194.profile7777,MergedCutProfiles.Batch194.profile7778,MergedCutProfiles.Batch194.profile7779,MergedCutProfiles.Batch194.profile7780,MergedCutProfiles.Batch194.profile7781]⟩
theorem profilesValid1169 : retention1169.ProfilesValid := by
  change ∀ j : Fin 16, (retention1169.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch194.valid7767
  · exact MergedCutProfiles.Batch193.valid7753
  · exact MergedCutProfiles.Batch194.valid7768
  · exact MergedCutProfiles.Batch194.valid7769
  · exact MergedCutProfiles.Batch194.valid7770
  · exact MergedCutProfiles.Batch194.valid7771
  · exact MergedCutProfiles.Batch194.valid7772
  · exact MergedCutProfiles.Batch194.valid7773
  · exact MergedCutProfiles.Batch194.valid7774
  · exact MergedCutProfiles.Batch194.valid7775
  · exact MergedCutProfiles.Batch194.valid7776
  · exact MergedCutProfiles.Batch194.valid7777
  · exact MergedCutProfiles.Batch194.valid7778
  · exact MergedCutProfiles.Batch194.valid7779
  · exact MergedCutProfiles.Batch194.valid7780
  · exact MergedCutProfiles.Batch194.valid7781
theorem numericValid1169 : retention1169.NumericValid := by decide +kernel
def certificate1169 : RatCutBinCertificate := ⟨⟨retention1169,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(1859186355740760303/1000000000000000000)⟩,(198229369835747023/200000000000000000),(377694768534542349/1000000000000000000),(127276483570499483/500000000000000000),(136767373629834427/1000000000000000000)⟩
theorem valid1169 : certificate1169.Valid := by decide +kernel
theorem sound1169 : certificate1169.Sound := rat_cut_bin_certificate_sound certificate1169 profilesValid1169 numericValid1169 valid1169

def retention1170 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(3439872158461217029/14684821021866378471),(170437263911600961/125000000000000000),(19/10),(248240325263450008947/160000000000000000000),true,MergedCutProfiles.Batch194.profile7782,![MergedCutProfiles.Batch194.profile7782,MergedCutProfiles.Batch194.profile7783,MergedCutProfiles.Batch194.profile7784,MergedCutProfiles.Batch194.profile7785,MergedCutProfiles.Batch194.profile7786,MergedCutProfiles.Batch194.profile7787,MergedCutProfiles.Batch194.profile7788,MergedCutProfiles.Batch194.profile7789,MergedCutProfiles.Batch194.profile7790,MergedCutProfiles.Batch194.profile7791,MergedCutProfiles.Batch194.profile7792,MergedCutProfiles.Batch194.profile7793,MergedCutProfiles.Batch194.profile7794,MergedCutProfiles.Batch194.profile7795,MergedCutProfiles.Batch194.profile7796,MergedCutProfiles.Batch194.profile7797]⟩
theorem profilesValid1170 : retention1170.ProfilesValid := by
  change ∀ j : Fin 16, (retention1170.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch194.valid7782
  · exact MergedCutProfiles.Batch194.valid7783
  · exact MergedCutProfiles.Batch194.valid7784
  · exact MergedCutProfiles.Batch194.valid7785
  · exact MergedCutProfiles.Batch194.valid7786
  · exact MergedCutProfiles.Batch194.valid7787
  · exact MergedCutProfiles.Batch194.valid7788
  · exact MergedCutProfiles.Batch194.valid7789
  · exact MergedCutProfiles.Batch194.valid7790
  · exact MergedCutProfiles.Batch194.valid7791
  · exact MergedCutProfiles.Batch194.valid7792
  · exact MergedCutProfiles.Batch194.valid7793
  · exact MergedCutProfiles.Batch194.valid7794
  · exact MergedCutProfiles.Batch194.valid7795
  · exact MergedCutProfiles.Batch194.valid7796
  · exact MergedCutProfiles.Batch194.valid7797
theorem numericValid1170 : retention1170.NumericValid := by decide +kernel
def certificate1170 : RatCutBinCertificate := ⟨⟨retention1170,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(753108162153820649/500000000000000000)⟩,(198229369835747023/200000000000000000),(405088378231952161/1000000000000000000),(114426175027340111/500000000000000000),(6873219685656041/50000000000000000)⟩
theorem valid1170 : certificate1170.Valid := by decide +kernel
theorem sound1170 : certificate1170.Sound := rat_cut_bin_certificate_sound certificate1170 profilesValid1170 numericValid1170 valid1170

def retention1171 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(2103898812565538138/4894940340622126157),(3439872158461217029/1000000000000000000),(11/10),(1416625381714696445377/1280000000000000000000),true,MergedCutProfiles.Batch194.profile7798,![MergedCutProfiles.Batch194.profile7798,MergedCutProfiles.Batch194.profile7799,MergedCutProfiles.Batch195.profile7800,MergedCutProfiles.Batch195.profile7801,MergedCutProfiles.Batch195.profile7802,MergedCutProfiles.Batch195.profile7803,MergedCutProfiles.Batch195.profile7804,MergedCutProfiles.Batch195.profile7805,MergedCutProfiles.Batch195.profile7806,MergedCutProfiles.Batch195.profile7807,MergedCutProfiles.Batch195.profile7808,MergedCutProfiles.Batch195.profile7809,MergedCutProfiles.Batch195.profile7810,MergedCutProfiles.Batch195.profile7811,MergedCutProfiles.Batch195.profile7812,MergedCutProfiles.Batch195.profile7813]⟩
theorem profilesValid1171 : retention1171.ProfilesValid := by
  change ∀ j : Fin 16, (retention1171.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch194.valid7798
  · exact MergedCutProfiles.Batch194.valid7799
  · exact MergedCutProfiles.Batch195.valid7800
  · exact MergedCutProfiles.Batch195.valid7801
  · exact MergedCutProfiles.Batch195.valid7802
  · exact MergedCutProfiles.Batch195.valid7803
  · exact MergedCutProfiles.Batch195.valid7804
  · exact MergedCutProfiles.Batch195.valid7805
  · exact MergedCutProfiles.Batch195.valid7806
  · exact MergedCutProfiles.Batch195.valid7807
  · exact MergedCutProfiles.Batch195.valid7808
  · exact MergedCutProfiles.Batch195.valid7809
  · exact MergedCutProfiles.Batch195.valid7810
  · exact MergedCutProfiles.Batch195.valid7811
  · exact MergedCutProfiles.Batch195.valid7812
  · exact MergedCutProfiles.Batch195.valid7813
theorem numericValid1171 : retention1171.NumericValid := by decide +kernel
def certificate1171 : RatCutBinCertificate := ⟨⟨retention1171,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(216104567043130043/200000000000000000)⟩,(198229369835747023/200000000000000000),(231298703677599701/500000000000000000),(22598366330900341/125000000000000000),(69789717602919933/500000000000000000)⟩
theorem valid1171 : certificate1171.Valid := by decide +kernel
theorem sound1171 : certificate1171.Sound := rat_cut_bin_certificate_sound certificate1171 profilesValid1171 numericValid1171 valid1171

def retention1172 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(7183299303877246826/14684821021866378471),(3155848218848307207/500000000000000000),(11/10),(642042543325821134580478288315624090151/631169643769661441400000000000000000000),false,MergedCutProfiles.Batch195.profile7814,(fun _ => MergedCutProfiles.Batch195.profile7814)⟩
theorem profilesValid1172 : retention1172.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7814
theorem numericValid1172 : retention1172.NumericValid := by decide +kernel
def certificate1172 : RatCutBinCertificate := ⟨⟨retention1172,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(198202622737582853/200000000000000000)⟩,(198229369835747023/200000000000000000),(471123771582880281/1000000000000000000),(174292116707389193/1000000000000000000),(137662770110616971/1000000000000000000)⟩
theorem valid1172 : certificate1172.Valid := by decide +kernel
theorem sound1172 : certificate1172.Sound := rat_cut_bin_certificate_sound certificate1172 profilesValid1172 numericValid1172 valid1172

def retention1173 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(2418377432305339765/4894940340622126157),(3591649651938623413/500000000000000000),(21/20),(2869284498535158858092562703010486465231/2873319721550898730400000000000000000000),false,MergedCutProfiles.Batch195.profile7815,(fun _ => MergedCutProfiles.Batch195.profile7815)⟩
theorem profilesValid1173 : retention1173.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7815
theorem numericValid1173 : retention1173.NumericValid := by decide +kernel
def certificate1173 : RatCutBinCertificate := ⟨⟨retention1173,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(121696734589490623/125000000000000000)⟩,(198229369835747023/200000000000000000),(474642870024800569/1000000000000000000),(17165664809928111/100000000000000000),(140393747476040189/1000000000000000000)⟩
theorem valid1173 : certificate1173.Valid := by decide +kernel
theorem sound1173 : certificate1173.Sound := rat_cut_bin_certificate_sound certificate1173 profilesValid1173 numericValid1173 valid1173

def retention1174 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(7327683619885179488/14684821021866378471),(1451026459383203859/200000000000000000),(21/20),(459424950766076362387760786202545182679/464328467002625234880000000000000000000),false,MergedCutProfiles.Batch195.profile7816,(fun _ => MergedCutProfiles.Batch195.profile7816)⟩
theorem profilesValid1174 : retention1174.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7816
theorem numericValid1174 : retention1174.NumericValid := by decide +kernel
def certificate1174 : RatCutBinCertificate := ⟨⟨retention1174,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(60276114364255727/62500000000000000)⟩,(198229369835747023/200000000000000000),(478792963606680981/1000000000000000000),(42145534000161809/250000000000000000),(68435521041995269/500000000000000000)⟩
theorem valid1174 : certificate1174.Valid := by decide +kernel
theorem sound1174 : certificate1174.Sound := rat_cut_bin_certificate_sound certificate1174 profilesValid1174 numericValid1174 valid1174

def retention1175 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(1/2),(228990113121411859/31250000000000000),(21/20),(180960056974226760365499262740140175159/183192090497129487200000000000000000000),false,MergedCutProfiles.Batch195.profile7817,(fun _ => MergedCutProfiles.Batch195.profile7817)⟩
theorem profilesValid1175 : retention1175.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7817
theorem numericValid1175 : retention1175.NumericValid := by decide +kernel
def certificate1175 : RatCutBinCertificate := ⟨⟨retention1175,(2246536598270571/1000000000000000),(155212952940275013/1000000000000000000),(7316857608312187941/500000000000000000),(215533313156228691711/1000000000000000000),(481397092629412107/500000000000000000)⟩,(198229369835747023/200000000000000000),(239623613288575707/500000000000000000),(5257743571877409/31250000000000000),(136540315046663771/1000000000000000000)⟩
theorem valid1175 : certificate1175.Valid := by decide +kernel
theorem sound1175 : certificate1175.Sound := rat_cut_bin_certificate_sound certificate1175 profilesValid1175 numericValid1175 valid1175

def certificates : List RatCutBinCertificate := [certificate1164,certificate1165,certificate1166,certificate1167,certificate1168,certificate1169,certificate1170,certificate1171,certificate1172,certificate1173,certificate1174,certificate1175]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1164,List.forall_mem_cons.mpr ⟨sound1165,List.forall_mem_cons.mpr ⟨sound1166,List.forall_mem_cons.mpr ⟨sound1167,List.forall_mem_cons.mpr ⟨sound1168,List.forall_mem_cons.mpr ⟨sound1169,List.forall_mem_cons.mpr ⟨sound1170,List.forall_mem_cons.mpr ⟨sound1171,List.forall_mem_cons.mpr ⟨sound1172,List.forall_mem_cons.mpr ⟨sound1173,List.forall_mem_cons.mpr ⟨sound1174,List.forall_mem_cons.mpr ⟨sound1175,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch097
