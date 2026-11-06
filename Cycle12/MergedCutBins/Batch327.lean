import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch336
import Cycle12.MergedCutProfiles.Batch337
import Cycle12.MergedCutProfiles.Batch338
import Cycle12.MergedCutProfiles.Batch339
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch465
import Cycle12.MergedCutProfiles.Batch466
import Cycle12.MergedCutProfiles.Batch596
import Cycle12.MergedCutProfiles.Batch597
import Cycle12.MergedCutProfiles.Batch598

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch327

def retention3924 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(32000000000000000000/513445127041050074639),(21819718893898134887/1000000000000000000),1,(8650476862376990349625777189292529837/4363943778779626977400000000000000000),false,MergedCutProfiles.Batch596.profile23874,(fun _ => MergedCutProfiles.Batch596.profile23874)⟩
theorem profilesValid3924 : retention3924.ProfilesValid := by
  exact MergedCutProfiles.Batch596.valid23874
theorem numericValid3924 : retention3924.NumericValid := by decide +kernel
def certificate3924 : RatCutBinCertificate := ⟨⟨retention3924,(1809609361896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(123378080230082773/62500000000000000)⟩,(999831001573772041/1000000000000000000),(3182412902932969/100000000000000000),(838968793196717333/1000000000000000000),(379624707541231047/250000000000000000)⟩
theorem valid3924 : certificate3924.Valid := by decide +kernel
theorem sound3924 : certificate3924.Sound := rat_cut_bin_certificate_sound certificate3924 profilesValid3924 numericValid3924 valid3924

def retention3925 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),64,1,(255377162141591932400424606355354448199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid3925 : retention3925.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid3925 : retention3925.NumericValid := by decide +kernel
def certificate3925 : RatCutBinCertificate := ⟨⟨retention3925,(1809609361896884107/1000000000000000000),(9018985876591161/200000000000000000),(124214676063420639/12500000000000000),(1282078338356391269001/125000000000000000),(989355025687601103/1000000000000000000)⟩,(999831001573772041/1000000000000000000),(992161520053001/15625000000000000),(376554922379198923/500000000000000000),(366812526399904041/500000000000000000)⟩
theorem valid3925 : certificate3925.Valid := by decide +kernel
theorem sound3925 : certificate3925.Sound := rat_cut_bin_certificate_sound certificate3925 profilesValid3925 numericValid3925 valid3925

def retention3926 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(569103371502828431/960649900360527327901),(563468684656265773/1000000000000000000),4,(1926637895338922825777808632108583/880419819775415270312500000000000),true,MergedCutProfiles.Batch596.profile23875,![MergedCutProfiles.Batch596.profile23875,MergedCutProfiles.Batch596.profile23876,MergedCutProfiles.Batch596.profile23877,MergedCutProfiles.Batch596.profile23878,MergedCutProfiles.Batch596.profile23879,MergedCutProfiles.Batch597.profile23880,MergedCutProfiles.Batch597.profile23881,MergedCutProfiles.Batch465.profile18621,MergedCutProfiles.Batch465.profile18611,MergedCutProfiles.Batch597.profile23882,MergedCutProfiles.Batch465.profile18639,MergedCutProfiles.Batch597.profile23883,MergedCutProfiles.Batch336.profile13476,MergedCutProfiles.Batch465.profile18612,MergedCutProfiles.Batch597.profile23884,MergedCutProfiles.Batch337.profile13492]⟩
theorem profilesValid3926 : retention3926.ProfilesValid := by
  change ∀ j : Fin 16, (retention3926.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch596.valid23875
  · exact MergedCutProfiles.Batch596.valid23876
  · exact MergedCutProfiles.Batch596.valid23877
  · exact MergedCutProfiles.Batch596.valid23878
  · exact MergedCutProfiles.Batch596.valid23879
  · exact MergedCutProfiles.Batch597.valid23880
  · exact MergedCutProfiles.Batch597.valid23881
  · exact MergedCutProfiles.Batch465.valid18621
  · exact MergedCutProfiles.Batch465.valid18611
  · exact MergedCutProfiles.Batch597.valid23882
  · exact MergedCutProfiles.Batch465.valid18639
  · exact MergedCutProfiles.Batch597.valid23883
  · exact MergedCutProfiles.Batch336.valid13476
  · exact MergedCutProfiles.Batch465.valid18612
  · exact MergedCutProfiles.Batch597.valid23884
  · exact MergedCutProfiles.Batch337.valid13492
theorem numericValid3926 : retention3926.NumericValid := by decide +kernel
def certificate3926 : RatCutBinCertificate := ⟨⟨retention3926,(115359482684794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(215304663617237671/100000000000000000)⟩,(249954731915541519/250000000000000000),(184615698155258157/250000000000000000),(9411672510627781/250000000000000000),(16353774030614661/1000000000000000000)⟩
theorem valid3926 : certificate3926.Valid := by decide +kernel
theorem sound3926 : certificate3926.Sound := rat_cut_bin_certificate_sound certificate3926 profilesValid3926 numericValid3926 valid3926

def retention3927 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1180353255000000000/960649900360527327901),(569103371502828431/1000000000000000000),4,(140583102156554822207/64000000000000000000),true,MergedCutProfiles.Batch596.profile23876,![MergedCutProfiles.Batch596.profile23876,MergedCutProfiles.Batch597.profile23885,MergedCutProfiles.Batch597.profile23886,MergedCutProfiles.Batch465.profile18621,MergedCutProfiles.Batch597.profile23887,MergedCutProfiles.Batch597.profile23883,MergedCutProfiles.Batch597.profile23888,MergedCutProfiles.Batch465.profile18622,MergedCutProfiles.Batch465.profile18613,MergedCutProfiles.Batch597.profile23889,MergedCutProfiles.Batch465.profile18614,MergedCutProfiles.Batch336.profile13477,MergedCutProfiles.Batch597.profile23890,MergedCutProfiles.Batch597.profile23891,MergedCutProfiles.Batch597.profile23892,MergedCutProfiles.Batch465.profile18629]⟩
theorem profilesValid3927 : retention3927.ProfilesValid := by
  change ∀ j : Fin 16, (retention3927.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch596.valid23876
  · exact MergedCutProfiles.Batch597.valid23885
  · exact MergedCutProfiles.Batch597.valid23886
  · exact MergedCutProfiles.Batch465.valid18621
  · exact MergedCutProfiles.Batch597.valid23887
  · exact MergedCutProfiles.Batch597.valid23883
  · exact MergedCutProfiles.Batch597.valid23888
  · exact MergedCutProfiles.Batch465.valid18622
  · exact MergedCutProfiles.Batch465.valid18613
  · exact MergedCutProfiles.Batch597.valid23889
  · exact MergedCutProfiles.Batch465.valid18614
  · exact MergedCutProfiles.Batch336.valid13477
  · exact MergedCutProfiles.Batch597.valid23890
  · exact MergedCutProfiles.Batch597.valid23891
  · exact MergedCutProfiles.Batch597.valid23892
  · exact MergedCutProfiles.Batch465.valid18629
theorem numericValid3927 : retention3927.NumericValid := by decide +kernel
def certificate3927 : RatCutBinCertificate := ⟨⟨retention3927,(115359482684794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(2161340339413930579/1000000000000000000)⟩,(249954731915541519/250000000000000000),(730676540444165739/1000000000000000000),(10012138780011939/250000000000000000),(437117148748957/25000000000000000)⟩
theorem valid3927 : certificate3927.Valid := by decide +kernel
theorem sound3927 : certificate3927.Sound := rat_cut_bin_certificate_sound certificate3927 profilesValid3927 numericValid3927 valid3927

def retention3928 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(2796475145120856158/960649900360527327901),(236070651/200000000),(27/10),(2344501087713971031/1000000000000000000),true,MergedCutProfiles.Batch596.profile23879,![MergedCutProfiles.Batch596.profile23879,MergedCutProfiles.Batch597.profile23882,MergedCutProfiles.Batch597.profile23888,MergedCutProfiles.Batch338.profile13522,MergedCutProfiles.Batch465.profile18623,MergedCutProfiles.Batch597.profile23891,MergedCutProfiles.Batch338.profile13535,MergedCutProfiles.Batch597.profile23893,MergedCutProfiles.Batch597.profile23894,MergedCutProfiles.Batch465.profile18630,MergedCutProfiles.Batch597.profile23895,MergedCutProfiles.Batch337.profile13509,MergedCutProfiles.Batch337.profile13495,MergedCutProfiles.Batch338.profile13536,MergedCutProfiles.Batch465.profile18620,MergedCutProfiles.Batch466.profile18643]⟩
theorem profilesValid3928 : retention3928.ProfilesValid := by
  change ∀ j : Fin 16, (retention3928.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch596.valid23879
  · exact MergedCutProfiles.Batch597.valid23882
  · exact MergedCutProfiles.Batch597.valid23888
  · exact MergedCutProfiles.Batch338.valid13522
  · exact MergedCutProfiles.Batch465.valid18623
  · exact MergedCutProfiles.Batch597.valid23891
  · exact MergedCutProfiles.Batch338.valid13535
  · exact MergedCutProfiles.Batch597.valid23893
  · exact MergedCutProfiles.Batch597.valid23894
  · exact MergedCutProfiles.Batch465.valid18630
  · exact MergedCutProfiles.Batch597.valid23895
  · exact MergedCutProfiles.Batch337.valid13509
  · exact MergedCutProfiles.Batch337.valid13495
  · exact MergedCutProfiles.Batch338.valid13536
  · exact MergedCutProfiles.Batch465.valid18620
  · exact MergedCutProfiles.Batch466.valid18643
theorem numericValid3928 : retention3928.NumericValid := by decide +kernel
def certificate3928 : RatCutBinCertificate := ⟨⟨retention3928,(115359482684794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(1160346713022127419/500000000000000000)⟩,(249954731915541519/250000000000000000),(441645026234608719/1000000000000000000),(197420727962694831/1000000000000000000),(26723048668652443/200000000000000000)⟩
theorem valid3928 : certificate3928.Valid := by decide +kernel
theorem sound3928 : certificate3928.Sound := rat_cut_bin_certificate_sound certificate3928 profilesValid3928 numericValid3928 valid3928

def retention3929 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(64000000000000000000/960649900360527327901),(1398237572560428079/500000000000000000),(31/20),(1277193835748010669271/640000000000000000000),true,MergedCutProfiles.Batch337.profile13484,![MergedCutProfiles.Batch337.profile13484,MergedCutProfiles.Batch337.profile13504,MergedCutProfiles.Batch597.profile23896,MergedCutProfiles.Batch338.profile13544,MergedCutProfiles.Batch597.profile23897,MergedCutProfiles.Batch597.profile23898,MergedCutProfiles.Batch597.profile23899,MergedCutProfiles.Batch597.profile23900,MergedCutProfiles.Batch597.profile23901,MergedCutProfiles.Batch597.profile23902,MergedCutProfiles.Batch597.profile23903,MergedCutProfiles.Batch597.profile23904,MergedCutProfiles.Batch597.profile23905,MergedCutProfiles.Batch597.profile23906,MergedCutProfiles.Batch597.profile23907,MergedCutProfiles.Batch597.profile23908]⟩
theorem profilesValid3929 : retention3929.ProfilesValid := by
  change ∀ j : Fin 16, (retention3929.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch337.valid13484
  · exact MergedCutProfiles.Batch337.valid13504
  · exact MergedCutProfiles.Batch597.valid23896
  · exact MergedCutProfiles.Batch338.valid13544
  · exact MergedCutProfiles.Batch597.valid23897
  · exact MergedCutProfiles.Batch597.valid23898
  · exact MergedCutProfiles.Batch597.valid23899
  · exact MergedCutProfiles.Batch597.valid23900
  · exact MergedCutProfiles.Batch597.valid23901
  · exact MergedCutProfiles.Batch597.valid23902
  · exact MergedCutProfiles.Batch597.valid23903
  · exact MergedCutProfiles.Batch597.valid23904
  · exact MergedCutProfiles.Batch597.valid23905
  · exact MergedCutProfiles.Batch597.valid23906
  · exact MergedCutProfiles.Batch597.valid23907
  · exact MergedCutProfiles.Batch597.valid23908
theorem numericValid3929 : retention3929.NumericValid := by decide +kernel
def certificate3929 : RatCutBinCertificate := ⟨⟨retention3929,(115359482684794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(24774350158058979/12500000000000000)⟩,(249954731915541519/250000000000000000),(366640836162752663/1000000000000000000),(132739100712014329/500000000000000000),(131039920951561887/500000000000000000)⟩
theorem valid3929 : certificate3929.Valid := by decide +kernel
theorem sound3929 : certificate3929.Sound := rat_cut_bin_certificate_sound certificate3929 profilesValid3929 numericValid3929 valid3929

def retention3930 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid3930 : retention3930.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid3930 : retention3930.NumericValid := by decide +kernel
def certificate3930 : RatCutBinCertificate := ⟨⟨retention3930,(115359482684794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(494375993015359367/500000000000000000)⟩,(249954731915541519/250000000000000000),(262120384912018109/500000000000000000),(1372023099806637/10000000000000000),(13357070048856137/100000000000000000)⟩
theorem valid3930 : certificate3930.Valid := by decide +kernel
theorem sound3930 : certificate3930.Sound := rat_cut_bin_certificate_sound certificate3930 profilesValid3930 numericValid3930 valid3930

def retention3931 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(64000000000000000000/960649900360527327901),(22112533556948853429/1000000000000000000),1,(174151098385177797921446944811624826539/88450134227795413716000000000000000000),false,MergedCutProfiles.Batch597.profile23909,(fun _ => MergedCutProfiles.Batch597.profile23909)⟩
theorem profilesValid3931 : retention3931.ProfilesValid := by
  exact MergedCutProfiles.Batch597.valid23909
theorem numericValid3931 : retention3931.NumericValid := by decide +kernel
def certificate3931 : RatCutBinCertificate := ⟨⟨retention3931,(113220608309794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(980132132506698773/500000000000000000)⟩,(199964456988692801/200000000000000000),(7950849090797029/250000000000000000),(33561148097247617/40000000000000000),(1510512233482876369/1000000000000000000)⟩
theorem valid3931 : certificate3931.Valid := by decide +kernel
theorem sound3931 : certificate3931.Sound := rat_cut_bin_certificate_sound certificate3931 profilesValid3931 numericValid3931 valid3931

def retention3932 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid3932 : retention3932.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid3932 : retention3932.NumericValid := by decide +kernel
def certificate3932 : RatCutBinCertificate := ⟨⟨retention3932,(113220608309794859/62500000000000000),(481579510880593/10000000000000000),(10080660298742288633/1000000000000000000),(9733859852215415768657/1000000000000000000),(247228868360294429/250000000000000000)⟩,(199964456988692801/200000000000000000),(31520925231292267/500000000000000000),(94283998223413753/125000000000000000),(734429186325896653/1000000000000000000)⟩
theorem valid3932 : certificate3932.Valid := by decide +kernel
theorem sound3932 : certificate3932.Sound := rat_cut_bin_certificate_sound certificate3932 profilesValid3932 numericValid3932 valid3932

def retention3933 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(598868451242960150/900307249488733784293),(282080585518748411/500000000000000000),4,(70074903030734671583/32000000000000000000),true,MergedCutProfiles.Batch597.profile23910,![MergedCutProfiles.Batch597.profile23910,MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch597.profile23912,MergedCutProfiles.Batch597.profile23913,MergedCutProfiles.Batch597.profile23914,MergedCutProfiles.Batch597.profile23915,MergedCutProfiles.Batch597.profile23916,MergedCutProfiles.Batch466.profile18673,MergedCutProfiles.Batch466.profile18651,MergedCutProfiles.Batch597.profile23917,MergedCutProfiles.Batch597.profile23918,MergedCutProfiles.Batch338.profile13555,MergedCutProfiles.Batch597.profile23919,MergedCutProfiles.Batch598.profile23920,MergedCutProfiles.Batch339.profile13571,MergedCutProfiles.Batch598.profile23921]⟩
theorem profilesValid3933 : retention3933.ProfilesValid := by
  change ∀ j : Fin 16, (retention3933.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch597.valid23910
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch597.valid23912
  · exact MergedCutProfiles.Batch597.valid23913
  · exact MergedCutProfiles.Batch597.valid23914
  · exact MergedCutProfiles.Batch597.valid23915
  · exact MergedCutProfiles.Batch597.valid23916
  · exact MergedCutProfiles.Batch466.valid18673
  · exact MergedCutProfiles.Batch466.valid18651
  · exact MergedCutProfiles.Batch597.valid23917
  · exact MergedCutProfiles.Batch597.valid23918
  · exact MergedCutProfiles.Batch338.valid13555
  · exact MergedCutProfiles.Batch597.valid23919
  · exact MergedCutProfiles.Batch598.valid23920
  · exact MergedCutProfiles.Batch339.valid13571
  · exact MergedCutProfiles.Batch598.valid23921
theorem numericValid3933 : retention3933.NumericValid := by decide +kernel
def certificate3933 : RatCutBinCertificate := ⟨⟨retention3933,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(2152759663848402487/1000000000000000000)⟩,(999810070437427249/1000000000000000000),(741327282754430489/1000000000000000000),(18391884677722029/500000000000000000),(15980807201316803/1000000000000000000)⟩
theorem valid3933 : certificate3933.Valid := by decide +kernel
theorem sound3933 : certificate3933.Sound := rat_cut_bin_certificate_sound certificate3933 profilesValid3933 numericValid3933 valid3933

def retention3934 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1152816283000000000/900307249488733784293),(11977369024859203/20000000000000000),4,(451105662916997977/200000000000000000),true,MergedCutProfiles.Batch597.profile23911,![MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch598.profile23922,MergedCutProfiles.Batch598.profile23923,MergedCutProfiles.Batch466.profile18666,MergedCutProfiles.Batch598.profile23924,MergedCutProfiles.Batch598.profile23925,MergedCutProfiles.Batch466.profile18652,MergedCutProfiles.Batch339.profile13571,MergedCutProfiles.Batch598.profile23926,MergedCutProfiles.Batch598.profile23927,MergedCutProfiles.Batch340.profile13607,MergedCutProfiles.Batch466.profile18667,MergedCutProfiles.Batch598.profile23928,MergedCutProfiles.Batch466.profile18655,MergedCutProfiles.Batch598.profile23929,MergedCutProfiles.Batch466.profile18656]⟩
theorem profilesValid3934 : retention3934.ProfilesValid := by
  change ∀ j : Fin 16, (retention3934.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch598.valid23922
  · exact MergedCutProfiles.Batch598.valid23923
  · exact MergedCutProfiles.Batch466.valid18666
  · exact MergedCutProfiles.Batch598.valid23924
  · exact MergedCutProfiles.Batch598.valid23925
  · exact MergedCutProfiles.Batch466.valid18652
  · exact MergedCutProfiles.Batch339.valid13571
  · exact MergedCutProfiles.Batch598.valid23926
  · exact MergedCutProfiles.Batch598.valid23927
  · exact MergedCutProfiles.Batch340.valid13607
  · exact MergedCutProfiles.Batch466.valid18667
  · exact MergedCutProfiles.Batch598.valid23928
  · exact MergedCutProfiles.Batch466.valid18655
  · exact MergedCutProfiles.Batch598.valid23929
  · exact MergedCutProfiles.Batch466.valid18656
theorem numericValid3934 : retention3934.NumericValid := by decide +kernel
def certificate3934 : RatCutBinCertificate := ⟨⟨retention3934,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(277305908000635691/125000000000000000)⟩,(999810070437427249/1000000000000000000),(138214124772910033/200000000000000000),(53569620373116297/1000000000000000000),(12059665954354467/500000000000000000)⟩
theorem valid3934 : certificate3934.Valid := by decide +kernel
theorem sound3934 : certificate3934.Sound := rat_cut_bin_certificate_sound certificate3934 profilesValid3934 numericValid3934 valid3934

def retention3935 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1166442884595908744/900307249488733784293),(1152816283/1000000000),(11/4),(118567104842407973/50000000000000000),true,MergedCutProfiles.Batch597.profile23911,![MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch597.profile23913,MergedCutProfiles.Batch598.profile23923,MergedCutProfiles.Batch466.profile18666,MergedCutProfiles.Batch597.profile23917,MergedCutProfiles.Batch338.profile13555,MergedCutProfiles.Batch466.profile18652,MergedCutProfiles.Batch598.profile23921,MergedCutProfiles.Batch466.profile18653,MergedCutProfiles.Batch598.profile23930,MergedCutProfiles.Batch598.profile23931,MergedCutProfiles.Batch466.profile18667,MergedCutProfiles.Batch598.profile23928,MergedCutProfiles.Batch466.profile18655,MergedCutProfiles.Batch598.profile23932,MergedCutProfiles.Batch466.profile18656]⟩
theorem profilesValid3935 : retention3935.ProfilesValid := by
  change ∀ j : Fin 16, (retention3935.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch597.valid23913
  · exact MergedCutProfiles.Batch598.valid23923
  · exact MergedCutProfiles.Batch466.valid18666
  · exact MergedCutProfiles.Batch597.valid23917
  · exact MergedCutProfiles.Batch338.valid13555
  · exact MergedCutProfiles.Batch466.valid18652
  · exact MergedCutProfiles.Batch598.valid23921
  · exact MergedCutProfiles.Batch466.valid18653
  · exact MergedCutProfiles.Batch598.valid23930
  · exact MergedCutProfiles.Batch598.valid23931
  · exact MergedCutProfiles.Batch466.valid18667
  · exact MergedCutProfiles.Batch598.valid23928
  · exact MergedCutProfiles.Batch466.valid18655
  · exact MergedCutProfiles.Batch598.valid23932
  · exact MergedCutProfiles.Batch466.valid18656
theorem numericValid3935 : retention3935.NumericValid := by decide +kernel
def certificate3935 : RatCutBinCertificate := ⟨⟨retention3935,(1846808941920205997/1000000000000000000),(51337219122942991/1000000000000000000),(10227353689100283593/1000000000000000000),(9255469691434617884019/1000000000000000000),(2345848889000501637/1000000000000000000)⟩,(999810070437427249/1000000000000000000),(444454659324930953/1000000000000000000),(24391688571491041/125000000000000000),(65567239275847017/500000000000000000)⟩
theorem valid3935 : certificate3935.Valid := by decide +kernel
theorem sound3935 : certificate3935.Sound := rat_cut_bin_certificate_sound certificate3935 profilesValid3935 numericValid3935 valid3935

def certificates : List RatCutBinCertificate := [certificate3924,certificate3925,certificate3926,certificate3927,certificate3928,certificate3929,certificate3930,certificate3931,certificate3932,certificate3933,certificate3934,certificate3935]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3924,List.forall_mem_cons.mpr ⟨sound3925,List.forall_mem_cons.mpr ⟨sound3926,List.forall_mem_cons.mpr ⟨sound3927,List.forall_mem_cons.mpr ⟨sound3928,List.forall_mem_cons.mpr ⟨sound3929,List.forall_mem_cons.mpr ⟨sound3930,List.forall_mem_cons.mpr ⟨sound3931,List.forall_mem_cons.mpr ⟨sound3932,List.forall_mem_cons.mpr ⟨sound3933,List.forall_mem_cons.mpr ⟨sound3934,List.forall_mem_cons.mpr ⟨sound3935,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch327
