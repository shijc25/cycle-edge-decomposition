import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch026
import Cycle12.MergedCutProfiles.Batch027
import Cycle12.MergedCutProfiles.Batch028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch013

def retention156 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(51463212166121420504/125904482924188692167),(1529899522757258259/250000000000000000),(11/10),(179393803827191038308202300018057903199/152989952275725825900000000000000000000),false,MergedCutProfiles.Batch026.profile1063,(fun _ => MergedCutProfiles.Batch026.profile1063)⟩
theorem profilesValid156 : retention156.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1063
theorem numericValid156 : retention156.NumericValid := by decide +kernel
def certificate156 : RatCutBinCertificate := ⟨⟨retention156,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(29198775760488553/25000000000000000)⟩,(249560024619351623/250000000000000000),(440493750647867047/1000000000000000000),(198363094629997923/1000000000000000000),(181579859514428297/1000000000000000000)⟩
theorem valid156 : certificate156.Valid := by decide +kernel
theorem sound156 : certificate156.Sound := rat_cut_bin_certificate_sound certificate156 profilesValid156 numericValid156 valid156

def retention157 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(62173167236465731077/125904482924188692167),(6432901520765177563/125000000000000000),1,(51919702872734666049510618386281394527/51463212166121420504000000000000000000),false,MergedCutProfiles.Batch026.profile1064,(fun _ => MergedCutProfiles.Batch026.profile1064)⟩
theorem profilesValid157 : retention157.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1064
theorem numericValid157 : retention157.NumericValid := by decide +kernel
def certificate157 : RatCutBinCertificate := ⟨⟨retention157,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(100465706404192261/100000000000000000)⟩,(249560024619351623/250000000000000000),(7068405593382293/15625000000000000),(188778732850315599/1000000000000000000),(185695581626837279/1000000000000000000)⟩
theorem valid157 : certificate157.Valid := by decide +kernel
theorem sound157 : certificate157.Sound := rat_cut_bin_certificate_sound certificate157 profilesValid157 numericValid157 valid157

def retention158 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(62794898908830388388/125904482924188692167),(62173167236465731077/1000000000000000000),1,(62167778410387832835116623228434320153/62173167236465731077000000000000000000),false,MergedCutProfiles.Batch026.profile1065,(fun _ => MergedCutProfiles.Batch026.profile1065)⟩
theorem profilesValid158 : retention158.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1065
theorem numericValid158 : retention158.NumericValid := by decide +kernel
def certificate158 : RatCutBinCertificate := ⟨⟨retention158,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(497850078178291283/500000000000000000)⟩,(249560024619351623/250000000000000000),(227523332315856091/500000000000000000),(186669693278572829/1000000000000000000),(91306315432706927/500000000000000000)⟩
theorem valid158 : certificate158.Valid := by decide +kernel
theorem sound158 : certificate158.Sound := rat_cut_bin_certificate_sound certificate158 profilesValid158 numericValid158 valid158

def retention159 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),(15698724727207597097/250000000000000000),1,(71177311965601412260984954677703323/71357839669125441350000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid159 : retention159.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid159 : retention159.NumericValid := by decide +kernel
def certificate159 : RatCutBinCertificate := ⟨⟨retention159,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(24831423444297469/25000000000000000)⟩,(249560024619351623/250000000000000000),(114024796807435549/250000000000000000),(185842208396715621/1000000000000000000),(5668509658196159/31250000000000000)⟩
theorem valid159 : certificate159.Valid := by decide +kernel
theorem sound159 : certificate159.Sound := rat_cut_bin_certificate_sound certificate159 profilesValid159 numericValid159 valid159

def retention160 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(50717947037064252419/125904482924188692167),(880995115915363757/250000000000000000),(13/10),(421738416263023085425479068658583207471/352398046366145502800000000000000000000),false,MergedCutProfiles.Batch026.profile1067,(fun _ => MergedCutProfiles.Batch026.profile1067)⟩
theorem profilesValid160 : retention160.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1067
theorem numericValid160 : retention160.NumericValid := by decide +kernel
def certificate160 : RatCutBinCertificate := ⟨⟨retention160,(1153237008472775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(297559772131177957/250000000000000000)⟩,(997902396693270899/1000000000000000000),(167135099636479491/500000000000000000),(299425595427367887/1000000000000000000),(113981577329755967/500000000000000000)⟩
theorem valid160 : certificate160.Valid := by decide +kernel
theorem sound160 : certificate160.Sound := rat_cut_bin_certificate_sound certificate160 profilesValid160 numericValid160 valid160

def retention161 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(62504389159446638771/125904482924188692167),(50717947037064252419/1000000000000000000),1,(20523908367868837186508335472921273/20450785095590424362500000000000000),false,MergedCutProfiles.Batch026.profile1068,(fun _ => MergedCutProfiles.Batch026.profile1068)⟩
theorem profilesValid161 : retention161.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1068
theorem numericValid161 : retention161.NumericValid := by decide +kernel
def certificate161 : RatCutBinCertificate := ⟨⟨retention161,(1153237008472775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(499276990516753637/500000000000000000)⟩,(997902396693270899/1000000000000000000),(199218802819168737/500000000000000000),(46983392161080617/200000000000000000),(229561254921825859/1000000000000000000)⟩
theorem valid161 : certificate161.Valid := by decide +kernel
theorem sound161 : certificate161.Sound := rat_cut_bin_certificate_sound certificate161 profilesValid161 numericValid161 valid161

def retention162 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),(62504389159446638771/1000000000000000000),1,(7793137471319578932487071489331408527/7813048644930829846375000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid162 : retention162.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid162 : retention162.NumericValid := by decide +kernel
def certificate162 : RatCutBinCertificate := ⟨⟨retention162,(1153237008472775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(496214978617705603/500000000000000000)⟩,(997902396693270899/1000000000000000000),(40089625912939367/100000000000000000),(46532433705288097/200000000000000000),(226811876009327109/1000000000000000000)⟩
theorem valid162 : certificate162.Valid := by decide +kernel
theorem sound162 : certificate162.Sound := rat_cut_bin_certificate_sound certificate162 profilesValid162 numericValid162 valid162

def retention163 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(679315923341955296/114167855278157797031),(166482678987833373/250000000000000000),4,(146422374612327556989/64000000000000000000),true,MergedCutProfiles.Batch026.profile1069,![MergedCutProfiles.Batch026.profile1069,MergedCutProfiles.Batch026.profile1070,MergedCutProfiles.Batch026.profile1071,MergedCutProfiles.Batch026.profile1072,MergedCutProfiles.Batch026.profile1073,MergedCutProfiles.Batch026.profile1074,MergedCutProfiles.Batch026.profile1075,MergedCutProfiles.Batch026.profile1076,MergedCutProfiles.Batch026.profile1077,MergedCutProfiles.Batch026.profile1078,MergedCutProfiles.Batch026.profile1079,MergedCutProfiles.Batch027.profile1080,MergedCutProfiles.Batch027.profile1081,MergedCutProfiles.Batch027.profile1082,MergedCutProfiles.Batch027.profile1083,MergedCutProfiles.Batch027.profile1084]⟩
theorem profilesValid163 : retention163.ProfilesValid := by
  change ∀ j : Fin 16, (retention163.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch026.valid1069
  · exact MergedCutProfiles.Batch026.valid1070
  · exact MergedCutProfiles.Batch026.valid1071
  · exact MergedCutProfiles.Batch026.valid1072
  · exact MergedCutProfiles.Batch026.valid1073
  · exact MergedCutProfiles.Batch026.valid1074
  · exact MergedCutProfiles.Batch026.valid1075
  · exact MergedCutProfiles.Batch026.valid1076
  · exact MergedCutProfiles.Batch026.valid1077
  · exact MergedCutProfiles.Batch026.valid1078
  · exact MergedCutProfiles.Batch026.valid1079
  · exact MergedCutProfiles.Batch027.valid1080
  · exact MergedCutProfiles.Batch027.valid1081
  · exact MergedCutProfiles.Batch027.valid1082
  · exact MergedCutProfiles.Batch027.valid1083
  · exact MergedCutProfiles.Batch027.valid1084
theorem numericValid163 : retention163.NumericValid := by decide +kernel
def certificate163 : RatCutBinCertificate := ⟨⟨retention163,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(567370715891185841/250000000000000000)⟩,(99808337533181583/100000000000000000),(11770541706852199/25000000000000000),(174519585521569653/1000000000000000000),(81447751714467891/1000000000000000000)⟩
theorem valid163 : certificate163.Valid := by decide +kernel
theorem sound163 : certificate163.Sound := rat_cut_bin_certificate_sound certificate163 profilesValid163 numericValid163 valid163

def retention164 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1146081873000000000/114167855278157797031),(21228622604436103/31250000000000000),(79/20),(45204059043848047563/20000000000000000000),true,MergedCutProfiles.Batch027.profile1085,![MergedCutProfiles.Batch027.profile1085,MergedCutProfiles.Batch027.profile1086,MergedCutProfiles.Batch026.profile1073,MergedCutProfiles.Batch027.profile1087,MergedCutProfiles.Batch027.profile1088,MergedCutProfiles.Batch027.profile1089,MergedCutProfiles.Batch027.profile1090,MergedCutProfiles.Batch027.profile1091,MergedCutProfiles.Batch027.profile1092,MergedCutProfiles.Batch027.profile1093,MergedCutProfiles.Batch027.profile1094,MergedCutProfiles.Batch027.profile1095,MergedCutProfiles.Batch027.profile1096,MergedCutProfiles.Batch027.profile1097,MergedCutProfiles.Batch027.profile1098,MergedCutProfiles.Batch027.profile1099]⟩
theorem profilesValid164 : retention164.ProfilesValid := by
  change ∀ j : Fin 16, (retention164.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch027.valid1085
  · exact MergedCutProfiles.Batch027.valid1086
  · exact MergedCutProfiles.Batch026.valid1073
  · exact MergedCutProfiles.Batch027.valid1087
  · exact MergedCutProfiles.Batch027.valid1088
  · exact MergedCutProfiles.Batch027.valid1089
  · exact MergedCutProfiles.Batch027.valid1090
  · exact MergedCutProfiles.Batch027.valid1091
  · exact MergedCutProfiles.Batch027.valid1092
  · exact MergedCutProfiles.Batch027.valid1093
  · exact MergedCutProfiles.Batch027.valid1094
  · exact MergedCutProfiles.Batch027.valid1095
  · exact MergedCutProfiles.Batch027.valid1096
  · exact MergedCutProfiles.Batch027.valid1097
  · exact MergedCutProfiles.Batch027.valid1098
  · exact MergedCutProfiles.Batch027.valid1099
theorem numericValid164 : retention164.NumericValid := by decide +kernel
def certificate164 : RatCutBinCertificate := ⟨⟨retention164,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(2242065797711231111/1000000000000000000)⟩,(99808337533181583/100000000000000000),(471132617371965569/1000000000000000000),(174285459186333027/1000000000000000000),(16294302420509119/200000000000000000)⟩
theorem valid164 : certificate164.Valid := by decide +kernel
theorem sound164 : certificate164.Sound := rat_cut_bin_certificate_sound certificate164 profilesValid164 numericValid164 valid164

def retention165 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1284220850408261955/114167855278157797031),(1146081873/1000000000),(5/2),(17724978355276158219/8000000000000000000),true,MergedCutProfiles.Batch027.profile1100,![MergedCutProfiles.Batch027.profile1100,MergedCutProfiles.Batch027.profile1101,MergedCutProfiles.Batch027.profile1102,MergedCutProfiles.Batch027.profile1103,MergedCutProfiles.Batch027.profile1104,MergedCutProfiles.Batch027.profile1105,MergedCutProfiles.Batch027.profile1106,MergedCutProfiles.Batch027.profile1092,MergedCutProfiles.Batch027.profile1093,MergedCutProfiles.Batch027.profile1107,MergedCutProfiles.Batch027.profile1108,MergedCutProfiles.Batch027.profile1109,MergedCutProfiles.Batch027.profile1110,MergedCutProfiles.Batch027.profile1111,MergedCutProfiles.Batch027.profile1112,MergedCutProfiles.Batch027.profile1113]⟩
theorem profilesValid165 : retention165.ProfilesValid := by
  change ∀ j : Fin 16, (retention165.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch027.valid1100
  · exact MergedCutProfiles.Batch027.valid1101
  · exact MergedCutProfiles.Batch027.valid1102
  · exact MergedCutProfiles.Batch027.valid1103
  · exact MergedCutProfiles.Batch027.valid1104
  · exact MergedCutProfiles.Batch027.valid1105
  · exact MergedCutProfiles.Batch027.valid1106
  · exact MergedCutProfiles.Batch027.valid1092
  · exact MergedCutProfiles.Batch027.valid1093
  · exact MergedCutProfiles.Batch027.valid1107
  · exact MergedCutProfiles.Batch027.valid1108
  · exact MergedCutProfiles.Batch027.valid1109
  · exact MergedCutProfiles.Batch027.valid1110
  · exact MergedCutProfiles.Batch027.valid1111
  · exact MergedCutProfiles.Batch027.valid1112
  · exact MergedCutProfiles.Batch027.valid1113
theorem numericValid165 : retention165.NumericValid := by decide +kernel
def certificate165 : RatCutBinCertificate := ⟨⟨retention165,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(440828617663213263/200000000000000000)⟩,(99808337533181583/100000000000000000),(91745450463373609/250000000000000000),(13256813987514871/50000000000000000),(89181433293403127/500000000000000000)⟩
theorem valid165 : certificate165.Valid := by decide +kernel
theorem sound165 : certificate165.Sound := rat_cut_bin_certificate_sound certificate165 profilesValid165 numericValid165 valid165

def retention166 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(4775964127028575065/114167855278157797031),(256844170081652391/200000000000000000),(23/10),(132960599734955985503/64000000000000000000),true,MergedCutProfiles.Batch026.profile1075,![MergedCutProfiles.Batch026.profile1075,MergedCutProfiles.Batch027.profile1114,MergedCutProfiles.Batch027.profile1115,MergedCutProfiles.Batch027.profile1116,MergedCutProfiles.Batch027.profile1117,MergedCutProfiles.Batch027.profile1118,MergedCutProfiles.Batch027.profile1119,MergedCutProfiles.Batch028.profile1120,MergedCutProfiles.Batch028.profile1121,MergedCutProfiles.Batch028.profile1122,MergedCutProfiles.Batch028.profile1123,MergedCutProfiles.Batch028.profile1124,MergedCutProfiles.Batch028.profile1125,MergedCutProfiles.Batch028.profile1126,MergedCutProfiles.Batch028.profile1127,MergedCutProfiles.Batch028.profile1128]⟩
theorem profilesValid166 : retention166.ProfilesValid := by
  change ∀ j : Fin 16, (retention166.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch026.valid1075
  · exact MergedCutProfiles.Batch027.valid1114
  · exact MergedCutProfiles.Batch027.valid1115
  · exact MergedCutProfiles.Batch027.valid1116
  · exact MergedCutProfiles.Batch027.valid1117
  · exact MergedCutProfiles.Batch027.valid1118
  · exact MergedCutProfiles.Batch027.valid1119
  · exact MergedCutProfiles.Batch028.valid1120
  · exact MergedCutProfiles.Batch028.valid1121
  · exact MergedCutProfiles.Batch028.valid1122
  · exact MergedCutProfiles.Batch028.valid1123
  · exact MergedCutProfiles.Batch028.valid1124
  · exact MergedCutProfiles.Batch028.valid1125
  · exact MergedCutProfiles.Batch028.valid1126
  · exact MergedCutProfiles.Batch028.valid1127
  · exact MergedCutProfiles.Batch028.valid1128
theorem numericValid166 : retention166.NumericValid := by decide +kernel
def certificate166 : RatCutBinCertificate := ⟨⟨retention166,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(2066948503531258343/1000000000000000000)⟩,(99808337533181583/100000000000000000),(372600282951281839/1000000000000000000),(64886850634094377/250000000000000000),(178446328064911523/1000000000000000000)⟩
theorem valid166 : certificate166.Valid := by decide +kernel
theorem sound166 : certificate166.Sound := rat_cut_bin_certificate_sound certificate166 profilesValid166 numericValid166 valid166

def retention167 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(43061054620558362450/114167855278157797031),(955192825405715013/200000000000000000),(6/5),(881943143410732655800709433574098333/707550241041270380000000000000000000),false,MergedCutProfiles.Batch028.profile1129,(fun _ => MergedCutProfiles.Batch028.profile1129)⟩
theorem profilesValid167 : retention167.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1129
theorem numericValid167 : retention167.NumericValid := by decide +kernel
def certificate167 : RatCutBinCertificate := ⟨⟨retention167,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(12409642330671553/10000000000000000)⟩,(99808337533181583/100000000000000000),(215635561352275683/500000000000000000),(20602144730505021/100000000000000000),(45028435608621867/250000000000000000)⟩
theorem valid167 : certificate167.Valid := by decide +kernel
theorem sound167 : certificate167.Sound := rat_cut_bin_certificate_sound certificate167 profilesValid167 numericValid167 valid167

def certificates : List RatCutBinCertificate := [certificate156,certificate157,certificate158,certificate159,certificate160,certificate161,certificate162,certificate163,certificate164,certificate165,certificate166,certificate167]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound156,List.forall_mem_cons.mpr ⟨sound157,List.forall_mem_cons.mpr ⟨sound158,List.forall_mem_cons.mpr ⟨sound159,List.forall_mem_cons.mpr ⟨sound160,List.forall_mem_cons.mpr ⟨sound161,List.forall_mem_cons.mpr ⟨sound162,List.forall_mem_cons.mpr ⟨sound163,List.forall_mem_cons.mpr ⟨sound164,List.forall_mem_cons.mpr ⟨sound165,List.forall_mem_cons.mpr ⟨sound166,List.forall_mem_cons.mpr ⟨sound167,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch013
