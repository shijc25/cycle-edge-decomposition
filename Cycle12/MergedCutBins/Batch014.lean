import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch029
import Cycle12.MergedCutProfiles.Batch030

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch014

def retention168 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(56332853955698959763/114167855278157797031),(861221092411167249/20000000000000000),1,(173737922639506434144485288356932796631/172244218482233449800000000000000000000),false,MergedCutProfiles.Batch028.profile1130,(fun _ => MergedCutProfiles.Batch028.profile1130)⟩
theorem profilesValid168 : retention168.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1130
theorem numericValid168 : retention168.NumericValid := by decide +kernel
def certificate168 : RatCutBinCertificate := ⟨⟨retention168,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(502040180873580577/500000000000000000)⟩,(99808337533181583/100000000000000000),(456500479192571881/1000000000000000000),(18552735564611971/100000000000000000),(90843250940680847/500000000000000000)⟩
theorem valid168 : certificate168.Valid := by decide +kernel
theorem sound168 : certificate168.Sound := rat_cut_bin_certificate_sound certificate168 profilesValid168 numericValid168 valid168

def retention169 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(56896182495255949361/114167855278157797031),(56332853955698959763/1000000000000000000),1,(11269708165818570276699056589383630277/11266570791139791952600000000000000000),false,MergedCutProfiles.Batch028.profile1131,(fun _ => MergedCutProfiles.Batch028.profile1131)⟩
theorem profilesValid169 : retention169.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1131
theorem numericValid169 : retention169.NumericValid := by decide +kernel
def certificate169 : RatCutBinCertificate := ⟨⟨retention169,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(497843408260771903/500000000000000000)⟩,(99808337533181583/100000000000000000),(229040476877266701/500000000000000000),(184290746221368047/1000000000000000000),(179960079887885411/1000000000000000000)⟩
theorem valid169 : certificate169.Valid := by decide +kernel
theorem sound169 : certificate169.Sound := rat_cut_bin_certificate_sound certificate169 profilesValid169 numericValid169 valid169

def retention170 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),(56896182495255949361/1000000000000000000),1,(3545548286435202226718268773731793817/3556011405953496835062500000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid170 : retention170.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid170 : retention170.NumericValid := by decide +kernel
def certificate170 : RatCutBinCertificate := ⟨⟨retention170,(1940031347895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(992465973831640851/1000000000000000000)⟩,(99808337533181583/100000000000000000),(114873618327577357/250000000000000000),(1431167083668929/7812500000000000),(89173283340830907/500000000000000000)⟩
theorem valid170 : certificate170.Valid := by decide +kernel
theorem sound170 : certificate170.Sound := rat_cut_bin_certificate_sound certificate170 profilesValid170 numericValid170 valid170

def retention171 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(46087387477214625847/114167855278157797031),(1786319061275095751/500000000000000000),(13/10),(427059938511389687012169473664465534631/357263812255019150200000000000000000000),false,MergedCutProfiles.Batch028.profile1133,(fun _ => MergedCutProfiles.Batch028.profile1133)⟩
theorem profilesValid171 : retention171.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1133
theorem numericValid171 : retention171.NumericValid := by decide +kernel
def certificate171 : RatCutBinCertificate := ⟨⟨retention171,(2311545622895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(118825072751618451/100000000000000000)⟩,(997716327524556783/1000000000000000000),(332448156188638637/1000000000000000000),(18839169138966389/62500000000000000),(57410369690487937/250000000000000000)⟩
theorem valid171 : certificate171.Valid := by decide +kernel
theorem sound171 : certificate171.Sound := rat_cut_bin_certificate_sound certificate171 profilesValid171 numericValid171 valid171

def retention172 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(56797724878589139691/114167855278157797031),(46087387477214625847/1000000000000000000),1,(46133087777586674614134425343992434509/46087387477214625847000000000000000000),false,MergedCutProfiles.Batch028.profile1134,(fun _ => MergedCutProfiles.Batch028.profile1134)⟩
theorem profilesValid172 : retention172.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1134
theorem numericValid172 : retention172.NumericValid := by decide +kernel
def certificate172 : RatCutBinCertificate := ⟨⟨retention172,(2311545622895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(995520652429810863/1000000000000000000)⟩,(997716327524556783/1000000000000000000),(79361841964482137/200000000000000000),(236418678861708583/1000000000000000000),(229852088159389841/1000000000000000000)⟩
theorem valid172 : certificate172.Valid := by decide +kernel
theorem sound172 : certificate172.Sound := rat_cut_bin_certificate_sound certificate172 profilesValid172 numericValid172 valid172

def retention173 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),(56797724878589139691/1000000000000000000),1,(7078771347235577452977704104221453339/7099715609823642461375000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid173 : retention173.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid173 : retention173.NumericValid := by decide +kernel
def certificate173 : RatCutBinCertificate := ⟨⟨retention173,(2311545622895587/1000000000000000),(10247703429141591/500000000000000000),(4329787462909040251/500000000000000000),(124176955782508323627/125000000000000000),(198315807514214993/200000000000000000)⟩,(997716327524556783/1000000000000000000),(49798320215125651/125000000000000000),(234963932734892217/1000000000000000000),(57115155945402789/250000000000000000)⟩
theorem valid173 : certificate173.Valid := by decide +kernel
theorem sound173 : certificate173.Sound := rat_cut_bin_certificate_sound certificate173 profilesValid173 numericValid173 valid173

def retention174 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(678279174294463859/103951496071048284220),(671563538905409761/1000000000000000000),(79/20),(2919863686095760825473/1280000000000000000000),true,MergedCutProfiles.Batch028.profile1135,![MergedCutProfiles.Batch028.profile1135,MergedCutProfiles.Batch028.profile1136,MergedCutProfiles.Batch028.profile1137,MergedCutProfiles.Batch028.profile1138,MergedCutProfiles.Batch028.profile1139,MergedCutProfiles.Batch028.profile1140,MergedCutProfiles.Batch028.profile1141,MergedCutProfiles.Batch028.profile1142,MergedCutProfiles.Batch028.profile1143,MergedCutProfiles.Batch028.profile1144,MergedCutProfiles.Batch028.profile1145,MergedCutProfiles.Batch028.profile1146,MergedCutProfiles.Batch028.profile1147,MergedCutProfiles.Batch028.profile1148,MergedCutProfiles.Batch028.profile1149,MergedCutProfiles.Batch028.profile1150]⟩
theorem profilesValid174 : retention174.ProfilesValid := by
  change ∀ j : Fin 16, (retention174.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch028.valid1135
  · exact MergedCutProfiles.Batch028.valid1136
  · exact MergedCutProfiles.Batch028.valid1137
  · exact MergedCutProfiles.Batch028.valid1138
  · exact MergedCutProfiles.Batch028.valid1139
  · exact MergedCutProfiles.Batch028.valid1140
  · exact MergedCutProfiles.Batch028.valid1141
  · exact MergedCutProfiles.Batch028.valid1142
  · exact MergedCutProfiles.Batch028.valid1143
  · exact MergedCutProfiles.Batch028.valid1144
  · exact MergedCutProfiles.Batch028.valid1145
  · exact MergedCutProfiles.Batch028.valid1146
  · exact MergedCutProfiles.Batch028.valid1147
  · exact MergedCutProfiles.Batch028.valid1148
  · exact MergedCutProfiles.Batch028.valid1149
  · exact MergedCutProfiles.Batch028.valid1150
theorem numericValid174 : retention174.NumericValid := by decide +kernel
def certificate174 : RatCutBinCertificate := ⟨⟨retention174,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(17667610735511169/7812500000000000)⟩,(249480270635237809/250000000000000000),(234258253806623509/500000000000000000),(2203270605705773/12500000000000000),(82798473315891117/1000000000000000000)⟩
theorem valid174 : certificate174.Valid := by decide +kernel
theorem sound174 : certificate174.Sound := rat_cut_bin_certificate_sound certificate174 profilesValid174 numericValid174 valid174

def retention175 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(443665418826969977/51975748035524142110),(678279174294463859/1000000000000000000),(39/10),(2898259931133339103279/1280000000000000000000),true,MergedCutProfiles.Batch028.profile1151,![MergedCutProfiles.Batch028.profile1151,MergedCutProfiles.Batch028.profile1152,MergedCutProfiles.Batch028.profile1153,MergedCutProfiles.Batch028.profile1154,MergedCutProfiles.Batch028.profile1155,MergedCutProfiles.Batch028.profile1156,MergedCutProfiles.Batch028.profile1157,MergedCutProfiles.Batch028.profile1158,MergedCutProfiles.Batch028.profile1159,MergedCutProfiles.Batch028.profile1147,MergedCutProfiles.Batch029.profile1160,MergedCutProfiles.Batch029.profile1161,MergedCutProfiles.Batch029.profile1162,MergedCutProfiles.Batch029.profile1163,MergedCutProfiles.Batch029.profile1164,MergedCutProfiles.Batch029.profile1165]⟩
theorem profilesValid175 : retention175.ProfilesValid := by
  change ∀ j : Fin 16, (retention175.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch028.valid1151
  · exact MergedCutProfiles.Batch028.valid1152
  · exact MergedCutProfiles.Batch028.valid1153
  · exact MergedCutProfiles.Batch028.valid1154
  · exact MergedCutProfiles.Batch028.valid1155
  · exact MergedCutProfiles.Batch028.valid1156
  · exact MergedCutProfiles.Batch028.valid1157
  · exact MergedCutProfiles.Batch028.valid1158
  · exact MergedCutProfiles.Batch028.valid1159
  · exact MergedCutProfiles.Batch028.valid1147
  · exact MergedCutProfiles.Batch029.valid1160
  · exact MergedCutProfiles.Batch029.valid1161
  · exact MergedCutProfiles.Batch029.valid1162
  · exact MergedCutProfiles.Batch029.valid1163
  · exact MergedCutProfiles.Batch029.valid1164
  · exact MergedCutProfiles.Batch029.valid1165
theorem numericValid175 : retention175.NumericValid := by decide +kernel
def certificate175 : RatCutBinCertificate := ⟨⟨retention175,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(2244825472112178113/1000000000000000000)⟩,(249480270635237809/250000000000000000),(93861043249091241/200000000000000000),(87832164843554399/500000000000000000),(16568184871528779/200000000000000000)⟩
theorem valid175 : certificate175.Valid := by decide +kernel
theorem sound175 : certificate175.Sound := rat_cut_bin_certificate_sound certificate175 profilesValid175 numericValid175 valid175

def retention176 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(56326257700000000/5197574803552414211),(443665418826969977/500000000000000000),(31/10),(1431684709973509257373/640000000000000000000),true,MergedCutProfiles.Batch029.profile1166,![MergedCutProfiles.Batch029.profile1166,MergedCutProfiles.Batch029.profile1167,MergedCutProfiles.Batch028.profile1139,MergedCutProfiles.Batch029.profile1168,MergedCutProfiles.Batch029.profile1169,MergedCutProfiles.Batch028.profile1144,MergedCutProfiles.Batch028.profile1159,MergedCutProfiles.Batch029.profile1170,MergedCutProfiles.Batch029.profile1171,MergedCutProfiles.Batch029.profile1172,MergedCutProfiles.Batch029.profile1163,MergedCutProfiles.Batch029.profile1173,MergedCutProfiles.Batch029.profile1174,MergedCutProfiles.Batch029.profile1175,MergedCutProfiles.Batch029.profile1176,MergedCutProfiles.Batch029.profile1177]⟩
theorem profilesValid176 : retention176.ProfilesValid := by
  change ∀ j : Fin 16, (retention176.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch029.valid1166
  · exact MergedCutProfiles.Batch029.valid1167
  · exact MergedCutProfiles.Batch028.valid1139
  · exact MergedCutProfiles.Batch029.valid1168
  · exact MergedCutProfiles.Batch029.valid1169
  · exact MergedCutProfiles.Batch028.valid1144
  · exact MergedCutProfiles.Batch028.valid1159
  · exact MergedCutProfiles.Batch029.valid1170
  · exact MergedCutProfiles.Batch029.valid1171
  · exact MergedCutProfiles.Batch029.valid1172
  · exact MergedCutProfiles.Batch029.valid1163
  · exact MergedCutProfiles.Batch029.valid1173
  · exact MergedCutProfiles.Batch029.valid1174
  · exact MergedCutProfiles.Batch029.valid1175
  · exact MergedCutProfiles.Batch029.valid1176
  · exact MergedCutProfiles.Batch029.valid1177
theorem numericValid176 : retention176.NumericValid := by decide +kernel
def certificate176 : RatCutBinCertificate := ⟨⟨retention176,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(1110777489186459697/500000000000000000)⟩,(249480270635237809/250000000000000000),(82075142351487651/200000000000000000),(224108979971336749/1000000000000000000),(15888016185430451/125000000000000000)⟩
theorem valid176 : certificate176.Valid := by decide +kernel
theorem sound176 : certificate176.Sound := rat_cut_bin_certificate_sound certificate176 profilesValid176 numericValid176 valid176

def retention177 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(57466043546829191/5197574803552414211),(563262577/500000000),(51/20),(444420743940828281/200000000000000000),true,MergedCutProfiles.Batch029.profile1166,![MergedCutProfiles.Batch029.profile1166,MergedCutProfiles.Batch029.profile1178,MergedCutProfiles.Batch029.profile1179,MergedCutProfiles.Batch029.profile1180,MergedCutProfiles.Batch029.profile1181,MergedCutProfiles.Batch029.profile1182,MergedCutProfiles.Batch029.profile1183,MergedCutProfiles.Batch029.profile1184,MergedCutProfiles.Batch029.profile1185,MergedCutProfiles.Batch029.profile1162,MergedCutProfiles.Batch029.profile1186,MergedCutProfiles.Batch029.profile1187,MergedCutProfiles.Batch029.profile1188,MergedCutProfiles.Batch029.profile1189,MergedCutProfiles.Batch029.profile1190,MergedCutProfiles.Batch029.profile1191]⟩
theorem profilesValid177 : retention177.ProfilesValid := by
  change ∀ j : Fin 16, (retention177.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch029.valid1166
  · exact MergedCutProfiles.Batch029.valid1178
  · exact MergedCutProfiles.Batch029.valid1179
  · exact MergedCutProfiles.Batch029.valid1180
  · exact MergedCutProfiles.Batch029.valid1181
  · exact MergedCutProfiles.Batch029.valid1182
  · exact MergedCutProfiles.Batch029.valid1183
  · exact MergedCutProfiles.Batch029.valid1184
  · exact MergedCutProfiles.Batch029.valid1185
  · exact MergedCutProfiles.Batch029.valid1162
  · exact MergedCutProfiles.Batch029.valid1186
  · exact MergedCutProfiles.Batch029.valid1187
  · exact MergedCutProfiles.Batch029.valid1188
  · exact MergedCutProfiles.Batch029.valid1189
  · exact MergedCutProfiles.Batch029.valid1190
  · exact MergedCutProfiles.Batch029.valid1191
theorem numericValid177 : retention177.NumericValid := by decide +kernel
def certificate177 : RatCutBinCertificate := ⟨⟨retention177,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(441878579002892859/200000000000000000)⟩,(249480270635237809/250000000000000000),(368408614386867709/1000000000000000000),(263708896362759611/1000000000000000000),(87561197942276193/500000000000000000)⟩
theorem valid177 : certificate177.Valid := by decide +kernel
theorem sound177 : certificate177.Sound := rat_cut_bin_certificate_sound certificate177 profilesValid177 numericValid177 valid177

def retention178 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(403002750825005377/25987874017762071055),(57466043546829191/50000000000000000),(5/2),(140428991374776906999/64000000000000000000),true,MergedCutProfiles.Batch029.profile1192,![MergedCutProfiles.Batch029.profile1192,MergedCutProfiles.Batch029.profile1193,MergedCutProfiles.Batch029.profile1194,MergedCutProfiles.Batch029.profile1195,MergedCutProfiles.Batch029.profile1183,MergedCutProfiles.Batch029.profile1160,MergedCutProfiles.Batch029.profile1172,MergedCutProfiles.Batch029.profile1196,MergedCutProfiles.Batch029.profile1197,MergedCutProfiles.Batch029.profile1189,MergedCutProfiles.Batch029.profile1198,MergedCutProfiles.Batch029.profile1199,MergedCutProfiles.Batch030.profile1200,MergedCutProfiles.Batch030.profile1201,MergedCutProfiles.Batch030.profile1202,MergedCutProfiles.Batch030.profile1203]⟩
theorem profilesValid178 : retention178.ProfilesValid := by
  change ∀ j : Fin 16, (retention178.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch029.valid1192
  · exact MergedCutProfiles.Batch029.valid1193
  · exact MergedCutProfiles.Batch029.valid1194
  · exact MergedCutProfiles.Batch029.valid1195
  · exact MergedCutProfiles.Batch029.valid1183
  · exact MergedCutProfiles.Batch029.valid1160
  · exact MergedCutProfiles.Batch029.valid1172
  · exact MergedCutProfiles.Batch029.valid1196
  · exact MergedCutProfiles.Batch029.valid1197
  · exact MergedCutProfiles.Batch029.valid1189
  · exact MergedCutProfiles.Batch029.valid1198
  · exact MergedCutProfiles.Batch029.valid1199
  · exact MergedCutProfiles.Batch030.valid1200
  · exact MergedCutProfiles.Batch030.valid1201
  · exact MergedCutProfiles.Batch030.valid1202
  · exact MergedCutProfiles.Batch030.valid1203
theorem numericValid178 : retention178.NumericValid := by decide +kernel
def certificate178 : RatCutBinCertificate := ⟨⟨retention178,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(2181741397422426111/1000000000000000000)⟩,(249480270635237809/250000000000000000),(369782542919861159/1000000000000000000),(262339635578200607/1000000000000000000),(43797315643609277/250000000000000000)⟩
theorem valid178 : certificate178.Valid := by decide +kernel
theorem sound178 : certificate178.Sound := rat_cut_bin_certificate_sound certificate178 profilesValid178 numericValid178 valid178

def retention179 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(12272364721295437047/103951496071048284220),(403002750825005377/250000000000000000),2,(11859316853784494697201320830793615287/6448044013200086032000000000000000000),false,MergedCutProfiles.Batch030.profile1204,(fun _ => MergedCutProfiles.Batch030.profile1204)⟩
theorem profilesValid179 : retention179.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1204
theorem numericValid179 : retention179.NumericValid := by decide +kernel
def certificate179 : RatCutBinCertificate := ⟨⟨retention179,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(1829242258615342101/1000000000000000000)⟩,(249480270635237809/250000000000000000),(77058299884940289/200000000000000000),(247232682770315637/1000000000000000000),(87869075797719693/500000000000000000)⟩
theorem valid179 : certificate179.Valid := by decide +kernel
theorem sound179 : certificate179.Sound := rat_cut_bin_certificate_sound certificate179 profilesValid179 numericValid179 valid179

def certificates : List RatCutBinCertificate := [certificate168,certificate169,certificate170,certificate171,certificate172,certificate173,certificate174,certificate175,certificate176,certificate177,certificate178,certificate179]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound168,List.forall_mem_cons.mpr ⟨sound169,List.forall_mem_cons.mpr ⟨sound170,List.forall_mem_cons.mpr ⟨sound171,List.forall_mem_cons.mpr ⟨sound172,List.forall_mem_cons.mpr ⟨sound173,List.forall_mem_cons.mpr ⟨sound174,List.forall_mem_cons.mpr ⟨sound175,List.forall_mem_cons.mpr ⟨sound176,List.forall_mem_cons.mpr ⟨sound177,List.forall_mem_cons.mpr ⟨sound178,List.forall_mem_cons.mpr ⟨sound179,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch014
