import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch015

def retention180 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(11992133938673687251/25987874017762071055),(12272364721295437047/1000000000000000000),(21/20),(21099819011924930879157471857961708300911/19635783554072699275200000000000000000000),false,MergedCutProfiles.Batch030.profile1205,(fun _ => MergedCutProfiles.Batch030.profile1205)⟩
theorem profilesValid180 : retention180.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1205
theorem numericValid180 : retention180.NumericValid := by decide +kernel
def certificate180 : RatCutBinCertificate := ⟨⟨retention180,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(534662864799086619/500000000000000000)⟩,(249480270635237809/250000000000000000),(45332400446856923/100000000000000000),(94014644975453683/500000000000000000),(7083259695746491/40000000000000000)⟩
theorem valid180 : certificate180.Valid := by decide +kernel
theorem sound180 : certificate180.Sound := rat_cut_bin_certificate_sound certificate180 profilesValid180 numericValid180 valid180

def retention181 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(5142876297141735339/10395149607104828422),(11992133938673687251/250000000000000000),1,(7726179095672406713390489176386009399/7674965720751159840640000000000000000),false,MergedCutProfiles.Batch030.profile1206,(fun _ => MergedCutProfiles.Batch030.profile1206)⟩
theorem profilesValid181 : retention181.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1206
theorem numericValid181 : retention181.NumericValid := by decide +kernel
def certificate181 : RatCutBinCertificate := ⟨⟨retention181,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(500844092557839351/500000000000000000)⟩,(249480270635237809/250000000000000000),(18368600524495979/40000000000000000),(36681357196955977/200000000000000000),(89790132663761401/500000000000000000)⟩
theorem valid181 : certificate181.Valid := by decide +kernel
theorem sound181 : certificate181.Sound := rat_cut_bin_certificate_sound certificate181 profilesValid181 numericValid181 valid181

def retention182 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(12985762650282881731/25987874017762071055),(5142876297141735339/100000000000000000),1,(205142053276311343622971655807073546431/205715051885669413560000000000000000000),false,MergedCutProfiles.Batch030.profile1207,(fun _ => MergedCutProfiles.Batch030.profile1207)⟩
theorem profilesValid182 : retention182.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1207
theorem numericValid182 : retention182.NumericValid := by decide +kernel
def certificate182 : RatCutBinCertificate := ⟨⟨retention182,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(496115001759453579/500000000000000000)⟩,(249480270635237809/250000000000000000),(115753780855477191/250000000000000000),(90232552598457449/500000000000000000),(21913077783181317/125000000000000000)⟩
theorem valid182 : certificate182.Valid := by decide +kernel
theorem sound182 : certificate182.Sound := rat_cut_bin_certificate_sound certificate182 profilesValid182 numericValid182 valid182

def retention183 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),(12985762650282881731/250000000000000000),1,(207073875223692614549800505412008413183/207772202404526107696000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid183 : retention183.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid183 : retention183.NumericValid := by decide +kernel
def certificate183 : RatCutBinCertificate := ⟨⟨retention183,(972731133584363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(198330875986319589/200000000000000000)⟩,(249480270635237809/250000000000000000),(463204613284077779/1000000000000000000),(180319238758201751/1000000000000000000),(87548031783078319/500000000000000000)⟩
theorem valid183 : certificate183.Valid := by decide +kernel
theorem sound183 : certificate183.Sound := rat_cut_bin_certificate_sound certificate183 profilesValid183 numericValid183 valid183

def retention184 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(10456477841867522503/25987874017762071055),(1808662218518331113/500000000000000000),(13/10),(433458108033811831063381605609452730079/361732443703666222600000000000000000000),false,MergedCutProfiles.Batch030.profile1209,(fun _ => MergedCutProfiles.Batch030.profile1209)⟩
theorem profilesValid184 : retention184.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1209
theorem numericValid184 : retention184.NumericValid := by decide +kernel
def certificate184 : RatCutBinCertificate := ⟨⟨retention184,(1159359005084363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(595280244134343381/500000000000000000)⟩,(24938055036253127/25000000000000000),(329698830864869809/1000000000000000000),(304465107004300697/1000000000000000000),(116379042579637039/500000000000000000)⟩
theorem valid184 : certificate184.Valid := by decide +kernel
theorem sound184 : certificate184.Sound := rat_cut_bin_certificate_sound certificate184 profilesValid184 numericValid184 valid184

def retention185 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(25772958033478391673/51975748035524142110),(10456477841867522503/250000000000000000),1,(33583092023435745439113487088077109787/33460729093976072009600000000000000000),false,MergedCutProfiles.Batch030.profile1210,(fun _ => MergedCutProfiles.Batch030.profile1210)⟩
theorem profilesValid185 : retention185.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1210
theorem numericValid185 : retention185.NumericValid := by decide +kernel
def certificate185 : RatCutBinCertificate := ⟨⟨retention185,(1159359005084363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(498857985461086323/500000000000000000)⟩,(24938055036253127/25000000000000000),(196712497592520647/500000000000000000),(239561021221239659/1000000000000000000),(116430369830497933/500000000000000000)⟩
theorem valid185 : certificate185.Valid := by decide +kernel
theorem sound185 : certificate185.Sound := rat_cut_bin_certificate_sound certificate185 profilesValid185 numericValid185 valid185

def retention186 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),(25772958033478391673/500000000000000000),1,(1643864065522767893102858561129730547/1649469314142617067072000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid186 : retention186.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid186 : retention186.NumericValid := by decide +kernel
def certificate186 : RatCutBinCertificate := ⟨⟨retention186,(1159359005084363907/500000000000000000),(702642711920787/31250000000000000),(8775613671743073521/1000000000000000000),(916665799546033481853/1000000000000000000),(495330423305509579/500000000000000000)⟩,(24938055036253127/25000000000000000),(198113412071800197/500000000000000000),(118478689567449371/500000000000000000),(229742347198798267/1000000000000000000)⟩
theorem valid186 : certificate186.Valid := by decide +kernel
theorem sound186 : certificate186.Sound := rat_cut_bin_certificate_sound certificate186 profilesValid186 numericValid186 valid186

def retention187 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(686544278477931553/95005518140300851637),(84968351296773707/125000000000000000),(39/10),(364025121564875026347/160000000000000000000),true,MergedCutProfiles.Batch030.profile1211,![MergedCutProfiles.Batch030.profile1211,MergedCutProfiles.Batch030.profile1212,MergedCutProfiles.Batch030.profile1213,MergedCutProfiles.Batch030.profile1214,MergedCutProfiles.Batch030.profile1215,MergedCutProfiles.Batch030.profile1216,MergedCutProfiles.Batch030.profile1217,MergedCutProfiles.Batch030.profile1218,MergedCutProfiles.Batch030.profile1219,MergedCutProfiles.Batch030.profile1220,MergedCutProfiles.Batch030.profile1221,MergedCutProfiles.Batch030.profile1222,MergedCutProfiles.Batch030.profile1223,MergedCutProfiles.Batch030.profile1224,MergedCutProfiles.Batch030.profile1225,MergedCutProfiles.Batch030.profile1226]⟩
theorem profilesValid187 : retention187.ProfilesValid := by
  change ∀ j : Fin 16, (retention187.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch030.valid1211
  · exact MergedCutProfiles.Batch030.valid1212
  · exact MergedCutProfiles.Batch030.valid1213
  · exact MergedCutProfiles.Batch030.valid1214
  · exact MergedCutProfiles.Batch030.valid1215
  · exact MergedCutProfiles.Batch030.valid1216
  · exact MergedCutProfiles.Batch030.valid1217
  · exact MergedCutProfiles.Batch030.valid1218
  · exact MergedCutProfiles.Batch030.valid1219
  · exact MergedCutProfiles.Batch030.valid1220
  · exact MergedCutProfiles.Batch030.valid1221
  · exact MergedCutProfiles.Batch030.valid1222
  · exact MergedCutProfiles.Batch030.valid1223
  · exact MergedCutProfiles.Batch030.valid1224
  · exact MergedCutProfiles.Batch030.valid1225
  · exact MergedCutProfiles.Batch030.valid1226
theorem numericValid187 : retention187.NumericValid := by decide +kernel
def certificate187 : RatCutBinCertificate := ⟨⟨retention187,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(2254150917503823663/1000000000000000000)⟩,(997755748188441097/1000000000000000000),(115734680409286073/250000000000000000),(90261970036187143/500000000000000000),(10679933872135467/125000000000000000)⟩
theorem valid187 : certificate187.Valid := by decide +kernel
theorem sound187 : certificate187.Sound := rat_cut_bin_certificate_sound certificate187 profilesValid187 numericValid187 valid187

def retention188 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(880446348716120977/95005518140300851637),(686544278477931553/1000000000000000000),(77/20),(2890439111438623935337/1280000000000000000000),true,MergedCutProfiles.Batch030.profile1227,![MergedCutProfiles.Batch030.profile1227,MergedCutProfiles.Batch030.profile1228,MergedCutProfiles.Batch030.profile1229,MergedCutProfiles.Batch030.profile1230,MergedCutProfiles.Batch030.profile1231,MergedCutProfiles.Batch030.profile1232,MergedCutProfiles.Batch030.profile1219,MergedCutProfiles.Batch030.profile1233,MergedCutProfiles.Batch030.profile1234,MergedCutProfiles.Batch030.profile1235,MergedCutProfiles.Batch030.profile1236,MergedCutProfiles.Batch030.profile1237,MergedCutProfiles.Batch030.profile1238,MergedCutProfiles.Batch030.profile1239,MergedCutProfiles.Batch031.profile1240,MergedCutProfiles.Batch031.profile1241]⟩
theorem profilesValid188 : retention188.ProfilesValid := by
  change ∀ j : Fin 16, (retention188.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch030.valid1227
  · exact MergedCutProfiles.Batch030.valid1228
  · exact MergedCutProfiles.Batch030.valid1229
  · exact MergedCutProfiles.Batch030.valid1230
  · exact MergedCutProfiles.Batch030.valid1231
  · exact MergedCutProfiles.Batch030.valid1232
  · exact MergedCutProfiles.Batch030.valid1219
  · exact MergedCutProfiles.Batch030.valid1233
  · exact MergedCutProfiles.Batch030.valid1234
  · exact MergedCutProfiles.Batch030.valid1235
  · exact MergedCutProfiles.Batch030.valid1236
  · exact MergedCutProfiles.Batch030.valid1237
  · exact MergedCutProfiles.Batch030.valid1238
  · exact MergedCutProfiles.Batch030.valid1239
  · exact MergedCutProfiles.Batch031.valid1240
  · exact MergedCutProfiles.Batch031.valid1241
theorem numericValid188 : retention188.NumericValid := by decide +kernel
def certificate188 : RatCutBinCertificate := ⟨⟨retention188,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(2237418771740601671/1000000000000000000)⟩,(997755748188441097/1000000000000000000),(92757227481892187/200000000000000000),(179872074055425969/1000000000000000000),(42733621584668823/500000000000000000)⟩
theorem valid188 : certificate188.Valid := by decide +kernel
theorem sound188 : certificate188.Sound := rat_cut_bin_certificate_sound certificate188 profilesValid188 numericValid188 valid188

def retention189 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1111052312000000000/95005518140300851637),(880446348716120977/1000000000000000000),(31/10),(2853839464955070853333/1280000000000000000000),true,MergedCutProfiles.Batch031.profile1242,![MergedCutProfiles.Batch031.profile1242,MergedCutProfiles.Batch031.profile1243,MergedCutProfiles.Batch031.profile1244,MergedCutProfiles.Batch030.profile1231,MergedCutProfiles.Batch030.profile1218,MergedCutProfiles.Batch031.profile1245,MergedCutProfiles.Batch031.profile1246,MergedCutProfiles.Batch030.profile1223,MergedCutProfiles.Batch031.profile1247,MergedCutProfiles.Batch031.profile1248,MergedCutProfiles.Batch031.profile1249,MergedCutProfiles.Batch031.profile1250,MergedCutProfiles.Batch031.profile1251,MergedCutProfiles.Batch031.profile1252,MergedCutProfiles.Batch031.profile1253,MergedCutProfiles.Batch031.profile1254]⟩
theorem profilesValid189 : retention189.ProfilesValid := by
  change ∀ j : Fin 16, (retention189.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch031.valid1242
  · exact MergedCutProfiles.Batch031.valid1243
  · exact MergedCutProfiles.Batch031.valid1244
  · exact MergedCutProfiles.Batch030.valid1231
  · exact MergedCutProfiles.Batch030.valid1218
  · exact MergedCutProfiles.Batch031.valid1245
  · exact MergedCutProfiles.Batch031.valid1246
  · exact MergedCutProfiles.Batch030.valid1223
  · exact MergedCutProfiles.Batch031.valid1247
  · exact MergedCutProfiles.Batch031.valid1248
  · exact MergedCutProfiles.Batch031.valid1249
  · exact MergedCutProfiles.Batch031.valid1250
  · exact MergedCutProfiles.Batch031.valid1251
  · exact MergedCutProfiles.Batch031.valid1252
  · exact MergedCutProfiles.Batch031.valid1253
  · exact MergedCutProfiles.Batch031.valid1254
theorem numericValid189 : retention189.NumericValid := by decide +kernel
def certificate189 : RatCutBinCertificate := ⟨⟨retention189,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(2212864936959045367/1000000000000000000)⟩,(997755748188441097/1000000000000000000),(410711825522150063/1000000000000000000),(13988109819655721/62500000000000000),(25262417293362283/200000000000000000)⟩
theorem valid189 : certificate189.Valid := by decide +kernel
theorem sound189 : certificate189.Sound := rat_cut_bin_certificate_sound certificate189 profilesValid189 numericValid189 valid189

def retention190 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1117933235138271284/95005518140300851637),(138881539/125000000),(51/20),(885492062364568989/400000000000000000),true,MergedCutProfiles.Batch031.profile1242,![MergedCutProfiles.Batch031.profile1242,MergedCutProfiles.Batch031.profile1243,MergedCutProfiles.Batch031.profile1255,MergedCutProfiles.Batch031.profile1256,MergedCutProfiles.Batch031.profile1257,MergedCutProfiles.Batch031.profile1258,MergedCutProfiles.Batch031.profile1246,MergedCutProfiles.Batch031.profile1259,MergedCutProfiles.Batch031.profile1247,MergedCutProfiles.Batch031.profile1248,MergedCutProfiles.Batch030.profile1239,MergedCutProfiles.Batch031.profile1260,MergedCutProfiles.Batch031.profile1261,MergedCutProfiles.Batch031.profile1252,MergedCutProfiles.Batch031.profile1262,MergedCutProfiles.Batch031.profile1263]⟩
theorem profilesValid190 : retention190.ProfilesValid := by
  change ∀ j : Fin 16, (retention190.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch031.valid1242
  · exact MergedCutProfiles.Batch031.valid1243
  · exact MergedCutProfiles.Batch031.valid1255
  · exact MergedCutProfiles.Batch031.valid1256
  · exact MergedCutProfiles.Batch031.valid1257
  · exact MergedCutProfiles.Batch031.valid1258
  · exact MergedCutProfiles.Batch031.valid1246
  · exact MergedCutProfiles.Batch031.valid1259
  · exact MergedCutProfiles.Batch031.valid1247
  · exact MergedCutProfiles.Batch031.valid1248
  · exact MergedCutProfiles.Batch030.valid1239
  · exact MergedCutProfiles.Batch031.valid1260
  · exact MergedCutProfiles.Batch031.valid1261
  · exact MergedCutProfiles.Batch031.valid1252
  · exact MergedCutProfiles.Batch031.valid1262
  · exact MergedCutProfiles.Batch031.valid1263
theorem numericValid190 : retention190.NumericValid := by decide +kernel
def certificate190 : RatCutBinCertificate := ⟨⟨retention190,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(219999541291020279/100000000000000000)⟩,(997755748188441097/1000000000000000000),(370078505978397061/1000000000000000000),(32755668283809777/125000000000000000),(172858821322858629/1000000000000000000)⟩
theorem valid190 : certificate190.Valid := by decide +kernel
theorem sound190 : certificate190.Sound := rat_cut_bin_certificate_sound certificate190 profilesValid190 numericValid190 valid190

def retention191 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1234893786266261086/95005518140300851637),(279483308784567821/250000000000000000),(51/20),(706828005491898111417/320000000000000000000),true,MergedCutProfiles.Batch031.profile1264,![MergedCutProfiles.Batch031.profile1264,MergedCutProfiles.Batch031.profile1265,MergedCutProfiles.Batch031.profile1266,MergedCutProfiles.Batch031.profile1267,MergedCutProfiles.Batch030.profile1219,MergedCutProfiles.Batch031.profile1268,MergedCutProfiles.Batch031.profile1269,MergedCutProfiles.Batch031.profile1270,MergedCutProfiles.Batch031.profile1248,MergedCutProfiles.Batch030.profile1239,MergedCutProfiles.Batch031.profile1271,MergedCutProfiles.Batch031.profile1272,MergedCutProfiles.Batch031.profile1273,MergedCutProfiles.Batch031.profile1274,MergedCutProfiles.Batch031.profile1275,MergedCutProfiles.Batch031.profile1276]⟩
theorem profilesValid191 : retention191.ProfilesValid := by
  change ∀ j : Fin 16, (retention191.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch031.valid1264
  · exact MergedCutProfiles.Batch031.valid1265
  · exact MergedCutProfiles.Batch031.valid1266
  · exact MergedCutProfiles.Batch031.valid1267
  · exact MergedCutProfiles.Batch030.valid1219
  · exact MergedCutProfiles.Batch031.valid1268
  · exact MergedCutProfiles.Batch031.valid1269
  · exact MergedCutProfiles.Batch031.valid1270
  · exact MergedCutProfiles.Batch031.valid1248
  · exact MergedCutProfiles.Batch030.valid1239
  · exact MergedCutProfiles.Batch031.valid1271
  · exact MergedCutProfiles.Batch031.valid1272
  · exact MergedCutProfiles.Batch031.valid1273
  · exact MergedCutProfiles.Batch031.valid1274
  · exact MergedCutProfiles.Batch031.valid1275
  · exact MergedCutProfiles.Batch031.valid1276
theorem numericValid191 : retention191.NumericValid := by decide +kernel
def certificate191 : RatCutBinCertificate := ⟨⟨retention191,(1949347535396698671/1000000000000000000),(12287303118992409/500000000000000000),(555878577904152321/62500000000000000),(53069362478983016179/62500000000000000),(1097551387512263393/500000000000000000)⟩,(997755748188441097/1000000000000000000),(5779527851841101/15625000000000000),(262232975120196531/1000000000000000000),(172935821847435127/1000000000000000000)⟩
theorem valid191 : certificate191.Valid := by decide +kernel
theorem sound191 : certificate191.Sound := rat_cut_bin_certificate_sound certificate191 profilesValid191 numericValid191 valid191

def certificates : List RatCutBinCertificate := [certificate180,certificate181,certificate182,certificate183,certificate184,certificate185,certificate186,certificate187,certificate188,certificate189,certificate190,certificate191]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound180,List.forall_mem_cons.mpr ⟨sound181,List.forall_mem_cons.mpr ⟨sound182,List.forall_mem_cons.mpr ⟨sound183,List.forall_mem_cons.mpr ⟨sound184,List.forall_mem_cons.mpr ⟨sound185,List.forall_mem_cons.mpr ⟨sound186,List.forall_mem_cons.mpr ⟨sound187,List.forall_mem_cons.mpr ⟨sound188,List.forall_mem_cons.mpr ⟨sound189,List.forall_mem_cons.mpr ⟨sound190,List.forall_mem_cons.mpr ⟨sound191,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch015
