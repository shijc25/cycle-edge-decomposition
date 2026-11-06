import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch041
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch331
import Cycle12.MergedCutProfiles.Batch332

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch178

def retention2136 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(57581753316831000709/136867250224018312986),(1089304490191547407/200000000000000000),(11/10),(99713500260051767599830640771642847479/87144359215323792560000000000000000000),false,MergedCutProfiles.Batch330.profile13221,(fun _ => MergedCutProfiles.Batch330.profile13221)⟩
theorem profilesValid2136 : retention2136.ProfilesValid := by
  exact MergedCutProfiles.Batch330.valid13221
theorem numericValid2136 : retention2136.NumericValid := by decide +kernel
def certificate2136 : RatCutBinCertificate := ⟨⟨retention2136,(2251960602753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(28381875972776529/25000000000000000)⟩,(99831184681307653/100000000000000000),(208843503080136233/1000000000000000000),(115958347512818919/250000000000000000),(12738297604380613/31250000000000000)⟩
theorem valid2136 : certificate2136.Valid := by decide +kernel
theorem sound2136 : certificate2136.Sound := rat_cut_bin_certificate_sound certificate2136 profilesValid2136 numericValid2136 valid2136

def retention2137 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(32000000000000000000/68433625112009156493),(57581753316831000709/1000000000000000000),1,(48904636059558758558585353102551461247/46065402653464800567200000000000000000),false,MergedCutProfiles.Batch330.profile13220,(fun _ => MergedCutProfiles.Batch330.profile13220)⟩
theorem profilesValid2137 : retention2137.ProfilesValid := by
  exact MergedCutProfiles.Batch330.valid13220
theorem numericValid2137 : retention2137.NumericValid := by decide +kernel
def certificate2137 : RatCutBinCertificate := ⟨⟨retention2137,(2251960602753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(1053490756319816231/1000000000000000000)⟩,(99831184681307653/100000000000000000),(56264095024875401/250000000000000000),(27445883977419957/62500000000000000),(90707744099808519/200000000000000000)⟩
theorem valid2137 : certificate2137.Valid := by decide +kernel
theorem sound2137 : certificate2137.Sound := rat_cut_bin_certificate_sound certificate2137 profilesValid2137 numericValid2137 valid2137

def retention2138 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid2138 : retention2138.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid2138 : retention2138.NumericValid := by decide +kernel
def certificate2138 : RatCutBinCertificate := ⟨⟨retention2138,(2251960602753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(247353412320048757/250000000000000000)⟩,(99831184681307653/100000000000000000),(239631640677397193/1000000000000000000),(417907575180634533/1000000000000000000),(203248041252679569/500000000000000000)⟩
theorem valid2138 : certificate2138.Valid := by decide +kernel
theorem sound2138 : certificate2138.Sound := rat_cut_bin_certificate_sound certificate2138 profilesValid2138 numericValid2138 valid2138

def retention2139 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(692095410042559447/126952512400278619267),(171310745060039467/250000000000000000),(39/10),(45929232755018315991/20000000000000000000),true,MergedCutProfiles.Batch330.profile13222,![MergedCutProfiles.Batch330.profile13222,MergedCutProfiles.Batch330.profile13223,MergedCutProfiles.Batch041.profile1655,MergedCutProfiles.Batch330.profile13224,MergedCutProfiles.Batch041.profile1641,MergedCutProfiles.Batch330.profile13225,MergedCutProfiles.Batch330.profile13226,MergedCutProfiles.Batch330.profile13227,MergedCutProfiles.Batch330.profile13228,MergedCutProfiles.Batch041.profile1643,MergedCutProfiles.Batch042.profile1683,MergedCutProfiles.Batch330.profile13229,MergedCutProfiles.Batch330.profile13230,MergedCutProfiles.Batch041.profile1674,MergedCutProfiles.Batch041.profile1644,MergedCutProfiles.Batch330.profile13231]⟩
theorem profilesValid2139 : retention2139.ProfilesValid := by
  change ∀ j : Fin 16, (retention2139.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch330.valid13222
  · exact MergedCutProfiles.Batch330.valid13223
  · exact MergedCutProfiles.Batch041.valid1655
  · exact MergedCutProfiles.Batch330.valid13224
  · exact MergedCutProfiles.Batch041.valid1641
  · exact MergedCutProfiles.Batch330.valid13225
  · exact MergedCutProfiles.Batch330.valid13226
  · exact MergedCutProfiles.Batch330.valid13227
  · exact MergedCutProfiles.Batch330.valid13228
  · exact MergedCutProfiles.Batch041.valid1643
  · exact MergedCutProfiles.Batch042.valid1683
  · exact MergedCutProfiles.Batch330.valid13229
  · exact MergedCutProfiles.Batch330.valid13230
  · exact MergedCutProfiles.Batch041.valid1674
  · exact MergedCutProfiles.Batch041.valid1644
  · exact MergedCutProfiles.Batch330.valid13231
theorem numericValid2139 : retention2139.NumericValid := by decide +kernel
def certificate2139 : RatCutBinCertificate := ⟨⟨retention2139,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(453410750841028149/200000000000000000)⟩,(39937578378027857/40000000000000000),(58564077209801503/125000000000000000),(176264597738957957/1000000000000000000),(5250201228280233/62500000000000000)⟩
theorem valid2139 : certificate2139.Valid := by decide +kernel
theorem sound2139 : certificate2139.Sound := rat_cut_bin_certificate_sound certificate2139 profilesValid2139 numericValid2139 valid2139

def retention2140 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(932840047732746344/126952512400278619267),(692095410042559447/1000000000000000000),(77/20),(2917029011460281870063/1280000000000000000000),true,MergedCutProfiles.Batch330.profile13232,![MergedCutProfiles.Batch330.profile13232,MergedCutProfiles.Batch330.profile13233,MergedCutProfiles.Batch330.profile13234,MergedCutProfiles.Batch330.profile13235,MergedCutProfiles.Batch330.profile13236,MergedCutProfiles.Batch330.profile13237,MergedCutProfiles.Batch330.profile13238,MergedCutProfiles.Batch330.profile13239,MergedCutProfiles.Batch041.profile1658,MergedCutProfiles.Batch331.profile13240,MergedCutProfiles.Batch331.profile13241,MergedCutProfiles.Batch331.profile13242,MergedCutProfiles.Batch041.profile1645,MergedCutProfiles.Batch331.profile13243,MergedCutProfiles.Batch041.profile1646,MergedCutProfiles.Batch331.profile13244]⟩
theorem profilesValid2140 : retention2140.ProfilesValid := by
  change ∀ j : Fin 16, (retention2140.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch330.valid13232
  · exact MergedCutProfiles.Batch330.valid13233
  · exact MergedCutProfiles.Batch330.valid13234
  · exact MergedCutProfiles.Batch330.valid13235
  · exact MergedCutProfiles.Batch330.valid13236
  · exact MergedCutProfiles.Batch330.valid13237
  · exact MergedCutProfiles.Batch330.valid13238
  · exact MergedCutProfiles.Batch330.valid13239
  · exact MergedCutProfiles.Batch041.valid1658
  · exact MergedCutProfiles.Batch331.valid13240
  · exact MergedCutProfiles.Batch331.valid13241
  · exact MergedCutProfiles.Batch331.valid13242
  · exact MergedCutProfiles.Batch041.valid1645
  · exact MergedCutProfiles.Batch331.valid13243
  · exact MergedCutProfiles.Batch041.valid1646
  · exact MergedCutProfiles.Batch331.valid13244
theorem numericValid2140 : retention2140.NumericValid := by decide +kernel
def certificate2140 : RatCutBinCertificate := ⟨⟨retention2140,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(2249898054838447339/1000000000000000000)⟩,(39937578378027857/40000000000000000),(469389420478367481/1000000000000000000),(43900159248014193/250000000000000000),(21001899775340987/250000000000000000)⟩
theorem valid2140 : certificate2140.Valid := by decide +kernel
theorem sound2140 : certificate2140.Sound := rat_cut_bin_certificate_sound certificate2140 profilesValid2140 numericValid2140 valid2140

def retention2141 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1150058225000000000/126952512400278619267),(116605005966593293/125000000000000000),3,(14434866735135482307/6400000000000000000),true,MergedCutProfiles.Batch331.profile13245,![MergedCutProfiles.Batch331.profile13245,MergedCutProfiles.Batch331.profile13246,MergedCutProfiles.Batch041.profile1641,MergedCutProfiles.Batch331.profile13247,MergedCutProfiles.Batch040.profile1627,MergedCutProfiles.Batch041.profile1643,MergedCutProfiles.Batch331.profile13248,MergedCutProfiles.Batch331.profile13249,MergedCutProfiles.Batch041.profile1644,MergedCutProfiles.Batch040.profile1631,MergedCutProfiles.Batch041.profile1660,MergedCutProfiles.Batch331.profile13250,MergedCutProfiles.Batch331.profile13244,MergedCutProfiles.Batch331.profile13251,MergedCutProfiles.Batch040.profile1635,MergedCutProfiles.Batch331.profile13252]⟩
theorem profilesValid2141 : retention2141.ProfilesValid := by
  change ∀ j : Fin 16, (retention2141.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch331.valid13245
  · exact MergedCutProfiles.Batch331.valid13246
  · exact MergedCutProfiles.Batch041.valid1641
  · exact MergedCutProfiles.Batch331.valid13247
  · exact MergedCutProfiles.Batch040.valid1627
  · exact MergedCutProfiles.Batch041.valid1643
  · exact MergedCutProfiles.Batch331.valid13248
  · exact MergedCutProfiles.Batch331.valid13249
  · exact MergedCutProfiles.Batch041.valid1644
  · exact MergedCutProfiles.Batch040.valid1631
  · exact MergedCutProfiles.Batch041.valid1660
  · exact MergedCutProfiles.Batch331.valid13250
  · exact MergedCutProfiles.Batch331.valid13244
  · exact MergedCutProfiles.Batch331.valid13251
  · exact MergedCutProfiles.Batch040.valid1635
  · exact MergedCutProfiles.Batch331.valid13252
theorem numericValid2141 : retention2141.NumericValid := by decide +kernel
def certificate2141 : RatCutBinCertificate := ⟨⟨retention2141,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(13955165562270021/6250000000000000)⟩,(39937578378027857/40000000000000000),(201438854481728391/500000000000000000),(230855984243157541/1000000000000000000),(67739850033464699/500000000000000000)⟩
theorem valid2141 : certificate2141.Valid := by decide +kernel
theorem sound2141 : certificate2141.Sound := rat_cut_bin_certificate_sound certificate2141 profilesValid2141 numericValid2141 valid2141

def retention2142 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1361505456629733283/126952512400278619267),(46002329/40000000),(5/2),(35617540032019367041/16000000000000000000),true,MergedCutProfiles.Batch330.profile13223,![MergedCutProfiles.Batch330.profile13223,MergedCutProfiles.Batch331.profile13253,MergedCutProfiles.Batch331.profile13254,MergedCutProfiles.Batch330.profile13227,MergedCutProfiles.Batch331.profile13255,MergedCutProfiles.Batch331.profile13256,MergedCutProfiles.Batch331.profile13257,MergedCutProfiles.Batch331.profile13258,MergedCutProfiles.Batch331.profile13259,MergedCutProfiles.Batch331.profile13260,MergedCutProfiles.Batch331.profile13244,MergedCutProfiles.Batch331.profile13261,MergedCutProfiles.Batch331.profile13262,MergedCutProfiles.Batch041.profile1649,MergedCutProfiles.Batch331.profile13263,MergedCutProfiles.Batch331.profile13264]⟩
theorem profilesValid2142 : retention2142.ProfilesValid := by
  change ∀ j : Fin 16, (retention2142.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch330.valid13223
  · exact MergedCutProfiles.Batch331.valid13253
  · exact MergedCutProfiles.Batch331.valid13254
  · exact MergedCutProfiles.Batch330.valid13227
  · exact MergedCutProfiles.Batch331.valid13255
  · exact MergedCutProfiles.Batch331.valid13256
  · exact MergedCutProfiles.Batch331.valid13257
  · exact MergedCutProfiles.Batch331.valid13258
  · exact MergedCutProfiles.Batch331.valid13259
  · exact MergedCutProfiles.Batch331.valid13260
  · exact MergedCutProfiles.Batch331.valid13244
  · exact MergedCutProfiles.Batch331.valid13261
  · exact MergedCutProfiles.Batch331.valid13262
  · exact MergedCutProfiles.Batch041.valid1649
  · exact MergedCutProfiles.Batch331.valid13263
  · exact MergedCutProfiles.Batch331.valid13264
theorem numericValid2142 : retention2142.NumericValid := by decide +kernel
def certificate2142 : RatCutBinCertificate := ⟨⟨retention2142,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(2207245059570868447/1000000000000000000)⟩,(39937578378027857/40000000000000000),(184521234760345459/500000000000000000),(52615311960878159/200000000000000000),(177383717429781941/1000000000000000000)⟩
theorem valid2142 : certificate2142.Valid := by decide +kernel
theorem sound2142 : certificate2142.Sound := rat_cut_bin_certificate_sound certificate2142 profilesValid2142 numericValid2142 valid2142

def retention2143 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(7390144483372443046/126952512400278619267),(1361505456629733283/1000000000000000000),(11/5),(2587200718681613138783/1280000000000000000000),true,MergedCutProfiles.Batch331.profile13265,![MergedCutProfiles.Batch331.profile13265,MergedCutProfiles.Batch041.profile1661,MergedCutProfiles.Batch331.profile13266,MergedCutProfiles.Batch331.profile13267,MergedCutProfiles.Batch331.profile13268,MergedCutProfiles.Batch331.profile13269,MergedCutProfiles.Batch331.profile13270,MergedCutProfiles.Batch331.profile13271,MergedCutProfiles.Batch331.profile13272,MergedCutProfiles.Batch331.profile13273,MergedCutProfiles.Batch331.profile13274,MergedCutProfiles.Batch331.profile13275,MergedCutProfiles.Batch331.profile13276,MergedCutProfiles.Batch331.profile13277,MergedCutProfiles.Batch331.profile13278,MergedCutProfiles.Batch331.profile13279]⟩
theorem profilesValid2143 : retention2143.ProfilesValid := by
  change ∀ j : Fin 16, (retention2143.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch331.valid13265
  · exact MergedCutProfiles.Batch041.valid1661
  · exact MergedCutProfiles.Batch331.valid13266
  · exact MergedCutProfiles.Batch331.valid13267
  · exact MergedCutProfiles.Batch331.valid13268
  · exact MergedCutProfiles.Batch331.valid13269
  · exact MergedCutProfiles.Batch331.valid13270
  · exact MergedCutProfiles.Batch331.valid13271
  · exact MergedCutProfiles.Batch331.valid13272
  · exact MergedCutProfiles.Batch331.valid13273
  · exact MergedCutProfiles.Batch331.valid13274
  · exact MergedCutProfiles.Batch331.valid13275
  · exact MergedCutProfiles.Batch331.valid13276
  · exact MergedCutProfiles.Batch331.valid13277
  · exact MergedCutProfiles.Batch331.valid13278
  · exact MergedCutProfiles.Batch331.valid13279
theorem numericValid2143 : retention2143.NumericValid := by decide +kernel
def certificate2143 : RatCutBinCertificate := ⟨⟨retention2143,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(250582689887454623/125000000000000000)⟩,(39937578378027857/40000000000000000),(590719896851369/1562500000000000),(12709842158283713/50000000000000000),(177283012415310257/1000000000000000000)⟩
theorem valid2143 : certificate2143.Valid := by decide +kernel
theorem sound2143 : certificate2143.Sound := rat_cut_bin_certificate_sound certificate2143 profilesValid2143 numericValid2143 valid2143

def retention2144 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(54066428967955346179/126952512400278619267),(3695072241686221523/500000000000000000),(21/20),(3341861898579486115733684301789421993511/2956057793348977218400000000000000000000),false,MergedCutProfiles.Batch332.profile13280,(fun _ => MergedCutProfiles.Batch332.profile13280)⟩
theorem profilesValid2144 : retention2144.ProfilesValid := by
  exact MergedCutProfiles.Batch332.valid13280
theorem numericValid2144 : retention2144.NumericValid := by decide +kernel
def certificate2144 : RatCutBinCertificate := ⟨⟨retention2144,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(1122595596844578983/1000000000000000000)⟩,(39937578378027857/40000000000000000),(451082090387369567/1000000000000000000),(94904254965938323/500000000000000000),(178061675907918079/1000000000000000000)⟩
theorem valid2144 : certificate2144.Valid := by decide +kernel
theorem sound2144 : certificate2144.Sound := rat_cut_bin_certificate_sound certificate2144 profilesValid2144 numericValid2144 valid2144

def retention2145 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(62769445559513346268/126952512400278619267),(54066428967955346179/1000000000000000000),1,(217972867296731478277958089179692006523/216265715871821384716000000000000000000),false,MergedCutProfiles.Batch332.profile13281,(fun _ => MergedCutProfiles.Batch332.profile13281)⟩
theorem profilesValid2145 : retention2145.ProfilesValid := by
  exact MergedCutProfiles.Batch332.valid13281
theorem numericValid2145 : retention2145.NumericValid := by decide +kernel
def certificate2145 : RatCutBinCertificate := ⟨⟨retention2145,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(1000353365954861177/1000000000000000000)⟩,(39937578378027857/40000000000000000),(45718595506510149/100000000000000000),(184990348537108819/1000000000000000000),(90703803238501717/500000000000000000)⟩
theorem valid2145 : certificate2145.Valid := by decide +kernel
theorem sound2145 : certificate2145.Sound := rat_cut_bin_certificate_sound certificate2145 profilesValid2145 numericValid2145 valid2145

def retention2146 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(63397140015108479731/126952512400278619267),(15692361389878336567/250000000000000000),1,(12537838190665744264973184332744611347/12553889111902669253600000000000000000),false,MergedCutProfiles.Batch332.profile13282,(fun _ => MergedCutProfiles.Batch332.profile13282)⟩
theorem profilesValid2146 : retention2146.ProfilesValid := by
  exact MergedCutProfiles.Batch332.valid13282
theorem numericValid2146 : retention2146.NumericValid := by decide +kernel
def certificate2146 : RatCutBinCertificate := ⟨⟨retention2146,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(991181036708970801/1000000000000000000)⟩,(39937578378027857/40000000000000000),(460330716589436341/1000000000000000000),(182539866293048793/1000000000000000000),(44459272868692453/250000000000000000)⟩
theorem valid2146 : certificate2146.Valid := by decide +kernel
theorem sound2146 : certificate2146.Sound := rat_cut_bin_certificate_sound certificate2146 profilesValid2146 numericValid2146 valid2146

def retention2147 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),(63397140015108479731/1000000000000000000),1,(50592066272303195876588295119144332311/50717712012086783784800000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid2147 : retention2147.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid2147 : retention2147.NumericValid := by decide +kernel
def certificate2147 : RatCutBinCertificate := ⟨⟨retention2147,(1963108699086418053/1000000000000000000),(36585906920747501/1000000000000000000),(9524976261342470737/1000000000000000000),(1215300036292237339909/1000000000000000000),(30936945129439619/31250000000000000)⟩,(39937578378027857/40000000000000000),(460821261860576837/1000000000000000000),(182159560807842369/1000000000000000000),(88641277444197051/500000000000000000)⟩
theorem valid2147 : certificate2147.Valid := by decide +kernel
theorem sound2147 : certificate2147.Sound := rat_cut_bin_certificate_sound certificate2147 profilesValid2147 numericValid2147 valid2147

def certificates : List RatCutBinCertificate := [certificate2136,certificate2137,certificate2138,certificate2139,certificate2140,certificate2141,certificate2142,certificate2143,certificate2144,certificate2145,certificate2146,certificate2147]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2136,List.forall_mem_cons.mpr ⟨sound2137,List.forall_mem_cons.mpr ⟨sound2138,List.forall_mem_cons.mpr ⟨sound2139,List.forall_mem_cons.mpr ⟨sound2140,List.forall_mem_cons.mpr ⟨sound2141,List.forall_mem_cons.mpr ⟨sound2142,List.forall_mem_cons.mpr ⟨sound2143,List.forall_mem_cons.mpr ⟨sound2144,List.forall_mem_cons.mpr ⟨sound2145,List.forall_mem_cons.mpr ⟨sound2146,List.forall_mem_cons.mpr ⟨sound2147,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch178
