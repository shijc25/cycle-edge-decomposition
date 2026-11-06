import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch053
import Cycle12.MergedCutProfiles.Batch054
import Cycle12.MergedCutProfiles.Batch055

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch027

def retention324 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(1/2),(24008318762963272801/1000000000000000000),1,(19034658177432741004628150504950870679/19206655010370618240800000000000000000),false,MergedCutProfiles.Batch053.profile2135,(fun _ => MergedCutProfiles.Batch053.profile2135)⟩
theorem profilesValid324 : retention324.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2135
theorem numericValid324 : retention324.NumericValid := by decide +kernel
def certificate324 : RatCutBinCertificate := ⟨⟨retention324,(1199906440567177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(195932445991624837/200000000000000000)⟩,(62207468005997529/62500000000000000),(103632346344484967/250000000000000000),(44086089025946987/200000000000000000),(206492179078743587/1000000000000000000)⟩
theorem valid324 : certificate324.Valid := by decide +kernel
theorem sound324 : certificate324.Sound := rat_cut_bin_certificate_sound certificate324 profilesValid324 numericValid324 valid324

def retention325 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(747167015452600629/46489286833483468562),(184942330557574413/250000000000000000),(7/2),(2209690564764813057/1000000000000000000),true,MergedCutProfiles.Batch053.profile2139,![MergedCutProfiles.Batch053.profile2139,MergedCutProfiles.Batch053.profile2140,MergedCutProfiles.Batch053.profile2141,MergedCutProfiles.Batch053.profile2142,MergedCutProfiles.Batch053.profile2143,MergedCutProfiles.Batch053.profile2144,MergedCutProfiles.Batch053.profile2145,MergedCutProfiles.Batch053.profile2146,MergedCutProfiles.Batch053.profile2147,MergedCutProfiles.Batch053.profile2148,MergedCutProfiles.Batch053.profile2149,MergedCutProfiles.Batch053.profile2150,MergedCutProfiles.Batch053.profile2151,MergedCutProfiles.Batch053.profile2152,MergedCutProfiles.Batch053.profile2153,MergedCutProfiles.Batch053.profile2154]⟩
theorem profilesValid325 : retention325.ProfilesValid := by
  change ∀ j : Fin 16, (retention325.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch053.valid2139
  · exact MergedCutProfiles.Batch053.valid2140
  · exact MergedCutProfiles.Batch053.valid2141
  · exact MergedCutProfiles.Batch053.valid2142
  · exact MergedCutProfiles.Batch053.valid2143
  · exact MergedCutProfiles.Batch053.valid2144
  · exact MergedCutProfiles.Batch053.valid2145
  · exact MergedCutProfiles.Batch053.valid2146
  · exact MergedCutProfiles.Batch053.valid2147
  · exact MergedCutProfiles.Batch053.valid2148
  · exact MergedCutProfiles.Batch053.valid2149
  · exact MergedCutProfiles.Batch053.valid2150
  · exact MergedCutProfiles.Batch053.valid2151
  · exact MergedCutProfiles.Batch053.valid2152
  · exact MergedCutProfiles.Batch053.valid2153
  · exact MergedCutProfiles.Batch053.valid2154
theorem numericValid325 : retention325.NumericValid := by decide +kernel
def certificate325 : RatCutBinCertificate := ⟨⟨retention325,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(543846715231075781/250000000000000000)⟩,(497987377948687399/500000000000000000),(433338079059417259/1000000000000000000),(5107201920132249/25000000000000000),(25477759492475829/250000000000000000)⟩
theorem valid325 : certificate325.Valid := by decide +kernel
theorem sound325 : certificate325.Sound := rat_cut_bin_certificate_sound certificate325 profilesValid325 numericValid325 valid325

def retention326 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(438056043255547284/23244643416741734281),(747167015452600629/1000000000000000000),(69/20),(2807600086901806513357/1280000000000000000000),true,MergedCutProfiles.Batch053.profile2155,![MergedCutProfiles.Batch053.profile2155,MergedCutProfiles.Batch053.profile2156,MergedCutProfiles.Batch053.profile2157,MergedCutProfiles.Batch053.profile2158,MergedCutProfiles.Batch053.profile2159,MergedCutProfiles.Batch054.profile2160,MergedCutProfiles.Batch054.profile2161,MergedCutProfiles.Batch054.profile2162,MergedCutProfiles.Batch054.profile2163,MergedCutProfiles.Batch054.profile2164,MergedCutProfiles.Batch054.profile2165,MergedCutProfiles.Batch054.profile2166,MergedCutProfiles.Batch054.profile2167,MergedCutProfiles.Batch054.profile2168,MergedCutProfiles.Batch054.profile2169,MergedCutProfiles.Batch054.profile2170]⟩
theorem profilesValid326 : retention326.ProfilesValid := by
  change ∀ j : Fin 16, (retention326.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch053.valid2155
  · exact MergedCutProfiles.Batch053.valid2156
  · exact MergedCutProfiles.Batch053.valid2157
  · exact MergedCutProfiles.Batch053.valid2158
  · exact MergedCutProfiles.Batch053.valid2159
  · exact MergedCutProfiles.Batch054.valid2160
  · exact MergedCutProfiles.Batch054.valid2161
  · exact MergedCutProfiles.Batch054.valid2162
  · exact MergedCutProfiles.Batch054.valid2163
  · exact MergedCutProfiles.Batch054.valid2164
  · exact MergedCutProfiles.Batch054.valid2165
  · exact MergedCutProfiles.Batch054.valid2166
  · exact MergedCutProfiles.Batch054.valid2167
  · exact MergedCutProfiles.Batch054.valid2168
  · exact MergedCutProfiles.Batch054.valid2169
  · exact MergedCutProfiles.Batch054.valid2170
theorem numericValid326 : retention326.NumericValid := by decide +kernel
def certificate326 : RatCutBinCertificate := ⟨⟨retention326,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(2159623910902755581/1000000000000000000)⟩,(497987377948687399/500000000000000000),(217159023687059407/500000000000000000),(20346971288291281/100000000000000000),(12749758280183721/125000000000000000)⟩
theorem valid326 : certificate326.Valid := by decide +kernel
theorem sound326 : certificate326.Sound := rat_cut_bin_certificate_sound certificate326 profilesValid326 numericValid326 valid326

def retention327 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(71022134000000000/3320663345248819183),(109514010813886821/125000000000000000),3,(13894793175996443417/6400000000000000000),true,MergedCutProfiles.Batch054.profile2171,![MergedCutProfiles.Batch054.profile2171,MergedCutProfiles.Batch054.profile2172,MergedCutProfiles.Batch053.profile2142,MergedCutProfiles.Batch054.profile2173,MergedCutProfiles.Batch054.profile2174,MergedCutProfiles.Batch053.profile2146,MergedCutProfiles.Batch054.profile2162,MergedCutProfiles.Batch054.profile2175,MergedCutProfiles.Batch053.profile2150,MergedCutProfiles.Batch054.profile2176,MergedCutProfiles.Batch054.profile2177,MergedCutProfiles.Batch053.profile2154,MergedCutProfiles.Batch054.profile2178,MergedCutProfiles.Batch054.profile2179,MergedCutProfiles.Batch054.profile2180,MergedCutProfiles.Batch054.profile2181]⟩
theorem profilesValid327 : retention327.ProfilesValid := by
  change ∀ j : Fin 16, (retention327.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch054.valid2171
  · exact MergedCutProfiles.Batch054.valid2172
  · exact MergedCutProfiles.Batch053.valid2142
  · exact MergedCutProfiles.Batch054.valid2173
  · exact MergedCutProfiles.Batch054.valid2174
  · exact MergedCutProfiles.Batch053.valid2146
  · exact MergedCutProfiles.Batch054.valid2162
  · exact MergedCutProfiles.Batch054.valid2175
  · exact MergedCutProfiles.Batch053.valid2150
  · exact MergedCutProfiles.Batch054.valid2176
  · exact MergedCutProfiles.Batch054.valid2177
  · exact MergedCutProfiles.Batch053.valid2154
  · exact MergedCutProfiles.Batch054.valid2178
  · exact MergedCutProfiles.Batch054.valid2179
  · exact MergedCutProfiles.Batch054.valid2180
  · exact MergedCutProfiles.Batch054.valid2181
theorem numericValid327 : retention327.NumericValid := by decide +kernel
def certificate327 : RatCutBinCertificate := ⟨⟨retention327,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(2141658276673919537/1000000000000000000)⟩,(497987377948687399/500000000000000000),(405563684737832291/1000000000000000000),(228423134648060857/1000000000000000000),(15954594526827353/125000000000000000)⟩
theorem valid327 : certificate327.Valid := by decide +kernel
theorem sound327 : certificate327.Sound := rat_cut_bin_certificate_sound certificate327 profilesValid327 numericValid327 valid327

def retention328 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(550707857544914316/23244643416741734281),(248577469/250000000),(27/10),(17232569927716057051/8000000000000000000),true,MergedCutProfiles.Batch054.profile2182,![MergedCutProfiles.Batch054.profile2182,MergedCutProfiles.Batch054.profile2183,MergedCutProfiles.Batch054.profile2184,MergedCutProfiles.Batch053.profile2159,MergedCutProfiles.Batch054.profile2185,MergedCutProfiles.Batch054.profile2186,MergedCutProfiles.Batch054.profile2187,MergedCutProfiles.Batch054.profile2164,MergedCutProfiles.Batch054.profile2176,MergedCutProfiles.Batch054.profile2188,MergedCutProfiles.Batch054.profile2189,MergedCutProfiles.Batch054.profile2169,MergedCutProfiles.Batch054.profile2190,MergedCutProfiles.Batch054.profile2191,MergedCutProfiles.Batch054.profile2192,MergedCutProfiles.Batch054.profile2193]⟩
theorem profilesValid328 : retention328.ProfilesValid := by
  change ∀ j : Fin 16, (retention328.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch054.valid2182
  · exact MergedCutProfiles.Batch054.valid2183
  · exact MergedCutProfiles.Batch054.valid2184
  · exact MergedCutProfiles.Batch053.valid2159
  · exact MergedCutProfiles.Batch054.valid2185
  · exact MergedCutProfiles.Batch054.valid2186
  · exact MergedCutProfiles.Batch054.valid2187
  · exact MergedCutProfiles.Batch054.valid2164
  · exact MergedCutProfiles.Batch054.valid2176
  · exact MergedCutProfiles.Batch054.valid2188
  · exact MergedCutProfiles.Batch054.valid2189
  · exact MergedCutProfiles.Batch054.valid2169
  · exact MergedCutProfiles.Batch054.valid2190
  · exact MergedCutProfiles.Batch054.valid2191
  · exact MergedCutProfiles.Batch054.valid2192
  · exact MergedCutProfiles.Batch054.valid2193
theorem numericValid328 : retention328.NumericValid := by decide +kernel
def certificate328 : RatCutBinCertificate := ⟨⟨retention328,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(265951052703169561/125000000000000000)⟩,(497987377948687399/500000000000000000),(385778574642400169/1000000000000000000),(12338423501869463/50000000000000000),(149628847271663551/1000000000000000000)⟩
theorem valid328 : certificate328.Valid := by decide +kernel
theorem sound328 : certificate328.Sound := rat_cut_bin_certificate_sound certificate328 profilesValid328 numericValid328 valid328

def retention329 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(1283033643723800897/23244643416741734281),(137676964386228579/125000000000000000),(5/2),(4072123168021895041/2000000000000000000),true,MergedCutProfiles.Batch054.profile2194,![MergedCutProfiles.Batch054.profile2194,MergedCutProfiles.Batch054.profile2195,MergedCutProfiles.Batch054.profile2187,MergedCutProfiles.Batch054.profile2196,MergedCutProfiles.Batch054.profile2197,MergedCutProfiles.Batch054.profile2191,MergedCutProfiles.Batch054.profile2198,MergedCutProfiles.Batch054.profile2199,MergedCutProfiles.Batch055.profile2200,MergedCutProfiles.Batch055.profile2201,MergedCutProfiles.Batch055.profile2202,MergedCutProfiles.Batch055.profile2203,MergedCutProfiles.Batch055.profile2204,MergedCutProfiles.Batch055.profile2205,MergedCutProfiles.Batch055.profile2206,MergedCutProfiles.Batch055.profile2207]⟩
theorem profilesValid329 : retention329.ProfilesValid := by
  change ∀ j : Fin 16, (retention329.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch054.valid2194
  · exact MergedCutProfiles.Batch054.valid2195
  · exact MergedCutProfiles.Batch054.valid2187
  · exact MergedCutProfiles.Batch054.valid2196
  · exact MergedCutProfiles.Batch054.valid2197
  · exact MergedCutProfiles.Batch054.valid2191
  · exact MergedCutProfiles.Batch054.valid2198
  · exact MergedCutProfiles.Batch054.valid2199
  · exact MergedCutProfiles.Batch055.valid2200
  · exact MergedCutProfiles.Batch055.valid2201
  · exact MergedCutProfiles.Batch055.valid2202
  · exact MergedCutProfiles.Batch055.valid2203
  · exact MergedCutProfiles.Batch055.valid2204
  · exact MergedCutProfiles.Batch055.valid2205
  · exact MergedCutProfiles.Batch055.valid2206
  · exact MergedCutProfiles.Batch055.valid2207
theorem numericValid329 : retention329.NumericValid := by decide +kernel
def certificate329 : RatCutBinCertificate := ⟨⟨retention329,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(2011558997339393599/1000000000000000000)⟩,(497987377948687399/500000000000000000),(390909090709382129/1000000000000000000),(60478988346308603/250000000000000000),(149934409163428257/1000000000000000000)⟩
theorem valid329 : certificate329.Valid := by decide +kernel
theorem sound329 : certificate329.Sound := rat_cut_bin_certificate_sound certificate329 profilesValid329 numericValid329 valid329

def retention330 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(14350456106813956925/46489286833483468562),(1283033643723800897/500000000000000000),(29/20),(1427330942271665127888519848220522013431/1026426914979040717600000000000000000000),false,MergedCutProfiles.Batch055.profile2208,(fun _ => MergedCutProfiles.Batch055.profile2208)⟩
theorem profilesValid330 : retention330.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2208
theorem numericValid330 : retention330.NumericValid := by decide +kernel
def certificate330 : RatCutBinCertificate := ⟨⟨retention330,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(1376370785835017171/1000000000000000000)⟩,(497987377948687399/500000000000000000),(219344674814147267/500000000000000000),(99923063579462021/500000000000000000),(150460806764662819/1000000000000000000)⟩
theorem valid330 : certificate330.Valid := by decide +kernel
theorem sound330 : certificate330.Sound := rat_cut_bin_certificate_sound certificate330 profilesValid330 numericValid330 valid330

def retention331 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(22455747943603892167/46489286833483468562),(574018244272558277/40000000000000000),(21/20),(949452702473918119636289970465118538279/918429190836093243200000000000000000000),false,MergedCutProfiles.Batch055.profile2209,(fun _ => MergedCutProfiles.Batch055.profile2209)⟩
theorem profilesValid331 : retention331.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2209
theorem numericValid331 : retention331.NumericValid := by decide +kernel
def certificate331 : RatCutBinCertificate := ⟨⟨retention331,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(51174405733784599/50000000000000000)⟩,(497987377948687399/500000000000000000),(47980700108192049/100000000000000000),(8391819364059841/50000000000000000),(153018823709608223/1000000000000000000)⟩
theorem valid331 : certificate331.Valid := by decide +kernel
theorem sound331 : certificate331.Sound := rat_cut_bin_certificate_sound certificate331 profilesValid331 numericValid331 valid331

def retention332 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(11568089781021516852/23244643416741734281),(22455747943603892167/1000000000000000000),1,(89364352275770331152684725996231165627/89822991774415568668000000000000000000),false,MergedCutProfiles.Batch055.profile2210,(fun _ => MergedCutProfiles.Batch055.profile2210)⟩
theorem profilesValid332 : retention332.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2210
theorem numericValid332 : retention332.NumericValid := by decide +kernel
def certificate332 : RatCutBinCertificate := ⟨⟨retention332,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(492546627191801747/500000000000000000)⟩,(497987377948687399/500000000000000000),(61189282562312781/125000000000000000),(80402612303811359/500000000000000000),(37781501675574829/250000000000000000)⟩
theorem valid332 : certificate332.Valid := by decide +kernel
theorem sound332 : certificate332.Sound := rat_cut_bin_certificate_sound certificate332 profilesValid332 numericValid332 valid332

def retention333 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(1/2),(2892022445255379213/125000000000000000),1,(1909992987884227510680993516324840021/1928014963503586142000000000000000000),false,MergedCutProfiles.Batch055.profile2211,(fun _ => MergedCutProfiles.Batch055.profile2211)⟩
theorem profilesValid333 : retention333.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2211
theorem numericValid333 : retention333.NumericValid := by decide +kernel
def certificate333 : RatCutBinCertificate := ⟨⟨retention333,(503842867031020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(196170373462019643/200000000000000000)⟩,(497987377948687399/500000000000000000),(3837192857949833/7812500000000000),(79815942082520567/500000000000000000),(1168663318993153/7812500000000000)⟩
theorem valid333 : certificate333.Valid := by decide +kernel
theorem sound333 : certificate333.Sound := rat_cut_bin_certificate_sound certificate333 profilesValid333 numericValid333 valid333

def retention334 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(19664409369767817945/46489286833483468562),(3732600285901326481/1000000000000000000),(5/4),(275628695496145070630348684074952472511/238886418297684894784000000000000000000),false,MergedCutProfiles.Batch055.profile2212,(fun _ => MergedCutProfiles.Batch055.profile2212)⟩
theorem profilesValid334 : retention334.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2212
theorem numericValid334 : retention334.NumericValid := by decide +kernel
def certificate334 : RatCutBinCertificate := ⟨⟨retention334,(600580117281020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(569601585594550793/500000000000000000)⟩,(995201726054026297/1000000000000000000),(355002273138157727/1000000000000000000),(277341295511061849/1000000000000000000),(10517842343332881/50000000000000000)⟩
theorem valid334 : certificate334.Valid := by decide +kernel
theorem sound334 : certificate334.Sound := rat_cut_bin_certificate_sound certificate334 profilesValid334 numericValid334 valid334

def retention335 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(23058066492027228411/46489286833483468562),(3932881873953563589/200000000000000000),1,(78388273578211248430932385844266333739/78657637479071271780000000000000000000),false,MergedCutProfiles.Batch055.profile2213,(fun _ => MergedCutProfiles.Batch055.profile2213)⟩
theorem profilesValid335 : retention335.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2213
theorem numericValid335 : retention335.NumericValid := by decide +kernel
def certificate335 : RatCutBinCertificate := ⟨⟨retention335,(600580117281020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(984893048193108421/1000000000000000000)⟩,(995201726054026297/1000000000000000000),(410622976860563789/1000000000000000000),(223888827250350891/1000000000000000000),(3264988340903399/15625000000000000)⟩
theorem valid335 : certificate335.Valid := by decide +kernel
theorem sound335 : certificate335.Sound := rat_cut_bin_certificate_sound certificate335 profilesValid335 numericValid335 valid335

def certificates : List RatCutBinCertificate := [certificate324,certificate325,certificate326,certificate327,certificate328,certificate329,certificate330,certificate331,certificate332,certificate333,certificate334,certificate335]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound324,List.forall_mem_cons.mpr ⟨sound325,List.forall_mem_cons.mpr ⟨sound326,List.forall_mem_cons.mpr ⟨sound327,List.forall_mem_cons.mpr ⟨sound328,List.forall_mem_cons.mpr ⟨sound329,List.forall_mem_cons.mpr ⟨sound330,List.forall_mem_cons.mpr ⟨sound331,List.forall_mem_cons.mpr ⟨sound332,List.forall_mem_cons.mpr ⟨sound333,List.forall_mem_cons.mpr ⟨sound334,List.forall_mem_cons.mpr ⟨sound335,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch027
