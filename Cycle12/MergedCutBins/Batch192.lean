import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch355
import Cycle12.MergedCutProfiles.Batch356
import Cycle12.MergedCutProfiles.Batch357

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch192

def retention2304 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1034140447000000000/56544910216936768259),(921282437067070239/1000000000000000000),(59/20),(2820559486465806142607/1280000000000000000000),true,MergedCutProfiles.Batch355.profile14229,![MergedCutProfiles.Batch355.profile14229,MergedCutProfiles.Batch355.profile14230,MergedCutProfiles.Batch355.profile14231,MergedCutProfiles.Batch355.profile14232,MergedCutProfiles.Batch355.profile14233,MergedCutProfiles.Batch355.profile14205,MergedCutProfiles.Batch355.profile14234,MergedCutProfiles.Batch355.profile14235,MergedCutProfiles.Batch355.profile14236,MergedCutProfiles.Batch355.profile14237,MergedCutProfiles.Batch355.profile14238,MergedCutProfiles.Batch355.profile14239,MergedCutProfiles.Batch356.profile14240,MergedCutProfiles.Batch356.profile14241,MergedCutProfiles.Batch356.profile14242,MergedCutProfiles.Batch356.profile14243]⟩
theorem profilesValid2304 : retention2304.ProfilesValid := by
  change ∀ j : Fin 16, (retention2304.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch355.valid14229
  · exact MergedCutProfiles.Batch355.valid14230
  · exact MergedCutProfiles.Batch355.valid14231
  · exact MergedCutProfiles.Batch355.valid14232
  · exact MergedCutProfiles.Batch355.valid14233
  · exact MergedCutProfiles.Batch355.valid14205
  · exact MergedCutProfiles.Batch355.valid14234
  · exact MergedCutProfiles.Batch355.valid14235
  · exact MergedCutProfiles.Batch355.valid14236
  · exact MergedCutProfiles.Batch355.valid14237
  · exact MergedCutProfiles.Batch355.valid14238
  · exact MergedCutProfiles.Batch355.valid14239
  · exact MergedCutProfiles.Batch356.valid14240
  · exact MergedCutProfiles.Batch356.valid14241
  · exact MergedCutProfiles.Batch356.valid14242
  · exact MergedCutProfiles.Batch356.valid14243
theorem numericValid2304 : retention2304.NumericValid := by decide +kernel
def certificate2304 : RatCutBinCertificate := ⟨⟨retention2304,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(2160889891756638991/1000000000000000000)⟩,(249276745144070473/250000000000000000),(23925333153350631/62500000000000000),(249611757948685427/1000000000000000000),(71769299572064323/500000000000000000)⟩
theorem valid2304 : certificate2304.Valid := by decide +kernel
theorem sound2304 : certificate2304.Sound := rat_cut_bin_certificate_sound certificate2304 profilesValid2304 numericValid2304 valid2304

def retention2305 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1038124109908155927/56544910216936768259),(1034140447/1000000000),(53/20),(8760513434530881013/4000000000000000000),true,MergedCutProfiles.Batch355.profile14229,![MergedCutProfiles.Batch355.profile14229,MergedCutProfiles.Batch356.profile14244,MergedCutProfiles.Batch355.profile14201,MergedCutProfiles.Batch355.profile14232,MergedCutProfiles.Batch356.profile14245,MergedCutProfiles.Batch355.profile14205,MergedCutProfiles.Batch355.profile14234,MergedCutProfiles.Batch355.profile14222,MergedCutProfiles.Batch355.profile14209,MergedCutProfiles.Batch356.profile14246,MergedCutProfiles.Batch356.profile14247,MergedCutProfiles.Batch355.profile14213,MergedCutProfiles.Batch356.profile14248,MergedCutProfiles.Batch356.profile14241,MergedCutProfiles.Batch356.profile14242,MergedCutProfiles.Batch356.profile14249]⟩
theorem profilesValid2305 : retention2305.ProfilesValid := by
  change ∀ j : Fin 16, (retention2305.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch355.valid14229
  · exact MergedCutProfiles.Batch356.valid14244
  · exact MergedCutProfiles.Batch355.valid14201
  · exact MergedCutProfiles.Batch355.valid14232
  · exact MergedCutProfiles.Batch356.valid14245
  · exact MergedCutProfiles.Batch355.valid14205
  · exact MergedCutProfiles.Batch355.valid14234
  · exact MergedCutProfiles.Batch355.valid14222
  · exact MergedCutProfiles.Batch355.valid14209
  · exact MergedCutProfiles.Batch356.valid14246
  · exact MergedCutProfiles.Batch356.valid14247
  · exact MergedCutProfiles.Batch355.valid14213
  · exact MergedCutProfiles.Batch356.valid14248
  · exact MergedCutProfiles.Batch356.valid14241
  · exact MergedCutProfiles.Batch356.valid14242
  · exact MergedCutProfiles.Batch356.valid14249
theorem numericValid2305 : retention2305.NumericValid := by decide +kernel
def certificate2305 : RatCutBinCertificate := ⟨⟨retention2305,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(2151795712531556953/1000000000000000000)⟩,(249276745144070473/250000000000000000),(365029091704016887/1000000000000000000),(53419751444470377/200000000000000000),(166748347628669421/1000000000000000000)⟩
theorem valid2305 : certificate2305.Valid := by decide +kernel
theorem sound2305 : certificate2305.Sound := rat_cut_bin_certificate_sound certificate2305 profilesValid2305 numericValid2305 valid2305

def retention2306 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1091078872764588869/56544910216936768259),(1038124109908155927/1000000000000000000),(53/20),(2799612104393600811087/1280000000000000000000),true,MergedCutProfiles.Batch356.profile14250,![MergedCutProfiles.Batch356.profile14250,MergedCutProfiles.Batch356.profile14251,MergedCutProfiles.Batch356.profile14252,MergedCutProfiles.Batch356.profile14253,MergedCutProfiles.Batch356.profile14254,MergedCutProfiles.Batch356.profile14255,MergedCutProfiles.Batch356.profile14256,MergedCutProfiles.Batch356.profile14257,MergedCutProfiles.Batch356.profile14258,MergedCutProfiles.Batch355.profile14211,MergedCutProfiles.Batch355.profile14225,MergedCutProfiles.Batch356.profile14259,MergedCutProfiles.Batch356.profile14260,MergedCutProfiles.Batch356.profile14261,MergedCutProfiles.Batch356.profile14262,MergedCutProfiles.Batch356.profile14263]⟩
theorem profilesValid2306 : retention2306.ProfilesValid := by
  change ∀ j : Fin 16, (retention2306.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch356.valid14250
  · exact MergedCutProfiles.Batch356.valid14251
  · exact MergedCutProfiles.Batch356.valid14252
  · exact MergedCutProfiles.Batch356.valid14253
  · exact MergedCutProfiles.Batch356.valid14254
  · exact MergedCutProfiles.Batch356.valid14255
  · exact MergedCutProfiles.Batch356.valid14256
  · exact MergedCutProfiles.Batch356.valid14257
  · exact MergedCutProfiles.Batch356.valid14258
  · exact MergedCutProfiles.Batch355.valid14211
  · exact MergedCutProfiles.Batch355.valid14225
  · exact MergedCutProfiles.Batch356.valid14259
  · exact MergedCutProfiles.Batch356.valid14260
  · exact MergedCutProfiles.Batch356.valid14261
  · exact MergedCutProfiles.Batch356.valid14262
  · exact MergedCutProfiles.Batch356.valid14263
theorem numericValid2306 : retention2306.NumericValid := by decide +kernel
def certificate2306 : RatCutBinCertificate := ⟨⟨retention2306,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(429772863421004157/200000000000000000)⟩,(249276745144070473/250000000000000000),(72983739476341033/200000000000000000),(267210014836778747/1000000000000000000),(2606074755563303/15625000000000000)⟩
theorem valid2306 : certificate2306.Valid := by decide +kernel
theorem sound2306 : certificate2306.Sound := rat_cut_bin_certificate_sound certificate2306 profilesValid2306 numericValid2306 valid2306

def retention2307 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1904816209601631016/56544910216936768259),(1091078872764588869/1000000000000000000),(51/20),(2721353125372196261653/1280000000000000000000),true,MergedCutProfiles.Batch356.profile14264,![MergedCutProfiles.Batch356.profile14264,MergedCutProfiles.Batch356.profile14265,MergedCutProfiles.Batch356.profile14266,MergedCutProfiles.Batch356.profile14267,MergedCutProfiles.Batch356.profile14268,MergedCutProfiles.Batch356.profile14247,MergedCutProfiles.Batch356.profile14269,MergedCutProfiles.Batch356.profile14270,MergedCutProfiles.Batch356.profile14271,MergedCutProfiles.Batch356.profile14272,MergedCutProfiles.Batch356.profile14273,MergedCutProfiles.Batch356.profile14274,MergedCutProfiles.Batch356.profile14275,MergedCutProfiles.Batch356.profile14276,MergedCutProfiles.Batch356.profile14277,MergedCutProfiles.Batch356.profile14278]⟩
theorem profilesValid2307 : retention2307.ProfilesValid := by
  change ∀ j : Fin 16, (retention2307.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch356.valid14264
  · exact MergedCutProfiles.Batch356.valid14265
  · exact MergedCutProfiles.Batch356.valid14266
  · exact MergedCutProfiles.Batch356.valid14267
  · exact MergedCutProfiles.Batch356.valid14268
  · exact MergedCutProfiles.Batch356.valid14247
  · exact MergedCutProfiles.Batch356.valid14269
  · exact MergedCutProfiles.Batch356.valid14270
  · exact MergedCutProfiles.Batch356.valid14271
  · exact MergedCutProfiles.Batch356.valid14272
  · exact MergedCutProfiles.Batch356.valid14273
  · exact MergedCutProfiles.Batch356.valid14274
  · exact MergedCutProfiles.Batch356.valid14275
  · exact MergedCutProfiles.Batch356.valid14276
  · exact MergedCutProfiles.Batch356.valid14277
  · exact MergedCutProfiles.Batch356.valid14278
theorem numericValid2307 : retention2307.NumericValid := by decide +kernel
def certificate2307 : RatCutBinCertificate := ⟨⟨retention2307,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(522292755769666153/250000000000000000)⟩,(249276745144070473/250000000000000000),(183730803265181877/500000000000000000),(264655665741903113/1000000000000000000),(166942219140066419/1000000000000000000)⟩
theorem valid2307 : certificate2307.Valid := by decide +kernel
theorem sound2307 : certificate2307.Sound := rat_cut_bin_certificate_sound certificate2307 profilesValid2307 numericValid2307 valid2307

def retention2308 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(12003481513818174287/56544910216936768259),(238102026200203877/125000000000000000),(7/4),(12270878383171173704107473357020717151/7619264838406524064000000000000000000),false,MergedCutProfiles.Batch356.profile14279,(fun _ => MergedCutProfiles.Batch356.profile14279)⟩
theorem profilesValid2308 : retention2308.ProfilesValid := by
  exact MergedCutProfiles.Batch356.valid14279
theorem numericValid2308 : retention2308.NumericValid := by decide +kernel
def certificate2308 : RatCutBinCertificate := ⟨⟨retention2308,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(99074566507944511/62500000000000000)⟩,(249276745144070473/250000000000000000),(198635623476610351/500000000000000000),(117995953730606231/500000000000000000),(33507756940998013/200000000000000000)⟩
theorem valid2308 : certificate2308.Valid := by decide +kernel
theorem sound2308 : certificate2308.Sound := rat_cut_bin_certificate_sound certificate2308 profilesValid2308 numericValid2308 valid2308

def retention2309 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(26608300130990700012/56544910216936768259),(12003481513818174287/1000000000000000000),(21/20),(20285987433990903945598209365475727240631/19205570422109078859200000000000000000000),false,MergedCutProfiles.Batch357.profile14280,(fun _ => MergedCutProfiles.Batch357.profile14280)⟩
theorem profilesValid2309 : retention2309.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14280
theorem numericValid2309 : retention2309.NumericValid := by decide +kernel
def certificate2309 : RatCutBinCertificate := ⟨⟨retention2309,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(1041067528498466237/1000000000000000000)⟩,(249276745144070473/250000000000000000),(28465370955923289/62500000000000000),(186355503608988223/1000000000000000000),(34155709829377901/200000000000000000)⟩
theorem valid2309 : certificate2309.Valid := by decide +kernel
theorem sound2309 : certificate2309.Sound := rat_cut_bin_certificate_sound certificate2309 profilesValid2309 numericValid2309 valid2309

def retention2310 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(27965590853748372186/56544910216936768259),(6652075032747675003/250000000000000000),1,(121280978467203074704076625388151573/120946818777230454600000000000000000),false,MergedCutProfiles.Batch357.profile14281,(fun _ => MergedCutProfiles.Batch357.profile14281)⟩
theorem profilesValid2310 : retention2310.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14281
theorem numericValid2310 : retention2310.NumericValid := by decide +kernel
def certificate2310 : RatCutBinCertificate := ⟨⟨retention2310,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(988298301655268097/1000000000000000000)⟩,(249276745144070473/250000000000000000),(92692755459253629/200000000000000000),(45029965925849449/250000000000000000),(85565160109988711/500000000000000000)⟩
theorem valid2310 : certificate2310.Valid := by decide +kernel
theorem sound2310 : certificate2310.Sound := rat_cut_bin_certificate_sound certificate2310 profilesValid2310 numericValid2310 valid2310

def retention2311 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(28245246762285855908/56544910216936768259),(13982795426874186093/500000000000000000),1,(37044926711028623220391391575218040821/37287454471664496248000000000000000000),false,MergedCutProfiles.Batch357.profile14282,(fun _ => MergedCutProfiles.Batch357.profile14282)⟩
theorem profilesValid2311 : retention2311.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14282
theorem numericValid2311 : retention2311.NumericValid := by decide +kernel
def certificate2311 : RatCutBinCertificate := ⟨⟨retention2311,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(979031167884201471/1000000000000000000)⟩,(249276745144070473/250000000000000000),(93438876448554953/200000000000000000),(35453184610285371/200000000000000000),(6687361838977323/40000000000000000)⟩
theorem valid2311 : certificate2311.Valid := by decide +kernel
theorem sound2311 : certificate2311.Sound := rat_cut_bin_certificate_sound certificate2311 profilesValid2311 numericValid2311 valid2311

def retention2312 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),(7061311690571463977/250000000000000000),1,(28037302465878928102374471748888079103/28245246762285855908000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid2312 : retention2312.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid2312 : retention2312.NumericValid := by decide +kernel
def certificate2312 : RatCutBinCertificate := ⟨⟨retention2312,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(978173342140582123/1000000000000000000)⟩,(249276745144070473/250000000000000000),(233738292403178701/500000000000000000),(7082050032729487/40000000000000000),(33379230959102591/200000000000000000)⟩
theorem valid2312 : certificate2312.Valid := by decide +kernel
theorem sound2312 : certificate2312.Sound := rat_cut_bin_certificate_sound certificate2312 profilesValid2312 numericValid2312 valid2312

def retention2313 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(24540170639740236614/56544910216936768259),(2785883101206189837/500000000000000000),(21/20),(2455913082603406252191204052005842123471/2228706480964951869600000000000000000000),false,MergedCutProfiles.Batch357.profile14284,(fun _ => MergedCutProfiles.Batch357.profile14284)⟩
theorem profilesValid2313 : retention2313.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14284
theorem numericValid2313 : retention2313.NumericValid := by decide +kernel
def certificate2313 : RatCutBinCertificate := ⟨⟨retention2313,(2357190291703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(1084514502680396239/1000000000000000000)⟩,(498339811742589401/500000000000000000),(111218629593017201/500000000000000000),(221522411252658347/500000000000000000),(387556575482485763/1000000000000000000)⟩
theorem valid2313 : certificate2313.Valid := by decide +kernel
theorem sound2313 : certificate2313.Sound := rat_cut_bin_certificate_sound certificate2313 profilesValid2313 numericValid2313 valid2313

def retention2314 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(27929003305774660493/56544910216936768259),(12270085319870118307/500000000000000000),1,(98476983817534542294383243483240784223/98160682558960946456000000000000000000),false,MergedCutProfiles.Batch357.profile14285,(fun _ => MergedCutProfiles.Batch357.profile14285)⟩
theorem profilesValid2314 : retention2314.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14285
theorem numericValid2314 : retention2314.NumericValid := by decide +kernel
def certificate2314 : RatCutBinCertificate := ⟨⟨retention2314,(2357190291703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(493310798126564651/500000000000000000)⟩,(498339811742589401/500000000000000000),(122253777152188179/500000000000000000),(205501854322935421/500000000000000000),(388512612229693679/1000000000000000000)⟩
theorem valid2314 : certificate2314.Valid := by decide +kernel
theorem sound2314 : certificate2314.Sound := rat_cut_bin_certificate_sound certificate2314 profilesValid2314 numericValid2314 valid2314

def retention2315 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(28208293338832407098/56544910216936768259),(27929003305774660493/1000000000000000000),1,(111131706190486743085357165556609546067/111716013223098641972000000000000000000),false,MergedCutProfiles.Batch357.profile14286,(fun _ => MergedCutProfiles.Batch357.profile14286)⟩
theorem profilesValid2315 : retention2315.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14286
theorem numericValid2315 : retention2315.NumericValid := by decide +kernel
def certificate2315 : RatCutBinCertificate := ⟨⟨retention2315,(2357190291703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(978169036888923379/1000000000000000000)⟩,(498339811742589401/500000000000000000),(49324078850622269/200000000000000000),(408041962766707033/1000000000000000000),(38432557526227271/100000000000000000)⟩
theorem valid2315 : certificate2315.Valid := by decide +kernel
theorem sound2315 : certificate2315.Sound := rat_cut_bin_certificate_sound certificate2315 profilesValid2315 numericValid2315 valid2315

def certificates : List RatCutBinCertificate := [certificate2304,certificate2305,certificate2306,certificate2307,certificate2308,certificate2309,certificate2310,certificate2311,certificate2312,certificate2313,certificate2314,certificate2315]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2304,List.forall_mem_cons.mpr ⟨sound2305,List.forall_mem_cons.mpr ⟨sound2306,List.forall_mem_cons.mpr ⟨sound2307,List.forall_mem_cons.mpr ⟨sound2308,List.forall_mem_cons.mpr ⟨sound2309,List.forall_mem_cons.mpr ⟨sound2310,List.forall_mem_cons.mpr ⟨sound2311,List.forall_mem_cons.mpr ⟨sound2312,List.forall_mem_cons.mpr ⟨sound2313,List.forall_mem_cons.mpr ⟨sound2314,List.forall_mem_cons.mpr ⟨sound2315,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch192
