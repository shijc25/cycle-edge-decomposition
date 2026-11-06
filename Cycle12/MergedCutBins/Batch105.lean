import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch206
import Cycle12.MergedCutProfiles.Batch207
import Cycle12.MergedCutProfiles.Batch208

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch105

def retention1260 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(1/2),(3438344137504933821/500000000000000000),(21/20),(2711789498314458122358240309430045272839/2750675310003947056800000000000000000000),false,MergedCutProfiles.Batch206.profile8278,(fun _ => MergedCutProfiles.Batch206.profile8278)⟩
theorem profilesValid1260 : retention1260.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8278
theorem numericValid1260 : retention1260.NumericValid := by decide +kernel
def certificate1260 : RatCutBinCertificate := ⟨⟨retention1260,(2615808633829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(191177890635049211/200000000000000000)⟩,(989516136685312413/1000000000000000000),(413468475539045723/1000000000000000000),(110683012237607023/500000000000000000),(22120360545597777/125000000000000000)⟩
theorem valid1260 : certificate1260.Valid := by decide +kernel
theorem sound1260 : certificate1260.Sound := rat_cut_bin_certificate_sound certificate1260 profilesValid1260 numericValid1260 valid1260

def retention1261 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(1258917851800415826/13664313896637635951),(109986137019307837/125000000000000000),(27/10),(38528929095054479723/20000000000000000000),true,MergedCutProfiles.Batch207.profile8282,![MergedCutProfiles.Batch207.profile8282,MergedCutProfiles.Batch207.profile8283,MergedCutProfiles.Batch207.profile8284,MergedCutProfiles.Batch207.profile8285,MergedCutProfiles.Batch207.profile8286,MergedCutProfiles.Batch207.profile8287,MergedCutProfiles.Batch207.profile8288,MergedCutProfiles.Batch207.profile8289,MergedCutProfiles.Batch207.profile8290,MergedCutProfiles.Batch207.profile8291,MergedCutProfiles.Batch207.profile8292,MergedCutProfiles.Batch207.profile8293,MergedCutProfiles.Batch207.profile8294,MergedCutProfiles.Batch207.profile8295,MergedCutProfiles.Batch207.profile8296,MergedCutProfiles.Batch207.profile8297]⟩
theorem profilesValid1261 : retention1261.ProfilesValid := by
  change ∀ j : Fin 16, (retention1261.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch207.valid8282
  · exact MergedCutProfiles.Batch207.valid8283
  · exact MergedCutProfiles.Batch207.valid8284
  · exact MergedCutProfiles.Batch207.valid8285
  · exact MergedCutProfiles.Batch207.valid8286
  · exact MergedCutProfiles.Batch207.valid8287
  · exact MergedCutProfiles.Batch207.valid8288
  · exact MergedCutProfiles.Batch207.valid8289
  · exact MergedCutProfiles.Batch207.valid8290
  · exact MergedCutProfiles.Batch207.valid8291
  · exact MergedCutProfiles.Batch207.valid8292
  · exact MergedCutProfiles.Batch207.valid8293
  · exact MergedCutProfiles.Batch207.valid8294
  · exact MergedCutProfiles.Batch207.valid8295
  · exact MergedCutProfiles.Batch207.valid8296
  · exact MergedCutProfiles.Batch207.valid8297
theorem numericValid1261 : retention1261.NumericValid := by decide +kernel
def certificate1261 : RatCutBinCertificate := ⟨⟨retention1261,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(929401784696376787/500000000000000000)⟩,(990819244341038607/1000000000000000000),(22374631959532773/62500000000000000),(137127919863497563/500000000000000000),(18097126731795981/125000000000000000)⟩
theorem valid1261 : certificate1261.Valid := by decide +kernel
theorem sound1261 : certificate1261.Sound := rat_cut_bin_certificate_sound certificate1261 profilesValid1261 numericValid1261 valid1261

def retention1262 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(3052106323382941264/13664313896637635951),(629458925900207913/500000000000000000),(39/20),(1007926186144808781153/640000000000000000000),true,MergedCutProfiles.Batch207.profile8298,![MergedCutProfiles.Batch207.profile8298,MergedCutProfiles.Batch207.profile8299,MergedCutProfiles.Batch207.profile8300,MergedCutProfiles.Batch207.profile8301,MergedCutProfiles.Batch207.profile8302,MergedCutProfiles.Batch207.profile8303,MergedCutProfiles.Batch207.profile8304,MergedCutProfiles.Batch207.profile8305,MergedCutProfiles.Batch207.profile8306,MergedCutProfiles.Batch207.profile8307,MergedCutProfiles.Batch207.profile8308,MergedCutProfiles.Batch207.profile8309,MergedCutProfiles.Batch207.profile8310,MergedCutProfiles.Batch207.profile8311,MergedCutProfiles.Batch207.profile8312,MergedCutProfiles.Batch207.profile8313]⟩
theorem profilesValid1262 : retention1262.ProfilesValid := by
  change ∀ j : Fin 16, (retention1262.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch207.valid8298
  · exact MergedCutProfiles.Batch207.valid8299
  · exact MergedCutProfiles.Batch207.valid8300
  · exact MergedCutProfiles.Batch207.valid8301
  · exact MergedCutProfiles.Batch207.valid8302
  · exact MergedCutProfiles.Batch207.valid8303
  · exact MergedCutProfiles.Batch207.valid8304
  · exact MergedCutProfiles.Batch207.valid8305
  · exact MergedCutProfiles.Batch207.valid8306
  · exact MergedCutProfiles.Batch207.valid8307
  · exact MergedCutProfiles.Batch207.valid8308
  · exact MergedCutProfiles.Batch207.valid8309
  · exact MergedCutProfiles.Batch207.valid8310
  · exact MergedCutProfiles.Batch207.valid8311
  · exact MergedCutProfiles.Batch207.valid8312
  · exact MergedCutProfiles.Batch207.valid8313
theorem numericValid1262 : retention1262.NumericValid := by decide +kernel
def certificate1262 : RatCutBinCertificate := ⟨⟨retention1262,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(1526032003813611577/1000000000000000000)⟩,(990819244341038607/1000000000000000000),(385815687275424329/1000000000000000000),(246733124615254783/1000000000000000000),(144816293299425381/1000000000000000000)⟩
theorem valid1262 : certificate1262.Valid := by decide +kernel
theorem sound1262 : certificate1262.Sound := rat_cut_bin_certificate_sound certificate1262 profilesValid1262 numericValid1262 valid1262

def retention1263 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(5769890625952882073/13664313896637635951),(190756645211433829/62500000000000000),(23/20),(45084543024165314059/40000000000000000000),true,MergedCutProfiles.Batch207.profile8314,![MergedCutProfiles.Batch207.profile8314,MergedCutProfiles.Batch207.profile8315,MergedCutProfiles.Batch207.profile8316,MergedCutProfiles.Batch207.profile8317,MergedCutProfiles.Batch207.profile8318,MergedCutProfiles.Batch207.profile8319,MergedCutProfiles.Batch208.profile8320,MergedCutProfiles.Batch208.profile8321,MergedCutProfiles.Batch208.profile8322,MergedCutProfiles.Batch208.profile8323,MergedCutProfiles.Batch208.profile8324,MergedCutProfiles.Batch208.profile8325,MergedCutProfiles.Batch208.profile8326,MergedCutProfiles.Batch208.profile8327,MergedCutProfiles.Batch208.profile8328,MergedCutProfiles.Batch208.profile8329]⟩
theorem profilesValid1263 : retention1263.ProfilesValid := by
  change ∀ j : Fin 16, (retention1263.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch207.valid8314
  · exact MergedCutProfiles.Batch207.valid8315
  · exact MergedCutProfiles.Batch207.valid8316
  · exact MergedCutProfiles.Batch207.valid8317
  · exact MergedCutProfiles.Batch207.valid8318
  · exact MergedCutProfiles.Batch207.valid8319
  · exact MergedCutProfiles.Batch208.valid8320
  · exact MergedCutProfiles.Batch208.valid8321
  · exact MergedCutProfiles.Batch208.valid8322
  · exact MergedCutProfiles.Batch208.valid8323
  · exact MergedCutProfiles.Batch208.valid8324
  · exact MergedCutProfiles.Batch208.valid8325
  · exact MergedCutProfiles.Batch208.valid8326
  · exact MergedCutProfiles.Batch208.valid8327
  · exact MergedCutProfiles.Batch208.valid8328
  · exact MergedCutProfiles.Batch208.valid8329
theorem numericValid1263 : retention1263.NumericValid := by decide +kernel
def certificate1263 : RatCutBinCertificate := ⟨⟨retention1263,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(137288233197660511/125000000000000000)⟩,(990819244341038607/1000000000000000000),(440853527521879221/1000000000000000000),(4951706989342269/25000000000000000),(147150830468263387/1000000000000000000)⟩
theorem valid1263 : certificate1263.Valid := by decide +kernel
theorem sound1263 : certificate1263.Sound := rat_cut_bin_certificate_sound certificate1263 profilesValid1263 numericValid1263 valid1263

def retention1264 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(6632340487734321253/13664313896637635951),(5769890625952882073/1000000000000000000),(11/10),(102555200911714482193512710095530693977/100345923929615340400000000000000000000),false,MergedCutProfiles.Batch208.profile8330,(fun _ => MergedCutProfiles.Batch208.profile8330)⟩
theorem profilesValid1264 : retention1264.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8330
theorem numericValid1264 : retention1264.NumericValid := by decide +kernel
def certificate1264 : RatCutBinCertificate := ⟨⟨retention1264,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(994464227843402123/1000000000000000000)⟩,(990819244341038607/1000000000000000000),(9042261102565951/20000000000000000),(47247234745702631/250000000000000000),(74032772000495027/500000000000000000)⟩
theorem valid1264 : certificate1264.Valid := by decide +kernel
theorem sound1264 : certificate1264.Sound := rat_cut_bin_certificate_sound certificate1264 profilesValid1264 numericValid1264 valid1264

def retention1265 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(6765650531537781111/13664313896637635951),(6632340487734321253/1000000000000000000),(21/20),(10547361932688925579480262338331640850871/10611744780374914004800000000000000000000),false,MergedCutProfiles.Batch208.profile8331,(fun _ => MergedCutProfiles.Batch208.profile8331)⟩
theorem profilesValid1265 : retention1265.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8331
theorem numericValid1265 : retention1265.NumericValid := by decide +kernel
def certificate1265 : RatCutBinCertificate := ⟨⟨retention1265,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(967633163587931881/1000000000000000000)⟩,(990819244341038607/1000000000000000000),(91886097199447853/200000000000000000),(45809787270225169/250000000000000000),(29531006077053993/200000000000000000)⟩
theorem valid1265 : certificate1265.Valid := by decide +kernel
theorem sound1265 : certificate1265.Sound := rat_cut_bin_certificate_sound certificate1265 profilesValid1265 numericValid1265 valid1265

def retention1266 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(1/2),(6765650531537781111/1000000000000000000),(21/20),(3555429319682813397168159103813159268253/3608346950153483259200000000000000000000),false,MergedCutProfiles.Batch208.profile8332,(fun _ => MergedCutProfiles.Batch208.profile8332)⟩
theorem profilesValid1266 : retention1266.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8332
theorem numericValid1266 : retention1266.NumericValid := by decide +kernel
def certificate1266 : RatCutBinCertificate := ⟨⟨retention1266,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(191807003157745011/200000000000000000)⟩,(990819244341038607/1000000000000000000),(462855324610754923/1000000000000000000),(90294088089996917/500000000000000000),(18088507204422353/125000000000000000)⟩
theorem valid1266 : certificate1266.Valid := by decide +kernel
theorem sound1266 : certificate1266.Sound := rat_cut_bin_certificate_sound certificate1266 profilesValid1266 numericValid1266 valid1266

def retention1267 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(1/2),64,1,(255404499356944497610344792832121040711/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch208.profile8332,(fun _ => MergedCutProfiles.Batch208.profile8332)⟩
theorem profilesValid1267 : retention1267.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8332
theorem numericValid1267 : retention1267.NumericValid := by decide +kernel
def certificate1267 : RatCutBinCertificate := ⟨⟨retention1267,(2277070887503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(972629063137531353/1000000000000000000)⟩,(990819244341038607/1000000000000000000),(212966970066513353/500000000000000000),(42108636831412291/200000000000000000),(1561293458932599/7812500000000000)⟩
theorem valid1267 : certificate1267.Valid := by decide +kernel
theorem sound1267 : certificate1267.Sound := rat_cut_bin_certificate_sound certificate1267 profilesValid1267 numericValid1267 valid1267

def retention1268 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(6328742703370858659/13664313896637635951),(3553675435647221703/1000000000000000000),(6/5),(378969598124640300660382517485866865871/355367543564722170300000000000000000000),false,MergedCutProfiles.Batch208.profile8333,(fun _ => MergedCutProfiles.Batch208.profile8333)⟩
theorem profilesValid1268 : retention1268.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8333
theorem numericValid1268 : retention1268.NumericValid := by decide +kernel
def certificate1268 : RatCutBinCertificate := ⟨⟨retention1268,(2617679062503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(1031860619379701089/1000000000000000000)⟩,(989443106206527503/1000000000000000000),(196470509300339841/500000000000000000),(7500399368589301/31250000000000000),(1326170166640527/7812500000000000)⟩
theorem valid1268 : certificate1268.Valid := by decide +kernel
theorem sound1268 : certificate1268.Sound := rat_cut_bin_certificate_sound certificate1268 profilesValid1268 numericValid1268 valid1268

def retention1269 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(6785268786673185896/13664313896637635951),(6328742703370858659/1000000000000000000),(21/20),(10020187349162658985323062063972836987919/10125988325393373854400000000000000000000),false,MergedCutProfiles.Batch208.profile8334,(fun _ => MergedCutProfiles.Batch208.profile8334)⟩
theorem profilesValid1269 : retention1269.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8334
theorem numericValid1269 : retention1269.NumericValid := by decide +kernel
def certificate1269 : RatCutBinCertificate := ⟨⟨retention1269,(2617679062503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(191863542617758563/200000000000000000)⟩,(989443106206527503/1000000000000000000),(211327466021394761/500000000000000000),(213354311137335669/1000000000000000000),(42357709499810271/250000000000000000)⟩
theorem valid1269 : certificate1269.Valid := by decide +kernel
theorem sound1269 : certificate1269.Sound := rat_cut_bin_certificate_sound certificate1269 profilesValid1269 numericValid1269 valid1269

def retention1270 : RatCutRetentionCertificate := ⟨(23/400),(231/4000),(1/2),(848158598334148237/125000000000000000),(21/20),(668640455621754876556592768490087698879/678526878667318589600000000000000000000),false,MergedCutProfiles.Batch208.profile8332,(fun _ => MergedCutProfiles.Batch208.profile8332)⟩
theorem profilesValid1270 : retention1270.ProfilesValid := by
  exact MergedCutProfiles.Batch208.valid8332
theorem numericValid1270 : retention1270.NumericValid := by decide +kernel
def certificate1270 : RatCutBinCertificate := ⟨⟨retention1270,(2617679062503412177/1000000000000000000),(166748257424990971/1000000000000000000),(3032189832589086713/200000000000000000),(41495202117139022471/200000000000000000),(238798999048271517/250000000000000000)⟩,(989443106206527503/1000000000000000000),(829059977548419/1953125000000000),(10589382134982187/50000000000000000),(21115890691472363/125000000000000000)⟩
theorem valid1270 : certificate1270.Valid := by decide +kernel
theorem sound1270 : certificate1270.Sound := rat_cut_bin_certificate_sound certificate1270 profilesValid1270 numericValid1270 valid1270

def retention1271 : RatCutRetentionCertificate := ⟨(231/4000),(29/500),(920607525381927631/13526363696142142574),(850165604181169593/1000000000000000000),(11/4),(7958334480455786691/4000000000000000000),true,MergedCutProfiles.Batch208.profile8335,![MergedCutProfiles.Batch208.profile8335,MergedCutProfiles.Batch208.profile8336,MergedCutProfiles.Batch208.profile8337,MergedCutProfiles.Batch208.profile8338,MergedCutProfiles.Batch208.profile8339,MergedCutProfiles.Batch208.profile8340,MergedCutProfiles.Batch208.profile8341,MergedCutProfiles.Batch208.profile8342,MergedCutProfiles.Batch208.profile8343,MergedCutProfiles.Batch208.profile8344,MergedCutProfiles.Batch208.profile8345,MergedCutProfiles.Batch208.profile8346,MergedCutProfiles.Batch208.profile8347,MergedCutProfiles.Batch208.profile8348,MergedCutProfiles.Batch208.profile8349,MergedCutProfiles.Batch208.profile8350]⟩
theorem profilesValid1271 : retention1271.ProfilesValid := by
  change ∀ j : Fin 16, (retention1271.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch208.valid8335
  · exact MergedCutProfiles.Batch208.valid8336
  · exact MergedCutProfiles.Batch208.valid8337
  · exact MergedCutProfiles.Batch208.valid8338
  · exact MergedCutProfiles.Batch208.valid8339
  · exact MergedCutProfiles.Batch208.valid8340
  · exact MergedCutProfiles.Batch208.valid8341
  · exact MergedCutProfiles.Batch208.valid8342
  · exact MergedCutProfiles.Batch208.valid8343
  · exact MergedCutProfiles.Batch208.valid8344
  · exact MergedCutProfiles.Batch208.valid8345
  · exact MergedCutProfiles.Batch208.valid8346
  · exact MergedCutProfiles.Batch208.valid8347
  · exact MergedCutProfiles.Batch208.valid8348
  · exact MergedCutProfiles.Batch208.valid8349
  · exact MergedCutProfiles.Batch208.valid8350
theorem numericValid1271 : retention1271.NumericValid := by decide +kernel
def certificate1271 : RatCutBinCertificate := ⟨⟨retention1271,(1142711195124929509/500000000000000000),(168442616661570077/1000000000000000000),(3807216807094491581/250000000000000000),(51575497878328939587/250000000000000000),(96002176948400743/50000000000000000)⟩,(495375731098478063/500000000000000000),(357284251757863051/1000000000000000000),(137492822141467887/500000000000000000),(14620082899083859/100000000000000000)⟩
theorem valid1271 : certificate1271.Valid := by decide +kernel
theorem sound1271 : certificate1271.Sound := rat_cut_bin_certificate_sound certificate1271 profilesValid1271 numericValid1271 valid1271

def certificates : List RatCutBinCertificate := [certificate1260,certificate1261,certificate1262,certificate1263,certificate1264,certificate1265,certificate1266,certificate1267,certificate1268,certificate1269,certificate1270,certificate1271]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1260,List.forall_mem_cons.mpr ⟨sound1261,List.forall_mem_cons.mpr ⟨sound1262,List.forall_mem_cons.mpr ⟨sound1263,List.forall_mem_cons.mpr ⟨sound1264,List.forall_mem_cons.mpr ⟨sound1265,List.forall_mem_cons.mpr ⟨sound1266,List.forall_mem_cons.mpr ⟨sound1267,List.forall_mem_cons.mpr ⟨sound1268,List.forall_mem_cons.mpr ⟨sound1269,List.forall_mem_cons.mpr ⟨sound1270,List.forall_mem_cons.mpr ⟨sound1271,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch105
