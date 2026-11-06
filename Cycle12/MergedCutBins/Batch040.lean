import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch079
import Cycle12.MergedCutProfiles.Batch080
import Cycle12.MergedCutProfiles.Batch081

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch040

def retention480 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(882308903273280356/32399124674329550227),(395417198090482139/500000000000000000),(13/4),(275758381322871495191/128000000000000000000),true,MergedCutProfiles.Batch079.profile3176,![MergedCutProfiles.Batch079.profile3176,MergedCutProfiles.Batch079.profile3177,MergedCutProfiles.Batch079.profile3178,MergedCutProfiles.Batch079.profile3179,MergedCutProfiles.Batch079.profile3180,MergedCutProfiles.Batch079.profile3181,MergedCutProfiles.Batch079.profile3182,MergedCutProfiles.Batch079.profile3183,MergedCutProfiles.Batch079.profile3184,MergedCutProfiles.Batch079.profile3185,MergedCutProfiles.Batch079.profile3186,MergedCutProfiles.Batch079.profile3187,MergedCutProfiles.Batch079.profile3188,MergedCutProfiles.Batch079.profile3189,MergedCutProfiles.Batch079.profile3190,MergedCutProfiles.Batch079.profile3191]⟩
theorem profilesValid480 : retention480.ProfilesValid := by
  change ∀ j : Fin 16, (retention480.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch079.valid3176
  · exact MergedCutProfiles.Batch079.valid3177
  · exact MergedCutProfiles.Batch079.valid3178
  · exact MergedCutProfiles.Batch079.valid3179
  · exact MergedCutProfiles.Batch079.valid3180
  · exact MergedCutProfiles.Batch079.valid3181
  · exact MergedCutProfiles.Batch079.valid3182
  · exact MergedCutProfiles.Batch079.valid3183
  · exact MergedCutProfiles.Batch079.valid3184
  · exact MergedCutProfiles.Batch079.valid3185
  · exact MergedCutProfiles.Batch079.valid3186
  · exact MergedCutProfiles.Batch079.valid3187
  · exact MergedCutProfiles.Batch079.valid3188
  · exact MergedCutProfiles.Batch079.valid3189
  · exact MergedCutProfiles.Batch079.valid3190
  · exact MergedCutProfiles.Batch079.valid3191
theorem numericValid480 : retention480.NumericValid := by decide +kernel
def certificate480 : RatCutBinCertificate := ⟨⟨retention480,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(2111865761428168451/1000000000000000000)⟩,(994719567412799441/1000000000000000000),(202953159417601687/500000000000000000),(114057035819897923/500000000000000000),(117583657555879139/1000000000000000000)⟩
theorem valid480 : certificate480.Valid := by decide +kernel
theorem sound480 : certificate480.Sound := rat_cut_bin_certificate_sound certificate480 profilesValid480 numericValid480 valid480

def retention481 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(930146564000000000/32399124674329550227),(220577225818320089/250000000000000000),(59/20),(685118638675403082057/320000000000000000000),true,MergedCutProfiles.Batch079.profile3192,![MergedCutProfiles.Batch079.profile3192,MergedCutProfiles.Batch079.profile3193,MergedCutProfiles.Batch079.profile3194,MergedCutProfiles.Batch079.profile3195,MergedCutProfiles.Batch079.profile3196,MergedCutProfiles.Batch079.profile3197,MergedCutProfiles.Batch079.profile3198,MergedCutProfiles.Batch079.profile3199,MergedCutProfiles.Batch080.profile3200,MergedCutProfiles.Batch080.profile3201,MergedCutProfiles.Batch080.profile3202,MergedCutProfiles.Batch080.profile3203,MergedCutProfiles.Batch080.profile3204,MergedCutProfiles.Batch080.profile3205,MergedCutProfiles.Batch080.profile3206,MergedCutProfiles.Batch080.profile3207]⟩
theorem profilesValid481 : retention481.ProfilesValid := by
  change ∀ j : Fin 16, (retention481.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch079.valid3192
  · exact MergedCutProfiles.Batch079.valid3193
  · exact MergedCutProfiles.Batch079.valid3194
  · exact MergedCutProfiles.Batch079.valid3195
  · exact MergedCutProfiles.Batch079.valid3196
  · exact MergedCutProfiles.Batch079.valid3197
  · exact MergedCutProfiles.Batch079.valid3198
  · exact MergedCutProfiles.Batch079.valid3199
  · exact MergedCutProfiles.Batch080.valid3200
  · exact MergedCutProfiles.Batch080.valid3201
  · exact MergedCutProfiles.Batch080.valid3202
  · exact MergedCutProfiles.Batch080.valid3203
  · exact MergedCutProfiles.Batch080.valid3204
  · exact MergedCutProfiles.Batch080.valid3205
  · exact MergedCutProfiles.Batch080.valid3206
  · exact MergedCutProfiles.Batch080.valid3207
theorem numericValid481 : retention481.NumericValid := by decide +kernel
def certificate481 : RatCutBinCertificate := ⟨⟨retention481,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(32850343005320193/15625000000000000)⟩,(994719567412799441/1000000000000000000),(388202785749335393/1000000000000000000),(122233586601381593/500000000000000000),(135933075819364921/1000000000000000000)⟩
theorem valid481 : certificate481.Valid := by decide +kernel
theorem sound481 : certificate481.Sound := rat_cut_bin_certificate_sound certificate481 profilesValid481 numericValid481 valid481

def retention482 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1014191332422603351/32399124674329550227),(232536641/250000000),(14/5),(16994237912541417121/8000000000000000000),true,MergedCutProfiles.Batch080.profile3208,![MergedCutProfiles.Batch080.profile3208,MergedCutProfiles.Batch080.profile3209,MergedCutProfiles.Batch080.profile3210,MergedCutProfiles.Batch080.profile3211,MergedCutProfiles.Batch080.profile3212,MergedCutProfiles.Batch080.profile3213,MergedCutProfiles.Batch079.profile3168,MergedCutProfiles.Batch080.profile3214,MergedCutProfiles.Batch080.profile3215,MergedCutProfiles.Batch080.profile3216,MergedCutProfiles.Batch080.profile3203,MergedCutProfiles.Batch080.profile3217,MergedCutProfiles.Batch080.profile3218,MergedCutProfiles.Batch080.profile3219,MergedCutProfiles.Batch080.profile3220,MergedCutProfiles.Batch080.profile3221]⟩
theorem profilesValid482 : retention482.ProfilesValid := by
  change ∀ j : Fin 16, (retention482.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch080.valid3208
  · exact MergedCutProfiles.Batch080.valid3209
  · exact MergedCutProfiles.Batch080.valid3210
  · exact MergedCutProfiles.Batch080.valid3211
  · exact MergedCutProfiles.Batch080.valid3212
  · exact MergedCutProfiles.Batch080.valid3213
  · exact MergedCutProfiles.Batch079.valid3168
  · exact MergedCutProfiles.Batch080.valid3214
  · exact MergedCutProfiles.Batch080.valid3215
  · exact MergedCutProfiles.Batch080.valid3216
  · exact MergedCutProfiles.Batch080.valid3203
  · exact MergedCutProfiles.Batch080.valid3217
  · exact MergedCutProfiles.Batch080.valid3218
  · exact MergedCutProfiles.Batch080.valid3219
  · exact MergedCutProfiles.Batch080.valid3220
  · exact MergedCutProfiles.Batch080.valid3221
theorem numericValid482 : retention482.NumericValid := by decide +kernel
def certificate482 : RatCutBinCertificate := ⟨⟨retention482,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(2087667326567075451/1000000000000000000)⟩,(994719567412799441/1000000000000000000),(382202741837949447/1000000000000000000),(250190814934777787/1000000000000000000),(14413024235072441/100000000000000000)⟩
theorem valid482 : certificate482.Valid := by decide +kernel
theorem sound482 : certificate482.Sound := rat_cut_bin_certificate_sound certificate482 profilesValid482 numericValid482 valid482

def retention483 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1936462942724610086/32399124674329550227),(1014191332422603351/1000000000000000000),(13/5),(646847727260834019779/320000000000000000000),true,MergedCutProfiles.Batch080.profile3222,![MergedCutProfiles.Batch080.profile3222,MergedCutProfiles.Batch080.profile3223,MergedCutProfiles.Batch080.profile3224,MergedCutProfiles.Batch080.profile3225,MergedCutProfiles.Batch080.profile3226,MergedCutProfiles.Batch080.profile3227,MergedCutProfiles.Batch080.profile3228,MergedCutProfiles.Batch080.profile3229,MergedCutProfiles.Batch080.profile3230,MergedCutProfiles.Batch080.profile3231,MergedCutProfiles.Batch080.profile3232,MergedCutProfiles.Batch080.profile3233,MergedCutProfiles.Batch080.profile3234,MergedCutProfiles.Batch080.profile3235,MergedCutProfiles.Batch080.profile3236,MergedCutProfiles.Batch080.profile3237]⟩
theorem profilesValid483 : retention483.ProfilesValid := by
  change ∀ j : Fin 16, (retention483.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch080.valid3222
  · exact MergedCutProfiles.Batch080.valid3223
  · exact MergedCutProfiles.Batch080.valid3224
  · exact MergedCutProfiles.Batch080.valid3225
  · exact MergedCutProfiles.Batch080.valid3226
  · exact MergedCutProfiles.Batch080.valid3227
  · exact MergedCutProfiles.Batch080.valid3228
  · exact MergedCutProfiles.Batch080.valid3229
  · exact MergedCutProfiles.Batch080.valid3230
  · exact MergedCutProfiles.Batch080.valid3231
  · exact MergedCutProfiles.Batch080.valid3232
  · exact MergedCutProfiles.Batch080.valid3233
  · exact MergedCutProfiles.Batch080.valid3234
  · exact MergedCutProfiles.Batch080.valid3235
  · exact MergedCutProfiles.Batch080.valid3236
  · exact MergedCutProfiles.Batch080.valid3237
theorem numericValid483 : retention483.NumericValid := by decide +kernel
def certificate483 : RatCutBinCertificate := ⟨⟨retention483,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(993700969471429883/500000000000000000)⟩,(994719567412799441/1000000000000000000),(387446866622876543/1000000000000000000),(30647892181143091/125000000000000000),(72201444708172387/500000000000000000)⟩
theorem valid483 : certificate483.Valid := by decide +kernel
theorem sound483 : certificate483.Sound := rat_cut_bin_certificate_sound certificate483 profilesValid483 numericValid483 valid483

def retention484 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(8614206091729885461/32399124674329550227),(968231471362305043/500000000000000000),(33/20),(1149586560176731423604804490590488768559/774585177089844034400000000000000000000),false,MergedCutProfiles.Batch080.profile3238,(fun _ => MergedCutProfiles.Batch080.profile3238)⟩
theorem profilesValid484 : retention484.ProfilesValid := by
  exact MergedCutProfiles.Batch080.valid3238
theorem numericValid484 : retention484.NumericValid := by decide +kernel
def certificate484 : RatCutBinCertificate := ⟨⟨retention484,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(146255701425731163/100000000000000000)⟩,(994719567412799441/1000000000000000000),(425935651297309147/1000000000000000000),(42108344752777609/200000000000000000),(4538049554546393/31250000000000000)⟩
theorem valid484 : certificate484.Valid := by decide +kernel
theorem sound484 : certificate484.Sound := rat_cut_bin_certificate_sound certificate484 profilesValid484 numericValid484 valid484

def retention485 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(15341044767764295526/32399124674329550227),(8614206091729885461/1000000000000000000),(21/20),(14381525379655353812139528129980891920079/13782729746767816737600000000000000000000),false,MergedCutProfiles.Batch080.profile3239,(fun _ => MergedCutProfiles.Batch080.profile3239)⟩
theorem profilesValid485 : retention485.ProfilesValid := by
  exact MergedCutProfiles.Batch080.valid3239
theorem numericValid485 : retention485.NumericValid := by decide +kernel
def certificate485 : RatCutBinCertificate := ⟨⟨retention485,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(1029716437304302379/1000000000000000000)⟩,(994719567412799441/1000000000000000000),(19329365064713071/40000000000000000),(165331826422821243/1000000000000000000),(145462602660615147/1000000000000000000)⟩
theorem valid485 : certificate485.Valid := by decide +kernel
theorem sound485 : certificate485.Sound := rat_cut_bin_certificate_sound certificate485 profilesValid485 numericValid485 valid485

def retention486 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(16123592229954295108/32399124674329550227),(7670522383882147763/500000000000000000),(21/20),(6168786162359060775305549053216947457311/6136417907105718210400000000000000000000),false,MergedCutProfiles.Batch081.profile3240,(fun _ => MergedCutProfiles.Batch081.profile3240)⟩
theorem profilesValid486 : retention486.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3240
theorem numericValid486 : retention486.NumericValid := by decide +kernel
def certificate486 : RatCutBinCertificate := ⟨⟨retention486,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(30985812161607801/31250000000000000)⟩,(994719567412799441/1000000000000000000),(485760384777487701/1000000000000000000),(163501194627914609/1000000000000000000),(145053340580837923/1000000000000000000)⟩
theorem valid486 : certificate486.Valid := by decide +kernel
theorem sound486 : certificate486.Sound := rat_cut_bin_certificate_sound certificate486 profilesValid486 numericValid486 valid486

def retention487 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1/2),(4030898057488573777/250000000000000000),(21/20),(100864893494149312904422489175112301061/100772451437214344425000000000000000000),false,MergedCutProfiles.Batch081.profile3241,(fun _ => MergedCutProfiles.Batch081.profile3241)⟩
theorem profilesValid487 : retention487.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3241
theorem numericValid487 : retention487.NumericValid := by decide +kernel
def certificate487 : RatCutBinCertificate := ⟨⟨retention487,(205916410838747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(987188551730279891/1000000000000000000)⟩,(994719567412799441/1000000000000000000),(243450473327950327/500000000000000000),(81339502381851617/500000000000000000),(5764460763194033/40000000000000000)⟩
theorem valid487 : certificate487.Valid := by decide +kernel
theorem sound487 : certificate487.Sound := rat_cut_bin_certificate_sound certificate487 profilesValid487 numericValid487 valid487

def retention488 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(14091627596575968417/32399124674329550227),(3789132726792578843/1000000000000000000),(6/5),(425748479257478304611084210829763170351/378913272679257884300000000000000000000),false,MergedCutProfiles.Batch081.profile3242,(fun _ => MergedCutProfiles.Batch081.profile3242)⟩
theorem profilesValid488 : retention488.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3242
theorem numericValid488 : retention488.NumericValid := by decide +kernel
def certificate488 : RatCutBinCertificate := ⟨⟨retention488,(245318025938747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(27622778772228351/25000000000000000)⟩,(993708697806734589/1000000000000000000),(359739283026064153/1000000000000000000),(272467604399142839/1000000000000000000),(103602310860350089/500000000000000000)⟩
theorem valid488 : certificate488.Valid := by decide +kernel
theorem sound488 : certificate488.Sound := rat_cut_bin_certificate_sound certificate488 profilesValid488 numericValid488 valid488

def retention489 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(16037586678031413790/32399124674329550227),(14091627596575968417/1000000000000000000),1,(13998282563803320966024373620781001693/14091627596575968417000000000000000000),false,MergedCutProfiles.Batch081.profile3243,(fun _ => MergedCutProfiles.Batch081.profile3243)⟩
theorem profilesValid489 : retention489.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3243
theorem numericValid489 : retention489.NumericValid := by decide +kernel
def certificate489 : RatCutBinCertificate := ⟨⟨retention489,(245318025938747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(488899453961814877/500000000000000000)⟩,(993708697806734589/1000000000000000000),(406504795625528901/1000000000000000000),(113787463313574769/500000000000000000),(206734045385752021/1000000000000000000)⟩
theorem valid489 : certificate489.Valid := by decide +kernel
theorem sound489 : certificate489.Sound := rat_cut_bin_certificate_sound certificate489 profilesValid489 numericValid489 valid489

def retention490 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(16197962544811727928/32399124674329550227),(1603758667803141379/100000000000000000),1,(158125676553667285489197706849220217/160375866780314137900000000000000000),false,MergedCutProfiles.Batch081.profile3244,(fun _ => MergedCutProfiles.Batch081.profile3244)⟩
theorem profilesValid490 : retention490.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3244
theorem numericValid490 : retention490.NumericValid := by decide +kernel
def certificate490 : RatCutBinCertificate := ⟨⟨retention490,(245318025938747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(970392354178801071/1000000000000000000)⟩,(993708697806734589/1000000000000000000),(409607457763545211/1000000000000000000),(44958789254028161/200000000000000000),(204362701690417439/1000000000000000000)⟩
theorem valid490 : certificate490.Valid := by decide +kernel
theorem sound490 : certificate490.Sound := rat_cut_bin_certificate_sound certificate490 profilesValid490 numericValid490 valid490

def retention491 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1/2),(2024745318101465991/125000000000000000),1,(7098510600109472655930402865692926783/7199094464360767968000000000000000000),false,MergedCutProfiles.Batch081.profile3241,(fun _ => MergedCutProfiles.Batch081.profile3241)⟩
theorem profilesValid491 : retention491.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3241
theorem numericValid491 : retention491.NumericValid := by decide +kernel
def certificate491 : RatCutBinCertificate := ⟨⟨retention491,(245318025938747817/100000000000000000),(70986334890534179/1000000000000000000),(11179644401673740689/1000000000000000000),(14527252830750459517/40000000000000000),(970451346090226971/1000000000000000000)⟩,(993708697806734589/1000000000000000000),(51197819812107957/125000000000000000),(44963234049918081/200000000000000000),(20451048974577469/100000000000000000)⟩
theorem valid491 : certificate491.Valid := by decide +kernel
theorem sound491 : certificate491.Sound := rat_cut_bin_certificate_sound certificate491 profilesValid491 numericValid491 valid491

def certificates : List RatCutBinCertificate := [certificate480,certificate481,certificate482,certificate483,certificate484,certificate485,certificate486,certificate487,certificate488,certificate489,certificate490,certificate491]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound480,List.forall_mem_cons.mpr ⟨sound481,List.forall_mem_cons.mpr ⟨sound482,List.forall_mem_cons.mpr ⟨sound483,List.forall_mem_cons.mpr ⟨sound484,List.forall_mem_cons.mpr ⟨sound485,List.forall_mem_cons.mpr ⟨sound486,List.forall_mem_cons.mpr ⟨sound487,List.forall_mem_cons.mpr ⟨sound488,List.forall_mem_cons.mpr ⟨sound489,List.forall_mem_cons.mpr ⟨sound490,List.forall_mem_cons.mpr ⟨sound491,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch040
