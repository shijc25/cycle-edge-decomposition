import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch205
import Cycle12.MergedCutProfiles.Batch206
import Cycle12.MergedCutProfiles.Batch207

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch104

def retention1248 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(1/2),(6871236350328339463/1000000000000000000),(21/20),(10838270139045599111385185803594571598311/10993978160525343140800000000000000000000),false,MergedCutProfiles.Batch205.profile8210,(fun _ => MergedCutProfiles.Batch205.profile8210)⟩
theorem profilesValid1248 : retention1248.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8210
theorem numericValid1248 : retention1248.NumericValid := by decide +kernel
def certificate1248 : RatCutBinCertificate := ⟨⟨retention1248,(522847955412878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(191193328150965221/200000000000000000)⟩,(197908454686327313/200000000000000000),(414137842179789703/1000000000000000000),(220775417015408879/1000000000000000000),(88246368936925073/500000000000000000)⟩
theorem valid1248 : certificate1248.Valid := by decide +kernel
theorem sound1248 : certificate1248.Sound := rat_cut_bin_certificate_sound certificate1248 profilesValid1248 numericValid1248 valid1248

def retention1249 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(911492599520710678/13804153658233638553),(850165604304907253/1000000000000000000),(14/5),(2563785581166122053121/1280000000000000000000),true,MergedCutProfiles.Batch205.profile8213,![MergedCutProfiles.Batch205.profile8213,MergedCutProfiles.Batch205.profile8214,MergedCutProfiles.Batch205.profile8215,MergedCutProfiles.Batch205.profile8216,MergedCutProfiles.Batch205.profile8217,MergedCutProfiles.Batch205.profile8218,MergedCutProfiles.Batch205.profile8219,MergedCutProfiles.Batch205.profile8220,MergedCutProfiles.Batch205.profile8221,MergedCutProfiles.Batch205.profile8222,MergedCutProfiles.Batch205.profile8223,MergedCutProfiles.Batch205.profile8224,MergedCutProfiles.Batch205.profile8225,MergedCutProfiles.Batch205.profile8226,MergedCutProfiles.Batch205.profile8227,MergedCutProfiles.Batch205.profile8228]⟩
theorem profilesValid1249 : retention1249.ProfilesValid := by
  change ∀ j : Fin 16, (retention1249.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch205.valid8213
  · exact MergedCutProfiles.Batch205.valid8214
  · exact MergedCutProfiles.Batch205.valid8215
  · exact MergedCutProfiles.Batch205.valid8216
  · exact MergedCutProfiles.Batch205.valid8217
  · exact MergedCutProfiles.Batch205.valid8218
  · exact MergedCutProfiles.Batch205.valid8219
  · exact MergedCutProfiles.Batch205.valid8220
  · exact MergedCutProfiles.Batch205.valid8221
  · exact MergedCutProfiles.Batch205.valid8222
  · exact MergedCutProfiles.Batch205.valid8223
  · exact MergedCutProfiles.Batch205.valid8224
  · exact MergedCutProfiles.Batch205.valid8225
  · exact MergedCutProfiles.Batch205.valid8226
  · exact MergedCutProfiles.Batch205.valid8227
  · exact MergedCutProfiles.Batch205.valid8228
theorem numericValid1249 : retention1249.NumericValid := by decide +kernel
def certificate1249 : RatCutBinCertificate := ⟨⟨retention1249,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(483317475466409977/250000000000000000)⟩,(495432000983987167/500000000000000000),(178286968873888717/500000000000000000),(68929331469816033/250000000000000000),(145952674932273279/1000000000000000000)⟩
theorem valid1249 : certificate1249.Valid := by decide +kernel
theorem sound1249 : certificate1249.Sound := rat_cut_bin_certificate_sound certificate1249 profilesValid1249 numericValid1249 valid1249

def retention1250 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(1304135157868974871/13804153658233638553),(455746299760355339/500000000000000000),(13/5),(306460776304971441831/160000000000000000000),true,MergedCutProfiles.Batch205.profile8229,![MergedCutProfiles.Batch205.profile8229,MergedCutProfiles.Batch205.profile8230,MergedCutProfiles.Batch205.profile8231,MergedCutProfiles.Batch205.profile8232,MergedCutProfiles.Batch205.profile8233,MergedCutProfiles.Batch205.profile8234,MergedCutProfiles.Batch205.profile8222,MergedCutProfiles.Batch205.profile8235,MergedCutProfiles.Batch205.profile8236,MergedCutProfiles.Batch205.profile8237,MergedCutProfiles.Batch205.profile8238,MergedCutProfiles.Batch205.profile8239,MergedCutProfiles.Batch206.profile8240,MergedCutProfiles.Batch206.profile8241,MergedCutProfiles.Batch206.profile8242,MergedCutProfiles.Batch206.profile8243]⟩
theorem profilesValid1250 : retention1250.ProfilesValid := by
  change ∀ j : Fin 16, (retention1250.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch205.valid8229
  · exact MergedCutProfiles.Batch205.valid8230
  · exact MergedCutProfiles.Batch205.valid8231
  · exact MergedCutProfiles.Batch205.valid8232
  · exact MergedCutProfiles.Batch205.valid8233
  · exact MergedCutProfiles.Batch205.valid8234
  · exact MergedCutProfiles.Batch205.valid8222
  · exact MergedCutProfiles.Batch205.valid8235
  · exact MergedCutProfiles.Batch205.valid8236
  · exact MergedCutProfiles.Batch205.valid8237
  · exact MergedCutProfiles.Batch205.valid8238
  · exact MergedCutProfiles.Batch205.valid8239
  · exact MergedCutProfiles.Batch206.valid8240
  · exact MergedCutProfiles.Batch206.valid8241
  · exact MergedCutProfiles.Batch206.valid8242
  · exact MergedCutProfiles.Batch206.valid8243
theorem numericValid1250 : retention1250.NumericValid := by decide +kernel
def certificate1250 : RatCutBinCertificate := ⟨⟨retention1250,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(1850669857162565639/1000000000000000000)⟩,(495432000983987167/500000000000000000),(362261576183949821/1000000000000000000),(269898002791384987/1000000000000000000),(36530661996596473/250000000000000000)⟩
theorem valid1250 : certificate1250.Valid := by decide +kernel
theorem sound1250 : certificate1250.Sound := rat_cut_bin_certificate_sound certificate1250 profilesValid1250 numericValid1250 valid1250

def retention1251 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(3099432068605024501/13804153658233638553),(1304135157868974871/1000000000000000000),(19/10),(2010248628363408767867/1280000000000000000000),true,MergedCutProfiles.Batch206.profile8244,![MergedCutProfiles.Batch206.profile8244,MergedCutProfiles.Batch206.profile8245,MergedCutProfiles.Batch206.profile8246,MergedCutProfiles.Batch206.profile8247,MergedCutProfiles.Batch206.profile8248,MergedCutProfiles.Batch206.profile8249,MergedCutProfiles.Batch206.profile8250,MergedCutProfiles.Batch206.profile8251,MergedCutProfiles.Batch206.profile8252,MergedCutProfiles.Batch206.profile8253,MergedCutProfiles.Batch206.profile8254,MergedCutProfiles.Batch206.profile8255,MergedCutProfiles.Batch206.profile8256,MergedCutProfiles.Batch206.profile8257,MergedCutProfiles.Batch206.profile8258,MergedCutProfiles.Batch206.profile8259]⟩
theorem profilesValid1251 : retention1251.ProfilesValid := by
  change ∀ j : Fin 16, (retention1251.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch206.valid8244
  · exact MergedCutProfiles.Batch206.valid8245
  · exact MergedCutProfiles.Batch206.valid8246
  · exact MergedCutProfiles.Batch206.valid8247
  · exact MergedCutProfiles.Batch206.valid8248
  · exact MergedCutProfiles.Batch206.valid8249
  · exact MergedCutProfiles.Batch206.valid8250
  · exact MergedCutProfiles.Batch206.valid8251
  · exact MergedCutProfiles.Batch206.valid8252
  · exact MergedCutProfiles.Batch206.valid8253
  · exact MergedCutProfiles.Batch206.valid8254
  · exact MergedCutProfiles.Batch206.valid8255
  · exact MergedCutProfiles.Batch206.valid8256
  · exact MergedCutProfiles.Batch206.valid8257
  · exact MergedCutProfiles.Batch206.valid8258
  · exact MergedCutProfiles.Batch206.valid8259
theorem numericValid1251 : retention1251.NumericValid := by decide +kernel
def certificate1251 : RatCutBinCertificate := ⟨⟨retention1251,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(761609677205261859/500000000000000000)⟩,(495432000983987167/500000000000000000),(388276078423022289/1000000000000000000),(15274864547647883/62500000000000000),(146432860263242599/1000000000000000000)⟩
theorem valid1251 : certificate1251.Valid := by decide +kernel
theorem sound1251 : certificate1251.Sound := rat_cut_bin_certificate_sound certificate1251 profilesValid1251 numericValid1251 valid1251

def retention1252 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(828763527968873353/1972021951176234079),(3099432068605024501/1000000000000000000),(23/20),(1448201013340831866917/1280000000000000000000),true,MergedCutProfiles.Batch206.profile8260,![MergedCutProfiles.Batch206.profile8260,MergedCutProfiles.Batch206.profile8261,MergedCutProfiles.Batch206.profile8262,MergedCutProfiles.Batch206.profile8263,MergedCutProfiles.Batch206.profile8264,MergedCutProfiles.Batch206.profile8265,MergedCutProfiles.Batch206.profile8266,MergedCutProfiles.Batch206.profile8267,MergedCutProfiles.Batch206.profile8268,MergedCutProfiles.Batch206.profile8269,MergedCutProfiles.Batch206.profile8270,MergedCutProfiles.Batch206.profile8271,MergedCutProfiles.Batch206.profile8272,MergedCutProfiles.Batch206.profile8273,MergedCutProfiles.Batch206.profile8274,MergedCutProfiles.Batch206.profile8275]⟩
theorem profilesValid1252 : retention1252.ProfilesValid := by
  change ∀ j : Fin 16, (retention1252.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch206.valid8260
  · exact MergedCutProfiles.Batch206.valid8261
  · exact MergedCutProfiles.Batch206.valid8262
  · exact MergedCutProfiles.Batch206.valid8263
  · exact MergedCutProfiles.Batch206.valid8264
  · exact MergedCutProfiles.Batch206.valid8265
  · exact MergedCutProfiles.Batch206.valid8266
  · exact MergedCutProfiles.Batch206.valid8267
  · exact MergedCutProfiles.Batch206.valid8268
  · exact MergedCutProfiles.Batch206.valid8269
  · exact MergedCutProfiles.Batch206.valid8270
  · exact MergedCutProfiles.Batch206.valid8271
  · exact MergedCutProfiles.Batch206.valid8272
  · exact MergedCutProfiles.Batch206.valid8273
  · exact MergedCutProfiles.Batch206.valid8274
  · exact MergedCutProfiles.Batch206.valid8275
theorem numericValid1252 : retention1252.NumericValid := by decide +kernel
def certificate1252 : RatCutBinCertificate := ⟨⟨retention1252,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(551394254516440351/500000000000000000)⟩,(495432000983987167/500000000000000000),(439981219344502501/1000000000000000000),(198783590018251107/1000000000000000000),(37163362160715163/250000000000000000)⟩
theorem valid1252 : certificate1252.Valid := by decide +kernel
theorem sound1252 : certificate1252.Sound := rat_cut_bin_certificate_sound certificate1252 profilesValid1252 numericValid1252 valid1252

def retention1253 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(6735181091203442232/13804153658233638553),(5801344695782113471/1000000000000000000),(11/10),(2360661086880432355422775690122944122639/2320537878312845388400000000000000000000),false,MergedCutProfiles.Batch206.profile8276,(fun _ => MergedCutProfiles.Batch206.profile8276)⟩
theorem profilesValid1253 : retention1253.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8276
theorem numericValid1253 : retention1253.NumericValid := by decide +kernel
def certificate1253 : RatCutBinCertificate := ⟨⟨retention1253,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(989918906546594173/1000000000000000000)⟩,(495432000983987167/500000000000000000),(453843867329049563/1000000000000000000),(187618303611140187/1000000000000000000),(146510011864968997/1000000000000000000)⟩
theorem valid1253 : certificate1253.Valid := by decide +kernel
theorem sound1253 : certificate1253.Sound := rat_cut_bin_certificate_sound certificate1253 profilesValid1253 numericValid1253 valid1253

def retention1254 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(6870558231136631422/13804153658233638553),(841897636400430279/125000000000000000),(21/20),(166617268821728228694366809287845703439/168379527280086055800000000000000000000),false,MergedCutProfiles.Batch206.profile8277,(fun _ => MergedCutProfiles.Batch206.profile8277)⟩
theorem profilesValid1254 : retention1254.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8277
theorem numericValid1254 : retention1254.NumericValid := by decide +kernel
def certificate1254 : RatCutBinCertificate := ⟨⟨retention1254,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(963406916767259053/1000000000000000000)⟩,(495432000983987167/500000000000000000),(23020011490781843/50000000000000000),(182485942936495227/1000000000000000000),(18343794269511103/125000000000000000)⟩
theorem valid1254 : certificate1254.Valid := by decide +kernel
theorem sound1254 : certificate1254.Sound := rat_cut_bin_certificate_sound certificate1254 profilesValid1254 numericValid1254 valid1254

def retention1255 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(1/2),(3435279115568315711/500000000000000000),(21/20),(2709293247297350911473959718671866825559/2748223292454652568800000000000000000000),false,MergedCutProfiles.Batch206.profile8278,(fun _ => MergedCutProfiles.Batch206.profile8278)⟩
theorem profilesValid1255 : retention1255.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8278
theorem numericValid1255 : retention1255.NumericValid := by decide +kernel
def certificate1255 : RatCutBinCertificate := ⟨⟨retention1255,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(191941486451609557/200000000000000000)⟩,(495432000983987167/500000000000000000),(230722969263752833/500000000000000000),(181676022889164479/1000000000000000000),(29186614855336121/200000000000000000)⟩
theorem valid1255 : certificate1255.Valid := by decide +kernel
theorem sound1255 : certificate1255.Sound := rat_cut_bin_certificate_sound certificate1255 profilesValid1255 numericValid1255 valid1255

def retention1256 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(1/2),64,1,(255404328366090509797118172072055508119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch206.profile8278,(fun _ => MergedCutProfiles.Batch206.profile8278)⟩
theorem profilesValid1256 : retention1256.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8278
theorem numericValid1256 : retention1256.NumericValid := by decide +kernel
def certificate1256 : RatCutBinCertificate := ⟨⟨retention1256,(2280107758829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(486396341826355181/500000000000000000)⟩,(495432000983987167/500000000000000000),(423297349945452997/1000000000000000000),(106400781332480021/500000000000000000),(25253992848312419/125000000000000000)⟩
theorem valid1256 : certificate1256.Valid := by decide +kernel
theorem sound1256 : certificate1256.Sound := rat_cut_bin_certificate_sound certificate1256 profilesValid1256 numericValid1256 valid1256

def retention1257 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(6350506248212445652/13804153658233638553),(3637570472078883113/1000000000000000000),(6/5),(390479376037220443156687353260255024831/363757047207888311300000000000000000000),false,MergedCutProfiles.Batch206.profile8279,(fun _ => MergedCutProfiles.Batch206.profile8279)⟩
theorem profilesValid1257 : retention1257.ProfilesValid := by
  exact MergedCutProfiles.Batch206.valid8279
theorem numericValid1257 : retention1257.NumericValid := by decide +kernel
def certificate1257 : RatCutBinCertificate := ⟨⟨retention1257,(2615808633829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(64950243060534771/62500000000000000)⟩,(989516136685312413/1000000000000000000),(38032012695843527/100000000000000000),(7875188594428277/31250000000000000),(90003040195501567/500000000000000000)⟩
theorem valid1257 : certificate1257.Valid := by decide +kernel
theorem sound1257 : certificate1257.Sound := rat_cut_bin_certificate_sound certificate1257 profilesValid1257 numericValid1257 valid1257

def retention1258 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(972657464640716781/1972021951176234079),(1587626562053111413/250000000000000000),(21/20),(39532253125585848889481488329211646621/39690664051327785325000000000000000000),false,MergedCutProfiles.Batch207.profile8280,(fun _ => MergedCutProfiles.Batch207.profile8280)⟩
theorem profilesValid1258 : retention1258.ProfilesValid := by
  exact MergedCutProfiles.Batch207.valid8280
theorem numericValid1258 : retention1258.NumericValid := by decide +kernel
def certificate1258 : RatCutBinCertificate := ⟨⟨retention1258,(2615808633829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(483017433467275813/500000000000000000)⟩,(989516136685312413/1000000000000000000),(102281545034284373/250000000000000000),(225223781428966897/1000000000000000000),(45011696977230171/250000000000000000)⟩
theorem valid1258 : certificate1258.Valid := by decide +kernel
theorem sound1258 : certificate1258.Sound := rat_cut_bin_certificate_sound certificate1258 profilesValid1258 numericValid1258 valid1258

def retention1259 : RatCutRetentionCertificate := ⟨(459/8000),(23/400),(6876688275009867642/13804153658233638553),(6808602252485017467/1000000000000000000),(21/20),(10774441712510664508369726219889473030991/10893763603976027947200000000000000000000),false,MergedCutProfiles.Batch207.profile8281,(fun _ => MergedCutProfiles.Batch207.profile8281)⟩
theorem profilesValid1259 : retention1259.ProfilesValid := by
  exact MergedCutProfiles.Batch207.valid8281
theorem numericValid1259 : retention1259.NumericValid := by decide +kernel
def certificate1259 : RatCutBinCertificate := ⟨⟨retention1259,(2615808633829020337/1000000000000000000),(165065648943161283/1000000000000000000),(15127208249511652027/1000000000000000000),(104487659163103801799/500000000000000000),(38362920585488281/40000000000000000)⟩,(989516136685312413/1000000000000000000),(412096002031426721/1000000000000000000),(55645099828081801/250000000000000000),(89129251861783599/500000000000000000)⟩
theorem valid1259 : certificate1259.Valid := by decide +kernel
theorem sound1259 : certificate1259.Sound := rat_cut_bin_certificate_sound certificate1259 profilesValid1259 numericValid1259 valid1259

def certificates : List RatCutBinCertificate := [certificate1248,certificate1249,certificate1250,certificate1251,certificate1252,certificate1253,certificate1254,certificate1255,certificate1256,certificate1257,certificate1258,certificate1259]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1248,List.forall_mem_cons.mpr ⟨sound1249,List.forall_mem_cons.mpr ⟨sound1250,List.forall_mem_cons.mpr ⟨sound1251,List.forall_mem_cons.mpr ⟨sound1252,List.forall_mem_cons.mpr ⟨sound1253,List.forall_mem_cons.mpr ⟨sound1254,List.forall_mem_cons.mpr ⟨sound1255,List.forall_mem_cons.mpr ⟨sound1256,List.forall_mem_cons.mpr ⟨sound1257,List.forall_mem_cons.mpr ⟨sound1258,List.forall_mem_cons.mpr ⟨sound1259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch104
