import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch006
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch308
import Cycle12.MergedCutProfiles.Batch309

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch163

def retention1956 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid1956 : retention1956.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid1956 : retention1956.NumericValid := by decide +kernel
def certificate1956 : RatCutBinCertificate := ⟨⟨retention1956,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(997166678563798121/1000000000000000000)⟩,(999923289900961431/1000000000000000000),(82575994103573961/200000000000000000),(55471544876386259/250000000000000000),(2178461845234443/10000000000000000)⟩
theorem valid1956 : certificate1956.Valid := by decide +kernel
theorem sound1956 : certificate1956.Sound := rat_cut_bin_certificate_sound certificate1956 profilesValid1956 numericValid1956 valid1956

def retention1957 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(64000000000000000000/3304960567845950649313),(2311402822644835119/500000000000000000),(23/20),(3845046083372909392674198173485868367071/1849122258115868095200000000000000000000),false,MergedCutProfiles.Batch308.profile12357,(fun _ => MergedCutProfiles.Batch308.profile12357)⟩
theorem profilesValid1957 : retention1957.ProfilesValid := by
  exact MergedCutProfiles.Batch308.valid12357
theorem numericValid1957 : retention1957.NumericValid := by decide +kernel
def certificate1957 : RatCutBinCertificate := ⟨⟨retention1957,(2069269614470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(2078904990006535037/1000000000000000000)⟩,(124989010157064001/125000000000000000),(121491323092264241/1000000000000000000),(620417959858396453/1000000000000000000),(836877279548098577/1000000000000000000)⟩
theorem valid1957 : certificate1957.Valid := by decide +kernel
theorem sound1957 : certificate1957.Sound := rat_cut_bin_certificate_sound certificate1957 profilesValid1957 numericValid1957 valid1957

def retention1958 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid1958 : retention1958.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid1958 : retention1958.NumericValid := by decide +kernel
def certificate1958 : RatCutBinCertificate := ⟨⟨retention1958,(2069269614470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(124639115677515379/125000000000000000)⟩,(124989010157064001/125000000000000000),(2026401715433281/8000000000000000),(7975900109768747/20000000000000000),(195754385150608401/500000000000000000)⟩
theorem valid1958 : certificate1958.Valid := by decide +kernel
theorem sound1958 : certificate1958.Sound := rat_cut_bin_certificate_sound certificate1958 profilesValid1958 numericValid1958 valid1958

def retention1959 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(30247108506567281/120871515643124418446),(575581717866339571/1000000000000000000),4,(1017037623683884602384067379826589707/460465374293071656800000000000000000),true,MergedCutProfiles.Batch308.profile12358,![MergedCutProfiles.Batch308.profile12358,MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch308.profile12359,MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch309.profile12360,MergedCutProfiles.Batch006.profile240,MergedCutProfiles.Batch309.profile12361,MergedCutProfiles.Batch006.profile241,MergedCutProfiles.Batch309.profile12362,MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch309.profile12363,MergedCutProfiles.Batch309.profile12364,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch309.profile12365,MergedCutProfiles.Batch006.profile245,MergedCutProfiles.Batch309.profile12366]⟩
theorem profilesValid1959 : retention1959.ProfilesValid := by
  change ∀ j : Fin 16, (retention1959.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12358
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch308.valid12359
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch309.valid12360
  · exact MergedCutProfiles.Batch006.valid240
  · exact MergedCutProfiles.Batch309.valid12361
  · exact MergedCutProfiles.Batch006.valid241
  · exact MergedCutProfiles.Batch309.valid12362
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch309.valid12363
  · exact MergedCutProfiles.Batch309.valid12364
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch309.valid12365
  · exact MergedCutProfiles.Batch006.valid245
  · exact MergedCutProfiles.Batch309.valid12366
theorem numericValid1959 : retention1959.NumericValid := by decide +kernel
def certificate1959 : RatCutBinCertificate := ⟨⟨retention1959,(1813683178389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(220672236701740679/100000000000000000)⟩,(999895948131541323/1000000000000000000),(36063928804832053/62500000000000000),(52843809069786821/500000000000000000),(23514716441655037/500000000000000000)⟩
theorem valid1959 : certificate1959.Valid := by decide +kernel
theorem sound1959 : certificate1959.Sound := rat_cut_bin_certificate_sound certificate1959 profilesValid1959 numericValid1959 valid1959

def retention1960 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(32475585625000000/60435757821562209223),(30247108506567281/50000000000000000),4,(1367058524751189798791004994380442359/604942170131345620000000000000000000),true,MergedCutProfiles.Batch005.profile238,![MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch309.profile12367,MergedCutProfiles.Batch006.profile255,MergedCutProfiles.Batch309.profile12363,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch006.profile245,MergedCutProfiles.Batch006.profile246,MergedCutProfiles.Batch006.profile247,MergedCutProfiles.Batch006.profile248,MergedCutProfiles.Batch006.profile249,MergedCutProfiles.Batch006.profile256,MergedCutProfiles.Batch006.profile251,MergedCutProfiles.Batch006.profile257,MergedCutProfiles.Batch006.profile253,MergedCutProfiles.Batch006.profile258]⟩
theorem profilesValid1960 : retention1960.ProfilesValid := by
  change ∀ j : Fin 16, (retention1960.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch309.valid12367
  · exact MergedCutProfiles.Batch006.valid255
  · exact MergedCutProfiles.Batch309.valid12363
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch006.valid245
  · exact MergedCutProfiles.Batch006.valid246
  · exact MergedCutProfiles.Batch006.valid247
  · exact MergedCutProfiles.Batch006.valid248
  · exact MergedCutProfiles.Batch006.valid249
  · exact MergedCutProfiles.Batch006.valid256
  · exact MergedCutProfiles.Batch006.valid251
  · exact MergedCutProfiles.Batch006.valid257
  · exact MergedCutProfiles.Batch006.valid253
  · exact MergedCutProfiles.Batch006.valid258
theorem numericValid1960 : retention1960.NumericValid := by decide +kernel
def certificate1960 : RatCutBinCertificate := ⟨⟨retention1960,(1813683178389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(2257822408481497733/1000000000000000000)⟩,(999895948131541323/1000000000000000000),(545315897382983219/1000000000000000000),(124009973119374587/1000000000000000000),(28375611327677773/500000000000000000)⟩
theorem valid1960 : certificate1960.Valid := by decide +kernel
theorem sound1960 : certificate1960.Sound := rat_cut_bin_certificate_sound certificate1960 profilesValid1960 numericValid1960 valid1960

def retention1961 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1218081069752529059/1208715156431244184460),(51960937/40000000),(12/5),(18581299688684188003/8000000000000000000),true,MergedCutProfiles.Batch006.profile254,![MergedCutProfiles.Batch006.profile254,MergedCutProfiles.Batch006.profile241,MergedCutProfiles.Batch309.profile12364,MergedCutProfiles.Batch309.profile12366,MergedCutProfiles.Batch006.profile267,MergedCutProfiles.Batch006.profile249,MergedCutProfiles.Batch006.profile252,MergedCutProfiles.Batch006.profile253,MergedCutProfiles.Batch309.profile12368,MergedCutProfiles.Batch006.profile268,MergedCutProfiles.Batch006.profile260,MergedCutProfiles.Batch309.profile12369,MergedCutProfiles.Batch006.profile262,MergedCutProfiles.Batch006.profile263,MergedCutProfiles.Batch006.profile264,MergedCutProfiles.Batch006.profile265]⟩
theorem profilesValid1961 : retention1961.ProfilesValid := by
  change ∀ j : Fin 16, (retention1961.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch006.valid254
  · exact MergedCutProfiles.Batch006.valid241
  · exact MergedCutProfiles.Batch309.valid12364
  · exact MergedCutProfiles.Batch309.valid12366
  · exact MergedCutProfiles.Batch006.valid267
  · exact MergedCutProfiles.Batch006.valid249
  · exact MergedCutProfiles.Batch006.valid252
  · exact MergedCutProfiles.Batch006.valid253
  · exact MergedCutProfiles.Batch309.valid12368
  · exact MergedCutProfiles.Batch006.valid268
  · exact MergedCutProfiles.Batch006.valid260
  · exact MergedCutProfiles.Batch309.valid12369
  · exact MergedCutProfiles.Batch006.valid262
  · exact MergedCutProfiles.Batch006.valid263
  · exact MergedCutProfiles.Batch006.valid264
  · exact MergedCutProfiles.Batch006.valid265
theorem numericValid1961 : retention1961.NumericValid := by decide +kernel
def certificate1961 : RatCutBinCertificate := ⟨⟨retention1961,(1813683178389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(18571726247200523/8000000000000000)⟩,(999895948131541323/1000000000000000000),(340395420399072281/1000000000000000000),(146385371853375789/500000000000000000),(43221578500012977/200000000000000000)⟩
theorem valid1961 : certificate1961.Valid := by decide +kernel
theorem sound1961 : certificate1961.Sound := rat_cut_bin_certificate_sound certificate1961 profilesValid1961 numericValid1961 valid1961

def retention1962 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1600000000000000000/60435757821562209223),(1218081069752529059/500000000000000000),(33/20),(1367225009441161741563/640000000000000000000),true,MergedCutProfiles.Batch309.profile12370,![MergedCutProfiles.Batch309.profile12370,MergedCutProfiles.Batch006.profile279,MergedCutProfiles.Batch309.profile12371,MergedCutProfiles.Batch007.profile280,MergedCutProfiles.Batch309.profile12372,MergedCutProfiles.Batch007.profile281,MergedCutProfiles.Batch309.profile12373,MergedCutProfiles.Batch007.profile282,MergedCutProfiles.Batch309.profile12374,MergedCutProfiles.Batch007.profile283,MergedCutProfiles.Batch309.profile12375,MergedCutProfiles.Batch007.profile284,MergedCutProfiles.Batch309.profile12376,MergedCutProfiles.Batch007.profile285,MergedCutProfiles.Batch309.profile12377,MergedCutProfiles.Batch007.profile286]⟩
theorem profilesValid1962 : retention1962.ProfilesValid := by
  change ∀ j : Fin 16, (retention1962.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch309.valid12370
  · exact MergedCutProfiles.Batch006.valid279
  · exact MergedCutProfiles.Batch309.valid12371
  · exact MergedCutProfiles.Batch007.valid280
  · exact MergedCutProfiles.Batch309.valid12372
  · exact MergedCutProfiles.Batch007.valid281
  · exact MergedCutProfiles.Batch309.valid12373
  · exact MergedCutProfiles.Batch007.valid282
  · exact MergedCutProfiles.Batch309.valid12374
  · exact MergedCutProfiles.Batch007.valid283
  · exact MergedCutProfiles.Batch309.valid12375
  · exact MergedCutProfiles.Batch007.valid284
  · exact MergedCutProfiles.Batch309.valid12376
  · exact MergedCutProfiles.Batch007.valid285
  · exact MergedCutProfiles.Batch309.valid12377
  · exact MergedCutProfiles.Batch007.valid286
theorem numericValid1962 : retention1962.NumericValid := by decide +kernel
def certificate1962 : RatCutBinCertificate := ⟨⟨retention1962,(1813683178389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(85418654385240697/40000000000000000)⟩,(999895948131541323/1000000000000000000),(71506753322706787/250000000000000000),(355928484791421709/1000000000000000000),(348416928761257277/1000000000000000000)⟩
theorem valid1962 : certificate1962.Valid := by decide +kernel
theorem sound1962 : certificate1962.Sound := rat_cut_bin_certificate_sound certificate1962 profilesValid1962 numericValid1962 valid1962

def retention1963 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid1963 : retention1963.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid1963 : retention1963.NumericValid := by decide +kernel
def certificate1963 : RatCutBinCertificate := ⟨⟨retention1963,(1813683178389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(498517997397036023/500000000000000000)⟩,(999895948131541323/1000000000000000000),(414875384738547871/1000000000000000000),(220125907679175239/1000000000000000000),(108042057723064443/500000000000000000)⟩
theorem valid1963 : certificate1963.Valid := by decide +kernel
theorem sound1963 : certificate1963.Sound := rat_cut_bin_certificate_sound certificate1963 profilesValid1963 numericValid1963 valid1963

def retention1964 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1600000000000000000/60435757821562209223),(2337335379661358019/500000000000000000),(23/20),(1277275345644235735371842808451355025957/623289434576362138400000000000000000000),false,MergedCutProfiles.Batch309.profile12378,(fun _ => MergedCutProfiles.Batch309.profile12378)⟩
theorem profilesValid1964 : retention1964.ProfilesValid := by
  exact MergedCutProfiles.Batch309.valid12378
theorem numericValid1964 : retention1964.NumericValid := by decide +kernel
def certificate1964 : RatCutBinCertificate := ⟨⟨retention1964,(2077245979389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(256074052007762657/125000000000000000)⟩,(499940413702706513/500000000000000000),(121978157518246313/1000000000000000000),(309708055203750967/500000000000000000),(828680800813786269/1000000000000000000)⟩
theorem valid1964 : certificate1964.Valid := by decide +kernel
theorem sound1964 : certificate1964.Sound := rat_cut_bin_certificate_sound certificate1964 profilesValid1964 numericValid1964 valid1964

def retention1965 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(1/2),64,1,(255368860549321472084694123425840443671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch007.profile295,(fun _ => MergedCutProfiles.Batch007.profile295)⟩
theorem profilesValid1965 : retention1965.ProfilesValid := by
  exact MergedCutProfiles.Batch007.valid295
theorem numericValid1965 : retention1965.NumericValid := by decide +kernel
def certificate1965 : RatCutBinCertificate := ⟨⟨retention1965,(2077245979389637159/1000000000000000000),(1970684370264843/1000000000000000000),(3584112713321703639/500000000000000000),(17405413990888538335399/1000000000000000000),(62310221016362299/62500000000000000)⟩,(499940413702706513/500000000000000000),(50128920332245697/200000000000000000),(402450129390637059/1000000000000000000),(79005277605178209/200000000000000000)⟩
theorem valid1965 : certificate1965.Valid := by decide +kernel
theorem sound1965 : certificate1965.Sound := rat_cut_bin_certificate_sound certificate1965 profilesValid1965 numericValid1965 valid1965

def retention1966 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(196596917649342466/614213302476857892387),(289084772545842269/500000000000000000),4,(283328787050476855981/128000000000000000000),true,MergedCutProfiles.Batch309.profile12379,![MergedCutProfiles.Batch309.profile12379,MergedCutProfiles.Batch309.profile12380,MergedCutProfiles.Batch309.profile12381,MergedCutProfiles.Batch007.profile298,MergedCutProfiles.Batch008.profile327,MergedCutProfiles.Batch007.profile299,MergedCutProfiles.Batch309.profile12382,MergedCutProfiles.Batch309.profile12383,MergedCutProfiles.Batch309.profile12384,MergedCutProfiles.Batch008.profile328,MergedCutProfiles.Batch309.profile12385,MergedCutProfiles.Batch007.profile302,MergedCutProfiles.Batch309.profile12386,MergedCutProfiles.Batch007.profile303,MergedCutProfiles.Batch008.profile329,MergedCutProfiles.Batch007.profile304]⟩
theorem profilesValid1966 : retention1966.ProfilesValid := by
  change ∀ j : Fin 16, (retention1966.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch309.valid12379
  · exact MergedCutProfiles.Batch309.valid12380
  · exact MergedCutProfiles.Batch309.valid12381
  · exact MergedCutProfiles.Batch007.valid298
  · exact MergedCutProfiles.Batch008.valid327
  · exact MergedCutProfiles.Batch007.valid299
  · exact MergedCutProfiles.Batch309.valid12382
  · exact MergedCutProfiles.Batch309.valid12383
  · exact MergedCutProfiles.Batch309.valid12384
  · exact MergedCutProfiles.Batch008.valid328
  · exact MergedCutProfiles.Batch309.valid12385
  · exact MergedCutProfiles.Batch007.valid302
  · exact MergedCutProfiles.Batch309.valid12386
  · exact MergedCutProfiles.Batch007.valid303
  · exact MergedCutProfiles.Batch008.valid329
  · exact MergedCutProfiles.Batch007.valid304
theorem numericValid1966 : retention1966.NumericValid := by decide +kernel
def certificate1966 : RatCutBinCertificate := ⟨⟨retention1966,(910533507816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(2210913459017929163/1000000000000000000)⟩,(999864646610345067/1000000000000000000),(286449757557633487/500000000000000000),(53984851747725173/500000000000000000),(9631690210258863/200000000000000000)⟩
theorem valid1966 : certificate1966.Valid := by decide +kernel
theorem sound1966 : certificate1966.Sound := rat_cut_bin_certificate_sound certificate1966 profilesValid1966 numericValid1966 valid1966

def retention1967 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1303852909000000000/1842639907430573677161),(294895376474013699/500000000000000000),4,(892720671112823027/400000000000000000),true,MergedCutProfiles.Batch007.profile297,![MergedCutProfiles.Batch007.profile297,MergedCutProfiles.Batch007.profile313,MergedCutProfiles.Batch309.profile12387,MergedCutProfiles.Batch309.profile12384,MergedCutProfiles.Batch309.profile12385,MergedCutProfiles.Batch309.profile12386,MergedCutProfiles.Batch007.profile304,MergedCutProfiles.Batch007.profile315,MergedCutProfiles.Batch008.profile330,MergedCutProfiles.Batch007.profile307,MergedCutProfiles.Batch007.profile308,MergedCutProfiles.Batch007.profile309,MergedCutProfiles.Batch008.profile331,MergedCutProfiles.Batch007.profile311,MergedCutProfiles.Batch007.profile312,MergedCutProfiles.Batch309.profile12388]⟩
theorem profilesValid1967 : retention1967.ProfilesValid := by
  change ∀ j : Fin 16, (retention1967.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch007.valid297
  · exact MergedCutProfiles.Batch007.valid313
  · exact MergedCutProfiles.Batch309.valid12387
  · exact MergedCutProfiles.Batch309.valid12384
  · exact MergedCutProfiles.Batch309.valid12385
  · exact MergedCutProfiles.Batch309.valid12386
  · exact MergedCutProfiles.Batch007.valid304
  · exact MergedCutProfiles.Batch007.valid315
  · exact MergedCutProfiles.Batch008.valid330
  · exact MergedCutProfiles.Batch007.valid307
  · exact MergedCutProfiles.Batch007.valid308
  · exact MergedCutProfiles.Batch007.valid309
  · exact MergedCutProfiles.Batch008.valid331
  · exact MergedCutProfiles.Batch007.valid311
  · exact MergedCutProfiles.Batch007.valid312
  · exact MergedCutProfiles.Batch309.valid12388
theorem numericValid1967 : retention1967.NumericValid := by decide +kernel
def certificate1967 : RatCutBinCertificate := ⟨⟨retention1967,(910533507816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(55730224699309607/25000000000000000)⟩,(999864646610345067/1000000000000000000),(280303715334607811/500000000000000000),(114949767311947619/1000000000000000000),(5181197252337443/100000000000000000)⟩
theorem valid1967 : certificate1967.Valid := by decide +kernel
theorem sound1967 : certificate1967.Sound := rat_cut_bin_certificate_sound certificate1967 profilesValid1967 numericValid1967 valid1967

def certificates : List RatCutBinCertificate := [certificate1956,certificate1957,certificate1958,certificate1959,certificate1960,certificate1961,certificate1962,certificate1963,certificate1964,certificate1965,certificate1966,certificate1967]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1956,List.forall_mem_cons.mpr ⟨sound1957,List.forall_mem_cons.mpr ⟨sound1958,List.forall_mem_cons.mpr ⟨sound1959,List.forall_mem_cons.mpr ⟨sound1960,List.forall_mem_cons.mpr ⟨sound1961,List.forall_mem_cons.mpr ⟨sound1962,List.forall_mem_cons.mpr ⟨sound1963,List.forall_mem_cons.mpr ⟨sound1964,List.forall_mem_cons.mpr ⟨sound1965,List.forall_mem_cons.mpr ⟨sound1966,List.forall_mem_cons.mpr ⟨sound1967,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch163
