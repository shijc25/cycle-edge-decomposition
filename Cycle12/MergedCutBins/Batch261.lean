import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch364
import Cycle12.MergedCutProfiles.Batch365
import Cycle12.MergedCutProfiles.Batch480
import Cycle12.MergedCutProfiles.Batch481
import Cycle12.MergedCutProfiles.Batch482

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch261

def retention3132 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1/2),(755570647036049363/12500000000000000),1,(235496885764684387852509280909300509/236115827198765425937500000000000000),false,MergedCutProfiles.Batch364.profile14563,(fun _ => MergedCutProfiles.Batch364.profile14563)⟩
theorem profilesValid3132 : retention3132.ProfilesValid := by
  exact MergedCutProfiles.Batch364.valid14563
theorem numericValid3132 : retention3132.NumericValid := by decide +kernel
def certificate3132 : RatCutBinCertificate := ⟨⟨retention3132,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(122687254448578299/125000000000000000)⟩,(499372494528345371/500000000000000000),(471384989157661807/1000000000000000000),(87047794492907761/500000000000000000),(167931146030557869/1000000000000000000)⟩
theorem valid3132 : certificate3132.Valid := by decide +kernel
theorem sound3132 : certificate3132.Sound := rat_cut_bin_certificate_sound certificate3132 profilesValid3132 numericValid3132 valid3132

def retention3133 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(55314274789232758203/121128682834672462648),(9989895199785492037/1000000000000000000),1,(10580815827613605875284429965614815833/9989895199785492037000000000000000000),false,MergedCutProfiles.Batch480.profile19238,(fun _ => MergedCutProfiles.Batch480.profile19238)⟩
theorem profilesValid3133 : retention3133.ProfilesValid := by
  exact MergedCutProfiles.Batch480.valid19238
theorem numericValid3133 : retention3133.NumericValid := by decide +kernel
def certificate3133 : RatCutBinCertificate := ⟨⟨retention3133,(540246928484127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(1042241452466124441/1000000000000000000)⟩,(998663605430282479/1000000000000000000),(60902588290179259/500000000000000000),(619771894205731779/1000000000000000000),(584105681504044911/1000000000000000000)⟩
theorem valid3133 : certificate3133.Valid := by decide +kernel
theorem sound3133 : certificate3133.Sound := rat_cut_bin_certificate_sound certificate3133 profilesValid3133 numericValid3133 valid3133

def retention3134 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(7487179171559368659/15141085354334057831),(55314274789232758203/1000000000000000000),1,(223011408793520798813415110779058279987/221257099156931032812000000000000000000),false,MergedCutProfiles.Batch480.profile19239,(fun _ => MergedCutProfiles.Batch480.profile19239)⟩
theorem profilesValid3134 : retention3134.ProfilesValid := by
  exact MergedCutProfiles.Batch480.valid19239
theorem numericValid3134 : retention3134.NumericValid := by decide +kernel
def certificate3134 : RatCutBinCertificate := ⟨⟨retention3134,(540246928484127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(991018535742034827/1000000000000000000)⟩,(998663605430282479/1000000000000000000),(128100938154451641/1000000000000000000),(606957027131306239/1000000000000000000),(295060587611899629/500000000000000000)⟩
theorem valid3134 : certificate3134.Valid := by decide +kernel
theorem sound3134 : certificate3134.Sound := rat_cut_bin_certificate_sound certificate3134 profilesValid3134 numericValid3134 valid3134

def retention3135 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(60496407706199698765/121128682834672462648),(7487179171559368659/125000000000000000),1,(2214995438271135953852863885937460717/2218423458239812936000000000000000000),false,MergedCutProfiles.Batch481.profile19240,(fun _ => MergedCutProfiles.Batch481.profile19240)⟩
theorem profilesValid3135 : retention3135.ProfilesValid := by
  exact MergedCutProfiles.Batch481.valid19240
theorem numericValid3135 : retention3135.NumericValid := by decide +kernel
def certificate3135 : RatCutBinCertificate := ⟨⟨retention3135,(540246928484127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(981544458045917027/1000000000000000000)⟩,(998663605430282479/1000000000000000000),(129337395893143373/1000000000000000000),(604472234766698537/1000000000000000000),(4663705217760037/8000000000000000)⟩
theorem valid3135 : certificate3135.Valid := by decide +kernel
theorem sound3135 : certificate3135.Sound := rat_cut_bin_certificate_sound certificate3135 profilesValid3135 numericValid3135 valid3135

def retention3136 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1/2),(12099281541239939753/200000000000000000),1,(1885563631741662747029003329103322297/1890512740818740586406250000000000000),false,MergedCutProfiles.Batch364.profile14563,(fun _ => MergedCutProfiles.Batch364.profile14563)⟩
theorem profilesValid3136 : retention3136.ProfilesValid := by
  exact MergedCutProfiles.Batch364.valid14563
theorem numericValid3136 : retention3136.NumericValid := by decide +kernel
def certificate3136 : RatCutBinCertificate := ⟨⟨retention3136,(540246928484127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(980471842703671571/1000000000000000000)⟩,(998663605430282479/1000000000000000000),(129478888253371191/1000000000000000000),(604188551527483847/1000000000000000000),(582155965535416301/1000000000000000000)⟩
theorem valid3136 : certificate3136.Valid := by decide +kernel
theorem sound3136 : certificate3136.Sound := rat_cut_bin_certificate_sound certificate3136 profilesValid3136 numericValid3136 valid3136

def retention3137 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(107243247616403353/16468023098777567652),(743270032984973733/1000000000000000000),(73/20),(2951674419585420149373/1280000000000000000000),true,MergedCutProfiles.Batch481.profile19241,![MergedCutProfiles.Batch481.profile19241,MergedCutProfiles.Batch481.profile19242,MergedCutProfiles.Batch481.profile19243,MergedCutProfiles.Batch481.profile19244,MergedCutProfiles.Batch481.profile19245,MergedCutProfiles.Batch481.profile19246,MergedCutProfiles.Batch481.profile19247,MergedCutProfiles.Batch481.profile19248,MergedCutProfiles.Batch481.profile19249,MergedCutProfiles.Batch481.profile19250,MergedCutProfiles.Batch481.profile19251,MergedCutProfiles.Batch481.profile19252,MergedCutProfiles.Batch481.profile19253,MergedCutProfiles.Batch481.profile19254,MergedCutProfiles.Batch481.profile19255,MergedCutProfiles.Batch481.profile19256]⟩
theorem profilesValid3137 : retention3137.ProfilesValid := by
  change ∀ j : Fin 16, (retention3137.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch481.valid19241
  · exact MergedCutProfiles.Batch481.valid19242
  · exact MergedCutProfiles.Batch481.valid19243
  · exact MergedCutProfiles.Batch481.valid19244
  · exact MergedCutProfiles.Batch481.valid19245
  · exact MergedCutProfiles.Batch481.valid19246
  · exact MergedCutProfiles.Batch481.valid19247
  · exact MergedCutProfiles.Batch481.valid19248
  · exact MergedCutProfiles.Batch481.valid19249
  · exact MergedCutProfiles.Batch481.valid19250
  · exact MergedCutProfiles.Batch481.valid19251
  · exact MergedCutProfiles.Batch481.valid19252
  · exact MergedCutProfiles.Batch481.valid19253
  · exact MergedCutProfiles.Batch481.valid19254
  · exact MergedCutProfiles.Batch481.valid19255
  · exact MergedCutProfiles.Batch481.valid19256
theorem numericValid3137 : retention3137.NumericValid := by decide +kernel
def certificate3137 : RatCutBinCertificate := ⟨⟨retention3137,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(1122918787517395257/500000000000000000)⟩,(998703306766094507/1000000000000000000),(450306415529980661/1000000000000000000),(11901668104517657/62500000000000000),(4768091480305237/50000000000000000)⟩
theorem valid3137 : certificate3137.Valid := by decide +kernel
theorem sound3137 : certificate3137.Sound := rat_cut_bin_certificate_sound certificate3137 profilesValid3137 numericValid3137 valid3137

def retention3138 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(27279888348589187/3202115602540082599),(750702733314823471/1000000000000000000),(18/5),(2928720247258709251699/1280000000000000000000),true,MergedCutProfiles.Batch481.profile19257,![MergedCutProfiles.Batch481.profile19257,MergedCutProfiles.Batch481.profile19258,MergedCutProfiles.Batch481.profile19259,MergedCutProfiles.Batch481.profile19260,MergedCutProfiles.Batch481.profile19261,MergedCutProfiles.Batch481.profile19262,MergedCutProfiles.Batch481.profile19263,MergedCutProfiles.Batch481.profile19264,MergedCutProfiles.Batch481.profile19265,MergedCutProfiles.Batch481.profile19266,MergedCutProfiles.Batch481.profile19267,MergedCutProfiles.Batch364.profile14587,MergedCutProfiles.Batch365.profile14601,MergedCutProfiles.Batch481.profile19268,MergedCutProfiles.Batch481.profile19269,MergedCutProfiles.Batch481.profile19270]⟩
theorem profilesValid3138 : retention3138.ProfilesValid := by
  change ∀ j : Fin 16, (retention3138.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch481.valid19257
  · exact MergedCutProfiles.Batch481.valid19258
  · exact MergedCutProfiles.Batch481.valid19259
  · exact MergedCutProfiles.Batch481.valid19260
  · exact MergedCutProfiles.Batch481.valid19261
  · exact MergedCutProfiles.Batch481.valid19262
  · exact MergedCutProfiles.Batch481.valid19263
  · exact MergedCutProfiles.Batch481.valid19264
  · exact MergedCutProfiles.Batch481.valid19265
  · exact MergedCutProfiles.Batch481.valid19266
  · exact MergedCutProfiles.Batch481.valid19267
  · exact MergedCutProfiles.Batch364.valid14587
  · exact MergedCutProfiles.Batch365.valid14601
  · exact MergedCutProfiles.Batch481.valid19268
  · exact MergedCutProfiles.Batch481.valid19269
  · exact MergedCutProfiles.Batch481.valid19270
theorem numericValid3138 : retention3138.NumericValid := by decide +kernel
def certificate3138 : RatCutBinCertificate := ⟨⟨retention3138,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(2228728705115286263/1000000000000000000)⟩,(998703306766094507/1000000000000000000),(451285539999047609/1000000000000000000),(189646590149684857/1000000000000000000),(95379608060373259/1000000000000000000)⟩
theorem valid3138 : certificate3138.Valid := by decide +kernel
theorem sound3138 : certificate3138.Sound := rat_cut_bin_certificate_sound certificate3138 profilesValid3138 numericValid3138 valid3138

def retention3139 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(30612358750000000/3202115602540082599),(245518995137302683/250000000000000000),(29/10),(727245858249510681603/320000000000000000000),true,MergedCutProfiles.Batch481.profile19271,![MergedCutProfiles.Batch481.profile19271,MergedCutProfiles.Batch481.profile19272,MergedCutProfiles.Batch481.profile19273,MergedCutProfiles.Batch481.profile19274,MergedCutProfiles.Batch481.profile19275,MergedCutProfiles.Batch481.profile19276,MergedCutProfiles.Batch364.profile14599,MergedCutProfiles.Batch481.profile19265,MergedCutProfiles.Batch481.profile19277,MergedCutProfiles.Batch481.profile19278,MergedCutProfiles.Batch364.profile14572,MergedCutProfiles.Batch481.profile19279,MergedCutProfiles.Batch482.profile19280,MergedCutProfiles.Batch365.profile14602,MergedCutProfiles.Batch364.profile14588,MergedCutProfiles.Batch482.profile19281]⟩
theorem profilesValid3139 : retention3139.ProfilesValid := by
  change ∀ j : Fin 16, (retention3139.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch481.valid19271
  · exact MergedCutProfiles.Batch481.valid19272
  · exact MergedCutProfiles.Batch481.valid19273
  · exact MergedCutProfiles.Batch481.valid19274
  · exact MergedCutProfiles.Batch481.valid19275
  · exact MergedCutProfiles.Batch481.valid19276
  · exact MergedCutProfiles.Batch364.valid14599
  · exact MergedCutProfiles.Batch481.valid19265
  · exact MergedCutProfiles.Batch481.valid19277
  · exact MergedCutProfiles.Batch481.valid19278
  · exact MergedCutProfiles.Batch364.valid14572
  · exact MergedCutProfiles.Batch481.valid19279
  · exact MergedCutProfiles.Batch482.valid19280
  · exact MergedCutProfiles.Batch365.valid14602
  · exact MergedCutProfiles.Batch364.valid14588
  · exact MergedCutProfiles.Batch482.valid19281
theorem numericValid3139 : retention3139.NumericValid := by decide +kernel
def certificate3139 : RatCutBinCertificate := ⟨⟨retention3139,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(2224846546351175403/1000000000000000000)⟩,(998703306766094507/1000000000000000000),(393598449910629577/1000000000000000000),(119699629074284359/500000000000000000),(7223508142607121/50000000000000000)⟩
theorem valid3139 : certificate3139.Valid := by decide +kernel
theorem sound3139 : certificate3139.Sound := rat_cut_bin_certificate_sound certificate3139 profilesValid3139 numericValid3139 valid3139

def retention3140 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(158089685196321157/16468023098777567652),(220408983/200000000),(13/5),(180566131067055807/80000000000000000),true,MergedCutProfiles.Batch481.profile19271,![MergedCutProfiles.Batch481.profile19271,MergedCutProfiles.Batch481.profile19272,MergedCutProfiles.Batch481.profile19273,MergedCutProfiles.Batch481.profile19274,MergedCutProfiles.Batch482.profile19282,MergedCutProfiles.Batch481.profile19276,MergedCutProfiles.Batch364.profile14599,MergedCutProfiles.Batch481.profile19265,MergedCutProfiles.Batch481.profile19277,MergedCutProfiles.Batch481.profile19278,MergedCutProfiles.Batch364.profile14572,MergedCutProfiles.Batch481.profile19279,MergedCutProfiles.Batch482.profile19280,MergedCutProfiles.Batch365.profile14602,MergedCutProfiles.Batch482.profile19283,MergedCutProfiles.Batch482.profile19281]⟩
theorem profilesValid3140 : retention3140.ProfilesValid := by
  change ∀ j : Fin 16, (retention3140.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch481.valid19271
  · exact MergedCutProfiles.Batch481.valid19272
  · exact MergedCutProfiles.Batch481.valid19273
  · exact MergedCutProfiles.Batch481.valid19274
  · exact MergedCutProfiles.Batch482.valid19282
  · exact MergedCutProfiles.Batch481.valid19276
  · exact MergedCutProfiles.Batch364.valid14599
  · exact MergedCutProfiles.Batch481.valid19265
  · exact MergedCutProfiles.Batch481.valid19277
  · exact MergedCutProfiles.Batch481.valid19278
  · exact MergedCutProfiles.Batch364.valid14572
  · exact MergedCutProfiles.Batch481.valid19279
  · exact MergedCutProfiles.Batch482.valid19280
  · exact MergedCutProfiles.Batch365.valid14602
  · exact MergedCutProfiles.Batch482.valid19283
  · exact MergedCutProfiles.Batch482.valid19281
theorem numericValid3140 : retention3140.NumericValid := by decide +kernel
def certificate3140 : RatCutBinCertificate := ⟨⟨retention3140,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(221422437648032891/100000000000000000)⟩,(998703306766094507/1000000000000000000),(93683543647118039/250000000000000000),(257447002235049829/1000000000000000000),(84379932790603101/500000000000000000)⟩
theorem valid3140 : certificate3140.Valid := by decide +kernel
theorem sound3140 : certificate3140.Sound := rat_cut_bin_certificate_sound certificate3140 profilesValid3140 numericValid3140 valid3140

def retention3141 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(399439776646093381/38425387230480991188),(1106627796374248099/1000000000000000000),(13/5),(2884756677001964074791/1280000000000000000000),true,MergedCutProfiles.Batch482.profile19284,![MergedCutProfiles.Batch482.profile19284,MergedCutProfiles.Batch364.profile14583,MergedCutProfiles.Batch482.profile19285,MergedCutProfiles.Batch482.profile19286,MergedCutProfiles.Batch481.profile19248,MergedCutProfiles.Batch482.profile19287,MergedCutProfiles.Batch482.profile19288,MergedCutProfiles.Batch482.profile19289,MergedCutProfiles.Batch481.profile19267,MergedCutProfiles.Batch481.profile19256,MergedCutProfiles.Batch481.profile19279,MergedCutProfiles.Batch482.profile19280,MergedCutProfiles.Batch482.profile19290,MergedCutProfiles.Batch482.profile19291,MergedCutProfiles.Batch365.profile14603,MergedCutProfiles.Batch482.profile19292]⟩
theorem profilesValid3141 : retention3141.ProfilesValid := by
  change ∀ j : Fin 16, (retention3141.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch482.valid19284
  · exact MergedCutProfiles.Batch364.valid14583
  · exact MergedCutProfiles.Batch482.valid19285
  · exact MergedCutProfiles.Batch482.valid19286
  · exact MergedCutProfiles.Batch481.valid19248
  · exact MergedCutProfiles.Batch482.valid19287
  · exact MergedCutProfiles.Batch482.valid19288
  · exact MergedCutProfiles.Batch482.valid19289
  · exact MergedCutProfiles.Batch481.valid19267
  · exact MergedCutProfiles.Batch481.valid19256
  · exact MergedCutProfiles.Batch481.valid19279
  · exact MergedCutProfiles.Batch482.valid19280
  · exact MergedCutProfiles.Batch482.valid19290
  · exact MergedCutProfiles.Batch482.valid19291
  · exact MergedCutProfiles.Batch365.valid14603
  · exact MergedCutProfiles.Batch482.valid19292
theorem numericValid3141 : retention3141.NumericValid := by decide +kernel
def certificate3141 : RatCutBinCertificate := ⟨⟨retention3141,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(2210863896370932357/1000000000000000000)⟩,(998703306766094507/1000000000000000000),(46824895628781551/125000000000000000),(51515906467319723/200000000000000000),(84404609016199651/500000000000000000)⟩
theorem valid3141 : certificate3141.Valid := by decide +kernel
theorem sound3141 : certificate3141.Sound := rat_cut_bin_certificate_sound certificate3141 profilesValid3141 numericValid3141 valid3141

def retention3142 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(248217000940938341/8234011549388783826),(1198319329938280143/1000000000000000000),(49/20),(688844572655453293289/320000000000000000000),true,MergedCutProfiles.Batch482.profile19293,![MergedCutProfiles.Batch482.profile19293,MergedCutProfiles.Batch481.profile19263,MergedCutProfiles.Batch482.profile19294,MergedCutProfiles.Batch482.profile19295,MergedCutProfiles.Batch482.profile19296,MergedCutProfiles.Batch482.profile19297,MergedCutProfiles.Batch364.profile14578,MergedCutProfiles.Batch482.profile19298,MergedCutProfiles.Batch482.profile19299,MergedCutProfiles.Batch482.profile19300,MergedCutProfiles.Batch482.profile19301,MergedCutProfiles.Batch482.profile19302,MergedCutProfiles.Batch482.profile19303,MergedCutProfiles.Batch365.profile14622,MergedCutProfiles.Batch482.profile19304,MergedCutProfiles.Batch482.profile19305]⟩
theorem profilesValid3142 : retention3142.ProfilesValid := by
  change ∀ j : Fin 16, (retention3142.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch482.valid19293
  · exact MergedCutProfiles.Batch481.valid19263
  · exact MergedCutProfiles.Batch482.valid19294
  · exact MergedCutProfiles.Batch482.valid19295
  · exact MergedCutProfiles.Batch482.valid19296
  · exact MergedCutProfiles.Batch482.valid19297
  · exact MergedCutProfiles.Batch364.valid14578
  · exact MergedCutProfiles.Batch482.valid19298
  · exact MergedCutProfiles.Batch482.valid19299
  · exact MergedCutProfiles.Batch482.valid19300
  · exact MergedCutProfiles.Batch482.valid19301
  · exact MergedCutProfiles.Batch482.valid19302
  · exact MergedCutProfiles.Batch482.valid19303
  · exact MergedCutProfiles.Batch365.valid14622
  · exact MergedCutProfiles.Batch482.valid19304
  · exact MergedCutProfiles.Batch482.valid19305
theorem numericValid3142 : retention3142.NumericValid := by decide +kernel
def certificate3142 : RatCutBinCertificate := ⟨⟨retention3142,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(422451859439717767/200000000000000000)⟩,(998703306766094507/1000000000000000000),(47314547925514213/125000000000000000),(63438485416268263/250000000000000000),(21107286052036717/125000000000000000)⟩
theorem valid3142 : certificate3142.Valid := by decide +kernel
theorem sound3142 : certificate3142.Sound := rat_cut_bin_certificate_sound certificate3142 profilesValid3142 numericValid3142 valid3142

def retention3143 : RatCutRetentionCertificate := ⟨(9/200),(23/500),(18926019003869354171/57638080845721486782),(1737519006586568387/500000000000000000),(13/10),(58568439509093475215480743626482486823/43437975164664209675000000000000000000),false,MergedCutProfiles.Batch482.profile19306,(fun _ => MergedCutProfiles.Batch482.profile19306)⟩
theorem profilesValid3143 : retention3143.ProfilesValid := by
  exact MergedCutProfiles.Batch482.valid19306
theorem numericValid3143 : retention3143.NumericValid := by decide +kernel
def certificate3143 : RatCutBinCertificate := ⟨⟨retention3143,(509465894602006859/250000000000000000),(19858540071699249/200000000000000000),(6138646236888365959/500000000000000000),(355794286259728427773/250000000000000000),(26537949725128253/20000000000000000)⟩,(998703306766094507/1000000000000000000),(86348919466448647/200000000000000000),(205623513879033471/1000000000000000000),(8547592423753043/50000000000000000)⟩
theorem valid3143 : certificate3143.Valid := by decide +kernel
theorem sound3143 : certificate3143.Sound := rat_cut_bin_certificate_sound certificate3143 profilesValid3143 numericValid3143 valid3143

def certificates : List RatCutBinCertificate := [certificate3132,certificate3133,certificate3134,certificate3135,certificate3136,certificate3137,certificate3138,certificate3139,certificate3140,certificate3141,certificate3142,certificate3143]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3132,List.forall_mem_cons.mpr ⟨sound3133,List.forall_mem_cons.mpr ⟨sound3134,List.forall_mem_cons.mpr ⟨sound3135,List.forall_mem_cons.mpr ⟨sound3136,List.forall_mem_cons.mpr ⟨sound3137,List.forall_mem_cons.mpr ⟨sound3138,List.forall_mem_cons.mpr ⟨sound3139,List.forall_mem_cons.mpr ⟨sound3140,List.forall_mem_cons.mpr ⟨sound3141,List.forall_mem_cons.mpr ⟨sound3142,List.forall_mem_cons.mpr ⟨sound3143,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch261
