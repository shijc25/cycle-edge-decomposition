import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch055
import Cycle12.MergedCutProfiles.Batch056
import Cycle12.MergedCutProfiles.Batch057

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch028

def retention336 : RatCutRetentionCertificate := ⟨(33/1000),(67/2000),(1/2),(23058066492027228411/1000000000000000000),1,(317245643962072523591194573788162843/320250923500378172375000000000000000),false,MergedCutProfiles.Batch055.profile2211,(fun _ => MergedCutProfiles.Batch055.profile2211)⟩
theorem profilesValid336 : retention336.ProfilesValid := by
  exact MergedCutProfiles.Batch055.valid2211
theorem numericValid336 : retention336.NumericValid := by decide +kernel
def certificate336 : RatCutBinCertificate := ⟨⟨retention336,(600580117281020813/250000000000000000),(49732941177381449/1000000000000000000),(5113447298603889531/500000000000000000),(47666931099808140293/100000000000000000),(978933427641718507/1000000000000000000)⟩,(995201726054026297/1000000000000000000),(206561398313156361/500000000000000000),(110835727046006781/500000000000000000),(25893259115410077/125000000000000000)⟩
theorem valid336 : certificate336.Valid := by decide +kernel
theorem sound336 : certificate336.Sound := rat_cut_bin_certificate_sound certificate336 profilesValid336 numericValid336 valid336

def retention337 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(377202614002210654/22507681237218344607),(29877434772452329/40000000000000000),(69/20),(17625979412472460161/8000000000000000000),true,MergedCutProfiles.Batch055.profile2214,![MergedCutProfiles.Batch055.profile2214,MergedCutProfiles.Batch055.profile2215,MergedCutProfiles.Batch055.profile2216,MergedCutProfiles.Batch055.profile2217,MergedCutProfiles.Batch055.profile2218,MergedCutProfiles.Batch055.profile2219,MergedCutProfiles.Batch055.profile2220,MergedCutProfiles.Batch055.profile2221,MergedCutProfiles.Batch055.profile2222,MergedCutProfiles.Batch055.profile2223,MergedCutProfiles.Batch055.profile2224,MergedCutProfiles.Batch055.profile2225,MergedCutProfiles.Batch055.profile2226,MergedCutProfiles.Batch055.profile2227,MergedCutProfiles.Batch055.profile2228,MergedCutProfiles.Batch055.profile2229]⟩
theorem profilesValid337 : retention337.ProfilesValid := by
  change ∀ j : Fin 16, (retention337.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch055.valid2214
  · exact MergedCutProfiles.Batch055.valid2215
  · exact MergedCutProfiles.Batch055.valid2216
  · exact MergedCutProfiles.Batch055.valid2217
  · exact MergedCutProfiles.Batch055.valid2218
  · exact MergedCutProfiles.Batch055.valid2219
  · exact MergedCutProfiles.Batch055.valid2220
  · exact MergedCutProfiles.Batch055.valid2221
  · exact MergedCutProfiles.Batch055.valid2222
  · exact MergedCutProfiles.Batch055.valid2223
  · exact MergedCutProfiles.Batch055.valid2224
  · exact MergedCutProfiles.Batch055.valid2225
  · exact MergedCutProfiles.Batch055.valid2226
  · exact MergedCutProfiles.Batch055.valid2227
  · exact MergedCutProfiles.Batch055.valid2228
  · exact MergedCutProfiles.Batch055.valid2229
theorem numericValid337 : retention337.NumericValid := by decide +kernel
def certificate337 : RatCutBinCertificate := ⟨⟨retention337,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(2168582634604693589/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(107172779505755977/250000000000000000),(208198967776599883/1000000000000000000),(13087311540640837/125000000000000000)⟩
theorem valid337 : certificate337.Valid := by decide +kernel
theorem sound337 : certificate337.Sound := rat_cut_bin_certificate_sound certificate337 profilesValid337 numericValid337 valid337

def retention338 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(433584677961365633/22507681237218344607),(188601307001105327/250000000000000000),(69/20),(702548597324325224951/320000000000000000000),true,MergedCutProfiles.Batch055.profile2230,![MergedCutProfiles.Batch055.profile2230,MergedCutProfiles.Batch055.profile2231,MergedCutProfiles.Batch055.profile2232,MergedCutProfiles.Batch055.profile2233,MergedCutProfiles.Batch055.profile2234,MergedCutProfiles.Batch055.profile2235,MergedCutProfiles.Batch055.profile2236,MergedCutProfiles.Batch055.profile2237,MergedCutProfiles.Batch055.profile2238,MergedCutProfiles.Batch055.profile2239,MergedCutProfiles.Batch056.profile2240,MergedCutProfiles.Batch056.profile2241,MergedCutProfiles.Batch055.profile2228,MergedCutProfiles.Batch055.profile2229,MergedCutProfiles.Batch056.profile2242,MergedCutProfiles.Batch056.profile2243]⟩
theorem profilesValid338 : retention338.ProfilesValid := by
  change ∀ j : Fin 16, (retention338.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch055.valid2230
  · exact MergedCutProfiles.Batch055.valid2231
  · exact MergedCutProfiles.Batch055.valid2232
  · exact MergedCutProfiles.Batch055.valid2233
  · exact MergedCutProfiles.Batch055.valid2234
  · exact MergedCutProfiles.Batch055.valid2235
  · exact MergedCutProfiles.Batch055.valid2236
  · exact MergedCutProfiles.Batch055.valid2237
  · exact MergedCutProfiles.Batch055.valid2238
  · exact MergedCutProfiles.Batch055.valid2239
  · exact MergedCutProfiles.Batch056.valid2240
  · exact MergedCutProfiles.Batch056.valid2241
  · exact MergedCutProfiles.Batch055.valid2228
  · exact MergedCutProfiles.Batch055.valid2229
  · exact MergedCutProfiles.Batch056.valid2242
  · exact MergedCutProfiles.Batch056.valid2243
theorem numericValid338 : retention338.NumericValid := by decide +kernel
def certificate338 : RatCutBinCertificate := ⟨⟨retention338,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(2160799589390193849/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(107027319376317137/250000000000000000),(208692182296361997/1000000000000000000),(104847023927992957/1000000000000000000)⟩
theorem valid338 : certificate338.Valid := by decide +kernel
theorem sound338 : certificate338.Sound := rat_cut_bin_certificate_sound certificate338 profilesValid338 numericValid338 valid338

def retention339 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(14832291000000000/682050946582374079),(433584677961365633/500000000000000000),(61/20),(1391766593576709992841/640000000000000000000),true,MergedCutProfiles.Batch056.profile2244,![MergedCutProfiles.Batch056.profile2244,MergedCutProfiles.Batch056.profile2245,MergedCutProfiles.Batch056.profile2246,MergedCutProfiles.Batch056.profile2247,MergedCutProfiles.Batch056.profile2248,MergedCutProfiles.Batch056.profile2249,MergedCutProfiles.Batch056.profile2250,MergedCutProfiles.Batch055.profile2238,MergedCutProfiles.Batch056.profile2251,MergedCutProfiles.Batch055.profile2226,MergedCutProfiles.Batch056.profile2252,MergedCutProfiles.Batch056.profile2253,MergedCutProfiles.Batch056.profile2254,MergedCutProfiles.Batch056.profile2255,MergedCutProfiles.Batch056.profile2256,MergedCutProfiles.Batch056.profile2257]⟩
theorem profilesValid339 : retention339.ProfilesValid := by
  change ∀ j : Fin 16, (retention339.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch056.valid2244
  · exact MergedCutProfiles.Batch056.valid2245
  · exact MergedCutProfiles.Batch056.valid2246
  · exact MergedCutProfiles.Batch056.valid2247
  · exact MergedCutProfiles.Batch056.valid2248
  · exact MergedCutProfiles.Batch056.valid2249
  · exact MergedCutProfiles.Batch056.valid2250
  · exact MergedCutProfiles.Batch055.valid2238
  · exact MergedCutProfiles.Batch056.valid2251
  · exact MergedCutProfiles.Batch055.valid2226
  · exact MergedCutProfiles.Batch056.valid2252
  · exact MergedCutProfiles.Batch056.valid2253
  · exact MergedCutProfiles.Batch056.valid2254
  · exact MergedCutProfiles.Batch056.valid2255
  · exact MergedCutProfiles.Batch056.valid2256
  · exact MergedCutProfiles.Batch056.valid2257
theorem numericValid339 : retention339.NumericValid := by decide +kernel
def certificate339 : RatCutBinCertificate := ⟨⟨retention339,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(1071994825275977791/500000000000000000)⟩,(995878319576412531/1000000000000000000),(3153154868385497/7812500000000000),(230196538575836053/1000000000000000000),(25445204798938259/200000000000000000)⟩
theorem valid339 : certificate339.Valid := by decide +kernel
theorem sound339 : certificate339.Sound := rat_cut_bin_certificate_sound certificate339 profilesValid339 numericValid339 valid339

def retention340 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(493459808486661983/22507681237218344607),(489465603/500000000),(11/4),(34652429259050414691/16000000000000000000),true,MergedCutProfiles.Batch056.profile2244,![MergedCutProfiles.Batch056.profile2244,MergedCutProfiles.Batch056.profile2258,MergedCutProfiles.Batch056.profile2259,MergedCutProfiles.Batch056.profile2247,MergedCutProfiles.Batch056.profile2260,MergedCutProfiles.Batch056.profile2261,MergedCutProfiles.Batch055.profile2237,MergedCutProfiles.Batch056.profile2262,MergedCutProfiles.Batch056.profile2263,MergedCutProfiles.Batch056.profile2264,MergedCutProfiles.Batch056.profile2265,MergedCutProfiles.Batch056.profile2266,MergedCutProfiles.Batch056.profile2267,MergedCutProfiles.Batch056.profile2268,MergedCutProfiles.Batch056.profile2269,MergedCutProfiles.Batch056.profile2270]⟩
theorem profilesValid340 : retention340.ProfilesValid := by
  change ∀ j : Fin 16, (retention340.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch056.valid2244
  · exact MergedCutProfiles.Batch056.valid2258
  · exact MergedCutProfiles.Batch056.valid2259
  · exact MergedCutProfiles.Batch056.valid2247
  · exact MergedCutProfiles.Batch056.valid2260
  · exact MergedCutProfiles.Batch056.valid2261
  · exact MergedCutProfiles.Batch055.valid2237
  · exact MergedCutProfiles.Batch056.valid2262
  · exact MergedCutProfiles.Batch056.valid2263
  · exact MergedCutProfiles.Batch056.valid2264
  · exact MergedCutProfiles.Batch056.valid2265
  · exact MergedCutProfiles.Batch056.valid2266
  · exact MergedCutProfiles.Batch056.valid2267
  · exact MergedCutProfiles.Batch056.valid2268
  · exact MergedCutProfiles.Batch056.valid2269
  · exact MergedCutProfiles.Batch056.valid2270
theorem numericValid340 : retention340.NumericValid := by decide +kernel
def certificate340 : RatCutBinCertificate := ⟨⟨retention340,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(106907276170949677/50000000000000000)⟩,(995878319576412531/1000000000000000000),(383368008127858839/1000000000000000000),(249071909160840623/1000000000000000000),(149541229657786513/1000000000000000000)⟩
theorem valid340 : certificate340.Valid := by decide +kernel
theorem sound340 : certificate340.Sound := rat_cut_bin_certificate_sound certificate340 profilesValid340 numericValid340 valid340

def retention341 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(181695540818514165/7502560412406114869),(493459808486661983/500000000000000000),(27/10),(1375481611760649496379/640000000000000000000),true,MergedCutProfiles.Batch056.profile2271,![MergedCutProfiles.Batch056.profile2271,MergedCutProfiles.Batch056.profile2272,MergedCutProfiles.Batch056.profile2273,MergedCutProfiles.Batch056.profile2274,MergedCutProfiles.Batch056.profile2275,MergedCutProfiles.Batch056.profile2276,MergedCutProfiles.Batch056.profile2277,MergedCutProfiles.Batch056.profile2278,MergedCutProfiles.Batch056.profile2264,MergedCutProfiles.Batch056.profile2265,MergedCutProfiles.Batch056.profile2279,MergedCutProfiles.Batch057.profile2280,MergedCutProfiles.Batch057.profile2281,MergedCutProfiles.Batch057.profile2282,MergedCutProfiles.Batch057.profile2283,MergedCutProfiles.Batch057.profile2284]⟩
theorem profilesValid341 : retention341.ProfilesValid := by
  change ∀ j : Fin 16, (retention341.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch056.valid2271
  · exact MergedCutProfiles.Batch056.valid2272
  · exact MergedCutProfiles.Batch056.valid2273
  · exact MergedCutProfiles.Batch056.valid2274
  · exact MergedCutProfiles.Batch056.valid2275
  · exact MergedCutProfiles.Batch056.valid2276
  · exact MergedCutProfiles.Batch056.valid2277
  · exact MergedCutProfiles.Batch056.valid2278
  · exact MergedCutProfiles.Batch056.valid2264
  · exact MergedCutProfiles.Batch056.valid2265
  · exact MergedCutProfiles.Batch056.valid2279
  · exact MergedCutProfiles.Batch057.valid2280
  · exact MergedCutProfiles.Batch057.valid2281
  · exact MergedCutProfiles.Batch057.valid2282
  · exact MergedCutProfiles.Batch057.valid2283
  · exact MergedCutProfiles.Batch057.valid2284
theorem numericValid341 : retention341.NumericValid := by decide +kernel
def certificate341 : RatCutBinCertificate := ⟨⟨retention341,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(1061030544520322253/500000000000000000)⟩,(995878319576412531/1000000000000000000),(192461729571446349/500000000000000000),(61895963990412857/250000000000000000),(37387295860348123/250000000000000000)⟩
theorem valid341 : certificate341.Valid := by decide +kernel
theorem sound341 : certificate341.Sound := rat_cut_bin_certificate_sound certificate341 profilesValid341 numericValid341 valid341

def retention342 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(2514727418980686383/45015362474436689214),(109017324491108499/100000000000000000),(5/2),(65020008415176585079/32000000000000000000),true,MergedCutProfiles.Batch057.profile2285,![MergedCutProfiles.Batch057.profile2285,MergedCutProfiles.Batch057.profile2286,MergedCutProfiles.Batch055.profile2223,MergedCutProfiles.Batch057.profile2287,MergedCutProfiles.Batch057.profile2288,MergedCutProfiles.Batch057.profile2289,MergedCutProfiles.Batch057.profile2290,MergedCutProfiles.Batch057.profile2291,MergedCutProfiles.Batch057.profile2292,MergedCutProfiles.Batch057.profile2293,MergedCutProfiles.Batch057.profile2294,MergedCutProfiles.Batch057.profile2295,MergedCutProfiles.Batch057.profile2296,MergedCutProfiles.Batch057.profile2297,MergedCutProfiles.Batch057.profile2298,MergedCutProfiles.Batch057.profile2299]⟩
theorem profilesValid342 : retention342.ProfilesValid := by
  change ∀ j : Fin 16, (retention342.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch057.valid2285
  · exact MergedCutProfiles.Batch057.valid2286
  · exact MergedCutProfiles.Batch055.valid2223
  · exact MergedCutProfiles.Batch057.valid2287
  · exact MergedCutProfiles.Batch057.valid2288
  · exact MergedCutProfiles.Batch057.valid2289
  · exact MergedCutProfiles.Batch057.valid2290
  · exact MergedCutProfiles.Batch057.valid2291
  · exact MergedCutProfiles.Batch057.valid2292
  · exact MergedCutProfiles.Batch057.valid2293
  · exact MergedCutProfiles.Batch057.valid2294
  · exact MergedCutProfiles.Batch057.valid2295
  · exact MergedCutProfiles.Batch057.valid2296
  · exact MergedCutProfiles.Batch057.valid2297
  · exact MergedCutProfiles.Batch057.valid2298
  · exact MergedCutProfiles.Batch057.valid2299
theorem numericValid342 : retention342.NumericValid := by decide +kernel
def certificate342 : RatCutBinCertificate := ⟨⟨retention342,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(100337795358051919/50000000000000000)⟩,(995878319576412531/1000000000000000000),(97616842163124453/250000000000000000),(242331080359366879/1000000000000000000),(149548083633386101/1000000000000000000)⟩
theorem valid342 : certificate342.Valid := by decide +kernel
theorem sound342 : certificate342.Sound := rat_cut_bin_certificate_sound certificate342 profilesValid342 numericValid342 valid342

def retention343 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(417764847723305173/1364101893164748158),(2514727418980686383/1000000000000000000),(29/20),(5610115805841384387085150297522722676671/4023563870369098212800000000000000000000),false,MergedCutProfiles.Batch057.profile2300,(fun _ => MergedCutProfiles.Batch057.profile2300)⟩
theorem profilesValid343 : retention343.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2300
theorem numericValid343 : retention343.NumericValid := by decide +kernel
def certificate343 : RatCutBinCertificate := ⟨⟨retention343,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(1379746009173060809/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(3417140247395817/7812500000000000),(100457692757197897/500000000000000000),(75457999587179173/500000000000000000)⟩
theorem valid343 : certificate343.Valid := by decide +kernel
theorem sound343 : certificate343.Sound := rat_cut_bin_certificate_sound certificate343 profilesValid343 numericValid343 valid343

def retention344 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(10894292520670697977/22507681237218344607),(13786239974869070709/1000000000000000000),(21/20),(22750468158422994745144745386792565551439/22057983959790513134400000000000000000000),false,MergedCutProfiles.Batch057.profile2301,(fun _ => MergedCutProfiles.Batch057.profile2301)⟩
theorem profilesValid344 : retention344.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2301
theorem numericValid344 : retention344.NumericValid := by decide +kernel
def certificate344 : RatCutBinCertificate := ⟨⟨retention344,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(1020844029372554021/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(240399040866868431/500000000000000000),(10444349523515117/62500000000000000),(75797149023081/500000000000000)⟩
theorem valid344 : certificate344.Valid := by decide +kernel
theorem sound344 : certificate344.Sound := rat_cut_bin_certificate_sound certificate344 profilesValid344 numericValid344 valid344

def retention345 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(22448800956679081595/45015362474436689214),(10894292520670697977/500000000000000000),1,(4223851682715712483498199574273929/4255583015886991397265625000000000),false,MergedCutProfiles.Batch057.profile2302,(fun _ => MergedCutProfiles.Batch057.profile2302)⟩
theorem profilesValid345 : retention345.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2302
theorem numericValid345 : retention345.NumericValid := by decide +kernel
def certificate345 : RatCutBinCertificate := ⟨⟨retention345,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(982496212889532583/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(490167210501947233/1000000000000000000),(80169616071074527/500000000000000000),(3001988589723993/20000000000000000)⟩
theorem valid345 : certificate345.Valid := by decide +kernel
theorem sound345 : certificate345.Sound := rat_cut_bin_certificate_sound certificate345 profilesValid345 numericValid345 valid345

def retention346 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(1/2),(4489760191335816319/200000000000000000),1,(88926173589492240123933707700989303979/89795203826716326380000000000000000000),false,MergedCutProfiles.Batch057.profile2303,(fun _ => MergedCutProfiles.Batch057.profile2303)⟩
theorem profilesValid346 : retention346.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2303
theorem numericValid346 : retention346.NumericValid := by decide +kernel
def certificate346 : RatCutBinCertificate := ⟨⟨retention346,(2016121258404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(980274701576694827/1000000000000000000)⟩,(995878319576412531/1000000000000000000),(30675052878699949/62500000000000000),(159887855422922427/1000000000000000000),(14954278504054919/100000000000000000)⟩
theorem valid346 : certificate346.Valid := by decide +kernel
theorem sound346 : certificate346.Sound := rat_cut_bin_certificate_sound certificate346 profilesValid346 numericValid346 valid346

def retention347 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(19104349057132466741/45015362474436689214),(467021589055879003/125000000000000000),(5/4),(17202144427376217653291952176382263719/14944690849788128096000000000000000000),false,MergedCutProfiles.Batch057.profile2304,(fun _ => MergedCutProfiles.Batch057.profile2304)⟩
theorem profilesValid347 : retention347.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2304
theorem numericValid347 : retention347.NumericValid := by decide +kernel
def certificate347 : RatCutBinCertificate := ⟨⟨retention347,(2407250113404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(1136057871916202447/1000000000000000000)⟩,(497539252454225241/500000000000000000),(354531350783546997/1000000000000000000),(34728655210633073/125000000000000000),(52561128853986887/250000000000000000)⟩
theorem valid347 : certificate347.Valid := by decide +kernel
theorem sound347 : certificate347.Sound := rat_cut_bin_certificate_sound certificate347 profilesValid347 numericValid347 valid347

def certificates : List RatCutBinCertificate := [certificate336,certificate337,certificate338,certificate339,certificate340,certificate341,certificate342,certificate343,certificate344,certificate345,certificate346,certificate347]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound336,List.forall_mem_cons.mpr ⟨sound337,List.forall_mem_cons.mpr ⟨sound338,List.forall_mem_cons.mpr ⟨sound339,List.forall_mem_cons.mpr ⟨sound340,List.forall_mem_cons.mpr ⟨sound341,List.forall_mem_cons.mpr ⟨sound342,List.forall_mem_cons.mpr ⟨sound343,List.forall_mem_cons.mpr ⟨sound344,List.forall_mem_cons.mpr ⟨sound345,List.forall_mem_cons.mpr ⟨sound346,List.forall_mem_cons.mpr ⟨sound347,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch028
