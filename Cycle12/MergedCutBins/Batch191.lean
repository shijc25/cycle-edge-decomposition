import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch353
import Cycle12.MergedCutProfiles.Batch354
import Cycle12.MergedCutProfiles.Batch355

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch191

def retention2292 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1053650323000000000/59659751619044898567),(933877555226453527/1000000000000000000),(29/10),(2818756232008937911347/1280000000000000000000),true,MergedCutProfiles.Batch353.profile14148,![MergedCutProfiles.Batch353.profile14148,MergedCutProfiles.Batch353.profile14149,MergedCutProfiles.Batch353.profile14150,MergedCutProfiles.Batch353.profile14151,MergedCutProfiles.Batch353.profile14152,MergedCutProfiles.Batch353.profile14153,MergedCutProfiles.Batch353.profile14154,MergedCutProfiles.Batch353.profile14140,MergedCutProfiles.Batch353.profile14155,MergedCutProfiles.Batch353.profile14156,MergedCutProfiles.Batch353.profile14130,MergedCutProfiles.Batch353.profile14157,MergedCutProfiles.Batch353.profile14158,MergedCutProfiles.Batch353.profile14159,MergedCutProfiles.Batch354.profile14160,MergedCutProfiles.Batch354.profile14161]⟩
theorem profilesValid2292 : retention2292.ProfilesValid := by
  change ∀ j : Fin 16, (retention2292.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch353.valid14148
  · exact MergedCutProfiles.Batch353.valid14149
  · exact MergedCutProfiles.Batch353.valid14150
  · exact MergedCutProfiles.Batch353.valid14151
  · exact MergedCutProfiles.Batch353.valid14152
  · exact MergedCutProfiles.Batch353.valid14153
  · exact MergedCutProfiles.Batch353.valid14154
  · exact MergedCutProfiles.Batch353.valid14140
  · exact MergedCutProfiles.Batch353.valid14155
  · exact MergedCutProfiles.Batch353.valid14156
  · exact MergedCutProfiles.Batch353.valid14130
  · exact MergedCutProfiles.Batch353.valid14157
  · exact MergedCutProfiles.Batch353.valid14158
  · exact MergedCutProfiles.Batch353.valid14159
  · exact MergedCutProfiles.Batch354.valid14160
  · exact MergedCutProfiles.Batch354.valid14161
theorem numericValid2292 : retention2292.NumericValid := by decide +kernel
def certificate2292 : RatCutBinCertificate := ⟨⟨retention2292,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(1080877387676371427/500000000000000000)⟩,(997203749536676761/1000000000000000000),(191409932143286389/500000000000000000),(62399450846900197/250000000000000000),(72712634023882549/500000000000000000)⟩
theorem valid2292 : certificate2292.Valid := by decide +kernel
theorem sound2292 : certificate2292.Sound := rat_cut_bin_certificate_sound certificate2292 profilesValid2292 numericValid2292 valid2292

def retention2293 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1221706908821520214/59659751619044898567),(1053650323/1000000000),(53/20),(3497518508181296231/1600000000000000000),true,MergedCutProfiles.Batch354.profile14162,![MergedCutProfiles.Batch354.profile14162,MergedCutProfiles.Batch354.profile14163,MergedCutProfiles.Batch354.profile14164,MergedCutProfiles.Batch354.profile14165,MergedCutProfiles.Batch354.profile14166,MergedCutProfiles.Batch354.profile14167,MergedCutProfiles.Batch353.profile14126,MergedCutProfiles.Batch354.profile14168,MergedCutProfiles.Batch354.profile14169,MergedCutProfiles.Batch354.profile14170,MergedCutProfiles.Batch354.profile14171,MergedCutProfiles.Batch354.profile14172,MergedCutProfiles.Batch354.profile14173,MergedCutProfiles.Batch354.profile14174,MergedCutProfiles.Batch354.profile14175,MergedCutProfiles.Batch354.profile14176]⟩
theorem profilesValid2293 : retention2293.ProfilesValid := by
  change ∀ j : Fin 16, (retention2293.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch354.valid14162
  · exact MergedCutProfiles.Batch354.valid14163
  · exact MergedCutProfiles.Batch354.valid14164
  · exact MergedCutProfiles.Batch354.valid14165
  · exact MergedCutProfiles.Batch354.valid14166
  · exact MergedCutProfiles.Batch354.valid14167
  · exact MergedCutProfiles.Batch353.valid14126
  · exact MergedCutProfiles.Batch354.valid14168
  · exact MergedCutProfiles.Batch354.valid14169
  · exact MergedCutProfiles.Batch354.valid14170
  · exact MergedCutProfiles.Batch354.valid14171
  · exact MergedCutProfiles.Batch354.valid14172
  · exact MergedCutProfiles.Batch354.valid14173
  · exact MergedCutProfiles.Batch354.valid14174
  · exact MergedCutProfiles.Batch354.valid14175
  · exact MergedCutProfiles.Batch354.valid14176
theorem numericValid2293 : retention2293.NumericValid := by decide +kernel
def certificate2293 : RatCutBinCertificate := ⟨⟨retention2293,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(268629151877280389/125000000000000000)⟩,(997203749536676761/1000000000000000000),(182445780453446569/500000000000000000),(66809342157124937/250000000000000000),(10462363391909327/62500000000000000)⟩
theorem valid2293 : certificate2293.Valid := by decide +kernel
theorem sound2293 : certificate2293.Sound := rat_cut_bin_certificate_sound certificate2293 profilesValid2293 numericValid2293 valid2293

def retention2294 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(3913521845445795907/59659751619044898567),(610853454410760107/500000000000000000),(47/20),(1284181790151810897091/640000000000000000000),true,MergedCutProfiles.Batch354.profile14177,![MergedCutProfiles.Batch354.profile14177,MergedCutProfiles.Batch354.profile14178,MergedCutProfiles.Batch354.profile14179,MergedCutProfiles.Batch354.profile14180,MergedCutProfiles.Batch354.profile14176,MergedCutProfiles.Batch354.profile14181,MergedCutProfiles.Batch354.profile14182,MergedCutProfiles.Batch354.profile14183,MergedCutProfiles.Batch354.profile14184,MergedCutProfiles.Batch354.profile14185,MergedCutProfiles.Batch354.profile14186,MergedCutProfiles.Batch354.profile14187,MergedCutProfiles.Batch354.profile14188,MergedCutProfiles.Batch354.profile14189,MergedCutProfiles.Batch354.profile14190,MergedCutProfiles.Batch354.profile14191]⟩
theorem profilesValid2294 : retention2294.ProfilesValid := by
  change ∀ j : Fin 16, (retention2294.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch354.valid14177
  · exact MergedCutProfiles.Batch354.valid14178
  · exact MergedCutProfiles.Batch354.valid14179
  · exact MergedCutProfiles.Batch354.valid14180
  · exact MergedCutProfiles.Batch354.valid14176
  · exact MergedCutProfiles.Batch354.valid14181
  · exact MergedCutProfiles.Batch354.valid14182
  · exact MergedCutProfiles.Batch354.valid14183
  · exact MergedCutProfiles.Batch354.valid14184
  · exact MergedCutProfiles.Batch354.valid14185
  · exact MergedCutProfiles.Batch354.valid14186
  · exact MergedCutProfiles.Batch354.valid14187
  · exact MergedCutProfiles.Batch354.valid14188
  · exact MergedCutProfiles.Batch354.valid14189
  · exact MergedCutProfiles.Batch354.valid14190
  · exact MergedCutProfiles.Batch354.valid14191
theorem numericValid2294 : retention2294.NumericValid := by decide +kernel
def certificate2294 : RatCutBinCertificate := ⟨⟨retention2294,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(986898692024974243/500000000000000000)⟩,(997203749536676761/1000000000000000000),(2989634644687233/8000000000000000),(129229581444254351/500000000000000000),(167408579898907033/1000000000000000000)⟩
theorem valid2294 : certificate2294.Valid := by decide +kernel
theorem sound2294 : certificate2294.Sound := rat_cut_bin_certificate_sound certificate2294 profilesValid2294 numericValid2294 valid2294

def retention2295 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(22104810726615435674/59659751619044898567),(3913521845445795907/1000000000000000000),(5/4),(315707984485900190882844096492730634839/250465398108530938048000000000000000000),false,MergedCutProfiles.Batch354.profile14192,(fun _ => MergedCutProfiles.Batch354.profile14192)⟩
theorem profilesValid2295 : retention2295.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14192
theorem numericValid2295 : retention2295.NumericValid := by decide +kernel
def certificate2295 : RatCutBinCertificate := ⟨⟨retention2295,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(1243072592506665371/1000000000000000000)⟩,(997203749536676761/1000000000000000000),(431902114622004477/1000000000000000000),(41098248604974893/200000000000000000),(169308065308744243/1000000000000000000)⟩
theorem valid2295 : certificate2295.Valid := by decide +kernel
theorem sound2295 : certificate2295.Sound := rat_cut_bin_certificate_sound certificate2295 profilesValid2295 numericValid2295 valid2295

def retention2296 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(29206886738072535053/59659751619044898567),(11052405363307717837/500000000000000000),1,(22339781657629686093610489991269592227/22104810726615435674000000000000000000),false,MergedCutProfiles.Batch354.profile14193,(fun _ => MergedCutProfiles.Batch354.profile14193)⟩
theorem profilesValid2296 : retention2296.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14193
theorem numericValid2296 : retention2296.NumericValid := by decide +kernel
def certificate2296 : RatCutBinCertificate := ⟨⟨retention2296,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(996699837444419057/1000000000000000000)⟩,(997203749536676761/1000000000000000000),(92688147757371193/200000000000000000),(90068790687603173/500000000000000000),(85652340290183063/500000000000000000)⟩
theorem valid2296 : certificate2296.Valid := by decide +kernel
theorem sound2296 : certificate2296.Sound := rat_cut_bin_certificate_sound certificate2296 profilesValid2296 numericValid2296 valid2296

def retention2297 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(9931315053835931003/19886583873014966189),(29206886738072535053/1000000000000000000),1,(45367075765053566535783921566600809/45635760528238336020312500000000000),false,MergedCutProfiles.Batch354.profile14194,(fun _ => MergedCutProfiles.Batch354.profile14194)⟩
theorem profilesValid2297 : retention2297.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14194
theorem numericValid2297 : retention2297.NumericValid := by decide +kernel
def certificate2297 : RatCutBinCertificate := ⟨⟨retention2297,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(196036481463504113/200000000000000000)⟩,(997203749536676761/1000000000000000000),(46724897221500519/100000000000000000),(177224383022199291/1000000000000000000),(167592964412734161/1000000000000000000)⟩
theorem valid2297 : certificate2297.Valid := by decide +kernel
theorem sound2297 : certificate2297.Sound := rat_cut_bin_certificate_sound certificate2297 profilesValid2297 numericValid2297 valid2297

def retention2298 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),(29793945161507793009/1000000000000000000),1,(39450991151860616668323494895332609241/39725260215343724012000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid2298 : retention2298.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid2298 : retention2298.NumericValid := by decide +kernel
def certificate2298 : RatCutBinCertificate := ⟨⟨retention2298,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(979165853230727381/1000000000000000000)⟩,(997203749536676761/1000000000000000000),(467488413105788473/1000000000000000000),(17704225671998859/100000000000000000),(20919983805850753/125000000000000000)⟩
theorem valid2298 : certificate2298.Valid := by decide +kernel
theorem sound2298 : certificate2298.Sound := rat_cut_bin_certificate_sound certificate2298 profilesValid2298 numericValid2298 valid2298

def retention2299 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(26069453965313457787/59659751619044898567),(1407927789106081393/250000000000000000),(21/20),(4826129391530537813218559756527428727/4399774340956504353125000000000000000),false,MergedCutProfiles.Batch354.profile14196,(fun _ => MergedCutProfiles.Batch354.profile14196)⟩
theorem profilesValid2299 : retention2299.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14196
theorem numericValid2299 : retention2299.NumericValid := by decide +kernel
def certificate2299 : RatCutBinCertificate := ⟨⟨retention2299,(469424246025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(108018566708551593/100000000000000000)⟩,(62300238564566759/62500000000000000),(55175691126917223/250000000000000000),(89130241440490549/200000000000000000),(389185730982803531/1000000000000000000)⟩
theorem valid2299 : certificate2299.Valid := by decide +kernel
theorem sound2299 : certificate2299.Sound := rat_cut_bin_certificate_sound certificate2299 profilesValid2299 numericValid2299 valid2299

def retention2300 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(29669470382488217939/59659751619044898567),(26069453965313457787/1000000000000000000),1,(2363259396647874346652811344640085823/2369950360483041617000000000000000000),false,MergedCutProfiles.Batch354.profile14197,(fun _ => MergedCutProfiles.Batch354.profile14197)⟩
theorem profilesValid2300 : retention2300.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14197
theorem numericValid2300 : retention2300.NumericValid := by decide +kernel
def certificate2300 : RatCutBinCertificate := ⟨⟨retention2300,(469424246025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(981254910648008609/1000000000000000000)⟩,(62300238564566759/62500000000000000),(242954160351561923/1000000000000000000),(826385392657797/2000000000000000),(97367046609395077/250000000000000000)⟩
theorem valid2300 : certificate2300.Valid := by decide +kernel
theorem sound2300 : certificate2300.Sound := rat_cut_bin_certificate_sound certificate2300 profilesValid2300 numericValid2300 valid2300

def retention2301 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),(29669470382488217939/1000000000000000000),1,(117854321408468154068162183329455788403/118677881529952871756000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid2301 : retention2301.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid2301 : retention2301.NumericValid := by decide +kernel
def certificate2301 : RatCutBinCertificate := ⟨⟨retention2301,(469424246025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(977138712099200313/1000000000000000000)⟩,(62300238564566759/62500000000000000),(243977605180717879/1000000000000000000),(205874699349961459/500000000000000000),(97060780555836273/250000000000000000)⟩
theorem valid2301 : certificate2301.Valid := by decide +kernel
theorem sound2301 : certificate2301.Sound := rat_cut_bin_certificate_sound certificate2301 profilesValid2301 numericValid2301 valid2301

def retention2302 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(777910149334702537/56544910216936768259),(770208068648220333/1000000000000000000),(17/5),(178443667139020102929/80000000000000000000),true,MergedCutProfiles.Batch354.profile14198,![MergedCutProfiles.Batch354.profile14198,MergedCutProfiles.Batch354.profile14199,MergedCutProfiles.Batch355.profile14200,MergedCutProfiles.Batch355.profile14201,MergedCutProfiles.Batch355.profile14202,MergedCutProfiles.Batch355.profile14203,MergedCutProfiles.Batch355.profile14204,MergedCutProfiles.Batch355.profile14205,MergedCutProfiles.Batch355.profile14206,MergedCutProfiles.Batch355.profile14207,MergedCutProfiles.Batch355.profile14208,MergedCutProfiles.Batch355.profile14209,MergedCutProfiles.Batch355.profile14210,MergedCutProfiles.Batch355.profile14211,MergedCutProfiles.Batch355.profile14212,MergedCutProfiles.Batch355.profile14213]⟩
theorem profilesValid2302 : retention2302.ProfilesValid := by
  change ∀ j : Fin 16, (retention2302.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch354.valid14198
  · exact MergedCutProfiles.Batch354.valid14199
  · exact MergedCutProfiles.Batch355.valid14200
  · exact MergedCutProfiles.Batch355.valid14201
  · exact MergedCutProfiles.Batch355.valid14202
  · exact MergedCutProfiles.Batch355.valid14203
  · exact MergedCutProfiles.Batch355.valid14204
  · exact MergedCutProfiles.Batch355.valid14205
  · exact MergedCutProfiles.Batch355.valid14206
  · exact MergedCutProfiles.Batch355.valid14207
  · exact MergedCutProfiles.Batch355.valid14208
  · exact MergedCutProfiles.Batch355.valid14209
  · exact MergedCutProfiles.Batch355.valid14210
  · exact MergedCutProfiles.Batch355.valid14211
  · exact MergedCutProfiles.Batch355.valid14212
  · exact MergedCutProfiles.Batch355.valid14213
theorem numericValid2302 : retention2302.NumericValid := by decide +kernel
def certificate2302 : RatCutBinCertificate := ⟨⟨retention2302,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(2181364227668320429/1000000000000000000)⟩,(249276745144070473/250000000000000000),(413597567462544441/1000000000000000000),(55313009384462703/250000000000000000),(14203632994235123/125000000000000000)⟩
theorem valid2302 : certificate2302.Valid := by decide +kernel
theorem sound2302 : certificate2302.Sound := rat_cut_bin_certificate_sound certificate2302 profilesValid2302 numericValid2302 valid2302

def retention2303 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(921282437067070239/56544910216936768259),(777910149334702537/1000000000000000000),(17/5),(2844152391096114028277/1280000000000000000000),true,MergedCutProfiles.Batch355.profile14214,![MergedCutProfiles.Batch355.profile14214,MergedCutProfiles.Batch355.profile14215,MergedCutProfiles.Batch355.profile14216,MergedCutProfiles.Batch355.profile14217,MergedCutProfiles.Batch355.profile14218,MergedCutProfiles.Batch355.profile14219,MergedCutProfiles.Batch355.profile14220,MergedCutProfiles.Batch355.profile14221,MergedCutProfiles.Batch355.profile14222,MergedCutProfiles.Batch355.profile14223,MergedCutProfiles.Batch355.profile14210,MergedCutProfiles.Batch355.profile14224,MergedCutProfiles.Batch355.profile14225,MergedCutProfiles.Batch355.profile14226,MergedCutProfiles.Batch355.profile14227,MergedCutProfiles.Batch355.profile14228]⟩
theorem profilesValid2303 : retention2303.ProfilesValid := by
  change ∀ j : Fin 16, (retention2303.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch355.valid14214
  · exact MergedCutProfiles.Batch355.valid14215
  · exact MergedCutProfiles.Batch355.valid14216
  · exact MergedCutProfiles.Batch355.valid14217
  · exact MergedCutProfiles.Batch355.valid14218
  · exact MergedCutProfiles.Batch355.valid14219
  · exact MergedCutProfiles.Batch355.valid14220
  · exact MergedCutProfiles.Batch355.valid14221
  · exact MergedCutProfiles.Batch355.valid14222
  · exact MergedCutProfiles.Batch355.valid14223
  · exact MergedCutProfiles.Batch355.valid14210
  · exact MergedCutProfiles.Batch355.valid14224
  · exact MergedCutProfiles.Batch355.valid14225
  · exact MergedCutProfiles.Batch355.valid14226
  · exact MergedCutProfiles.Batch355.valid14227
  · exact MergedCutProfiles.Batch355.valid14228
theorem numericValid2303 : retention2303.NumericValid := by decide +kernel
def certificate2303 : RatCutBinCertificate := ⟨⟨retention2303,(2053875624703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(2172812467007510641/1000000000000000000)⟩,(249276745144070473/250000000000000000),(51642639052878759/125000000000000000),(221655263651936089/1000000000000000000),(113698658846132793/1000000000000000000)⟩
theorem valid2303 : certificate2303.Valid := by decide +kernel
theorem sound2303 : certificate2303.Sound := rat_cut_bin_certificate_sound certificate2303 profilesValid2303 numericValid2303 valid2303

def certificates : List RatCutBinCertificate := [certificate2292,certificate2293,certificate2294,certificate2295,certificate2296,certificate2297,certificate2298,certificate2299,certificate2300,certificate2301,certificate2302,certificate2303]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2292,List.forall_mem_cons.mpr ⟨sound2293,List.forall_mem_cons.mpr ⟨sound2294,List.forall_mem_cons.mpr ⟨sound2295,List.forall_mem_cons.mpr ⟨sound2296,List.forall_mem_cons.mpr ⟨sound2297,List.forall_mem_cons.mpr ⟨sound2298,List.forall_mem_cons.mpr ⟨sound2299,List.forall_mem_cons.mpr ⟨sound2300,List.forall_mem_cons.mpr ⟨sound2301,List.forall_mem_cons.mpr ⟨sound2302,List.forall_mem_cons.mpr ⟨sound2303,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch191
