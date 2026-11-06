import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch049
import Cycle12.MergedCutProfiles.Batch336
import Cycle12.MergedCutProfiles.Batch337
import Cycle12.MergedCutProfiles.Batch338

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch182

def retention2184 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(51274596539921991755/102689025408210014927),(50766927267249496787/1000000000000000000),1,(10132024336097616064987338654201146049/10153385453449899357400000000000000000),false,MergedCutProfiles.Batch336.profile13472,(fun _ => MergedCutProfiles.Batch336.profile13472)⟩
theorem profilesValid2184 : retention2184.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13472
theorem numericValid2184 : retention2184.NumericValid := by decide +kernel
def certificate2184 : RatCutBinCertificate := ⟨⟨retention2184,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(494448327926044319/500000000000000000)⟩,(249536954702024071/250000000000000000),(232630524306620987/500000000000000000),(178741204218721819/1000000000000000000),(34610950913758521/200000000000000000)⟩
theorem valid2184 : certificate2184.Valid := by decide +kernel
theorem sound2184 : certificate2184.Sound := rat_cut_bin_certificate_sound certificate2184 profilesValid2184 numericValid2184 valid2184

def retention2185 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),(10254919307984398351/200000000000000000),1,(204399964545686431374136372079340638179/205098386159687967020000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid2185 : retention2185.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid2185 : retention2185.NumericValid := by decide +kernel
def certificate2185 : RatCutBinCertificate := ⟨⟨retention2185,(247890140746105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(987595197402530967/1000000000000000000)⟩,(249536954702024071/250000000000000000),(232896979910373341/500000000000000000),(178333751735863611/1000000000000000000),(21558748247817123/125000000000000000)⟩
theorem valid2185 : certificate2185.Valid := by decide +kernel
theorem sound2185 : certificate2185.Sound := rat_cut_bin_certificate_sound certificate2185 profilesValid2185 numericValid2185 valid2185

def retention2186 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(43346803034654899776/102689025408210014927),(1094312402224019879/200000000000000000),(11/10),(99959845620349347569969749137700230079/87544992177921590320000000000000000000),false,MergedCutProfiles.Batch336.profile13473,(fun _ => MergedCutProfiles.Batch336.profile13473)⟩
theorem profilesValid2186 : retention2186.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13473
theorem numericValid2186 : retention2186.NumericValid := by decide +kernel
def certificate2186 : RatCutBinCertificate := ⟨⟨retention2186,(285426218246105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(282603149379210779/250000000000000000)⟩,(997867331086661767/1000000000000000000),(213406090474914151/1000000000000000000),(456762607629072339/1000000000000000000),(80004337469737989/200000000000000000)⟩
theorem valid2186 : certificate2186.Valid := by decide +kernel
theorem sound2186 : certificate2186.Sound := rat_cut_bin_certificate_sound certificate2186 profilesValid2186 numericValid2186 valid2186

def retention2187 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(50827535564150105227/102689025408210014927),(677293797416482809/15625000000000000),1,(43592668992251363332279198128371149127/43346803034654899776000000000000000000),false,MergedCutProfiles.Batch336.profile13474,(fun _ => MergedCutProfiles.Batch336.profile13474)⟩
theorem profilesValid2187 : retention2187.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13474
theorem numericValid2187 : retention2187.NumericValid := by decide +kernel
def certificate2187 : RatCutBinCertificate := ⟨⟨retention2187,(285426218246105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(995309838176635747/1000000000000000000)⟩,(997867331086661767/1000000000000000000),(12118685247882091/50000000000000000),(51751645032219111/125000000000000000),(100488403297371853/250000000000000000)⟩
theorem valid2187 : certificate2187.Valid := by decide +kernel
theorem sound2187 : certificate2187.Sound := rat_cut_bin_certificate_sound certificate2187 profilesValid2187 numericValid2187 valid2187

def retention2188 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(51335810919791606280/102689025408210014927),(50827535564150105227/1000000000000000000),1,(10132161670721588403555756998682564657/10165507112830021045400000000000000000),false,MergedCutProfiles.Batch336.profile13475,(fun _ => MergedCutProfiles.Batch336.profile13475)⟩
theorem profilesValid2188 : retention2188.ProfilesValid := by
  exact MergedCutProfiles.Batch336.valid13475
theorem numericValid2188 : retention2188.NumericValid := by decide +kernel
def certificate2188 : RatCutBinCertificate := ⟨⟨retention2188,(285426218246105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(493178759677312679/500000000000000000)⟩,(997867331086661767/1000000000000000000),(244573522608215819/1000000000000000000),(410910964051943809/1000000000000000000),(396733765160007639/1000000000000000000)⟩
theorem valid2188 : certificate2188.Valid := by decide +kernel
theorem sound2188 : certificate2188.Sound := rat_cut_bin_certificate_sound certificate2188 profilesValid2188 numericValid2188 valid2188

def retention2189 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),(1283395272994790157/25000000000000000),1,(204645185653851203887598016939556015079/205343243679166425120000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid2189 : retention2189.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid2189 : retention2189.NumericValid := by decide +kernel
def certificate2189 : RatCutBinCertificate := ⟨⟨retention2189,(285426218246105133/125000000000000000),(9018985876591161/200000000000000000),(9937081155939274967/1000000000000000000),(1025653079030248895453/1000000000000000000),(123279787994590821/125000000000000000)⟩,(997867331086661767/1000000000000000000),(122301543192874687/500000000000000000),(82173881226970507/200000000000000000),(396721448955116791/1000000000000000000)⟩
theorem valid2189 : certificate2189.Valid := by decide +kernel
theorem sound2189 : certificate2189.Sound := rat_cut_bin_certificate_sound certificate2189 profilesValid2189 numericValid2189 valid2189

def retention2190 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(119508897847781351/16010831672675455465),(709953848600681293/1000000000000000000),(15/4),(9115647545181039801/4000000000000000000),true,MergedCutProfiles.Batch336.profile13476,![MergedCutProfiles.Batch336.profile13476,MergedCutProfiles.Batch336.profile13477,MergedCutProfiles.Batch336.profile13478,MergedCutProfiles.Batch336.profile13479,MergedCutProfiles.Batch337.profile13480,MergedCutProfiles.Batch337.profile13481,MergedCutProfiles.Batch337.profile13482,MergedCutProfiles.Batch337.profile13483,MergedCutProfiles.Batch337.profile13484,MergedCutProfiles.Batch337.profile13485,MergedCutProfiles.Batch337.profile13486,MergedCutProfiles.Batch337.profile13487,MergedCutProfiles.Batch337.profile13488,MergedCutProfiles.Batch337.profile13489,MergedCutProfiles.Batch337.profile13490,MergedCutProfiles.Batch337.profile13491]⟩
theorem profilesValid2190 : retention2190.ProfilesValid := by
  change ∀ j : Fin 16, (retention2190.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch336.valid13476
  · exact MergedCutProfiles.Batch336.valid13477
  · exact MergedCutProfiles.Batch336.valid13478
  · exact MergedCutProfiles.Batch336.valid13479
  · exact MergedCutProfiles.Batch337.valid13480
  · exact MergedCutProfiles.Batch337.valid13481
  · exact MergedCutProfiles.Batch337.valid13482
  · exact MergedCutProfiles.Batch337.valid13483
  · exact MergedCutProfiles.Batch337.valid13484
  · exact MergedCutProfiles.Batch337.valid13485
  · exact MergedCutProfiles.Batch337.valid13486
  · exact MergedCutProfiles.Batch337.valid13487
  · exact MergedCutProfiles.Batch337.valid13488
  · exact MergedCutProfiles.Batch337.valid13489
  · exact MergedCutProfiles.Batch337.valid13490
  · exact MergedCutProfiles.Batch337.valid13491
theorem numericValid2190 : retention2190.NumericValid := by decide +kernel
def certificate2190 : RatCutBinCertificate := ⟨⟨retention2190,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(1121633387360975237/500000000000000000)⟩,(998047922835710343/1000000000000000000),(14175323261866111/31250000000000000),(187802845412065187/1000000000000000000),(45761741864206621/500000000000000000)⟩
theorem valid2190 : certificate2190.Valid := by decide +kernel
theorem sound2190 : certificate2190.Sound := rat_cut_bin_certificate_sound certificate2190 profilesValid2190 numericValid2190 valid2190

def retention2191 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(30348917681037825/3202166334535091093),(358526693543344053/500000000000000000),(15/4),(290427737340997121177/128000000000000000000),true,MergedCutProfiles.Batch337.profile13492,![MergedCutProfiles.Batch337.profile13492,MergedCutProfiles.Batch337.profile13493,MergedCutProfiles.Batch337.profile13494,MergedCutProfiles.Batch337.profile13495,MergedCutProfiles.Batch337.profile13496,MergedCutProfiles.Batch337.profile13497,MergedCutProfiles.Batch337.profile13498,MergedCutProfiles.Batch337.profile13499,MergedCutProfiles.Batch337.profile13500,MergedCutProfiles.Batch337.profile13501,MergedCutProfiles.Batch337.profile13489,MergedCutProfiles.Batch337.profile13502,MergedCutProfiles.Batch337.profile13503,MergedCutProfiles.Batch337.profile13504,MergedCutProfiles.Batch337.profile13505,MergedCutProfiles.Batch337.profile13506]⟩
theorem profilesValid2191 : retention2191.ProfilesValid := by
  change ∀ j : Fin 16, (retention2191.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch337.valid13492
  · exact MergedCutProfiles.Batch337.valid13493
  · exact MergedCutProfiles.Batch337.valid13494
  · exact MergedCutProfiles.Batch337.valid13495
  · exact MergedCutProfiles.Batch337.valid13496
  · exact MergedCutProfiles.Batch337.valid13497
  · exact MergedCutProfiles.Batch337.valid13498
  · exact MergedCutProfiles.Batch337.valid13499
  · exact MergedCutProfiles.Batch337.valid13500
  · exact MergedCutProfiles.Batch337.valid13501
  · exact MergedCutProfiles.Batch337.valid13489
  · exact MergedCutProfiles.Batch337.valid13502
  · exact MergedCutProfiles.Batch337.valid13503
  · exact MergedCutProfiles.Batch337.valid13504
  · exact MergedCutProfiles.Batch337.valid13505
  · exact MergedCutProfiles.Batch337.valid13506
theorem numericValid2191 : retention2191.NumericValid := by decide +kernel
def certificate2191 : RatCutBinCertificate := ⟨⟨retention2191,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(2233321592961611419/1000000000000000000)⟩,(998047922835710343/1000000000000000000),(56640539102517899/125000000000000000),(188187317974863739/1000000000000000000),(91544501642797021/1000000000000000000)⟩
theorem valid2191 : certificate2191.Valid := by decide +kernel
theorem sound2191 : certificate2191.Sound := rat_cut_bin_certificate_sound certificate2191 profilesValid2191 numericValid2191 valid2191

def retention2192 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(110540205500000000/9606499003605273279),(3641870121724539/4000000000000000),(61/20),(287143480027158519467/128000000000000000000),true,MergedCutProfiles.Batch337.profile13507,![MergedCutProfiles.Batch337.profile13507,MergedCutProfiles.Batch337.profile13508,MergedCutProfiles.Batch337.profile13509,MergedCutProfiles.Batch337.profile13510,MergedCutProfiles.Batch337.profile13497,MergedCutProfiles.Batch337.profile13511,MergedCutProfiles.Batch337.profile13512,MergedCutProfiles.Batch337.profile13513,MergedCutProfiles.Batch337.profile13514,MergedCutProfiles.Batch337.profile13515,MergedCutProfiles.Batch337.profile13516,MergedCutProfiles.Batch337.profile13517,MergedCutProfiles.Batch337.profile13518,MergedCutProfiles.Batch337.profile13519,MergedCutProfiles.Batch338.profile13520,MergedCutProfiles.Batch338.profile13521]⟩
theorem profilesValid2192 : retention2192.ProfilesValid := by
  change ∀ j : Fin 16, (retention2192.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch337.valid13507
  · exact MergedCutProfiles.Batch337.valid13508
  · exact MergedCutProfiles.Batch337.valid13509
  · exact MergedCutProfiles.Batch337.valid13510
  · exact MergedCutProfiles.Batch337.valid13497
  · exact MergedCutProfiles.Batch337.valid13511
  · exact MergedCutProfiles.Batch337.valid13512
  · exact MergedCutProfiles.Batch337.valid13513
  · exact MergedCutProfiles.Batch337.valid13514
  · exact MergedCutProfiles.Batch337.valid13515
  · exact MergedCutProfiles.Batch337.valid13516
  · exact MergedCutProfiles.Batch337.valid13517
  · exact MergedCutProfiles.Batch337.valid13518
  · exact MergedCutProfiles.Batch337.valid13519
  · exact MergedCutProfiles.Batch338.valid13520
  · exact MergedCutProfiles.Batch338.valid13521
theorem numericValid2192 : retention2192.NumericValid := by decide +kernel
def certificate2192 : RatCutBinCertificate := ⟨⟨retention2192,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(2214317102532482421/1000000000000000000)⟩,(998047922835710343/1000000000000000000),(100830116090660267/250000000000000000),(230453725157959143/1000000000000000000),(2646695702265381/20000000000000000)⟩
theorem valid2192 : certificate2192.Valid := by decide +kernel
theorem sound2192 : certificate2192.Sound := rat_cut_bin_certificate_sound certificate2192 profilesValid2192 numericValid2192 valid2192

def retention2193 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(381535369555015523/32021663345350910930),(221080411/200000000),(13/5),(17833154393594115849/8000000000000000000),true,MergedCutProfiles.Batch338.profile13522,![MergedCutProfiles.Batch338.profile13522,MergedCutProfiles.Batch338.profile13523,MergedCutProfiles.Batch338.profile13524,MergedCutProfiles.Batch337.profile13496,MergedCutProfiles.Batch338.profile13525,MergedCutProfiles.Batch338.profile13526,MergedCutProfiles.Batch338.profile13527,MergedCutProfiles.Batch338.profile13528,MergedCutProfiles.Batch338.profile13529,MergedCutProfiles.Batch337.profile13491,MergedCutProfiles.Batch338.profile13530,MergedCutProfiles.Batch337.profile13505,MergedCutProfiles.Batch338.profile13531,MergedCutProfiles.Batch338.profile13532,MergedCutProfiles.Batch338.profile13533,MergedCutProfiles.Batch338.profile13534]⟩
theorem profilesValid2193 : retention2193.ProfilesValid := by
  change ∀ j : Fin 16, (retention2193.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch338.valid13522
  · exact MergedCutProfiles.Batch338.valid13523
  · exact MergedCutProfiles.Batch338.valid13524
  · exact MergedCutProfiles.Batch337.valid13496
  · exact MergedCutProfiles.Batch338.valid13525
  · exact MergedCutProfiles.Batch338.valid13526
  · exact MergedCutProfiles.Batch338.valid13527
  · exact MergedCutProfiles.Batch338.valid13528
  · exact MergedCutProfiles.Batch338.valid13529
  · exact MergedCutProfiles.Batch337.valid13491
  · exact MergedCutProfiles.Batch338.valid13530
  · exact MergedCutProfiles.Batch337.valid13505
  · exact MergedCutProfiles.Batch338.valid13531
  · exact MergedCutProfiles.Batch338.valid13532
  · exact MergedCutProfiles.Batch338.valid13533
  · exact MergedCutProfiles.Batch338.valid13534
theorem numericValid2193 : retention2193.NumericValid := by decide +kernel
def certificate2193 : RatCutBinCertificate := ⟨⟨retention2193,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(1102215194503451399/500000000000000000)⟩,(998047922835710343/1000000000000000000),(369868595751614079/1000000000000000000),(262254045006400707/1000000000000000000),(85658272746211187/500000000000000000)⟩
theorem valid2193 : certificate2193.Valid := by decide +kernel
theorem sound2193 : certificate2193.Sound := rat_cut_bin_certificate_sound certificate2193 profilesValid2193 numericValid2193 valid2193

def retention2194 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(131898652384927719/6404332669070182186),(1144606108665046569/1000000000000000000),(5/2),(557317011031550931721/256000000000000000000),true,MergedCutProfiles.Batch338.profile13535,![MergedCutProfiles.Batch338.profile13535,MergedCutProfiles.Batch338.profile13536,MergedCutProfiles.Batch338.profile13537,MergedCutProfiles.Batch337.profile13486,MergedCutProfiles.Batch337.profile13514,MergedCutProfiles.Batch337.profile13503,MergedCutProfiles.Batch338.profile13538,MergedCutProfiles.Batch338.profile13539,MergedCutProfiles.Batch338.profile13540,MergedCutProfiles.Batch338.profile13541,MergedCutProfiles.Batch338.profile13542,MergedCutProfiles.Batch338.profile13543,MergedCutProfiles.Batch338.profile13544,MergedCutProfiles.Batch338.profile13545,MergedCutProfiles.Batch338.profile13546,MergedCutProfiles.Batch338.profile13547]⟩
theorem profilesValid2194 : retention2194.ProfilesValid := by
  change ∀ j : Fin 16, (retention2194.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch338.valid13535
  · exact MergedCutProfiles.Batch338.valid13536
  · exact MergedCutProfiles.Batch338.valid13537
  · exact MergedCutProfiles.Batch337.valid13486
  · exact MergedCutProfiles.Batch337.valid13514
  · exact MergedCutProfiles.Batch337.valid13503
  · exact MergedCutProfiles.Batch338.valid13538
  · exact MergedCutProfiles.Batch338.valid13539
  · exact MergedCutProfiles.Batch338.valid13540
  · exact MergedCutProfiles.Batch338.valid13541
  · exact MergedCutProfiles.Batch338.valid13542
  · exact MergedCutProfiles.Batch338.valid13543
  · exact MergedCutProfiles.Batch338.valid13544
  · exact MergedCutProfiles.Batch338.valid13545
  · exact MergedCutProfiles.Batch338.valid13546
  · exact MergedCutProfiles.Batch338.valid13547
theorem numericValid2194 : retention2194.NumericValid := by decide +kernel
def certificate2194 : RatCutBinCertificate := ⟨⟨retention2194,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(86130247894632001/40000000000000000)⟩,(998047922835710343/1000000000000000000),(2330525006050949/6250000000000000),(259267435202766817/1000000000000000000),(85629522839775849/500000000000000000)⟩
theorem valid2194 : certificate2194.Valid := by decide +kernel
theorem sound2194 : certificate2194.Sound := rat_cut_bin_certificate_sound certificate2194 profilesValid2194 numericValid2194 valid2194

def retention2195 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(9281340866164056944/48032495018026366395),(395695957154783157/200000000000000000),(7/4),(23268189347059724473976472302880175391/14069189587725623360000000000000000000),false,MergedCutProfiles.Batch338.profile13548,(fun _ => MergedCutProfiles.Batch338.profile13548)⟩
theorem profilesValid2195 : retention2195.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13548
theorem numericValid2195 : retention2195.NumericValid := by decide +kernel
def certificate2195 : RatCutBinCertificate := ⟨⟨retention2195,(1989651640567177437/1000000000000000000),(481579510880593/10000000000000000),(5040277059339899121/500000000000000000),(486687866250905701561/500000000000000000),(818602872839636797/500000000000000000)⟩,(998047922835710343/1000000000000000000),(400158248962267771/1000000000000000000),(29167174844085353/125000000000000000),(669854057006219/3906250000000000)⟩
theorem valid2195 : certificate2195.Valid := by decide +kernel
theorem sound2195 : certificate2195.Sound := rat_cut_bin_certificate_sound certificate2195 profilesValid2195 numericValid2195 valid2195

def certificates : List RatCutBinCertificate := [certificate2184,certificate2185,certificate2186,certificate2187,certificate2188,certificate2189,certificate2190,certificate2191,certificate2192,certificate2193,certificate2194,certificate2195]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2184,List.forall_mem_cons.mpr ⟨sound2185,List.forall_mem_cons.mpr ⟨sound2186,List.forall_mem_cons.mpr ⟨sound2187,List.forall_mem_cons.mpr ⟨sound2188,List.forall_mem_cons.mpr ⟨sound2189,List.forall_mem_cons.mpr ⟨sound2190,List.forall_mem_cons.mpr ⟨sound2191,List.forall_mem_cons.mpr ⟨sound2192,List.forall_mem_cons.mpr ⟨sound2193,List.forall_mem_cons.mpr ⟨sound2194,List.forall_mem_cons.mpr ⟨sound2195,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch182
