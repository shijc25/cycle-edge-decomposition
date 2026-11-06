import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch059
import Cycle12.MergedCutProfiles.Batch060
import Cycle12.MergedCutProfiles.Batch061

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch030

def retention360 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(9319920240545812196/21803343000876340869),(1877893750711201899/500000000000000000),(5/4),(22938465653420567839485255169290521733/20030866674252820256000000000000000000),false,MergedCutProfiles.Batch059.profile2382,(fun _ => MergedCutProfiles.Batch059.profile2382)⟩
theorem profilesValid360 : retention360.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2382
theorem numericValid360 : retention360.NumericValid := by decide +kernel
def certificate360 : RatCutBinCertificate := ⟨⟨retention360,(602748354546147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(564885587436451787/500000000000000000)⟩,(124369634423980457/125000000000000000),(355026166257155777/1000000000000000000),(69329138823079313/250000000000000000),(209033122046444573/1000000000000000000)⟩
theorem valid360 : certificate360.Valid := by decide +kernel
theorem sound360 : certificate360.Sound := rat_cut_bin_certificate_sound certificate360 profilesValid360 numericValid360 valid360

def retention361 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(3091468018799479159/6229526571678954534),(2329980060136453049/125000000000000000),1,(18552829945098977195735764576334232463/18639840481091624392000000000000000000),false,MergedCutProfiles.Batch059.profile2383,(fun _ => MergedCutProfiles.Batch059.profile2383)⟩
theorem profilesValid361 : retention361.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2383
theorem numericValid361 : retention361.NumericValid := by decide +kernel
def certificate361 : RatCutBinCertificate := ⟨⟨retention361,(602748354546147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(245756110449380403/250000000000000000)⟩,(124369634423980457/125000000000000000),(408024777318391313/1000000000000000000),(226209588904262197/1000000000000000000),(26267446067115049/125000000000000000)⟩
theorem valid361 : certificate361.Valid := by decide +kernel
theorem sound361 : certificate361.Sound := rat_cut_bin_certificate_sound certificate361 profilesValid361 numericValid361 valid361

def retention362 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(1/2),(21640276131596354113/1000000000000000000),1,(2677730308994503934334081897252974843/2705034516449544264125000000000000000),false,MergedCutProfiles.Batch059.profile2381,(fun _ => MergedCutProfiles.Batch059.profile2381)⟩
theorem profilesValid362 : retention362.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2381
theorem numericValid362 : retention362.NumericValid := by decide +kernel
def certificate362 : RatCutBinCertificate := ⟨⟨retention362,(602748354546147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(977598591566539831/1000000000000000000)⟩,(124369634423980457/125000000000000000),(41028938914512449/100000000000000000),(224185872459602607/1000000000000000000),(208612044174727907/1000000000000000000)⟩
theorem valid362 : certificate362.Valid := by decide +kernel
theorem sound362 : certificate362.Sound := rat_cut_bin_certificate_sound certificate362 profilesValid362 numericValid362 valid362

def retention363 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(378857178655482158/21462816999703401623),(750212234961350807/1000000000000000000),(69/20),(2818345419460037616191/1280000000000000000000),true,MergedCutProfiles.Batch059.profile2384,![MergedCutProfiles.Batch059.profile2384,MergedCutProfiles.Batch059.profile2385,MergedCutProfiles.Batch059.profile2386,MergedCutProfiles.Batch059.profile2387,MergedCutProfiles.Batch059.profile2388,MergedCutProfiles.Batch059.profile2389,MergedCutProfiles.Batch059.profile2390,MergedCutProfiles.Batch059.profile2391,MergedCutProfiles.Batch059.profile2392,MergedCutProfiles.Batch059.profile2393,MergedCutProfiles.Batch059.profile2394,MergedCutProfiles.Batch059.profile2395,MergedCutProfiles.Batch059.profile2396,MergedCutProfiles.Batch059.profile2397,MergedCutProfiles.Batch059.profile2398,MergedCutProfiles.Batch059.profile2399]⟩
theorem profilesValid363 : retention363.ProfilesValid := by
  change ∀ j : Fin 16, (retention363.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch059.valid2384
  · exact MergedCutProfiles.Batch059.valid2385
  · exact MergedCutProfiles.Batch059.valid2386
  · exact MergedCutProfiles.Batch059.valid2387
  · exact MergedCutProfiles.Batch059.valid2388
  · exact MergedCutProfiles.Batch059.valid2389
  · exact MergedCutProfiles.Batch059.valid2390
  · exact MergedCutProfiles.Batch059.valid2391
  · exact MergedCutProfiles.Batch059.valid2392
  · exact MergedCutProfiles.Batch059.valid2393
  · exact MergedCutProfiles.Batch059.valid2394
  · exact MergedCutProfiles.Batch059.valid2395
  · exact MergedCutProfiles.Batch059.valid2396
  · exact MergedCutProfiles.Batch059.valid2397
  · exact MergedCutProfiles.Batch059.valid2398
  · exact MergedCutProfiles.Batch059.valid2399
theorem numericValid363 : retention363.NumericValid := by decide +kernel
def certificate363 : RatCutBinCertificate := ⟨⟨retention363,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(1082907342653771019/500000000000000000)⟩,(995723499330951699/1000000000000000000),(212991219560694963/500000000000000000),(210501795357972489/1000000000000000000),(52909716081557133/500000000000000000)⟩
theorem valid363 : certificate363.Valid := by decide +kernel
theorem sound363 : certificate363.Sound := rat_cut_bin_certificate_sound certificate363 profilesValid363 numericValid363 valid363

def retention364 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(879682845876160061/42925633999406803246),(189428589327741079/250000000000000000),(17/5),(699152882500849180639/320000000000000000000),true,MergedCutProfiles.Batch060.profile2400,![MergedCutProfiles.Batch060.profile2400,MergedCutProfiles.Batch060.profile2401,MergedCutProfiles.Batch060.profile2402,MergedCutProfiles.Batch060.profile2403,MergedCutProfiles.Batch060.profile2404,MergedCutProfiles.Batch059.profile2390,MergedCutProfiles.Batch060.profile2405,MergedCutProfiles.Batch060.profile2406,MergedCutProfiles.Batch060.profile2407,MergedCutProfiles.Batch060.profile2408,MergedCutProfiles.Batch060.profile2409,MergedCutProfiles.Batch060.profile2410,MergedCutProfiles.Batch060.profile2411,MergedCutProfiles.Batch060.profile2412,MergedCutProfiles.Batch060.profile2413,MergedCutProfiles.Batch060.profile2414]⟩
theorem profilesValid364 : retention364.ProfilesValid := by
  change ∀ j : Fin 16, (retention364.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch060.valid2400
  · exact MergedCutProfiles.Batch060.valid2401
  · exact MergedCutProfiles.Batch060.valid2402
  · exact MergedCutProfiles.Batch060.valid2403
  · exact MergedCutProfiles.Batch060.valid2404
  · exact MergedCutProfiles.Batch059.valid2390
  · exact MergedCutProfiles.Batch060.valid2405
  · exact MergedCutProfiles.Batch060.valid2406
  · exact MergedCutProfiles.Batch060.valid2407
  · exact MergedCutProfiles.Batch060.valid2408
  · exact MergedCutProfiles.Batch060.valid2409
  · exact MergedCutProfiles.Batch060.valid2410
  · exact MergedCutProfiles.Batch060.valid2411
  · exact MergedCutProfiles.Batch060.valid2412
  · exact MergedCutProfiles.Batch060.valid2413
  · exact MergedCutProfiles.Batch060.valid2414
theorem numericValid364 : retention364.NumericValid := by decide +kernel
def certificate364 : RatCutBinCertificate := ⟨⟨retention364,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(1074678535894363401/500000000000000000)⟩,(995723499330951699/1000000000000000000),(427137077184063379/1000000000000000000),(209518061660854921/1000000000000000000),(105820091168616421/1000000000000000000)⟩
theorem valid364 : certificate364.Valid := by decide +kernel
theorem sound364 : certificate364.Sound := rat_cut_bin_certificate_sound certificate364 profilesValid364 numericValid364 valid364

def retention365 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(70211693000000000/3066116714243343089),(879682845876160061/1000000000000000000),3,(554962104231195336437/256000000000000000000),true,MergedCutProfiles.Batch060.profile2415,![MergedCutProfiles.Batch060.profile2415,MergedCutProfiles.Batch060.profile2416,MergedCutProfiles.Batch060.profile2417,MergedCutProfiles.Batch060.profile2418,MergedCutProfiles.Batch060.profile2419,MergedCutProfiles.Batch060.profile2420,MergedCutProfiles.Batch059.profile2392,MergedCutProfiles.Batch060.profile2407,MergedCutProfiles.Batch060.profile2421,MergedCutProfiles.Batch059.profile2396,MergedCutProfiles.Batch060.profile2422,MergedCutProfiles.Batch060.profile2423,MergedCutProfiles.Batch060.profile2424,MergedCutProfiles.Batch060.profile2425,MergedCutProfiles.Batch060.profile2426,MergedCutProfiles.Batch060.profile2427]⟩
theorem profilesValid365 : retention365.ProfilesValid := by
  change ∀ j : Fin 16, (retention365.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch060.valid2415
  · exact MergedCutProfiles.Batch060.valid2416
  · exact MergedCutProfiles.Batch060.valid2417
  · exact MergedCutProfiles.Batch060.valid2418
  · exact MergedCutProfiles.Batch060.valid2419
  · exact MergedCutProfiles.Batch060.valid2420
  · exact MergedCutProfiles.Batch059.valid2392
  · exact MergedCutProfiles.Batch060.valid2407
  · exact MergedCutProfiles.Batch060.valid2421
  · exact MergedCutProfiles.Batch059.valid2396
  · exact MergedCutProfiles.Batch060.valid2422
  · exact MergedCutProfiles.Batch060.valid2423
  · exact MergedCutProfiles.Batch060.valid2424
  · exact MergedCutProfiles.Batch060.valid2425
  · exact MergedCutProfiles.Batch060.valid2426
  · exact MergedCutProfiles.Batch060.valid2427
theorem numericValid365 : retention365.NumericValid := by decide +kernel
def certificate365 : RatCutBinCertificate := ⟨⟨retention365,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(2136501031339200241/1000000000000000000)⟩,(995723499330951699/1000000000000000000),(200158180090824211/500000000000000000),(116596311537223933/500000000000000000),(32532343626031303/250000000000000000)⟩
theorem valid365 : certificate365.Valid := by decide +kernel
theorem sound365 : certificate365.Sound := rat_cut_bin_certificate_sound certificate365 profilesValid365 numericValid365 valid365

def retention366 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(78993195836500735/3066116714243343089),(491481851/500000000),(27/10),(34281084141968108529/16000000000000000000),true,MergedCutProfiles.Batch060.profile2428,![MergedCutProfiles.Batch060.profile2428,MergedCutProfiles.Batch060.profile2429,MergedCutProfiles.Batch060.profile2430,MergedCutProfiles.Batch060.profile2431,MergedCutProfiles.Batch060.profile2432,MergedCutProfiles.Batch060.profile2433,MergedCutProfiles.Batch060.profile2434,MergedCutProfiles.Batch060.profile2421,MergedCutProfiles.Batch060.profile2435,MergedCutProfiles.Batch060.profile2436,MergedCutProfiles.Batch059.profile2399,MergedCutProfiles.Batch060.profile2437,MergedCutProfiles.Batch060.profile2438,MergedCutProfiles.Batch060.profile2439,MergedCutProfiles.Batch061.profile2440,MergedCutProfiles.Batch061.profile2441]⟩
theorem profilesValid366 : retention366.ProfilesValid := by
  change ∀ j : Fin 16, (retention366.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch060.valid2428
  · exact MergedCutProfiles.Batch060.valid2429
  · exact MergedCutProfiles.Batch060.valid2430
  · exact MergedCutProfiles.Batch060.valid2431
  · exact MergedCutProfiles.Batch060.valid2432
  · exact MergedCutProfiles.Batch060.valid2433
  · exact MergedCutProfiles.Batch060.valid2434
  · exact MergedCutProfiles.Batch060.valid2421
  · exact MergedCutProfiles.Batch060.valid2435
  · exact MergedCutProfiles.Batch060.valid2436
  · exact MergedCutProfiles.Batch059.valid2399
  · exact MergedCutProfiles.Batch060.valid2437
  · exact MergedCutProfiles.Batch060.valid2438
  · exact MergedCutProfiles.Batch060.valid2439
  · exact MergedCutProfiles.Batch061.valid2440
  · exact MergedCutProfiles.Batch061.valid2441
theorem numericValid366 : retention366.NumericValid := by decide +kernel
def certificate366 : RatCutBinCertificate := ⟨⟨retention366,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(528595011649071533/250000000000000000)⟩,(995723499330951699/1000000000000000000),(385119177347825941/1000000000000000000),(123698531829838511/500000000000000000),(14885501521939191/100000000000000000)⟩
theorem valid366 : certificate366.Valid := by decide +kernel
theorem sound366 : certificate366.Sound := rat_cut_bin_certificate_sound certificate366 profilesValid366 numericValid366 valid366

def retention367 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(2762384370762872897/42925633999406803246),(110590474171101029/100000000000000000),(49/20),(2562332449891685779/1280000000000000000),true,MergedCutProfiles.Batch061.profile2442,![MergedCutProfiles.Batch061.profile2442,MergedCutProfiles.Batch060.profile2432,MergedCutProfiles.Batch061.profile2443,MergedCutProfiles.Batch060.profile2436,MergedCutProfiles.Batch061.profile2444,MergedCutProfiles.Batch061.profile2440,MergedCutProfiles.Batch061.profile2445,MergedCutProfiles.Batch061.profile2446,MergedCutProfiles.Batch061.profile2447,MergedCutProfiles.Batch061.profile2448,MergedCutProfiles.Batch061.profile2449,MergedCutProfiles.Batch061.profile2450,MergedCutProfiles.Batch061.profile2451,MergedCutProfiles.Batch061.profile2452,MergedCutProfiles.Batch061.profile2453,MergedCutProfiles.Batch061.profile2454]⟩
theorem profilesValid367 : retention367.ProfilesValid := by
  change ∀ j : Fin 16, (retention367.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch061.valid2442
  · exact MergedCutProfiles.Batch060.valid2432
  · exact MergedCutProfiles.Batch061.valid2443
  · exact MergedCutProfiles.Batch060.valid2436
  · exact MergedCutProfiles.Batch061.valid2444
  · exact MergedCutProfiles.Batch061.valid2440
  · exact MergedCutProfiles.Batch061.valid2445
  · exact MergedCutProfiles.Batch061.valid2446
  · exact MergedCutProfiles.Batch061.valid2447
  · exact MergedCutProfiles.Batch061.valid2448
  · exact MergedCutProfiles.Batch061.valid2449
  · exact MergedCutProfiles.Batch061.valid2450
  · exact MergedCutProfiles.Batch061.valid2451
  · exact MergedCutProfiles.Batch061.valid2452
  · exact MergedCutProfiles.Batch061.valid2453
  · exact MergedCutProfiles.Batch061.valid2454
theorem numericValid367 : retention367.NumericValid := by decide +kernel
def certificate367 : RatCutBinCertificate := ⟨⟨retention367,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(1976244511182417581/1000000000000000000)⟩,(995723499330951699/1000000000000000000),(392400038871989397/1000000000000000000),(240518452040733659/1000000000000000000),(148762652876488567/1000000000000000000)⟩
theorem valid367 : certificate367.Valid := by decide +kernel
theorem sound367 : certificate367.Sound := rat_cut_bin_certificate_sound certificate367 profilesValid367 numericValid367 valid367

def retention368 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(7133140636665230310/21462816999703401623),(2762384370762872897/1000000000000000000),(27/20),(5890661441021245836037315567373541722039/4419814993220596635200000000000000000000),false,MergedCutProfiles.Batch061.profile2455,(fun _ => MergedCutProfiles.Batch061.profile2455)⟩
theorem profilesValid368 : retention368.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2455
theorem numericValid368 : retention368.NumericValid := by decide +kernel
def certificate368 : RatCutBinCertificate := ⟨⟨retention368,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(1318690946018693511/1000000000000000000)⟩,(995723499330951699/1000000000000000000),(223481007241491189/500000000000000000),(96553680757587937/500000000000000000),(18595293482428801/125000000000000000)⟩
theorem valid368 : certificate368.Valid := by decide +kernel
theorem sound368 : certificate368.Sound := rat_cut_bin_certificate_sound certificate368 profilesValid368 numericValid368 valid368

def retention369 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(10411013038442558287/21462816999703401623),(713314063666523031/50000000000000000),(21/20),(58758215533351937147870542604889557639/57065125093321842480000000000000000000),false,MergedCutProfiles.Batch061.profile2456,(fun _ => MergedCutProfiles.Batch061.profile2456)⟩
theorem profilesValid369 : retention369.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2456
theorem numericValid369 : retention369.NumericValid := by decide +kernel
def certificate369 : RatCutBinCertificate := ⟨⟨retention369,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(40748318447557771/40000000000000000)⟩,(995723499330951699/1000000000000000000),(240123652024318711/500000000000000000),(167513244910292259/1000000000000000000),(151959973287955951/1000000000000000000)⟩
theorem valid369 : certificate369.Valid := by decide +kernel
theorem sound369 : certificate369.Sound := rat_cut_bin_certificate_sound certificate369 profilesValid369 numericValid369 valid369

def retention370 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(10620274400515253709/21462816999703401623),(10411013038442558287/500000000000000000),1,(5203312583663349469047640913595678013/5205506519221279143500000000000000000),false,MergedCutProfiles.Batch061.profile2457,(fun _ => MergedCutProfiles.Batch061.profile2457)⟩
theorem profilesValid370 : retention370.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2457
theorem numericValid370 : retention370.NumericValid := by decide +kernel
def certificate370 : RatCutBinCertificate := ⟨⟨retention370,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(197827810631310137/200000000000000000)⟩,(995723499330951699/1000000000000000000),(97389418641946329/200000000000000000),(81322897827566267/500000000000000000),(7645505088764851/50000000000000000)⟩
theorem valid370 : certificate370.Valid := by decide +kernel
theorem sound370 : certificate370.Sound := rat_cut_bin_certificate_sound certificate370 profilesValid370 numericValid370 valid370

def retention371 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(21452954289040812493/42925633999406803246),(10620274400515253709/500000000000000000),1,(623143556084877552930497838786954561/629349594104607627200000000000000000),false,MergedCutProfiles.Batch061.profile2458,(fun _ => MergedCutProfiles.Batch061.profile2458)⟩
theorem profilesValid371 : retention371.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2458
theorem numericValid371 : retention371.NumericValid := by decide +kernel
def certificate371 : RatCutBinCertificate := ⟨⟨retention371,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(979699484279699883/1000000000000000000)⟩,(995723499330951699/1000000000000000000),(2456537224170429/5000000000000000),(31905512628032811/200000000000000000),(37185889588376653/250000000000000000)⟩
theorem valid371 : certificate371.Valid := by decide +kernel
theorem sound371 : certificate371.Sound := rat_cut_bin_certificate_sound certificate371 profilesValid371 numericValid371 valid371

def certificates : List RatCutBinCertificate := [certificate360,certificate361,certificate362,certificate363,certificate364,certificate365,certificate366,certificate367,certificate368,certificate369,certificate370,certificate371]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound360,List.forall_mem_cons.mpr ⟨sound361,List.forall_mem_cons.mpr ⟨sound362,List.forall_mem_cons.mpr ⟨sound363,List.forall_mem_cons.mpr ⟨sound364,List.forall_mem_cons.mpr ⟨sound365,List.forall_mem_cons.mpr ⟨sound366,List.forall_mem_cons.mpr ⟨sound367,List.forall_mem_cons.mpr ⟨sound368,List.forall_mem_cons.mpr ⟨sound369,List.forall_mem_cons.mpr ⟨sound370,List.forall_mem_cons.mpr ⟨sound371,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch030
