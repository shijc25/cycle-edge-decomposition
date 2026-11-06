import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch061
import Cycle12.MergedCutProfiles.Batch062
import Cycle12.MergedCutProfiles.Batch063

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch031

def retention372 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(1/2),(21452954289040812493/1000000000000000000),1,(84937092446302977171275708064242990067/85811817156163249972000000000000000000),false,MergedCutProfiles.Batch061.profile2459,(fun _ => MergedCutProfiles.Batch061.profile2459)⟩
theorem profilesValid372 : retention372.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2459
theorem numericValid372 : retention372.NumericValid := by decide +kernel
def certificate372 : RatCutBinCertificate := ⟨⟨retention372,(1014182578104943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(30605218642332927/31250000000000000)⟩,(995723499330951699/1000000000000000000),(245655454612638131/500000000000000000),(7976255053462621/50000000000000000),(148758074789103353/1000000000000000000)⟩
theorem valid372 : certificate372.Valid := by decide +kernel
theorem sound372 : certificate372.Sound := rat_cut_bin_certificate_sound certificate372 profilesValid372 numericValid372 valid372

def retention373 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(9103285737294427838/21462816999703401623),(472455735680865129/125000000000000000),(5/4),(4353858061797530026484409478493162831/3779645885446921032000000000000000000),false,MergedCutProfiles.Batch061.profile2460,(fun _ => MergedCutProfiles.Batch061.profile2460)⟩
theorem profilesValid373 : retention373.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2460
theorem numericValid373 : retention373.NumericValid := by decide +kernel
def certificate373 : RatCutBinCertificate := ⟨⟨retention373,(1206973030604943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(1136391948774412749/1000000000000000000)⟩,(248727582245689491/250000000000000000),(1369043257863191/3906250000000000),(35257262657129759/125000000000000000),(26732444034937533/125000000000000000)⟩
theorem valid373 : certificate373.Valid := by decide +kernel
theorem sound373 : certificate373.Sound := rat_cut_bin_certificate_sound certificate373 profilesValid373 numericValid373 valid373

def retention374 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(10674318454189931994/21462816999703401623),(4551642868647213919/250000000000000000),1,(72309563584422410705211588056304018583/72826285898355422704000000000000000000),false,MergedCutProfiles.Batch061.profile2461,(fun _ => MergedCutProfiles.Batch061.profile2461)⟩
theorem profilesValid374 : retention374.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2461
theorem numericValid374 : retention374.NumericValid := by decide +kernel
def certificate374 : RatCutBinCertificate := ⟨⟨retention374,(1206973030604943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(980480747775449003/1000000000000000000)⟩,(248727582245689491/250000000000000000),(406205887528224363/1000000000000000000),(14240255712848989/62500000000000000),(52719023634861703/250000000000000000)⟩
theorem valid374 : certificate374.Valid := by decide +kernel
theorem sound374 : certificate374.Sound := rat_cut_bin_certificate_sound certificate374 profilesValid374 numericValid374 valid374

def retention375 : RatCutRetentionCertificate := ⟨(69/2000),(139/4000),(1/2),(5337159227094965997/250000000000000000),1,(84519199210982587910640875348370666887/85394547633519455952000000000000000000),false,MergedCutProfiles.Batch061.profile2459,(fun _ => MergedCutProfiles.Batch061.profile2459)⟩
theorem profilesValid375 : retention375.ProfilesValid := by
  exact MergedCutProfiles.Batch061.valid2459
theorem numericValid375 : retention375.NumericValid := by decide +kernel
def certificate375 : RatCutBinCertificate := ⟨⟨retention375,(1206973030604943321/500000000000000000),(10759811487997001/200000000000000000),(5226540752278388613/500000000000000000),(449289212885837113749/1000000000000000000),(977325395913177501/1000000000000000000)⟩,(248727582245689491/250000000000000000),(203758673426432189/500000000000000000),(7083273832289341/31250000000000000),(105363759253232749/500000000000000000)⟩
theorem valid375 : certificate375.Valid := by decide +kernel
theorem sound375 : certificate375.Sound := rat_cut_bin_certificate_sound certificate375 profilesValid375 numericValid375 valid375

def retention376 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(190669401534716971/10564877438800875298),(37756317135587519/50000000000000000),(17/5),(8779502779470071077/4000000000000000000),true,MergedCutProfiles.Batch061.profile2462,![MergedCutProfiles.Batch061.profile2462,MergedCutProfiles.Batch061.profile2463,MergedCutProfiles.Batch061.profile2464,MergedCutProfiles.Batch061.profile2465,MergedCutProfiles.Batch061.profile2466,MergedCutProfiles.Batch061.profile2467,MergedCutProfiles.Batch061.profile2468,MergedCutProfiles.Batch061.profile2469,MergedCutProfiles.Batch061.profile2470,MergedCutProfiles.Batch061.profile2471,MergedCutProfiles.Batch061.profile2472,MergedCutProfiles.Batch061.profile2473,MergedCutProfiles.Batch061.profile2474,MergedCutProfiles.Batch061.profile2475,MergedCutProfiles.Batch061.profile2476,MergedCutProfiles.Batch061.profile2477]⟩
theorem profilesValid376 : retention376.ProfilesValid := by
  change ∀ j : Fin 16, (retention376.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch061.valid2462
  · exact MergedCutProfiles.Batch061.valid2463
  · exact MergedCutProfiles.Batch061.valid2464
  · exact MergedCutProfiles.Batch061.valid2465
  · exact MergedCutProfiles.Batch061.valid2466
  · exact MergedCutProfiles.Batch061.valid2467
  · exact MergedCutProfiles.Batch061.valid2468
  · exact MergedCutProfiles.Batch061.valid2469
  · exact MergedCutProfiles.Batch061.valid2470
  · exact MergedCutProfiles.Batch061.valid2471
  · exact MergedCutProfiles.Batch061.valid2472
  · exact MergedCutProfiles.Batch061.valid2473
  · exact MergedCutProfiles.Batch061.valid2474
  · exact MergedCutProfiles.Batch061.valid2475
  · exact MergedCutProfiles.Batch061.valid2476
  · exact MergedCutProfiles.Batch061.valid2477
theorem numericValid376 : retention376.NumericValid := by decide +kernel
def certificate376 : RatCutBinCertificate := ⟨⟨retention376,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(2159042466280667219/1000000000000000000)⟩,(995685607421386069/1000000000000000000),(424751754780644899/1000000000000000000),(26444220541885261/125000000000000000),(21431330860525131/200000000000000000)⟩
theorem valid376 : certificate376.Valid := by decide +kernel
theorem sound376 : certificate376.Sound := rat_cut_bin_certificate_sound certificate376 profilesValid376 numericValid376 valid376

def retention377 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(876678241270428355/42259509755203501192),(190669401534716971/250000000000000000),(17/5),(699783928688276403971/320000000000000000000),true,MergedCutProfiles.Batch061.profile2478,![MergedCutProfiles.Batch061.profile2478,MergedCutProfiles.Batch061.profile2479,MergedCutProfiles.Batch062.profile2480,MergedCutProfiles.Batch062.profile2481,MergedCutProfiles.Batch062.profile2482,MergedCutProfiles.Batch062.profile2483,MergedCutProfiles.Batch062.profile2484,MergedCutProfiles.Batch062.profile2485,MergedCutProfiles.Batch062.profile2486,MergedCutProfiles.Batch062.profile2487,MergedCutProfiles.Batch062.profile2488,MergedCutProfiles.Batch062.profile2489,MergedCutProfiles.Batch062.profile2490,MergedCutProfiles.Batch061.profile2477,MergedCutProfiles.Batch062.profile2491,MergedCutProfiles.Batch062.profile2492]⟩
theorem profilesValid377 : retention377.ProfilesValid := by
  change ∀ j : Fin 16, (retention377.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch061.valid2478
  · exact MergedCutProfiles.Batch061.valid2479
  · exact MergedCutProfiles.Batch062.valid2480
  · exact MergedCutProfiles.Batch062.valid2481
  · exact MergedCutProfiles.Batch062.valid2482
  · exact MergedCutProfiles.Batch062.valid2483
  · exact MergedCutProfiles.Batch062.valid2484
  · exact MergedCutProfiles.Batch062.valid2485
  · exact MergedCutProfiles.Batch062.valid2486
  · exact MergedCutProfiles.Batch062.valid2487
  · exact MergedCutProfiles.Batch062.valid2488
  · exact MergedCutProfiles.Batch062.valid2489
  · exact MergedCutProfiles.Batch062.valid2490
  · exact MergedCutProfiles.Batch061.valid2477
  · exact MergedCutProfiles.Batch062.valid2491
  · exact MergedCutProfiles.Batch062.valid2492
theorem numericValid377 : retention377.NumericValid := by decide +kernel
def certificate377 : RatCutBinCertificate := ⟨⟨retention377,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(2150991565569299723/1000000000000000000)⟩,(995685607421386069/1000000000000000000),(424266679063540357/1000000000000000000),(105984689039151377/500000000000000000),(53628238806671473/500000000000000000)⟩
theorem valid377 : certificate377.Valid := by decide +kernel
theorem sound377 : certificate377.Sound := rat_cut_bin_certificate_sound certificate377 profilesValid377 numericValid377 valid377

def retention378 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(120795193375000000/5282438719400437649),(175335648254085671/200000000000000000),3,(554708473582703627803/256000000000000000000),true,MergedCutProfiles.Batch062.profile2493,![MergedCutProfiles.Batch062.profile2493,MergedCutProfiles.Batch062.profile2494,MergedCutProfiles.Batch062.profile2495,MergedCutProfiles.Batch062.profile2496,MergedCutProfiles.Batch062.profile2497,MergedCutProfiles.Batch062.profile2498,MergedCutProfiles.Batch062.profile2499,MergedCutProfiles.Batch062.profile2500,MergedCutProfiles.Batch062.profile2501,MergedCutProfiles.Batch062.profile2488,MergedCutProfiles.Batch062.profile2502,MergedCutProfiles.Batch062.profile2503,MergedCutProfiles.Batch062.profile2504,MergedCutProfiles.Batch062.profile2505,MergedCutProfiles.Batch062.profile2506,MergedCutProfiles.Batch062.profile2507]⟩
theorem profilesValid378 : retention378.ProfilesValid := by
  change ∀ j : Fin 16, (retention378.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch062.valid2493
  · exact MergedCutProfiles.Batch062.valid2494
  · exact MergedCutProfiles.Batch062.valid2495
  · exact MergedCutProfiles.Batch062.valid2496
  · exact MergedCutProfiles.Batch062.valid2497
  · exact MergedCutProfiles.Batch062.valid2498
  · exact MergedCutProfiles.Batch062.valid2499
  · exact MergedCutProfiles.Batch062.valid2500
  · exact MergedCutProfiles.Batch062.valid2501
  · exact MergedCutProfiles.Batch062.valid2488
  · exact MergedCutProfiles.Batch062.valid2502
  · exact MergedCutProfiles.Batch062.valid2503
  · exact MergedCutProfiles.Batch062.valid2504
  · exact MergedCutProfiles.Batch062.valid2505
  · exact MergedCutProfiles.Batch062.valid2506
  · exact MergedCutProfiles.Batch062.valid2507
theorem numericValid378 : retention378.NumericValid := by decide +kernel
def certificate378 : RatCutBinCertificate := ⟨⟨retention378,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(1067606228185572969/500000000000000000)⟩,(995685607421386069/1000000000000000000),(400221605646319003/1000000000000000000),(58319844562932307/250000000000000000),(65007456311011543/500000000000000000)⟩
theorem valid378 : certificate378.Valid := by decide +kernel
theorem sound378 : certificate378.Sound := rat_cut_bin_certificate_sound certificate378 profilesValid378 numericValid378 valid378

def retention379 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(493931492817796329/21129754877601750596),(966361547/1000000000),(11/4),(4311656499539063729/2000000000000000000),true,MergedCutProfiles.Batch062.profile2508,![MergedCutProfiles.Batch062.profile2508,MergedCutProfiles.Batch062.profile2509,MergedCutProfiles.Batch062.profile2510,MergedCutProfiles.Batch062.profile2511,MergedCutProfiles.Batch062.profile2512,MergedCutProfiles.Batch062.profile2513,MergedCutProfiles.Batch062.profile2514,MergedCutProfiles.Batch062.profile2486,MergedCutProfiles.Batch062.profile2515,MergedCutProfiles.Batch061.profile2474,MergedCutProfiles.Batch062.profile2516,MergedCutProfiles.Batch062.profile2517,MergedCutProfiles.Batch062.profile2518,MergedCutProfiles.Batch062.profile2519,MergedCutProfiles.Batch063.profile2520,MergedCutProfiles.Batch063.profile2521]⟩
theorem profilesValid379 : retention379.ProfilesValid := by
  change ∀ j : Fin 16, (retention379.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch062.valid2508
  · exact MergedCutProfiles.Batch062.valid2509
  · exact MergedCutProfiles.Batch062.valid2510
  · exact MergedCutProfiles.Batch062.valid2511
  · exact MergedCutProfiles.Batch062.valid2512
  · exact MergedCutProfiles.Batch062.valid2513
  · exact MergedCutProfiles.Batch062.valid2514
  · exact MergedCutProfiles.Batch062.valid2486
  · exact MergedCutProfiles.Batch062.valid2515
  · exact MergedCutProfiles.Batch061.valid2474
  · exact MergedCutProfiles.Batch062.valid2516
  · exact MergedCutProfiles.Batch062.valid2517
  · exact MergedCutProfiles.Batch062.valid2518
  · exact MergedCutProfiles.Batch062.valid2519
  · exact MergedCutProfiles.Batch063.valid2520
  · exact MergedCutProfiles.Batch063.valid2521
theorem numericValid379 : retention379.NumericValid := by decide +kernel
def certificate379 : RatCutBinCertificate := ⟨⟨retention379,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(2126845538434224747/1000000000000000000)⟩,(995685607421386069/1000000000000000000),(192426996548542041/500000000000000000),(24765017785620749/100000000000000000),(29522796345185507/200000000000000000)⟩
theorem valid379 : certificate379.Valid := by decide +kernel
theorem sound379 : certificate379.Sound := rat_cut_bin_certificate_sound certificate379 profilesValid379 numericValid379 valid379

def retention380 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(633433549736166949/21129754877601750596),(493931492817796329/500000000000000000),(27/10),(1361932712793713275117/640000000000000000000),true,MergedCutProfiles.Batch063.profile2522,![MergedCutProfiles.Batch063.profile2522,MergedCutProfiles.Batch063.profile2523,MergedCutProfiles.Batch061.profile2466,MergedCutProfiles.Batch063.profile2524,MergedCutProfiles.Batch063.profile2525,MergedCutProfiles.Batch061.profile2471,MergedCutProfiles.Batch062.profile2515,MergedCutProfiles.Batch063.profile2526,MergedCutProfiles.Batch062.profile2490,MergedCutProfiles.Batch063.profile2527,MergedCutProfiles.Batch062.profile2492,MergedCutProfiles.Batch063.profile2528,MergedCutProfiles.Batch063.profile2529,MergedCutProfiles.Batch063.profile2530,MergedCutProfiles.Batch063.profile2531,MergedCutProfiles.Batch063.profile2532]⟩
theorem profilesValid380 : retention380.ProfilesValid := by
  change ∀ j : Fin 16, (retention380.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch063.valid2522
  · exact MergedCutProfiles.Batch063.valid2523
  · exact MergedCutProfiles.Batch061.valid2466
  · exact MergedCutProfiles.Batch063.valid2524
  · exact MergedCutProfiles.Batch063.valid2525
  · exact MergedCutProfiles.Batch061.valid2471
  · exact MergedCutProfiles.Batch062.valid2515
  · exact MergedCutProfiles.Batch063.valid2526
  · exact MergedCutProfiles.Batch062.valid2490
  · exact MergedCutProfiles.Batch063.valid2527
  · exact MergedCutProfiles.Batch062.valid2492
  · exact MergedCutProfiles.Batch063.valid2528
  · exact MergedCutProfiles.Batch063.valid2529
  · exact MergedCutProfiles.Batch063.valid2530
  · exact MergedCutProfiles.Batch063.valid2531
  · exact MergedCutProfiles.Batch063.valid2532
theorem numericValid380 : retention380.NumericValid := by decide +kernel
def certificate380 : RatCutBinCertificate := ⟨⟨retention380,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(2099564115602593823/1000000000000000000)⟩,(995685607421386069/1000000000000000000),(38620321732971319/100000000000000000),(246364260832572599/1000000000000000000),(147589447923008721/1000000000000000000)⟩
theorem valid380 : certificate380.Valid := by decide +kernel
theorem sound380 : certificate380.Sound := rat_cut_bin_certificate_sound certificate380 profilesValid380 numericValid380 valid380

def retention381 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(4758540508867928107/42259509755203501192),(633433549736166949/500000000000000000),(11/5),(1185840856993282043249/640000000000000000000),true,MergedCutProfiles.Batch063.profile2533,![MergedCutProfiles.Batch063.profile2533,MergedCutProfiles.Batch063.profile2534,MergedCutProfiles.Batch063.profile2535,MergedCutProfiles.Batch063.profile2531,MergedCutProfiles.Batch063.profile2536,MergedCutProfiles.Batch063.profile2537,MergedCutProfiles.Batch063.profile2538,MergedCutProfiles.Batch063.profile2539,MergedCutProfiles.Batch063.profile2540,MergedCutProfiles.Batch063.profile2541,MergedCutProfiles.Batch063.profile2542,MergedCutProfiles.Batch063.profile2543,MergedCutProfiles.Batch063.profile2544,MergedCutProfiles.Batch063.profile2545,MergedCutProfiles.Batch063.profile2546,MergedCutProfiles.Batch063.profile2547]⟩
theorem profilesValid381 : retention381.ProfilesValid := by
  change ∀ j : Fin 16, (retention381.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch063.valid2533
  · exact MergedCutProfiles.Batch063.valid2534
  · exact MergedCutProfiles.Batch063.valid2535
  · exact MergedCutProfiles.Batch063.valid2531
  · exact MergedCutProfiles.Batch063.valid2536
  · exact MergedCutProfiles.Batch063.valid2537
  · exact MergedCutProfiles.Batch063.valid2538
  · exact MergedCutProfiles.Batch063.valid2539
  · exact MergedCutProfiles.Batch063.valid2540
  · exact MergedCutProfiles.Batch063.valid2541
  · exact MergedCutProfiles.Batch063.valid2542
  · exact MergedCutProfiles.Batch063.valid2543
  · exact MergedCutProfiles.Batch063.valid2544
  · exact MergedCutProfiles.Batch063.valid2545
  · exact MergedCutProfiles.Batch063.valid2546
  · exact MergedCutProfiles.Batch063.valid2547
theorem numericValid381 : retention381.NumericValid := by decide +kernel
def certificate381 : RatCutBinCertificate := ⟨⟨retention381,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(114355638744680081/62500000000000000)⟩,(995685607421386069/1000000000000000000),(401693054325508513/1000000000000000000),(231934678372694519/1000000000000000000),(147824897379617919/1000000000000000000)⟩
theorem valid381 : certificate381.Valid := by decide +kernel
theorem sound381 : certificate381.Sound := rat_cut_bin_certificate_sound certificate381 profilesValid381 numericValid381 valid381

def retention382 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(17521598977942512163/42259509755203501192),(4758540508867928107/1000000000000000000),(23/20),(8856102630958525567335377739796779018279/7613664814188684971200000000000000000000),false,MergedCutProfiles.Batch063.profile2548,(fun _ => MergedCutProfiles.Batch063.profile2548)⟩
theorem profilesValid382 : retention382.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2548
theorem numericValid382 : retention382.NumericValid := by decide +kernel
def certificate382 : RatCutBinCertificate := ⟨⟨retention382,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(575532749239734173/500000000000000000)⟩,(995685607421386069/1000000000000000000),(58404872347086469/125000000000000000),(35446397402743811/200000000000000000),(74632139025363857/500000000000000000)⟩
theorem valid382 : certificate382.Valid := by decide +kernel
theorem sound382 : certificate382.Sound := rat_cut_bin_certificate_sound certificate382 profilesValid382 numericValid382 valid382

def retention383 : RatCutRetentionCertificate := ⟨(139/4000),(7/200),(20750907314316814803/42259509755203501192),(17521598977942512163/1000000000000000000),1,(14082317128120847603924582313476886519/14017279182354009730400000000000000000),false,MergedCutProfiles.Batch063.profile2549,(fun _ => MergedCutProfiles.Batch063.profile2549)⟩
theorem profilesValid383 : retention383.ProfilesValid := by
  exact MergedCutProfiles.Batch063.valid2549
theorem numericValid383 : retention383.NumericValid := by decide +kernel
def certificate383 : RatCutBinCertificate := ⟨⟨retention383,(2023751653844675581/1000000000000000000),(853665110250683/15625000000000000),(5245761250897765603/500000000000000000),(221972292908710853387/500000000000000000),(248525271798640887/250000000000000000)⟩,(995685607421386069/1000000000000000000),(15268751950995819/31250000000000000),(8072956310291283/50000000000000000),(75607178858591389/500000000000000000)⟩
theorem valid383 : certificate383.Valid := by decide +kernel
theorem sound383 : certificate383.Sound := rat_cut_bin_certificate_sound certificate383 profilesValid383 numericValid383 valid383

def certificates : List RatCutBinCertificate := [certificate372,certificate373,certificate374,certificate375,certificate376,certificate377,certificate378,certificate379,certificate380,certificate381,certificate382,certificate383]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound372,List.forall_mem_cons.mpr ⟨sound373,List.forall_mem_cons.mpr ⟨sound374,List.forall_mem_cons.mpr ⟨sound375,List.forall_mem_cons.mpr ⟨sound376,List.forall_mem_cons.mpr ⟨sound377,List.forall_mem_cons.mpr ⟨sound378,List.forall_mem_cons.mpr ⟨sound379,List.forall_mem_cons.mpr ⟨sound380,List.forall_mem_cons.mpr ⟨sound381,List.forall_mem_cons.mpr ⟨sound382,List.forall_mem_cons.mpr ⟨sound383,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch031
