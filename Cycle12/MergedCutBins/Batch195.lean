import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch361
import Cycle12.MergedCutProfiles.Batch362
import Cycle12.MergedCutProfiles.Batch363
import Cycle12.MergedCutProfiles.Batch364

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch195

def retention2340 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(25138511537113931431/50959872109573080536),(892366103517235459/40000000000000000),1,(12791559075236577830557544477803225677/12748087193103363700000000000000000000),false,MergedCutProfiles.Batch361.profile14448,(fun _ => MergedCutProfiles.Batch361.profile14448)⟩
theorem profilesValid2340 : retention2340.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14448
theorem numericValid2340 : retention2340.NumericValid := by decide +kernel
def certificate2340 : RatCutBinCertificate := ⟨⟨retention2340,(474839029431201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(197090443192784601/200000000000000000)⟩,(498218111286115099/500000000000000000),(245027681180248991/1000000000000000000),(82054587939448537/200000000000000000),(192895559541278893/500000000000000000)⟩
theorem valid2340 : certificate2340.Valid := by decide +kernel
theorem sound2340 : certificate2340.Sound := rat_cut_bin_certificate_sound certificate2340 profilesValid2340 numericValid2340 valid2340

def retention2341 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(12694948326242535373/25479936054786540268),(25138511537113931431/1000000000000000000),1,(5002650730604520294391651751973957993/5027702307422786286200000000000000000),false,MergedCutProfiles.Batch361.profile14449,(fun _ => MergedCutProfiles.Batch361.profile14449)⟩
theorem profilesValid2341 : retention2341.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14449
theorem numericValid2341 : retention2341.NumericValid := by decide +kernel
def certificate2341 : RatCutBinCertificate := ⟨⟨retention2341,(474839029431201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(195411889900862777/200000000000000000)⟩,(498218111286115099/500000000000000000),(247132425272666993/1000000000000000000),(407326897050485023/1000000000000000000),(7634028485127633/20000000000000000)⟩
theorem valid2341 : certificate2341.Valid := by decide +kernel
theorem sound2341 : certificate2341.Sound := rat_cut_bin_certificate_sound certificate2341 profilesValid2341 numericValid2341 valid2341

def retention2342 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),(12694948326242535373/500000000000000000),1,(4028449790170788122119077279614110359/4062383464397611319360000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid2342 : retention2342.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid2342 : retention2342.NumericValid := by decide +kernel
def certificate2342 : RatCutBinCertificate := ⟨⟨retention2342,(474839029431201179/200000000000000000),(5622540848385301/62500000000000000),(5946856131163015797/500000000000000000),(609442028547261214253/1000000000000000000),(121711126920592849/125000000000000000)⟩,(498218111286115099/500000000000000000),(49597575320519809/200000000000000000),(81226913499590813/200000000000000000),(5929071077741989/15625000000000000)⟩
theorem valid2342 : certificate2342.Valid := by decide +kernel
theorem sound2342 : certificate2342.Sound := rat_cut_bin_certificate_sound certificate2342 profilesValid2342 numericValid2342 valid2342

def retention2343 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(802978156357610702/48451473133868985059),(397513938790896387/500000000000000000),(33/10),(88688844658279455927/40000000000000000000),true,MergedCutProfiles.Batch361.profile14450,![MergedCutProfiles.Batch361.profile14450,MergedCutProfiles.Batch361.profile14451,MergedCutProfiles.Batch361.profile14452,MergedCutProfiles.Batch361.profile14453,MergedCutProfiles.Batch361.profile14454,MergedCutProfiles.Batch361.profile14455,MergedCutProfiles.Batch361.profile14456,MergedCutProfiles.Batch361.profile14457,MergedCutProfiles.Batch361.profile14458,MergedCutProfiles.Batch361.profile14459,MergedCutProfiles.Batch361.profile14460,MergedCutProfiles.Batch361.profile14461,MergedCutProfiles.Batch361.profile14462,MergedCutProfiles.Batch361.profile14463,MergedCutProfiles.Batch361.profile14464,MergedCutProfiles.Batch361.profile14465]⟩
theorem profilesValid2343 : retention2343.ProfilesValid := by
  change ∀ j : Fin 16, (retention2343.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch361.valid14450
  · exact MergedCutProfiles.Batch361.valid14451
  · exact MergedCutProfiles.Batch361.valid14452
  · exact MergedCutProfiles.Batch361.valid14453
  · exact MergedCutProfiles.Batch361.valid14454
  · exact MergedCutProfiles.Batch361.valid14455
  · exact MergedCutProfiles.Batch361.valid14456
  · exact MergedCutProfiles.Batch361.valid14457
  · exact MergedCutProfiles.Batch361.valid14458
  · exact MergedCutProfiles.Batch361.valid14459
  · exact MergedCutProfiles.Batch361.valid14460
  · exact MergedCutProfiles.Batch361.valid14461
  · exact MergedCutProfiles.Batch361.valid14462
  · exact MergedCutProfiles.Batch361.valid14463
  · exact MergedCutProfiles.Batch361.valid14464
  · exact MergedCutProfiles.Batch361.valid14465
theorem numericValid2343 : retention2343.NumericValid := by decide +kernel
def certificate2343 : RatCutBinCertificate := ⟨⟨retention2343,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(1081595557654212817/500000000000000000)⟩,(996764798866066293/1000000000000000000),(49311027488982481/125000000000000000),(119285331575048201/500000000000000000),(24929571169862343/200000000000000000)⟩
theorem valid2343 : certificate2343.Valid := by decide +kernel
theorem sound2343 : certificate2343.Sound := rat_cut_bin_certificate_sound certificate2343 profilesValid2343 numericValid2343 valid2343

def retention2344 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(941555038485136879/48451473133868985059),(401489078178805351/500000000000000000),(13/4),(11260400195914954331/5120000000000000000),true,MergedCutProfiles.Batch361.profile14466,![MergedCutProfiles.Batch361.profile14466,MergedCutProfiles.Batch361.profile14467,MergedCutProfiles.Batch361.profile14468,MergedCutProfiles.Batch361.profile14469,MergedCutProfiles.Batch361.profile14470,MergedCutProfiles.Batch361.profile14456,MergedCutProfiles.Batch361.profile14471,MergedCutProfiles.Batch361.profile14472,MergedCutProfiles.Batch361.profile14473,MergedCutProfiles.Batch361.profile14474,MergedCutProfiles.Batch361.profile14475,MergedCutProfiles.Batch361.profile14476,MergedCutProfiles.Batch361.profile14477,MergedCutProfiles.Batch361.profile14478,MergedCutProfiles.Batch361.profile14479,MergedCutProfiles.Batch362.profile14480]⟩
theorem profilesValid2344 : retention2344.ProfilesValid := by
  change ∀ j : Fin 16, (retention2344.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch361.valid14466
  · exact MergedCutProfiles.Batch361.valid14467
  · exact MergedCutProfiles.Batch361.valid14468
  · exact MergedCutProfiles.Batch361.valid14469
  · exact MergedCutProfiles.Batch361.valid14470
  · exact MergedCutProfiles.Batch361.valid14456
  · exact MergedCutProfiles.Batch361.valid14471
  · exact MergedCutProfiles.Batch361.valid14472
  · exact MergedCutProfiles.Batch361.valid14473
  · exact MergedCutProfiles.Batch361.valid14474
  · exact MergedCutProfiles.Batch361.valid14475
  · exact MergedCutProfiles.Batch361.valid14476
  · exact MergedCutProfiles.Batch361.valid14477
  · exact MergedCutProfiles.Batch361.valid14478
  · exact MergedCutProfiles.Batch361.valid14479
  · exact MergedCutProfiles.Batch362.valid14480
theorem numericValid2344 : retention2344.NumericValid := by decide +kernel
def certificate2344 : RatCutBinCertificate := ⟨⟨retention2344,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(2146085531130420809/1000000000000000000)⟩,(996764798866066293/1000000000000000000),(395709624710021953/1000000000000000000),(118718250048732619/500000000000000000),(124650449731773909/1000000000000000000)⟩
theorem valid2344 : certificate2344.Valid := by decide +kernel
theorem sound2344 : certificate2344.Sound := rat_cut_bin_certificate_sound certificate2344 profilesValid2344 numericValid2344 valid2344

def retention2345 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1017301393000000000/48451473133868985059),(941555038485136879/1000000000000000000),(57/20),(2796941511116074541671/1280000000000000000000),true,MergedCutProfiles.Batch362.profile14481,![MergedCutProfiles.Batch362.profile14481,MergedCutProfiles.Batch362.profile14482,MergedCutProfiles.Batch362.profile14483,MergedCutProfiles.Batch362.profile14484,MergedCutProfiles.Batch362.profile14485,MergedCutProfiles.Batch362.profile14486,MergedCutProfiles.Batch362.profile14487,MergedCutProfiles.Batch362.profile14488,MergedCutProfiles.Batch362.profile14489,MergedCutProfiles.Batch362.profile14490,MergedCutProfiles.Batch361.profile14463,MergedCutProfiles.Batch362.profile14491,MergedCutProfiles.Batch361.profile14478,MergedCutProfiles.Batch362.profile14492,MergedCutProfiles.Batch362.profile14493,MergedCutProfiles.Batch362.profile14494]⟩
theorem profilesValid2345 : retention2345.ProfilesValid := by
  change ∀ j : Fin 16, (retention2345.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch362.valid14481
  · exact MergedCutProfiles.Batch362.valid14482
  · exact MergedCutProfiles.Batch362.valid14483
  · exact MergedCutProfiles.Batch362.valid14484
  · exact MergedCutProfiles.Batch362.valid14485
  · exact MergedCutProfiles.Batch362.valid14486
  · exact MergedCutProfiles.Batch362.valid14487
  · exact MergedCutProfiles.Batch362.valid14488
  · exact MergedCutProfiles.Batch362.valid14489
  · exact MergedCutProfiles.Batch362.valid14490
  · exact MergedCutProfiles.Batch361.valid14463
  · exact MergedCutProfiles.Batch362.valid14491
  · exact MergedCutProfiles.Batch361.valid14478
  · exact MergedCutProfiles.Batch362.valid14492
  · exact MergedCutProfiles.Batch362.valid14493
  · exact MergedCutProfiles.Batch362.valid14494
theorem numericValid2345 : retention2345.NumericValid := by decide +kernel
def certificate2345 : RatCutBinCertificate := ⟨⟨retention2345,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(21384483455411013/10000000000000000)⟩,(996764798866066293/1000000000000000000),(46090093267016343/125000000000000000),(13169868818813019/50000000000000000),(30773173965081057/200000000000000000)⟩
theorem valid2345 : certificate2345.Valid := by decide +kernel
theorem sound2345 : certificate2345.Sound := rat_cut_bin_certificate_sound certificate2345 profilesValid2345 numericValid2345 valid2345

def retention2346 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1019569187141535499/48451473133868985059),(1017301393/1000000000),(53/20),(4349163959181062003/2000000000000000000),true,MergedCutProfiles.Batch362.profile14481,![MergedCutProfiles.Batch362.profile14481,MergedCutProfiles.Batch362.profile14495,MergedCutProfiles.Batch362.profile14483,MergedCutProfiles.Batch362.profile14484,MergedCutProfiles.Batch362.profile14496,MergedCutProfiles.Batch362.profile14486,MergedCutProfiles.Batch362.profile14487,MergedCutProfiles.Batch362.profile14497,MergedCutProfiles.Batch362.profile14489,MergedCutProfiles.Batch362.profile14490,MergedCutProfiles.Batch361.profile14463,MergedCutProfiles.Batch361.profile14477,MergedCutProfiles.Batch361.profile14478,MergedCutProfiles.Batch362.profile14492,MergedCutProfiles.Batch362.profile14493,MergedCutProfiles.Batch362.profile14498]⟩
theorem profilesValid2346 : retention2346.ProfilesValid := by
  change ∀ j : Fin 16, (retention2346.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch362.valid14481
  · exact MergedCutProfiles.Batch362.valid14495
  · exact MergedCutProfiles.Batch362.valid14483
  · exact MergedCutProfiles.Batch362.valid14484
  · exact MergedCutProfiles.Batch362.valid14496
  · exact MergedCutProfiles.Batch362.valid14486
  · exact MergedCutProfiles.Batch362.valid14487
  · exact MergedCutProfiles.Batch362.valid14497
  · exact MergedCutProfiles.Batch362.valid14489
  · exact MergedCutProfiles.Batch362.valid14490
  · exact MergedCutProfiles.Batch361.valid14463
  · exact MergedCutProfiles.Batch361.valid14477
  · exact MergedCutProfiles.Batch361.valid14478
  · exact MergedCutProfiles.Batch362.valid14492
  · exact MergedCutProfiles.Batch362.valid14493
  · exact MergedCutProfiles.Batch362.valid14498
theorem numericValid2346 : retention2346.NumericValid := by decide +kernel
def certificate2346 : RatCutBinCertificate := ⟨⟨retention2346,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(532798580646778853/250000000000000000)⟩,(996764798866066293/1000000000000000000),(71536026178817049/200000000000000000),(6864461714203309/25000000000000000),(10590182629128119/62500000000000000)⟩
theorem valid2346 : certificate2346.Valid := by decide +kernel
theorem sound2346 : certificate2346.Sound := rat_cut_bin_certificate_sound certificate2346 profilesValid2346 numericValid2346 valid2346

def retention2347 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1050463153081111167/48451473133868985059),(1019569187141535499/1000000000000000000),(53/20),(86924479109152584001/40000000000000000000),true,MergedCutProfiles.Batch362.profile14499,![MergedCutProfiles.Batch362.profile14499,MergedCutProfiles.Batch362.profile14500,MergedCutProfiles.Batch362.profile14501,MergedCutProfiles.Batch362.profile14502,MergedCutProfiles.Batch362.profile14503,MergedCutProfiles.Batch362.profile14504,MergedCutProfiles.Batch362.profile14505,MergedCutProfiles.Batch362.profile14506,MergedCutProfiles.Batch362.profile14507,MergedCutProfiles.Batch362.profile14508,MergedCutProfiles.Batch362.profile14509,MergedCutProfiles.Batch362.profile14510,MergedCutProfiles.Batch362.profile14511,MergedCutProfiles.Batch362.profile14512,MergedCutProfiles.Batch362.profile14513,MergedCutProfiles.Batch362.profile14514]⟩
theorem profilesValid2347 : retention2347.ProfilesValid := by
  change ∀ j : Fin 16, (retention2347.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch362.valid14499
  · exact MergedCutProfiles.Batch362.valid14500
  · exact MergedCutProfiles.Batch362.valid14501
  · exact MergedCutProfiles.Batch362.valid14502
  · exact MergedCutProfiles.Batch362.valid14503
  · exact MergedCutProfiles.Batch362.valid14504
  · exact MergedCutProfiles.Batch362.valid14505
  · exact MergedCutProfiles.Batch362.valid14506
  · exact MergedCutProfiles.Batch362.valid14507
  · exact MergedCutProfiles.Batch362.valid14508
  · exact MergedCutProfiles.Batch362.valid14509
  · exact MergedCutProfiles.Batch362.valid14510
  · exact MergedCutProfiles.Batch362.valid14511
  · exact MergedCutProfiles.Batch362.valid14512
  · exact MergedCutProfiles.Batch362.valid14513
  · exact MergedCutProfiles.Batch362.valid14514
theorem numericValid2347 : retention2347.NumericValid := by decide +kernel
def certificate2347 : RatCutBinCertificate := ⟨⟨retention2347,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(2129724326474952663/1000000000000000000)⟩,(996764798866066293/1000000000000000000),(8939670541141329/25000000000000000),(54934880200601321/200000000000000000),(2648418416984187/15625000000000000)⟩
theorem valid2347 : certificate2347.Valid := by decide +kernel
theorem sound2347 : certificate2347.Sound := rat_cut_bin_certificate_sound certificate2347 profilesValid2347 numericValid2347 valid2347

def retention2348 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1488088997763997691/48451473133868985059),(1050463153081111167/1000000000000000000),(13/5),(2735479574961728434723/1280000000000000000000),true,MergedCutProfiles.Batch362.profile14515,![MergedCutProfiles.Batch362.profile14515,MergedCutProfiles.Batch362.profile14516,MergedCutProfiles.Batch362.profile14517,MergedCutProfiles.Batch362.profile14518,MergedCutProfiles.Batch362.profile14519,MergedCutProfiles.Batch363.profile14520,MergedCutProfiles.Batch361.profile14462,MergedCutProfiles.Batch363.profile14521,MergedCutProfiles.Batch363.profile14522,MergedCutProfiles.Batch363.profile14523,MergedCutProfiles.Batch362.profile14498,MergedCutProfiles.Batch363.profile14524,MergedCutProfiles.Batch363.profile14525,MergedCutProfiles.Batch363.profile14526,MergedCutProfiles.Batch363.profile14527,MergedCutProfiles.Batch363.profile14528]⟩
theorem profilesValid2348 : retention2348.ProfilesValid := by
  change ∀ j : Fin 16, (retention2348.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch362.valid14515
  · exact MergedCutProfiles.Batch362.valid14516
  · exact MergedCutProfiles.Batch362.valid14517
  · exact MergedCutProfiles.Batch362.valid14518
  · exact MergedCutProfiles.Batch362.valid14519
  · exact MergedCutProfiles.Batch363.valid14520
  · exact MergedCutProfiles.Batch361.valid14462
  · exact MergedCutProfiles.Batch363.valid14521
  · exact MergedCutProfiles.Batch363.valid14522
  · exact MergedCutProfiles.Batch363.valid14523
  · exact MergedCutProfiles.Batch362.valid14498
  · exact MergedCutProfiles.Batch363.valid14524
  · exact MergedCutProfiles.Batch363.valid14525
  · exact MergedCutProfiles.Batch363.valid14526
  · exact MergedCutProfiles.Batch363.valid14527
  · exact MergedCutProfiles.Batch363.valid14528
theorem numericValid2348 : retention2348.NumericValid := by decide +kernel
def certificate2348 : RatCutBinCertificate := ⟨⟨retention2348,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(1047262214401870309/500000000000000000)⟩,(996764798866066293/1000000000000000000),(89758200912432677/250000000000000000),(273190495827758573/1000000000000000000),(84655712559953449/500000000000000000)⟩
theorem valid2348 : certificate2348.Valid := by decide +kernel
theorem sound2348 : certificate2348.Sound := rat_cut_bin_certificate_sound certificate2348 profilesValid2348 numericValid2348 valid2348

def retention2349 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(7026890982785445851/48451473133868985059),(1488088997763997691/1000000000000000000),2,(453887306853312891787/256000000000000000000),true,MergedCutProfiles.Batch363.profile14529,![MergedCutProfiles.Batch363.profile14529,MergedCutProfiles.Batch363.profile14530,MergedCutProfiles.Batch363.profile14531,MergedCutProfiles.Batch363.profile14532,MergedCutProfiles.Batch363.profile14533,MergedCutProfiles.Batch363.profile14534,MergedCutProfiles.Batch363.profile14535,MergedCutProfiles.Batch363.profile14536,MergedCutProfiles.Batch363.profile14537,MergedCutProfiles.Batch363.profile14538,MergedCutProfiles.Batch363.profile14539,MergedCutProfiles.Batch363.profile14540,MergedCutProfiles.Batch363.profile14541,MergedCutProfiles.Batch363.profile14542,MergedCutProfiles.Batch363.profile14543,MergedCutProfiles.Batch363.profile14544]⟩
theorem profilesValid2349 : retention2349.ProfilesValid := by
  change ∀ j : Fin 16, (retention2349.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch363.valid14529
  · exact MergedCutProfiles.Batch363.valid14530
  · exact MergedCutProfiles.Batch363.valid14531
  · exact MergedCutProfiles.Batch363.valid14532
  · exact MergedCutProfiles.Batch363.valid14533
  · exact MergedCutProfiles.Batch363.valid14534
  · exact MergedCutProfiles.Batch363.valid14535
  · exact MergedCutProfiles.Batch363.valid14536
  · exact MergedCutProfiles.Batch363.valid14537
  · exact MergedCutProfiles.Batch363.valid14538
  · exact MergedCutProfiles.Batch363.valid14539
  · exact MergedCutProfiles.Batch363.valid14540
  · exact MergedCutProfiles.Batch363.valid14541
  · exact MergedCutProfiles.Batch363.valid14542
  · exact MergedCutProfiles.Batch363.valid14543
  · exact MergedCutProfiles.Batch363.valid14544
theorem numericValid2349 : retention2349.NumericValid := by decide +kernel
def certificate2349 : RatCutBinCertificate := ⟨⟨retention2349,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(1740252074639485559/1000000000000000000)⟩,(996764798866066293/1000000000000000000),(378815434247820471/1000000000000000000),(253463555440487579/1000000000000000000),(42504525029333639/250000000000000000)⟩
theorem valid2349 : certificate2349.Valid := by decide +kernel
theorem sound2349 : certificate2349.Sound := rat_cut_bin_certificate_sound certificate2349 profilesValid2349 numericValid2349 valid2349

def retention2350 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(21416923207518398013/48451473133868985059),(7026890982785445851/1000000000000000000),1,(275350938261046295531/256000000000000000000),true,MergedCutProfiles.Batch363.profile14545,![MergedCutProfiles.Batch363.profile14545,MergedCutProfiles.Batch363.profile14546,MergedCutProfiles.Batch363.profile14547,MergedCutProfiles.Batch363.profile14548,MergedCutProfiles.Batch363.profile14549,MergedCutProfiles.Batch363.profile14550,MergedCutProfiles.Batch363.profile14551,MergedCutProfiles.Batch363.profile14552,MergedCutProfiles.Batch363.profile14553,MergedCutProfiles.Batch363.profile14554,MergedCutProfiles.Batch363.profile14555,MergedCutProfiles.Batch363.profile14556,MergedCutProfiles.Batch363.profile14557,MergedCutProfiles.Batch363.profile14558,MergedCutProfiles.Batch363.profile14559,MergedCutProfiles.Batch364.profile14560]⟩
theorem profilesValid2350 : retention2350.ProfilesValid := by
  change ∀ j : Fin 16, (retention2350.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch363.valid14545
  · exact MergedCutProfiles.Batch363.valid14546
  · exact MergedCutProfiles.Batch363.valid14547
  · exact MergedCutProfiles.Batch363.valid14548
  · exact MergedCutProfiles.Batch363.valid14549
  · exact MergedCutProfiles.Batch363.valid14550
  · exact MergedCutProfiles.Batch363.valid14551
  · exact MergedCutProfiles.Batch363.valid14552
  · exact MergedCutProfiles.Batch363.valid14553
  · exact MergedCutProfiles.Batch363.valid14554
  · exact MergedCutProfiles.Batch363.valid14555
  · exact MergedCutProfiles.Batch363.valid14556
  · exact MergedCutProfiles.Batch363.valid14557
  · exact MergedCutProfiles.Batch363.valid14558
  · exact MergedCutProfiles.Batch363.valid14559
  · exact MergedCutProfiles.Batch364.valid14560
theorem numericValid2350 : retention2350.NumericValid := by decide +kernel
def certificate2350 : RatCutBinCertificate := ⟨⟨retention2350,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(1059217503042218471/1000000000000000000)⟩,(996764798866066293/1000000000000000000),(114167371473401057/250000000000000000),(185394858952701801/1000000000000000000),(170058769978765637/1000000000000000000)⟩
theorem valid2350 : certificate2350.Valid := by decide +kernel
theorem sound2350 : certificate2350.Sound := rat_cut_bin_certificate_sound certificate2350 profilesValid2350 numericValid2350 valid2350

def retention2351 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(23894183305590099451/48451473133868985059),(21416923207518398013/1000000000000000000),1,(17188597284329473724820384534623271871/17133538566014718410400000000000000000),false,MergedCutProfiles.Batch364.profile14561,(fun _ => MergedCutProfiles.Batch364.profile14561)⟩
theorem profilesValid2351 : retention2351.ProfilesValid := by
  exact MergedCutProfiles.Batch364.valid14561
theorem numericValid2351 : retention2351.NumericValid := by decide +kernel
def certificate2351 : RatCutBinCertificate := ⟨⟨retention2351,(2092104631341272169/1000000000000000000),(11819389720817643/125000000000000000),(6041489091680422967/500000000000000000),(588684561178441291931/1000000000000000000),(493420828639815713/500000000000000000)⟩,(996764798866066293/1000000000000000000),(229027435278234797/500000000000000000),(92155555087960907/500000000000000000),(17329722430324163/100000000000000000)⟩
theorem valid2351 : certificate2351.Valid := by decide +kernel
theorem sound2351 : certificate2351.Sound := rat_cut_bin_certificate_sound certificate2351 profilesValid2351 numericValid2351 valid2351

def certificates : List RatCutBinCertificate := [certificate2340,certificate2341,certificate2342,certificate2343,certificate2344,certificate2345,certificate2346,certificate2347,certificate2348,certificate2349,certificate2350,certificate2351]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2340,List.forall_mem_cons.mpr ⟨sound2341,List.forall_mem_cons.mpr ⟨sound2342,List.forall_mem_cons.mpr ⟨sound2343,List.forall_mem_cons.mpr ⟨sound2344,List.forall_mem_cons.mpr ⟨sound2345,List.forall_mem_cons.mpr ⟨sound2346,List.forall_mem_cons.mpr ⟨sound2347,List.forall_mem_cons.mpr ⟨sound2348,List.forall_mem_cons.mpr ⟨sound2349,List.forall_mem_cons.mpr ⟨sound2350,List.forall_mem_cons.mpr ⟨sound2351,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch195
