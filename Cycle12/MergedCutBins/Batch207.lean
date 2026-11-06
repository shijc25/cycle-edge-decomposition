import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch191
import Cycle12.MergedCutProfiles.Batch192
import Cycle12.MergedCutProfiles.Batch193
import Cycle12.MergedCutProfiles.Batch386
import Cycle12.MergedCutProfiles.Batch387
import Cycle12.MergedCutProfiles.Batch388

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch207

def retention2484 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(13748326248615219457/30628615555587275304),(1348902944002520283/250000000000000000),(21/20),(578649085002654175975133588208768285551/539561177601008113200000000000000000000),false,MergedCutProfiles.Batch386.profile15457,(fun _ => MergedCutProfiles.Batch386.profile15457)⟩
theorem profilesValid2484 : retention2484.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15457
theorem numericValid2484 : retention2484.NumericValid := by decide +kernel
def certificate2484 : RatCutBinCertificate := ⟨⟨retention2484,(1233255741346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(1045403940399363037/1000000000000000000)⟩,(199036603016851301/200000000000000000),(224309158186089581/1000000000000000000),(13757712096151763/31250000000000000),(5794719205337439/15625000000000000)⟩
theorem valid2484 : certificate2484.Valid := by decide +kernel
theorem sound2484 : certificate2484.Sound := rat_cut_bin_certificate_sound certificate2484 profilesValid2484 numericValid2484 valid2484

def retention2485 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(3796676340397998947/7657153888896818826),(13748326248615219457/1000000000000000000),1,(1557687571612410431964947219954918889/1571237285556025080800000000000000000),false,MergedCutProfiles.Batch386.profile15458,(fun _ => MergedCutProfiles.Batch386.profile15458)⟩
theorem profilesValid2485 : retention2485.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15458
theorem numericValid2485 : retention2485.NumericValid := by decide +kernel
def certificate2485 : RatCutBinCertificate := ⟨⟨retention2485,(1233255741346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(482812491623184949/500000000000000000)⟩,(199036603016851301/200000000000000000),(60710338356990627/250000000000000000),(413352040023989249/1000000000000000000),(23192873808365553/62500000000000000)⟩
theorem valid2485 : certificate2485.Valid := by decide +kernel
theorem sound2485 : certificate2485.Sound := rat_cut_bin_certificate_sound certificate2485 profilesValid2485 numericValid2485 valid2485

def retention2486 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),(3796676340397998947/250000000000000000),1,(11967847827416239494117147128307115227/12149364289273596630400000000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid2486 : retention2486.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid2486 : retention2486.NumericValid := by decide +kernel
def certificate2486 : RatCutBinCertificate := ⟨⟨retention2486,(1233255741346584823/500000000000000000),(14887102204219317/100000000000000000),(285189018766043241/20000000000000000),(27458151097991125517/62500000000000000),(59956764382718417/62500000000000000)⟩,(199036603016851301/200000000000000000),(244440389930997467/1000000000000000000),(411098152802210667/1000000000000000000),(369091696099451733/1000000000000000000)⟩
theorem valid2486 : certificate2486.Valid := by decide +kernel
theorem sound2486 : certificate2486.Sound := rat_cut_bin_certificate_sound certificate2486 profilesValid2486 numericValid2486 valid2486

def retention2487 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(887110394428382498/29990236408876285893),(439163561598209157/500000000000000000),(57/20),(10666228181148423993/5000000000000000000),true,MergedCutProfiles.Batch386.profile15459,![MergedCutProfiles.Batch386.profile15459,MergedCutProfiles.Batch386.profile15460,MergedCutProfiles.Batch386.profile15461,MergedCutProfiles.Batch386.profile15462,MergedCutProfiles.Batch386.profile15463,MergedCutProfiles.Batch386.profile15464,MergedCutProfiles.Batch386.profile15465,MergedCutProfiles.Batch386.profile15466,MergedCutProfiles.Batch386.profile15467,MergedCutProfiles.Batch386.profile15468,MergedCutProfiles.Batch386.profile15469,MergedCutProfiles.Batch386.profile15470,MergedCutProfiles.Batch386.profile15471,MergedCutProfiles.Batch386.profile15472,MergedCutProfiles.Batch386.profile15473,MergedCutProfiles.Batch386.profile15474]⟩
theorem profilesValid2487 : retention2487.ProfilesValid := by
  change ∀ j : Fin 16, (retention2487.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch386.valid15459
  · exact MergedCutProfiles.Batch386.valid15460
  · exact MergedCutProfiles.Batch386.valid15461
  · exact MergedCutProfiles.Batch386.valid15462
  · exact MergedCutProfiles.Batch386.valid15463
  · exact MergedCutProfiles.Batch386.valid15464
  · exact MergedCutProfiles.Batch386.valid15465
  · exact MergedCutProfiles.Batch386.valid15466
  · exact MergedCutProfiles.Batch386.valid15467
  · exact MergedCutProfiles.Batch386.valid15468
  · exact MergedCutProfiles.Batch386.valid15469
  · exact MergedCutProfiles.Batch386.valid15470
  · exact MergedCutProfiles.Batch386.valid15471
  · exact MergedCutProfiles.Batch386.valid15472
  · exact MergedCutProfiles.Batch386.valid15473
  · exact MergedCutProfiles.Batch386.valid15474
theorem numericValid2487 : retention2487.NumericValid := by decide +kernel
def certificate2487 : RatCutBinCertificate := ⟨⟨retention2487,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(516756127620627581/250000000000000000)⟩,(99567232708146153/100000000000000000),(66905720773791339/200000000000000000),(299142598779006883/1000000000000000000),(167355124048132387/1000000000000000000)⟩
theorem valid2487 : certificate2487.Valid := by decide +kernel
theorem sound2487 : certificate2487.Sound := rat_cut_bin_certificate_sound certificate2487 profilesValid2487 numericValid2487 valid2487

def retention2488 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(989720987061530354/29990236408876285893),(443555197214191249/500000000000000000),(57/20),(42519567623822954349/20000000000000000000),true,MergedCutProfiles.Batch386.profile15475,![MergedCutProfiles.Batch386.profile15475,MergedCutProfiles.Batch386.profile15476,MergedCutProfiles.Batch386.profile15477,MergedCutProfiles.Batch386.profile15478,MergedCutProfiles.Batch386.profile15479,MergedCutProfiles.Batch387.profile15480,MergedCutProfiles.Batch387.profile15481,MergedCutProfiles.Batch387.profile15482,MergedCutProfiles.Batch387.profile15483,MergedCutProfiles.Batch387.profile15484,MergedCutProfiles.Batch387.profile15485,MergedCutProfiles.Batch191.profile7674,MergedCutProfiles.Batch387.profile15486,MergedCutProfiles.Batch387.profile15487,MergedCutProfiles.Batch387.profile15488,MergedCutProfiles.Batch387.profile15489]⟩
theorem profilesValid2488 : retention2488.ProfilesValid := by
  change ∀ j : Fin 16, (retention2488.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch386.valid15475
  · exact MergedCutProfiles.Batch386.valid15476
  · exact MergedCutProfiles.Batch386.valid15477
  · exact MergedCutProfiles.Batch386.valid15478
  · exact MergedCutProfiles.Batch386.valid15479
  · exact MergedCutProfiles.Batch387.valid15480
  · exact MergedCutProfiles.Batch387.valid15481
  · exact MergedCutProfiles.Batch387.valid15482
  · exact MergedCutProfiles.Batch387.valid15483
  · exact MergedCutProfiles.Batch387.valid15484
  · exact MergedCutProfiles.Batch387.valid15485
  · exact MergedCutProfiles.Batch191.valid7674
  · exact MergedCutProfiles.Batch387.valid15486
  · exact MergedCutProfiles.Batch387.valid15487
  · exact MergedCutProfiles.Batch387.valid15488
  · exact MergedCutProfiles.Batch387.valid15489
theorem numericValid2488 : retention2488.NumericValid := by decide +kernel
def certificate2488 : RatCutBinCertificate := ⟨⟨retention2488,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(514939336666051207/250000000000000000)⟩,(99567232708146153/100000000000000000),(334280004642689493/1000000000000000000),(74853713313856133/250000000000000000),(83711387123567357/500000000000000000)⟩
theorem valid2488 : certificate2488.Valid := by decide +kernel
theorem sound2488 : certificate2488.Sound := rat_cut_bin_certificate_sound certificate2488 profilesValid2488 numericValid2488 valid2488

def retention2489 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(110391232000000000/3332248489875142877),(494860493530765177/500000000000000000),(53/20),(2662126523304734653/1250000000000000000),true,MergedCutProfiles.Batch386.profile15475,![MergedCutProfiles.Batch386.profile15475,MergedCutProfiles.Batch386.profile15476,MergedCutProfiles.Batch386.profile15477,MergedCutProfiles.Batch386.profile15478,MergedCutProfiles.Batch387.profile15490,MergedCutProfiles.Batch387.profile15491,MergedCutProfiles.Batch387.profile15481,MergedCutProfiles.Batch387.profile15482,MergedCutProfiles.Batch387.profile15483,MergedCutProfiles.Batch387.profile15484,MergedCutProfiles.Batch387.profile15492,MergedCutProfiles.Batch191.profile7674,MergedCutProfiles.Batch387.profile15493,MergedCutProfiles.Batch387.profile15487,MergedCutProfiles.Batch387.profile15488,MergedCutProfiles.Batch387.profile15489]⟩
theorem profilesValid2489 : retention2489.ProfilesValid := by
  change ∀ j : Fin 16, (retention2489.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch386.valid15475
  · exact MergedCutProfiles.Batch386.valid15476
  · exact MergedCutProfiles.Batch386.valid15477
  · exact MergedCutProfiles.Batch386.valid15478
  · exact MergedCutProfiles.Batch387.valid15490
  · exact MergedCutProfiles.Batch387.valid15491
  · exact MergedCutProfiles.Batch387.valid15481
  · exact MergedCutProfiles.Batch387.valid15482
  · exact MergedCutProfiles.Batch387.valid15483
  · exact MergedCutProfiles.Batch387.valid15484
  · exact MergedCutProfiles.Batch387.valid15492
  · exact MergedCutProfiles.Batch191.valid7674
  · exact MergedCutProfiles.Batch387.valid15493
  · exact MergedCutProfiles.Batch387.valid15487
  · exact MergedCutProfiles.Batch387.valid15488
  · exact MergedCutProfiles.Batch387.valid15489
theorem numericValid2489 : retention2489.NumericValid := by decide +kernel
def certificate2489 : RatCutBinCertificate := ⟨⟨retention2489,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(1034063789927280097/500000000000000000)⟩,(99567232708146153/100000000000000000),(63634607675463919/200000000000000000),(158726938202453223/500000000000000000),(23745072514611791/125000000000000000)⟩
theorem valid2489 : certificate2489.Valid := by decide +kernel
theorem sound2489 : certificate2489.Sound := rat_cut_bin_certificate_sound certificate2489 profilesValid2489 numericValid2489 valid2489

def retention2490 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1126394804878530280/29990236408876285893),(15523767/15625000),(53/20),(676788526103750089/320000000000000000),true,MergedCutProfiles.Batch387.profile15494,![MergedCutProfiles.Batch387.profile15494,MergedCutProfiles.Batch387.profile15495,MergedCutProfiles.Batch387.profile15496,MergedCutProfiles.Batch387.profile15497,MergedCutProfiles.Batch387.profile15498,MergedCutProfiles.Batch191.profile7671,MergedCutProfiles.Batch387.profile15499,MergedCutProfiles.Batch192.profile7715,MergedCutProfiles.Batch387.profile15500,MergedCutProfiles.Batch387.profile15501,MergedCutProfiles.Batch386.profile15472,MergedCutProfiles.Batch192.profile7690,MergedCutProfiles.Batch387.profile15502,MergedCutProfiles.Batch387.profile15503,MergedCutProfiles.Batch191.profile7677,MergedCutProfiles.Batch387.profile15504]⟩
theorem profilesValid2490 : retention2490.ProfilesValid := by
  change ∀ j : Fin 16, (retention2490.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch387.valid15494
  · exact MergedCutProfiles.Batch387.valid15495
  · exact MergedCutProfiles.Batch387.valid15496
  · exact MergedCutProfiles.Batch387.valid15497
  · exact MergedCutProfiles.Batch387.valid15498
  · exact MergedCutProfiles.Batch191.valid7671
  · exact MergedCutProfiles.Batch387.valid15499
  · exact MergedCutProfiles.Batch192.valid7715
  · exact MergedCutProfiles.Batch387.valid15500
  · exact MergedCutProfiles.Batch387.valid15501
  · exact MergedCutProfiles.Batch386.valid15472
  · exact MergedCutProfiles.Batch192.valid7690
  · exact MergedCutProfiles.Batch387.valid15502
  · exact MergedCutProfiles.Batch387.valid15503
  · exact MergedCutProfiles.Batch191.valid7677
  · exact MergedCutProfiles.Batch387.valid15504
theorem numericValid2490 : retention2490.NumericValid := by decide +kernel
def certificate2490 : RatCutBinCertificate := ⟨⟨retention2490,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(513347634139579909/250000000000000000)⟩,(99567232708146153/100000000000000000),(159982580499079953/500000000000000000),(788518299739317/2500000000000000),(46965458902390819/250000000000000000)⟩
theorem valid2490 : certificate2490.Valid := by decide +kernel
theorem sound2490 : certificate2490.Sound := rat_cut_bin_certificate_sound certificate2490 profilesValid2490 numericValid2490 valid2490

def retention2491 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(2496896504542793752/29990236408876285893),(28159870121963257/25000000000000000),(47/20),(15640520471062125237/8000000000000000000),true,MergedCutProfiles.Batch387.profile15505,![MergedCutProfiles.Batch387.profile15505,MergedCutProfiles.Batch387.profile15490,MergedCutProfiles.Batch387.profile15506,MergedCutProfiles.Batch387.profile15507,MergedCutProfiles.Batch387.profile15508,MergedCutProfiles.Batch387.profile15509,MergedCutProfiles.Batch387.profile15510,MergedCutProfiles.Batch387.profile15511,MergedCutProfiles.Batch387.profile15512,MergedCutProfiles.Batch387.profile15513,MergedCutProfiles.Batch193.profile7730,MergedCutProfiles.Batch387.profile15514,MergedCutProfiles.Batch387.profile15515,MergedCutProfiles.Batch387.profile15516,MergedCutProfiles.Batch387.profile15517,MergedCutProfiles.Batch387.profile15518]⟩
theorem profilesValid2491 : retention2491.ProfilesValid := by
  change ∀ j : Fin 16, (retention2491.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch387.valid15505
  · exact MergedCutProfiles.Batch387.valid15490
  · exact MergedCutProfiles.Batch387.valid15506
  · exact MergedCutProfiles.Batch387.valid15507
  · exact MergedCutProfiles.Batch387.valid15508
  · exact MergedCutProfiles.Batch387.valid15509
  · exact MergedCutProfiles.Batch387.valid15510
  · exact MergedCutProfiles.Batch387.valid15511
  · exact MergedCutProfiles.Batch387.valid15512
  · exact MergedCutProfiles.Batch387.valid15513
  · exact MergedCutProfiles.Batch193.valid7730
  · exact MergedCutProfiles.Batch387.valid15514
  · exact MergedCutProfiles.Batch387.valid15515
  · exact MergedCutProfiles.Batch387.valid15516
  · exact MergedCutProfiles.Batch387.valid15517
  · exact MergedCutProfiles.Batch387.valid15518
theorem numericValid2491 : retention2491.NumericValid := by decide +kernel
def certificate2491 : RatCutBinCertificate := ⟨⟨retention2491,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(118778880448949499/62500000000000000)⟩,(99567232708146153/100000000000000000),(329400773889290663/1000000000000000000),(152397936821085947/500000000000000000),(93923027329987829/500000000000000000)⟩
theorem valid2491 : certificate2491.Valid := by decide +kernel
theorem sound2491 : certificate2491.Sound := rat_cut_bin_certificate_sound certificate2491 profilesValid2491 numericValid2491 valid2491

def retention2492 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(9662897568220129123/29990236408876285893),(312112063067849219/125000000000000000),(7/5),(48374310804211681453197213210706175857/35669950064897053600000000000000000000),false,MergedCutProfiles.Batch387.profile15519,(fun _ => MergedCutProfiles.Batch387.profile15519)⟩
theorem profilesValid2492 : retention2492.ProfilesValid := by
  exact MergedCutProfiles.Batch387.valid15519
theorem numericValid2492 : retention2492.NumericValid := by decide +kernel
def certificate2492 : RatCutBinCertificate := ⟨⟨retention2492,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(264727170284461461/200000000000000000)⟩,(99567232708146153/100000000000000000),(188415818157821671/500000000000000000),(127697146022496443/500000000000000000),(189123808312555471/1000000000000000000)⟩
theorem valid2492 : certificate2492.Valid := by decide +kernel
theorem sound2492 : certificate2492.Sound := rat_cut_bin_certificate_sound certificate2492 profilesValid2492 numericValid2492 valid2492

def retention2493 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(14386737750700761700/29990236408876285893),(9662897568220129123/1000000000000000000),(21/20),(15989977492424091000969742389742243513071/15460636109152206596800000000000000000000),false,MergedCutProfiles.Batch388.profile15520,(fun _ => MergedCutProfiles.Batch388.profile15520)⟩
theorem profilesValid2493 : retention2493.ProfilesValid := by
  exact MergedCutProfiles.Batch388.valid15520
theorem numericValid2493 : retention2493.NumericValid := by decide +kernel
def certificate2493 : RatCutBinCertificate := ⟨⟨retention2493,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(252460827018697943/250000000000000000)⟩,(99567232708146153/100000000000000000),(417136502498760293/1000000000000000000),(13633927270010711/62500000000000000),(190759953220227437/1000000000000000000)⟩
theorem valid2493 : certificate2493.Valid := by decide +kernel
theorem sound2493 : certificate2493.Sound := rat_cut_bin_certificate_sound certificate2493 profilesValid2493 numericValid2493 valid2493

def retention2494 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(14822670291284745482/29990236408876285893),(143867377507007617/10000000000000000),1,(2290990886256967576543503325314620551/2301878040112121872000000000000000000),false,MergedCutProfiles.Batch388.profile15521,(fun _ => MergedCutProfiles.Batch388.profile15521)⟩
theorem profilesValid2494 : retention2494.ProfilesValid := by
  exact MergedCutProfiles.Batch388.valid15521
theorem numericValid2494 : retention2494.NumericValid := by decide +kernel
def certificate2494 : RatCutBinCertificate := ⟨⟨retention2494,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(972037504336624009/1000000000000000000)⟩,(99567232708146153/100000000000000000),(106058328869125427/250000000000000000),(105998992215822309/500000000000000000),(48039892489128301/250000000000000000)⟩
theorem valid2494 : certificate2494.Valid := by decide +kernel
theorem sound2494 : certificate2494.Sound := rat_cut_bin_certificate_sound certificate2494 profilesValid2494 numericValid2494 valid2494

def retention2495 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(14970896994197592937/29990236408876285893),(7411335145642372741/500000000000000000),1,(58473808300991136095799946565987995071/59290681165138981928000000000000000000),false,MergedCutProfiles.Batch388.profile15522,(fun _ => MergedCutProfiles.Batch388.profile15522)⟩
theorem profilesValid2495 : retention2495.ProfilesValid := by
  exact MergedCutProfiles.Batch388.valid15522
theorem numericValid2495 : retention2495.NumericValid := by decide +kernel
def certificate2495 : RatCutBinCertificate := ⟨⟨retention2495,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(60186861242810871/62500000000000000)⟩,(99567232708146153/100000000000000000),(26729058880814689/62500000000000000),(104534684428242031/500000000000000000),(2352498470371741/12500000000000000)⟩
theorem valid2495 : certificate2495.Valid := by decide +kernel
theorem sound2495 : certificate2495.Sound := rat_cut_bin_certificate_sound certificate2495 profilesValid2495 numericValid2495 valid2495

def certificates : List RatCutBinCertificate := [certificate2484,certificate2485,certificate2486,certificate2487,certificate2488,certificate2489,certificate2490,certificate2491,certificate2492,certificate2493,certificate2494,certificate2495]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2484,List.forall_mem_cons.mpr ⟨sound2485,List.forall_mem_cons.mpr ⟨sound2486,List.forall_mem_cons.mpr ⟨sound2487,List.forall_mem_cons.mpr ⟨sound2488,List.forall_mem_cons.mpr ⟨sound2489,List.forall_mem_cons.mpr ⟨sound2490,List.forall_mem_cons.mpr ⟨sound2491,List.forall_mem_cons.mpr ⟨sound2492,List.forall_mem_cons.mpr ⟨sound2493,List.forall_mem_cons.mpr ⟨sound2494,List.forall_mem_cons.mpr ⟨sound2495,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch207
