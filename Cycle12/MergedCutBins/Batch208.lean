import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch193
import Cycle12.MergedCutProfiles.Batch194
import Cycle12.MergedCutProfiles.Batch388
import Cycle12.MergedCutProfiles.Batch389
import Cycle12.MergedCutProfiles.Batch390

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch208

def retention2496 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1/2),(14970896994197592937/1000000000000000000),1,(58974962753082645162780672429699994467/59883587976790371748000000000000000000),false,MergedCutProfiles.Batch193.profile7747,(fun _ => MergedCutProfiles.Batch193.profile7747)⟩
theorem profilesValid2496 : retention2496.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7747
theorem numericValid2496 : retention2496.NumericValid := by decide +kernel
def certificate2496 : RatCutBinCertificate := ⟨⟨retention2496,(1108707362149860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(15024906511003621/15625000000000000)⟩,(99567232708146153/100000000000000000),(428104339555235487/1000000000000000000),(208696371479175141/1000000000000000000),(46930482529061919/250000000000000000)⟩
theorem valid2496 : certificate2496.Valid := by decide +kernel
theorem sound2496 : certificate2496.Sound := rat_cut_bin_certificate_sound certificate2496 profilesValid2496 numericValid2496 valid2496

def retention2497 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(345745817442447733/768980420740417587),(2672414285588011631/500000000000000000),(21/20),(2288778151112797386372846839146587440999/2137931428470409304800000000000000000000),false,MergedCutProfiles.Batch388.profile15523,(fun _ => MergedCutProfiles.Batch388.profile15523)⟩
theorem profilesValid2497 : retention2497.ProfilesValid := by
  exact MergedCutProfiles.Batch388.valid15523
theorem numericValid2497 : retention2497.NumericValid := by decide +kernel
def certificate2497 : RatCutBinCertificate := ⟨⟨retention2497,(1237861567649860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(260830027897816607/250000000000000000)⟩,(995167766950070011/1000000000000000000),(44982525414342759/200000000000000000),(439348008922181249/1000000000000000000),(184472954846072219/500000000000000000)⟩
theorem valid2497 : certificate2497.Valid := by decide +kernel
theorem sound2497 : certificate2497.Sound := rat_cut_bin_certificate_sound certificate2497 profilesValid2497 numericValid2497 valid2497

def retention2498 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(14894820708897125864/29990236408876285893),(13484086880255461587/1000000000000000000),1,(32071127424749646936689845317092413/32413670385229474968750000000000000),false,MergedCutProfiles.Batch388.profile15524,(fun _ => MergedCutProfiles.Batch388.profile15524)⟩
theorem profilesValid2498 : retention2498.ProfilesValid := by
  exact MergedCutProfiles.Batch388.valid15524
theorem numericValid2498 : retention2498.NumericValid := by decide +kernel
def certificate2498 : RatCutBinCertificate := ⟨⟨retention2498,(1237861567649860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(963492881863240039/1000000000000000000)⟩,(995167766950070011/1000000000000000000),(24354706878680689/100000000000000000),(41235603994655819/100000000000000000),(184473481392626553/500000000000000000)⟩
theorem valid2498 : certificate2498.Valid := by decide +kernel
theorem sound2498 : certificate2498.Sound := rat_cut_bin_certificate_sound certificate2498 profilesValid2498 numericValid2498 valid2498

def retention2499 : RatCutRetentionCertificate := ⟨(11/200),(111/2000),(1/2),(1861852588612140733/125000000000000000),1,(58670177224027627815146492485526831583/59579282835588503456000000000000000000),false,MergedCutProfiles.Batch193.profile7747,(fun _ => MergedCutProfiles.Batch193.profile7747)⟩
theorem profilesValid2499 : retention2499.ProfilesValid := by
  exact MergedCutProfiles.Batch193.valid7747
theorem numericValid2499 : retention2499.NumericValid := by decide +kernel
def certificate2499 : RatCutBinCertificate := ⟨⟨retention2499,(1237861567649860331/500000000000000000),(30403935940526677/200000000000000000),(906850057938533849/62500000000000000),(436437688724035953827/1000000000000000000),(191760409243883439/200000000000000000)⟩,(995167766950070011/1000000000000000000),(12236929828216359/50000000000000000),(205339481994348887/500000000000000000),(368096648503547567/1000000000000000000)⟩
theorem valid2499 : certificate2499.Valid := by decide +kernel
theorem sound2499 : certificate2499.Sound := rat_cut_bin_certificate_sound certificate2499 profilesValid2499 numericValid2499 valid2499

def retention2500 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(148790089726183786/4894940340622126157),(883901523125844273/1000000000000000000),(57/20),(85367270179631400483/40000000000000000000),true,MergedCutProfiles.Batch388.profile15525,![MergedCutProfiles.Batch388.profile15525,MergedCutProfiles.Batch388.profile15526,MergedCutProfiles.Batch388.profile15527,MergedCutProfiles.Batch388.profile15528,MergedCutProfiles.Batch388.profile15529,MergedCutProfiles.Batch388.profile15530,MergedCutProfiles.Batch388.profile15531,MergedCutProfiles.Batch388.profile15532,MergedCutProfiles.Batch388.profile15533,MergedCutProfiles.Batch388.profile15534,MergedCutProfiles.Batch388.profile15535,MergedCutProfiles.Batch388.profile15536,MergedCutProfiles.Batch388.profile15537,MergedCutProfiles.Batch388.profile15538,MergedCutProfiles.Batch388.profile15539,MergedCutProfiles.Batch388.profile15540]⟩
theorem profilesValid2500 : retention2500.ProfilesValid := by
  change ∀ j : Fin 16, (retention2500.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch388.valid15525
  · exact MergedCutProfiles.Batch388.valid15526
  · exact MergedCutProfiles.Batch388.valid15527
  · exact MergedCutProfiles.Batch388.valid15528
  · exact MergedCutProfiles.Batch388.valid15529
  · exact MergedCutProfiles.Batch388.valid15530
  · exact MergedCutProfiles.Batch388.valid15531
  · exact MergedCutProfiles.Batch388.valid15532
  · exact MergedCutProfiles.Batch388.valid15533
  · exact MergedCutProfiles.Batch388.valid15534
  · exact MergedCutProfiles.Batch388.valid15535
  · exact MergedCutProfiles.Batch388.valid15536
  · exact MergedCutProfiles.Batch388.valid15537
  · exact MergedCutProfiles.Batch388.valid15538
  · exact MergedCutProfiles.Batch388.valid15539
  · exact MergedCutProfiles.Batch388.valid15540
theorem numericValid2500 : retention2500.NumericValid := by decide +kernel
def certificate2500 : RatCutBinCertificate := ⟨⟨retention2500,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(413430211051616573/200000000000000000)⟩,(995635036137647583/1000000000000000000),(165480119118058309/500000000000000000),(75767060499576039/250000000000000000),(33958437101381059/200000000000000000)⟩
theorem valid2500 : certificate2500.Valid := by decide +kernel
theorem sound2500 : certificate2500.Sound := rat_cut_bin_certificate_sound certificate2500 profilesValid2500 numericValid2500 valid2500

def retention2501 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(487671482500000000/14684821021866378471),(223185134589275679/250000000000000000),(14/5),(42354933573387606789/20000000000000000000),true,MergedCutProfiles.Batch388.profile15541,![MergedCutProfiles.Batch388.profile15541,MergedCutProfiles.Batch388.profile15542,MergedCutProfiles.Batch388.profile15543,MergedCutProfiles.Batch388.profile15544,MergedCutProfiles.Batch388.profile15545,MergedCutProfiles.Batch388.profile15546,MergedCutProfiles.Batch388.profile15547,MergedCutProfiles.Batch388.profile15548,MergedCutProfiles.Batch388.profile15549,MergedCutProfiles.Batch388.profile15550,MergedCutProfiles.Batch388.profile15536,MergedCutProfiles.Batch388.profile15551,MergedCutProfiles.Batch193.profile7757,MergedCutProfiles.Batch388.profile15552,MergedCutProfiles.Batch388.profile15553,MergedCutProfiles.Batch388.profile15554]⟩
theorem profilesValid2501 : retention2501.ProfilesValid := by
  change ∀ j : Fin 16, (retention2501.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch388.valid15541
  · exact MergedCutProfiles.Batch388.valid15542
  · exact MergedCutProfiles.Batch388.valid15543
  · exact MergedCutProfiles.Batch388.valid15544
  · exact MergedCutProfiles.Batch388.valid15545
  · exact MergedCutProfiles.Batch388.valid15546
  · exact MergedCutProfiles.Batch388.valid15547
  · exact MergedCutProfiles.Batch388.valid15548
  · exact MergedCutProfiles.Batch388.valid15549
  · exact MergedCutProfiles.Batch388.valid15550
  · exact MergedCutProfiles.Batch388.valid15536
  · exact MergedCutProfiles.Batch388.valid15551
  · exact MergedCutProfiles.Batch193.valid7757
  · exact MergedCutProfiles.Batch388.valid15552
  · exact MergedCutProfiles.Batch388.valid15553
  · exact MergedCutProfiles.Batch388.valid15554
theorem numericValid2501 : retention2501.NumericValid := by decide +kernel
def certificate2501 : RatCutBinCertificate := ⟨⟨retention2501,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(410378376683601067/200000000000000000)⟩,(995635036137647583/1000000000000000000),(41501950587921937/125000000000000000),(75475807388675433/250000000000000000),(85097934255962461/500000000000000000)⟩
theorem valid2501 : certificate2501.Valid := by decide +kernel
theorem sound2501 : certificate2501.Sound := rat_cut_bin_certificate_sound certificate2501 profilesValid2501 numericValid2501 valid2501

def retention2502 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(166000393404995568/4894940340622126157),(195068593/200000000),(53/20),(8486067060625539827/4000000000000000000),true,MergedCutProfiles.Batch388.profile15555,![MergedCutProfiles.Batch388.profile15555,MergedCutProfiles.Batch388.profile15556,MergedCutProfiles.Batch388.profile15557,MergedCutProfiles.Batch388.profile15558,MergedCutProfiles.Batch388.profile15559,MergedCutProfiles.Batch389.profile15560,MergedCutProfiles.Batch389.profile15561,MergedCutProfiles.Batch389.profile15562,MergedCutProfiles.Batch388.profile15534,MergedCutProfiles.Batch389.profile15563,MergedCutProfiles.Batch194.profile7769,MergedCutProfiles.Batch389.profile15564,MergedCutProfiles.Batch389.profile15565,MergedCutProfiles.Batch389.profile15566,MergedCutProfiles.Batch389.profile15567,MergedCutProfiles.Batch389.profile15568]⟩
theorem profilesValid2502 : retention2502.ProfilesValid := by
  change ∀ j : Fin 16, (retention2502.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch388.valid15555
  · exact MergedCutProfiles.Batch388.valid15556
  · exact MergedCutProfiles.Batch388.valid15557
  · exact MergedCutProfiles.Batch388.valid15558
  · exact MergedCutProfiles.Batch388.valid15559
  · exact MergedCutProfiles.Batch389.valid15560
  · exact MergedCutProfiles.Batch389.valid15561
  · exact MergedCutProfiles.Batch389.valid15562
  · exact MergedCutProfiles.Batch388.valid15534
  · exact MergedCutProfiles.Batch389.valid15563
  · exact MergedCutProfiles.Batch194.valid7769
  · exact MergedCutProfiles.Batch389.valid15564
  · exact MergedCutProfiles.Batch389.valid15565
  · exact MergedCutProfiles.Batch389.valid15566
  · exact MergedCutProfiles.Batch389.valid15567
  · exact MergedCutProfiles.Batch389.valid15568
theorem numericValid2502 : retention2502.NumericValid := by decide +kernel
def certificate2502 : RatCutBinCertificate := ⟨⟨retention2502,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(2059190200452684437/1000000000000000000)⟩,(995635036137647583/1000000000000000000),(159487348988784533/500000000000000000),(31653716191557963/100000000000000000),(22965767923463/122070312500000)⟩
theorem valid2502 : certificate2502.Valid := by decide +kernel
theorem sound2502 : certificate2502.Sound := rat_cut_bin_certificate_sound certificate2502 profilesValid2502 numericValid2502 valid2502

def retention2503 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(1215312159961318517/29369642043732756942),(31125073763436669/31250000000000000),(13/5),(41881142337842967263/20000000000000000000),true,MergedCutProfiles.Batch389.profile15569,![MergedCutProfiles.Batch389.profile15569,MergedCutProfiles.Batch389.profile15570,MergedCutProfiles.Batch389.profile15571,MergedCutProfiles.Batch388.profile15545,MergedCutProfiles.Batch389.profile15572,MergedCutProfiles.Batch389.profile15573,MergedCutProfiles.Batch389.profile15574,MergedCutProfiles.Batch389.profile15575,MergedCutProfiles.Batch194.profile7769,MergedCutProfiles.Batch389.profile15576,MergedCutProfiles.Batch388.profile15539,MergedCutProfiles.Batch389.profile15577,MergedCutProfiles.Batch389.profile15578,MergedCutProfiles.Batch389.profile15579,MergedCutProfiles.Batch389.profile15580,MergedCutProfiles.Batch389.profile15581]⟩
theorem profilesValid2503 : retention2503.ProfilesValid := by
  change ∀ j : Fin 16, (retention2503.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch389.valid15569
  · exact MergedCutProfiles.Batch389.valid15570
  · exact MergedCutProfiles.Batch389.valid15571
  · exact MergedCutProfiles.Batch388.valid15545
  · exact MergedCutProfiles.Batch389.valid15572
  · exact MergedCutProfiles.Batch389.valid15573
  · exact MergedCutProfiles.Batch389.valid15574
  · exact MergedCutProfiles.Batch389.valid15575
  · exact MergedCutProfiles.Batch194.valid7769
  · exact MergedCutProfiles.Batch389.valid15576
  · exact MergedCutProfiles.Batch388.valid15539
  · exact MergedCutProfiles.Batch389.valid15577
  · exact MergedCutProfiles.Batch389.valid15578
  · exact MergedCutProfiles.Batch389.valid15579
  · exact MergedCutProfiles.Batch389.valid15580
  · exact MergedCutProfiles.Batch389.valid15581
theorem numericValid2503 : retention2503.NumericValid := by decide +kernel
def certificate2503 : RatCutBinCertificate := ⟨⟨retention2503,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(508226635344001093/250000000000000000)⟩,(995635036137647583/1000000000000000000),(320404705426005557/1000000000000000000),(157453451030959939/500000000000000000),(9407225219892861/50000000000000000)⟩
theorem valid2503 : certificate2503.Valid := by decide +kernel
theorem sound2503 : certificate2503.Sound := rat_cut_bin_certificate_sound certificate2503 profilesValid2503 numericValid2503 valid2503

def retention2504 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(1095731045775840101/9789880681244252314),(1215312159961318517/1000000000000000000),(11/5),(2388545861606506836217/1280000000000000000000),true,MergedCutProfiles.Batch389.profile15582,![MergedCutProfiles.Batch389.profile15582,MergedCutProfiles.Batch389.profile15583,MergedCutProfiles.Batch388.profile15535,MergedCutProfiles.Batch389.profile15584,MergedCutProfiles.Batch389.profile15585,MergedCutProfiles.Batch389.profile15586,MergedCutProfiles.Batch389.profile15587,MergedCutProfiles.Batch389.profile15588,MergedCutProfiles.Batch389.profile15589,MergedCutProfiles.Batch389.profile15590,MergedCutProfiles.Batch389.profile15591,MergedCutProfiles.Batch389.profile15592,MergedCutProfiles.Batch389.profile15593,MergedCutProfiles.Batch389.profile15594,MergedCutProfiles.Batch389.profile15595,MergedCutProfiles.Batch389.profile15596]⟩
theorem profilesValid2504 : retention2504.ProfilesValid := by
  change ∀ j : Fin 16, (retention2504.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch389.valid15582
  · exact MergedCutProfiles.Batch389.valid15583
  · exact MergedCutProfiles.Batch388.valid15535
  · exact MergedCutProfiles.Batch389.valid15584
  · exact MergedCutProfiles.Batch389.valid15585
  · exact MergedCutProfiles.Batch389.valid15586
  · exact MergedCutProfiles.Batch389.valid15587
  · exact MergedCutProfiles.Batch389.valid15588
  · exact MergedCutProfiles.Batch389.valid15589
  · exact MergedCutProfiles.Batch389.valid15590
  · exact MergedCutProfiles.Batch389.valid15591
  · exact MergedCutProfiles.Batch389.valid15592
  · exact MergedCutProfiles.Batch389.valid15593
  · exact MergedCutProfiles.Batch389.valid15594
  · exact MergedCutProfiles.Batch389.valid15595
  · exact MergedCutProfiles.Batch389.valid15596
theorem numericValid2504 : retention2504.NumericValid := by decide +kernel
def certificate2504 : RatCutBinCertificate := ⟨⟨retention2504,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(1814308885875870821/1000000000000000000)⟩,(995635036137647583/1000000000000000000),(166645849554085843/500000000000000000),(18781189117225271/62500000000000000),(23553340844111479/125000000000000000)⟩
theorem valid2504 : certificate2504.Valid := by decide +kernel
theorem sound2504 : certificate2504.Sound := rat_cut_bin_certificate_sound certificate2504 profilesValid2504 numericValid2504 valid2504

def retention2505 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(5588872488316773050/14684821021866378471),(3287193137327520303/1000000000000000000),(6/5),(1562961139000533612363/1280000000000000000000),true,MergedCutProfiles.Batch389.profile15597,![MergedCutProfiles.Batch389.profile15597,MergedCutProfiles.Batch389.profile15598,MergedCutProfiles.Batch389.profile15599,MergedCutProfiles.Batch390.profile15600,MergedCutProfiles.Batch390.profile15601,MergedCutProfiles.Batch390.profile15602,MergedCutProfiles.Batch390.profile15603,MergedCutProfiles.Batch194.profile7794,MergedCutProfiles.Batch390.profile15604,MergedCutProfiles.Batch390.profile15605,MergedCutProfiles.Batch390.profile15606,MergedCutProfiles.Batch390.profile15607,MergedCutProfiles.Batch390.profile15608,MergedCutProfiles.Batch390.profile15609,MergedCutProfiles.Batch390.profile15610,MergedCutProfiles.Batch390.profile15611]⟩
theorem profilesValid2505 : retention2505.ProfilesValid := by
  change ∀ j : Fin 16, (retention2505.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch389.valid15597
  · exact MergedCutProfiles.Batch389.valid15598
  · exact MergedCutProfiles.Batch389.valid15599
  · exact MergedCutProfiles.Batch390.valid15600
  · exact MergedCutProfiles.Batch390.valid15601
  · exact MergedCutProfiles.Batch390.valid15602
  · exact MergedCutProfiles.Batch390.valid15603
  · exact MergedCutProfiles.Batch194.valid7794
  · exact MergedCutProfiles.Batch390.valid15604
  · exact MergedCutProfiles.Batch390.valid15605
  · exact MergedCutProfiles.Batch390.valid15606
  · exact MergedCutProfiles.Batch390.valid15607
  · exact MergedCutProfiles.Batch390.valid15608
  · exact MergedCutProfiles.Batch390.valid15609
  · exact MergedCutProfiles.Batch390.valid15610
  · exact MergedCutProfiles.Batch390.valid15611
theorem numericValid2505 : retention2505.NumericValid := by decide +kernel
def certificate2505 : RatCutBinCertificate := ⟨⟨retention2505,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(596420697410915981/500000000000000000)⟩,(995635036137647583/1000000000000000000),(78993666749305049/200000000000000000),(119062196190084373/500000000000000000),(23516672751984041/125000000000000000)⟩
theorem valid2505 : certificate2505.Valid := by decide +kernel
theorem sound2505 : certificate2505.Sound := rat_cut_bin_certificate_sound certificate2505 profilesValid2505 numericValid2505 valid2505

def retention2506 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(2389116298363003310/4894940340622126157),(111777449766335461/10000000000000000),(21/20),(11408348526172048784361406243249730051/11177744976633546100000000000000000000),false,MergedCutProfiles.Batch390.profile15612,(fun _ => MergedCutProfiles.Batch390.profile15612)⟩
theorem profilesValid2506 : retention2506.ProfilesValid := by
  exact MergedCutProfiles.Batch390.valid15612
theorem numericValid2506 : retention2506.NumericValid := by decide +kernel
def certificate2506 : RatCutBinCertificate := ⟨⟨retention2506,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(995937847152423813/1000000000000000000)⟩,(995635036137647583/1000000000000000000),(208763668918384739/500000000000000000),(217801305290469291/1000000000000000000),(190265303525659517/1000000000000000000)⟩
theorem valid2506 : certificate2506.Valid := by decide +kernel
theorem sound2506 : certificate2506.Sound := rat_cut_bin_certificate_sound certificate2506 profilesValid2506 numericValid2506 valid2506

def retention2507 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(7311412607880299030/14684821021866378471),(716734889508900993/50000000000000000),1,(755471052594978539748702089391380709/764517215476161059200000000000000000),false,MergedCutProfiles.Batch390.profile15613,(fun _ => MergedCutProfiles.Batch390.profile15613)⟩
theorem profilesValid2507 : retention2507.ProfilesValid := by
  exact MergedCutProfiles.Batch390.valid15613
theorem numericValid2507 : retention2507.NumericValid := by decide +kernel
def certificate2507 : RatCutBinCertificate := ⟨⟨retention2507,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(964650709407196833/1000000000000000000)⟩,(995635036137647583/1000000000000000000),(53226170050868631/125000000000000000),(82284970778103/390625000000000),(11845408111950691/62500000000000000)⟩
theorem valid2507 : certificate2507.Valid := by decide +kernel
theorem sound2507 : certificate2507.Sound := rat_cut_bin_certificate_sound certificate2507 profilesValid2507 numericValid2507 valid2507

def certificates : List RatCutBinCertificate := [certificate2496,certificate2497,certificate2498,certificate2499,certificate2500,certificate2501,certificate2502,certificate2503,certificate2504,certificate2505,certificate2506,certificate2507]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2496,List.forall_mem_cons.mpr ⟨sound2497,List.forall_mem_cons.mpr ⟨sound2498,List.forall_mem_cons.mpr ⟨sound2499,List.forall_mem_cons.mpr ⟨sound2500,List.forall_mem_cons.mpr ⟨sound2501,List.forall_mem_cons.mpr ⟨sound2502,List.forall_mem_cons.mpr ⟨sound2503,List.forall_mem_cons.mpr ⟨sound2504,List.forall_mem_cons.mpr ⟨sound2505,List.forall_mem_cons.mpr ⟨sound2506,List.forall_mem_cons.mpr ⟨sound2507,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch208
