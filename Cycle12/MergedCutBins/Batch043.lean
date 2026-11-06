import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch085
import Cycle12.MergedCutProfiles.Batch086
import Cycle12.MergedCutProfiles.Batch087
import Cycle12.MergedCutProfiles.Batch088

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch043

def retention516 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(13293825941534841679/30653648054070669896),(743950670740583891/200000000000000000),(5/4),(269638818773390881969970780924611143439/238064214636986845120000000000000000000),false,MergedCutProfiles.Batch085.profile3434,(fun _ => MergedCutProfiles.Batch085.profile3434)⟩
theorem profilesValid516 : retention516.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3434
theorem numericValid516 : retention516.NumericValid := by decide +kernel
def certificate516 : RatCutBinCertificate := ⟨⟨retention516,(246141835257401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(1112309924691697451/1000000000000000000)⟩,(496728322888589461/500000000000000000),(73197559915844079/200000000000000000),(66533488374320397/250000000000000000),(98683043543911493/500000000000000000)⟩
theorem valid516 : certificate516.Valid := by decide +kernel
theorem sound516 : certificate516.Sound := rat_cut_bin_certificate_sound certificate516 profilesValid516 numericValid516 valid516

def retention517 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(1891201746913818789/3831706006758833737),(13293825941534841679/1000000000000000000),1,(52912435179150931539236037401924361939/53175303766139366716000000000000000000),false,MergedCutProfiles.Batch085.profile3435,(fun _ => MergedCutProfiles.Batch085.profile3435)⟩
theorem profilesValid517 : retention517.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3435
theorem numericValid517 : retention517.NumericValid := by decide +kernel
def certificate517 : RatCutBinCertificate := ⟨⟨retention517,(246141835257401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(39152019975401647/40000000000000000)⟩,(496728322888589461/500000000000000000),(415908923262513209/1000000000000000000),(219217937341399981/1000000000000000000),(99252388981007583/500000000000000000)⟩
theorem valid517 : certificate517.Valid := by decide +kernel
theorem sound517 : certificate517.Sound := rat_cut_bin_certificate_sound certificate517 profilesValid517 numericValid517 valid517

def retention518 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(1910113764382956977/3831706006758833737),(1891201746913818789/125000000000000000),1,(11956506691727178389054632758612717907/12103691180248440249600000000000000000),false,MergedCutProfiles.Batch085.profile3436,(fun _ => MergedCutProfiles.Batch085.profile3436)⟩
theorem profilesValid518 : retention518.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3436
theorem numericValid518 : retention518.NumericValid := by decide +kernel
def certificate518 : RatCutBinCertificate := ⟨⟨retention518,(246141835257401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(485791833596493209/500000000000000000)⟩,(496728322888589461/500000000000000000),(418998255666623639/1000000000000000000),(27064902621631311/125000000000000000),(39268258330350377/200000000000000000)⟩
theorem valid518 : certificate518.Valid := by decide +kernel
theorem sound518 : certificate518.Sound := rat_cut_bin_certificate_sound certificate518 profilesValid518 numericValid518 valid518

def retention519 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(1/2),(1910113764382956977/125000000000000000),1,(12042611179187193153739780469463298539/12224728092050924652800000000000000000),false,MergedCutProfiles.Batch085.profile3433,(fun _ => MergedCutProfiles.Batch085.profile3433)⟩
theorem profilesValid519 : retention519.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3433
theorem numericValid519 : retention519.NumericValid := by decide +kernel
def certificate519 : RatCutBinCertificate := ⟨⟨retention519,(246141835257401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(968846546885483001/1000000000000000000)⟩,(496728322888589461/500000000000000000),(420181981446604337/1000000000000000000),(215491209192618671/1000000000000000000),(195008253788731099/1000000000000000000)⟩
theorem valid519 : certificate519.Valid := by decide +kernel
theorem sound519 : certificate519.Sound := rat_cut_bin_certificate_sound certificate519 profilesValid519 numericValid519 valid519

def retention520 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(797357911508509539/29829875809522449283),(789463278721296573/1000000000000000000),(16/5),(171966999425110700397/80000000000000000000),true,MergedCutProfiles.Batch085.profile3437,![MergedCutProfiles.Batch085.profile3437,MergedCutProfiles.Batch085.profile3438,MergedCutProfiles.Batch085.profile3439,MergedCutProfiles.Batch086.profile3440,MergedCutProfiles.Batch086.profile3441,MergedCutProfiles.Batch086.profile3442,MergedCutProfiles.Batch086.profile3443,MergedCutProfiles.Batch086.profile3444,MergedCutProfiles.Batch086.profile3445,MergedCutProfiles.Batch086.profile3446,MergedCutProfiles.Batch086.profile3447,MergedCutProfiles.Batch086.profile3448,MergedCutProfiles.Batch086.profile3449,MergedCutProfiles.Batch086.profile3450,MergedCutProfiles.Batch086.profile3451,MergedCutProfiles.Batch086.profile3452]⟩
theorem profilesValid520 : retention520.ProfilesValid := by
  change ∀ j : Fin 16, (retention520.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch085.valid3437
  · exact MergedCutProfiles.Batch085.valid3438
  · exact MergedCutProfiles.Batch085.valid3439
  · exact MergedCutProfiles.Batch086.valid3440
  · exact MergedCutProfiles.Batch086.valid3441
  · exact MergedCutProfiles.Batch086.valid3442
  · exact MergedCutProfiles.Batch086.valid3443
  · exact MergedCutProfiles.Batch086.valid3444
  · exact MergedCutProfiles.Batch086.valid3445
  · exact MergedCutProfiles.Batch086.valid3446
  · exact MergedCutProfiles.Batch086.valid3447
  · exact MergedCutProfiles.Batch086.valid3448
  · exact MergedCutProfiles.Batch086.valid3449
  · exact MergedCutProfiles.Batch086.valid3450
  · exact MergedCutProfiles.Batch086.valid3451
  · exact MergedCutProfiles.Batch086.valid3452
theorem numericValid520 : retention520.NumericValid := by decide +kernel
def certificate520 : RatCutBinCertificate := ⟨⟨retention520,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(526236201066475679/250000000000000000)⟩,(248598831217909067/250000000000000000),(402845081294994017/1000000000000000000),(230885646879560833/1000000000000000000),(59852683049723149/500000000000000000)⟩
theorem valid520 : certificate520.Valid := by decide +kernel
theorem sound520 : certificate520.Sound := rat_cut_bin_certificate_sound certificate520 profilesValid520 numericValid520 valid520

def retention521 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(127083854690458375/4261410829931778469),(797357911508509539/1000000000000000000),(16/5),(2741375034714237920407/1280000000000000000000),true,MergedCutProfiles.Batch086.profile3453,![MergedCutProfiles.Batch086.profile3453,MergedCutProfiles.Batch086.profile3454,MergedCutProfiles.Batch086.profile3455,MergedCutProfiles.Batch086.profile3456,MergedCutProfiles.Batch086.profile3457,MergedCutProfiles.Batch086.profile3458,MergedCutProfiles.Batch086.profile3459,MergedCutProfiles.Batch086.profile3460,MergedCutProfiles.Batch086.profile3461,MergedCutProfiles.Batch086.profile3462,MergedCutProfiles.Batch086.profile3463,MergedCutProfiles.Batch086.profile3464,MergedCutProfiles.Batch086.profile3465,MergedCutProfiles.Batch086.profile3466,MergedCutProfiles.Batch086.profile3467,MergedCutProfiles.Batch086.profile3468]⟩
theorem profilesValid521 : retention521.ProfilesValid := by
  change ∀ j : Fin 16, (retention521.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch086.valid3453
  · exact MergedCutProfiles.Batch086.valid3454
  · exact MergedCutProfiles.Batch086.valid3455
  · exact MergedCutProfiles.Batch086.valid3456
  · exact MergedCutProfiles.Batch086.valid3457
  · exact MergedCutProfiles.Batch086.valid3458
  · exact MergedCutProfiles.Batch086.valid3459
  · exact MergedCutProfiles.Batch086.valid3460
  · exact MergedCutProfiles.Batch086.valid3461
  · exact MergedCutProfiles.Batch086.valid3462
  · exact MergedCutProfiles.Batch086.valid3463
  · exact MergedCutProfiles.Batch086.valid3464
  · exact MergedCutProfiles.Batch086.valid3465
  · exact MergedCutProfiles.Batch086.valid3466
  · exact MergedCutProfiles.Batch086.valid3467
  · exact MergedCutProfiles.Batch086.valid3468
theorem numericValid521 : retention521.NumericValid := by decide +kernel
def certificate521 : RatCutBinCertificate := ⟨⟨retention521,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(65533018646835949/31250000000000000)⟩,(248598831217909067/250000000000000000),(40252784119046169/100000000000000000),(231174195592934597/1000000000000000000),(119743370906115999/1000000000000000000)⟩
theorem valid521 : certificate521.Valid := by decide +kernel
theorem sound521 : certificate521.Sound := rat_cut_bin_certificate_sound certificate521 profilesValid521 numericValid521 valid521

def retention522 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(914777907000000000/29829875809522449283),(7116695862665669/8000000000000000),(29/10),(545142467237386590289/256000000000000000000),true,MergedCutProfiles.Batch086.profile3469,![MergedCutProfiles.Batch086.profile3469,MergedCutProfiles.Batch086.profile3470,MergedCutProfiles.Batch086.profile3471,MergedCutProfiles.Batch086.profile3472,MergedCutProfiles.Batch086.profile3473,MergedCutProfiles.Batch086.profile3474,MergedCutProfiles.Batch086.profile3475,MergedCutProfiles.Batch086.profile3476,MergedCutProfiles.Batch086.profile3477,MergedCutProfiles.Batch086.profile3478,MergedCutProfiles.Batch086.profile3479,MergedCutProfiles.Batch087.profile3480,MergedCutProfiles.Batch087.profile3481,MergedCutProfiles.Batch087.profile3482,MergedCutProfiles.Batch087.profile3483,MergedCutProfiles.Batch087.profile3484]⟩
theorem profilesValid522 : retention522.ProfilesValid := by
  change ∀ j : Fin 16, (retention522.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch086.valid3469
  · exact MergedCutProfiles.Batch086.valid3470
  · exact MergedCutProfiles.Batch086.valid3471
  · exact MergedCutProfiles.Batch086.valid3472
  · exact MergedCutProfiles.Batch086.valid3473
  · exact MergedCutProfiles.Batch086.valid3474
  · exact MergedCutProfiles.Batch086.valid3475
  · exact MergedCutProfiles.Batch086.valid3476
  · exact MergedCutProfiles.Batch086.valid3477
  · exact MergedCutProfiles.Batch086.valid3478
  · exact MergedCutProfiles.Batch086.valid3479
  · exact MergedCutProfiles.Batch087.valid3480
  · exact MergedCutProfiles.Batch087.valid3481
  · exact MergedCutProfiles.Batch087.valid3482
  · exact MergedCutProfiles.Batch087.valid3483
  · exact MergedCutProfiles.Batch087.valid3484
theorem numericValid522 : retention522.NumericValid := by decide +kernel
def certificate522 : RatCutBinCertificate := ⟨⟨retention522,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(65281418778753311/31250000000000000)⟩,(248598831217909067/250000000000000000),(192503310362182063/500000000000000000),(2475044748905773/10000000000000000),(69229367923410287/500000000000000000)⟩
theorem valid522 : certificate522.Valid := by decide +kernel
theorem sound522 : certificate522.Sound := rat_cut_bin_certificate_sound certificate522 profilesValid522 numericValid522 valid522

def retention523 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(134902072569970975/4261410829931778469),(914777907/1000000000),(57/20),(17018063688829177811/8000000000000000000),true,MergedCutProfiles.Batch087.profile3485,![MergedCutProfiles.Batch087.profile3485,MergedCutProfiles.Batch087.profile3486,MergedCutProfiles.Batch087.profile3487,MergedCutProfiles.Batch087.profile3488,MergedCutProfiles.Batch087.profile3489,MergedCutProfiles.Batch087.profile3490,MergedCutProfiles.Batch087.profile3491,MergedCutProfiles.Batch087.profile3492,MergedCutProfiles.Batch087.profile3493,MergedCutProfiles.Batch087.profile3494,MergedCutProfiles.Batch087.profile3495,MergedCutProfiles.Batch087.profile3496,MergedCutProfiles.Batch087.profile3497,MergedCutProfiles.Batch087.profile3498,MergedCutProfiles.Batch087.profile3499,MergedCutProfiles.Batch087.profile3500]⟩
theorem profilesValid523 : retention523.ProfilesValid := by
  change ∀ j : Fin 16, (retention523.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch087.valid3485
  · exact MergedCutProfiles.Batch087.valid3486
  · exact MergedCutProfiles.Batch087.valid3487
  · exact MergedCutProfiles.Batch087.valid3488
  · exact MergedCutProfiles.Batch087.valid3489
  · exact MergedCutProfiles.Batch087.valid3490
  · exact MergedCutProfiles.Batch087.valid3491
  · exact MergedCutProfiles.Batch087.valid3492
  · exact MergedCutProfiles.Batch087.valid3493
  · exact MergedCutProfiles.Batch087.valid3494
  · exact MergedCutProfiles.Batch087.valid3495
  · exact MergedCutProfiles.Batch087.valid3496
  · exact MergedCutProfiles.Batch087.valid3497
  · exact MergedCutProfiles.Batch087.valid3498
  · exact MergedCutProfiles.Batch087.valid3499
  · exact MergedCutProfiles.Batch087.valid3500
theorem numericValid523 : retention523.NumericValid := by decide +kernel
def certificate523 : RatCutBinCertificate := ⟨⟨retention523,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(208749817643697797/100000000000000000)⟩,(248598831217909067/250000000000000000),(11898144283298717/31250000000000000),(251599791783770593/1000000000000000000),(71462622423093681/500000000000000000)⟩
theorem valid523 : certificate523.Valid := by decide +kernel
theorem sound523 : certificate523.Sound := rat_cut_bin_certificate_sound certificate523 profilesValid523 numericValid523 valid523

def retention524 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(180027338801580500/4261410829931778469),(37772580319591873/40000000000000000),(11/4),(533393767240565843829/256000000000000000000),true,MergedCutProfiles.Batch087.profile3501,![MergedCutProfiles.Batch087.profile3501,MergedCutProfiles.Batch087.profile3502,MergedCutProfiles.Batch087.profile3488,MergedCutProfiles.Batch087.profile3503,MergedCutProfiles.Batch087.profile3504,MergedCutProfiles.Batch087.profile3492,MergedCutProfiles.Batch087.profile3505,MergedCutProfiles.Batch086.profile3479,MergedCutProfiles.Batch087.profile3496,MergedCutProfiles.Batch087.profile3506,MergedCutProfiles.Batch087.profile3507,MergedCutProfiles.Batch087.profile3500,MergedCutProfiles.Batch087.profile3508,MergedCutProfiles.Batch087.profile3509,MergedCutProfiles.Batch087.profile3510,MergedCutProfiles.Batch087.profile3511]⟩
theorem profilesValid524 : retention524.ProfilesValid := by
  change ∀ j : Fin 16, (retention524.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch087.valid3501
  · exact MergedCutProfiles.Batch087.valid3502
  · exact MergedCutProfiles.Batch087.valid3488
  · exact MergedCutProfiles.Batch087.valid3503
  · exact MergedCutProfiles.Batch087.valid3504
  · exact MergedCutProfiles.Batch087.valid3492
  · exact MergedCutProfiles.Batch087.valid3505
  · exact MergedCutProfiles.Batch086.valid3479
  · exact MergedCutProfiles.Batch087.valid3496
  · exact MergedCutProfiles.Batch087.valid3506
  · exact MergedCutProfiles.Batch087.valid3507
  · exact MergedCutProfiles.Batch087.valid3500
  · exact MergedCutProfiles.Batch087.valid3508
  · exact MergedCutProfiles.Batch087.valid3509
  · exact MergedCutProfiles.Batch087.valid3510
  · exact MergedCutProfiles.Batch087.valid3511
theorem numericValid524 : retention524.NumericValid := by decide +kernel
def certificate524 : RatCutBinCertificate := ⟨⟨retention524,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(8180818742824179/4000000000000000)⟩,(248598831217909067/250000000000000000),(191745598791674817/500000000000000000),(248953827892345927/1000000000000000000),(28597550010793647/200000000000000000)⟩
theorem valid524 : certificate524.Valid := by decide +kernel
theorem sound524 : certificate524.Sound := rat_cut_bin_certificate_sound certificate524 profilesValid524 numericValid524 valid524

def retention525 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(4242717381179116806/29829875809522449283),(2520382743222127/2000000000000000),(43/20),(908416436368202183/512000000000000000),true,MergedCutProfiles.Batch087.profile3512,![MergedCutProfiles.Batch087.profile3512,MergedCutProfiles.Batch087.profile3493,MergedCutProfiles.Batch086.profile3452,MergedCutProfiles.Batch087.profile3513,MergedCutProfiles.Batch087.profile3514,MergedCutProfiles.Batch087.profile3515,MergedCutProfiles.Batch087.profile3516,MergedCutProfiles.Batch087.profile3517,MergedCutProfiles.Batch087.profile3518,MergedCutProfiles.Batch087.profile3519,MergedCutProfiles.Batch088.profile3520,MergedCutProfiles.Batch088.profile3521,MergedCutProfiles.Batch088.profile3522,MergedCutProfiles.Batch088.profile3523,MergedCutProfiles.Batch088.profile3524,MergedCutProfiles.Batch088.profile3525]⟩
theorem profilesValid525 : retention525.ProfilesValid := by
  change ∀ j : Fin 16, (retention525.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch087.valid3512
  · exact MergedCutProfiles.Batch087.valid3493
  · exact MergedCutProfiles.Batch086.valid3452
  · exact MergedCutProfiles.Batch087.valid3513
  · exact MergedCutProfiles.Batch087.valid3514
  · exact MergedCutProfiles.Batch087.valid3515
  · exact MergedCutProfiles.Batch087.valid3516
  · exact MergedCutProfiles.Batch087.valid3517
  · exact MergedCutProfiles.Batch087.valid3518
  · exact MergedCutProfiles.Batch087.valid3519
  · exact MergedCutProfiles.Batch088.valid3520
  · exact MergedCutProfiles.Batch088.valid3521
  · exact MergedCutProfiles.Batch088.valid3522
  · exact MergedCutProfiles.Batch088.valid3523
  · exact MergedCutProfiles.Batch088.valid3524
  · exact MergedCutProfiles.Batch088.valid3525
theorem numericValid525 : retention525.NumericValid := by decide +kernel
def certificate525 : RatCutBinCertificate := ⟨⟨retention525,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(174425672651693681/100000000000000000)⟩,(248598831217909067/250000000000000000),(403026131432286011/1000000000000000000),(5768027074127721/25000000000000000),(71555806866819527/500000000000000000)⟩
theorem valid525 : certificate525.Valid := by decide +kernel
theorem sound525 : certificate525.Sound := rat_cut_bin_certificate_sound certificate525 profilesValid525 numericValid525 valid525

def retention526 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(12426604368722198724/29829875809522449283),(2121358690589558403/500000000000000000),(23/20),(1957819311993143227247451811210466326439/1697086952471646722400000000000000000000),false,MergedCutProfiles.Batch088.profile3526,(fun _ => MergedCutProfiles.Batch088.profile3526)⟩
theorem profilesValid526 : retention526.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3526
theorem numericValid526 : retention526.NumericValid := by decide +kernel
def certificate526 : RatCutBinCertificate := ⟨⟨retention526,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(1137592462002536283/1000000000000000000)⟩,(248598831217909067/250000000000000000),(233848094726071393/500000000000000000),(176884314847952011/1000000000000000000),(14458729634914897/100000000000000000)⟩
theorem valid526 : certificate526.Valid := by decide +kernel
theorem sound526 : certificate526.Sound := rat_cut_bin_certificate_sound certificate526 profilesValid526 numericValid526 valid526

def retention527 : RatCutRetentionCertificate := ⟨(81/2000),(41/1000),(2102411802970854250/4261410829931778469),(3106651092180549681/250000000000000000),(21/20),(78575606989725507626024828848839650489/77666277304513742025000000000000000000),false,MergedCutProfiles.Batch088.profile3527,(fun _ => MergedCutProfiles.Batch088.profile3527)⟩
theorem profilesValid527 : retention527.ProfilesValid := by
  exact MergedCutProfiles.Batch088.valid3527
theorem numericValid527 : retention527.NumericValid := by decide +kernel
def certificate527 : RatCutBinCertificate := ⟨⟨retention527,(207210314825986613/100000000000000000),(77009395027439323/1000000000000000000),(2287828182800729229/200000000000000000),(342151075683948305859/1000000000000000000),(997060836344872963/1000000000000000000)⟩,(248598831217909067/250000000000000000),(97182192670587043/200000000000000000),(81696247337024331/500000000000000000),(143785853582712561/1000000000000000000)⟩
theorem valid527 : certificate527.Valid := by decide +kernel
theorem sound527 : certificate527.Sound := rat_cut_bin_certificate_sound certificate527 profilesValid527 numericValid527 valid527

def certificates : List RatCutBinCertificate := [certificate516,certificate517,certificate518,certificate519,certificate520,certificate521,certificate522,certificate523,certificate524,certificate525,certificate526,certificate527]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound516,List.forall_mem_cons.mpr ⟨sound517,List.forall_mem_cons.mpr ⟨sound518,List.forall_mem_cons.mpr ⟨sound519,List.forall_mem_cons.mpr ⟨sound520,List.forall_mem_cons.mpr ⟨sound521,List.forall_mem_cons.mpr ⟨sound522,List.forall_mem_cons.mpr ⟨sound523,List.forall_mem_cons.mpr ⟨sound524,List.forall_mem_cons.mpr ⟨sound525,List.forall_mem_cons.mpr ⟨sound526,List.forall_mem_cons.mpr ⟨sound527,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch043
