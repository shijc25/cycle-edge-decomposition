import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch250
import Cycle12.MergedCutProfiles.Batch540
import Cycle12.MergedCutProfiles.Batch541
import Cycle12.MergedCutProfiles.Batch542

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch293

def retention3516 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(27718017519904598645/55589954979483376786),(12798562070051343659/500000000000000000),1,(1272875159240609038203836961651707301/1279856207005134365900000000000000000),false,MergedCutProfiles.Batch540.profile21611,(fun _ => MergedCutProfiles.Batch540.profile21611)⟩
theorem profilesValid3516 : retention3516.ProfilesValid := by
  exact MergedCutProfiles.Batch540.valid21611
theorem numericValid3516 : retention3516.NumericValid := by decide +kernel
def certificate3516 : RatCutBinCertificate := ⟨⟨retention3516,(288214371685437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(483125305285718149/500000000000000000)⟩,(998022273588358479/1000000000000000000),(61815816261754999/500000000000000000),(308012933825310029/500000000000000000),(286210571182840911/500000000000000000)⟩
theorem valid3516 : certificate3516.Valid := by decide +kernel
theorem sound3516 : certificate3516.Sound := rat_cut_bin_certificate_sound certificate3516 profilesValid3516 numericValid3516 valid3516

def retention3517 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1/2),(5543603503980919729/200000000000000000),1,(1100489155540620752953802806788343/1108720700796183945800000000000000),false,MergedCutProfiles.Batch250.profile10024,(fun _ => MergedCutProfiles.Batch250.profile10024)⟩
theorem profilesValid3517 : retention3517.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10024
theorem numericValid3517 : retention3517.NumericValid := by decide +kernel
def certificate3517 : RatCutBinCertificate := ⟨⟨retention3517,(288214371685437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(964280822257845099/1000000000000000000)⟩,(998022273588358479/1000000000000000000),(123884181510603607/1000000000000000000),(615509729739041723/1000000000000000000),(572410044664812889/1000000000000000000)⟩
theorem valid3517 : certificate3517.Valid := by decide +kernel
theorem sound3517 : certificate3517.Sound := rat_cut_bin_certificate_sound certificate3517 profilesValid3517 numericValid3517 valid3517

def retention3518 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(919729947486444265/55065286028488616857),(227655927595654521/250000000000000000),(29/10),(22250580853266642099/10000000000000000000),true,MergedCutProfiles.Batch540.profile21612,![MergedCutProfiles.Batch540.profile21612,MergedCutProfiles.Batch540.profile21613,MergedCutProfiles.Batch540.profile21614,MergedCutProfiles.Batch540.profile21615,MergedCutProfiles.Batch540.profile21616,MergedCutProfiles.Batch540.profile21617,MergedCutProfiles.Batch540.profile21618,MergedCutProfiles.Batch540.profile21619,MergedCutProfiles.Batch540.profile21620,MergedCutProfiles.Batch540.profile21621,MergedCutProfiles.Batch540.profile21622,MergedCutProfiles.Batch540.profile21623,MergedCutProfiles.Batch540.profile21624,MergedCutProfiles.Batch540.profile21625,MergedCutProfiles.Batch540.profile21626,MergedCutProfiles.Batch540.profile21627]⟩
theorem profilesValid3518 : retention3518.ProfilesValid := by
  change ∀ j : Fin 16, (retention3518.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch540.valid21612
  · exact MergedCutProfiles.Batch540.valid21613
  · exact MergedCutProfiles.Batch540.valid21614
  · exact MergedCutProfiles.Batch540.valid21615
  · exact MergedCutProfiles.Batch540.valid21616
  · exact MergedCutProfiles.Batch540.valid21617
  · exact MergedCutProfiles.Batch540.valid21618
  · exact MergedCutProfiles.Batch540.valid21619
  · exact MergedCutProfiles.Batch540.valid21620
  · exact MergedCutProfiles.Batch540.valid21621
  · exact MergedCutProfiles.Batch540.valid21622
  · exact MergedCutProfiles.Batch540.valid21623
  · exact MergedCutProfiles.Batch540.valid21624
  · exact MergedCutProfiles.Batch540.valid21625
  · exact MergedCutProfiles.Batch540.valid21626
  · exact MergedCutProfiles.Batch540.valid21627
theorem numericValid3518 : retention3518.NumericValid := by decide +kernel
def certificate3518 : RatCutBinCertificate := ⟨⟨retention3518,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(53613329202485669/25000000000000000)⟩,(199612820902076689/200000000000000000),(307692766017538149/1000000000000000000),(412031704758147/1250000000000000),(189988510074055349/1000000000000000000)⟩
theorem valid3518 : certificate3518.Valid := by decide +kernel
theorem sound3518 : certificate3518.Sound := rat_cut_bin_certificate_sound certificate3518 profilesValid3518 numericValid3518 valid3518

def retention3519 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(1089240252474593218/55065286028488616857),(183945989497288853/200000000000000000),(57/20),(17637244241951860479/8000000000000000000),true,MergedCutProfiles.Batch540.profile21628,![MergedCutProfiles.Batch540.profile21628,MergedCutProfiles.Batch540.profile21629,MergedCutProfiles.Batch540.profile21630,MergedCutProfiles.Batch540.profile21631,MergedCutProfiles.Batch540.profile21632,MergedCutProfiles.Batch540.profile21633,MergedCutProfiles.Batch540.profile21634,MergedCutProfiles.Batch540.profile21635,MergedCutProfiles.Batch540.profile21636,MergedCutProfiles.Batch540.profile21637,MergedCutProfiles.Batch540.profile21624,MergedCutProfiles.Batch540.profile21638,MergedCutProfiles.Batch540.profile21639,MergedCutProfiles.Batch541.profile21640,MergedCutProfiles.Batch541.profile21641,MergedCutProfiles.Batch541.profile21642]⟩
theorem profilesValid3519 : retention3519.ProfilesValid := by
  change ∀ j : Fin 16, (retention3519.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch540.valid21628
  · exact MergedCutProfiles.Batch540.valid21629
  · exact MergedCutProfiles.Batch540.valid21630
  · exact MergedCutProfiles.Batch540.valid21631
  · exact MergedCutProfiles.Batch540.valid21632
  · exact MergedCutProfiles.Batch540.valid21633
  · exact MergedCutProfiles.Batch540.valid21634
  · exact MergedCutProfiles.Batch540.valid21635
  · exact MergedCutProfiles.Batch540.valid21636
  · exact MergedCutProfiles.Batch540.valid21637
  · exact MergedCutProfiles.Batch540.valid21624
  · exact MergedCutProfiles.Batch540.valid21638
  · exact MergedCutProfiles.Batch540.valid21639
  · exact MergedCutProfiles.Batch541.valid21640
  · exact MergedCutProfiles.Batch541.valid21641
  · exact MergedCutProfiles.Batch541.valid21642
theorem numericValid3519 : retention3519.NumericValid := by decide +kernel
def certificate3519 : RatCutBinCertificate := ⟨⟨retention3519,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(2125518923619994337/1000000000000000000)⟩,(199612820902076689/200000000000000000),(309054386194824287/1000000000000000000),(41003021142628499/125000000000000000),(38001835217535913/200000000000000000)⟩
theorem valid3519 : certificate3519.Valid := by decide +kernel
theorem sound3519 : certificate3519.Sound := rat_cut_bin_certificate_sound certificate3519 profilesValid3519 numericValid3519 valid3519

def retention3520 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(1108516105000000000/55065286028488616857),(544620126237296609/500000000000000000),(5/2),(17576169966347646071/8000000000000000000),true,MergedCutProfiles.Batch540.profile21628,![MergedCutProfiles.Batch540.profile21628,MergedCutProfiles.Batch541.profile21643,MergedCutProfiles.Batch541.profile21644,MergedCutProfiles.Batch541.profile21645,MergedCutProfiles.Batch540.profile21617,MergedCutProfiles.Batch541.profile21646,MergedCutProfiles.Batch541.profile21647,MergedCutProfiles.Batch541.profile21648,MergedCutProfiles.Batch541.profile21649,MergedCutProfiles.Batch540.profile21623,MergedCutProfiles.Batch541.profile21650,MergedCutProfiles.Batch541.profile21651,MergedCutProfiles.Batch541.profile21652,MergedCutProfiles.Batch541.profile21653,MergedCutProfiles.Batch541.profile21654,MergedCutProfiles.Batch541.profile21655]⟩
theorem profilesValid3520 : retention3520.ProfilesValid := by
  change ∀ j : Fin 16, (retention3520.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch540.valid21628
  · exact MergedCutProfiles.Batch541.valid21643
  · exact MergedCutProfiles.Batch541.valid21644
  · exact MergedCutProfiles.Batch541.valid21645
  · exact MergedCutProfiles.Batch540.valid21617
  · exact MergedCutProfiles.Batch541.valid21646
  · exact MergedCutProfiles.Batch541.valid21647
  · exact MergedCutProfiles.Batch541.valid21648
  · exact MergedCutProfiles.Batch541.valid21649
  · exact MergedCutProfiles.Batch540.valid21623
  · exact MergedCutProfiles.Batch541.valid21650
  · exact MergedCutProfiles.Batch541.valid21651
  · exact MergedCutProfiles.Batch541.valid21652
  · exact MergedCutProfiles.Batch541.valid21653
  · exact MergedCutProfiles.Batch541.valid21654
  · exact MergedCutProfiles.Batch541.valid21655
theorem numericValid3520 : retention3520.NumericValid := by decide +kernel
def certificate3520 : RatCutBinCertificate := ⟨⟨retention3520,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(1063801695646079201/500000000000000000)⟩,(199612820902076689/200000000000000000),(143563591554625311/500000000000000000),(354554503850779559/1000000000000000000),(229364013368057409/1000000000000000000)⟩
theorem valid3520 : certificate3520.Valid := by decide +kernel
theorem sound3520 : certificate3520.Sound := rat_cut_bin_certificate_sound certificate3520 profilesValid3520 numericValid3520 valid3520

def retention3521 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(1329080107179907379/55065286028488616857),(221703221/200000000),(49/20),(1740040179827350411/800000000000000000),true,MergedCutProfiles.Batch541.profile21656,![MergedCutProfiles.Batch541.profile21656,MergedCutProfiles.Batch541.profile21657,MergedCutProfiles.Batch541.profile21658,MergedCutProfiles.Batch541.profile21659,MergedCutProfiles.Batch541.profile21646,MergedCutProfiles.Batch541.profile21660,MergedCutProfiles.Batch541.profile21661,MergedCutProfiles.Batch541.profile21662,MergedCutProfiles.Batch540.profile21624,MergedCutProfiles.Batch541.profile21651,MergedCutProfiles.Batch541.profile21663,MergedCutProfiles.Batch541.profile21664,MergedCutProfiles.Batch541.profile21665,MergedCutProfiles.Batch541.profile21666,MergedCutProfiles.Batch541.profile21667,MergedCutProfiles.Batch541.profile21668]⟩
theorem profilesValid3521 : retention3521.ProfilesValid := by
  change ∀ j : Fin 16, (retention3521.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch541.valid21656
  · exact MergedCutProfiles.Batch541.valid21657
  · exact MergedCutProfiles.Batch541.valid21658
  · exact MergedCutProfiles.Batch541.valid21659
  · exact MergedCutProfiles.Batch541.valid21646
  · exact MergedCutProfiles.Batch541.valid21660
  · exact MergedCutProfiles.Batch541.valid21661
  · exact MergedCutProfiles.Batch541.valid21662
  · exact MergedCutProfiles.Batch540.valid21624
  · exact MergedCutProfiles.Batch541.valid21651
  · exact MergedCutProfiles.Batch541.valid21663
  · exact MergedCutProfiles.Batch541.valid21664
  · exact MergedCutProfiles.Batch541.valid21665
  · exact MergedCutProfiles.Batch541.valid21666
  · exact MergedCutProfiles.Batch541.valid21667
  · exact MergedCutProfiles.Batch541.valid21668
theorem numericValid3521 : retention3521.NumericValid := by decide +kernel
def certificate3521 : RatCutBinCertificate := ⟨⟨retention3521,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(1053510356246023467/500000000000000000)⟩,(199612820902076689/200000000000000000),(57574370698675747/200000000000000000),(353626877656660407/1000000000000000000),(230448453504275707/1000000000000000000)⟩
theorem valid3521 : certificate3521.Valid := by decide +kernel
theorem sound3521 : certificate3521.Sound := rat_cut_bin_certificate_sound certificate3521 profilesValid3521 numericValid3521 valid3521

def retention3522 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(4610233059069712068/55065286028488616857),(1329080107179907379/1000000000000000000),(43/20),(2514383250522844366163/1280000000000000000000),true,MergedCutProfiles.Batch541.profile21669,![MergedCutProfiles.Batch541.profile21669,MergedCutProfiles.Batch540.profile21621,MergedCutProfiles.Batch540.profile21626,MergedCutProfiles.Batch541.profile21670,MergedCutProfiles.Batch541.profile21671,MergedCutProfiles.Batch541.profile21672,MergedCutProfiles.Batch541.profile21673,MergedCutProfiles.Batch541.profile21674,MergedCutProfiles.Batch541.profile21675,MergedCutProfiles.Batch541.profile21676,MergedCutProfiles.Batch541.profile21677,MergedCutProfiles.Batch541.profile21678,MergedCutProfiles.Batch541.profile21679,MergedCutProfiles.Batch542.profile21680,MergedCutProfiles.Batch542.profile21681,MergedCutProfiles.Batch542.profile21682]⟩
theorem profilesValid3522 : retention3522.ProfilesValid := by
  change ∀ j : Fin 16, (retention3522.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch541.valid21669
  · exact MergedCutProfiles.Batch540.valid21621
  · exact MergedCutProfiles.Batch540.valid21626
  · exact MergedCutProfiles.Batch541.valid21670
  · exact MergedCutProfiles.Batch541.valid21671
  · exact MergedCutProfiles.Batch541.valid21672
  · exact MergedCutProfiles.Batch541.valid21673
  · exact MergedCutProfiles.Batch541.valid21674
  · exact MergedCutProfiles.Batch541.valid21675
  · exact MergedCutProfiles.Batch541.valid21676
  · exact MergedCutProfiles.Batch541.valid21677
  · exact MergedCutProfiles.Batch541.valid21678
  · exact MergedCutProfiles.Batch541.valid21679
  · exact MergedCutProfiles.Batch542.valid21680
  · exact MergedCutProfiles.Batch542.valid21681
  · exact MergedCutProfiles.Batch542.valid21682
theorem numericValid3522 : retention3522.NumericValid := by decide +kernel
def certificate3522 : RatCutBinCertificate := ⟨⟨retention3522,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(476165697539334937/250000000000000000)⟩,(199612820902076689/200000000000000000),(297084292551543131/1000000000000000000),(85576983368764893/250000000000000000),(230954004588736543/1000000000000000000)⟩
theorem valid3522 : certificate3522.Valid := by decide +kernel
theorem sound3522 : certificate3522.Sound := rat_cut_bin_certificate_sound certificate3522 profilesValid3522 numericValid3522 valid3522

def retention3523 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(21769937927095726423/55065286028488616857),(1152558264767428017/250000000000000000),(11/10),(379443586616940096621/320000000000000000000),true,MergedCutProfiles.Batch542.profile21683,![MergedCutProfiles.Batch542.profile21683,MergedCutProfiles.Batch542.profile21684,MergedCutProfiles.Batch542.profile21685,MergedCutProfiles.Batch542.profile21686,MergedCutProfiles.Batch542.profile21687,MergedCutProfiles.Batch542.profile21688,MergedCutProfiles.Batch542.profile21689,MergedCutProfiles.Batch542.profile21690,MergedCutProfiles.Batch542.profile21691,MergedCutProfiles.Batch542.profile21692,MergedCutProfiles.Batch542.profile21693,MergedCutProfiles.Batch542.profile21694,MergedCutProfiles.Batch542.profile21695,MergedCutProfiles.Batch542.profile21696,MergedCutProfiles.Batch542.profile21697,MergedCutProfiles.Batch542.profile21698]⟩
theorem profilesValid3523 : retention3523.ProfilesValid := by
  change ∀ j : Fin 16, (retention3523.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch542.valid21683
  · exact MergedCutProfiles.Batch542.valid21684
  · exact MergedCutProfiles.Batch542.valid21685
  · exact MergedCutProfiles.Batch542.valid21686
  · exact MergedCutProfiles.Batch542.valid21687
  · exact MergedCutProfiles.Batch542.valid21688
  · exact MergedCutProfiles.Batch542.valid21689
  · exact MergedCutProfiles.Batch542.valid21690
  · exact MergedCutProfiles.Batch542.valid21691
  · exact MergedCutProfiles.Batch542.valid21692
  · exact MergedCutProfiles.Batch542.valid21693
  · exact MergedCutProfiles.Batch542.valid21694
  · exact MergedCutProfiles.Batch542.valid21695
  · exact MergedCutProfiles.Batch542.valid21696
  · exact MergedCutProfiles.Batch542.valid21697
  · exact MergedCutProfiles.Batch542.valid21698
theorem numericValid3523 : retention3523.NumericValid := by decide +kernel
def certificate3523 : RatCutBinCertificate := ⟨⟨retention3523,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(1155218513285907413/1000000000000000000)⟩,(199612820902076689/200000000000000000),(181887971499115509/500000000000000000),(33545458431860029/125000000000000000),(232981713606812757/1000000000000000000)⟩
theorem valid3523 : certificate3523.Valid := by decide +kernel
theorem sound3523 : certificate3523.Sound := rat_cut_bin_certificate_sound certificate3523 profilesValid3523 numericValid3523 valid3523

def retention3524 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(27097387003649139137/55065286028488616857),(21769937927095726423/1000000000000000000),1,(87566551811736195596810433373190729307/87079751708382905692000000000000000000),false,MergedCutProfiles.Batch542.profile21699,(fun _ => MergedCutProfiles.Batch542.profile21699)⟩
theorem profilesValid3524 : retention3524.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21699
theorem numericValid3524 : retention3524.NumericValid := by decide +kernel
def certificate3524 : RatCutBinCertificate := ⟨⟨retention3524,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(195565026324367049/200000000000000000)⟩,(199612820902076689/200000000000000000),(382227278622389619/1000000000000000000),(50033443560506043/200000000000000000),(233638055547334793/1000000000000000000)⟩
theorem valid3524 : certificate3524.Valid := by decide +kernel
theorem sound3524 : certificate3524.Sound := rat_cut_bin_certificate_sound certificate3524 profilesValid3524 numericValid3524 valid3524

def retention3525 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(27368360873685630529/55065286028488616857),(27097387003649139137/1000000000000000000),1,(3381206086048421569453560062376789843/3387173375456142392125000000000000000),false,MergedCutProfiles.Batch542.profile21700,(fun _ => MergedCutProfiles.Batch542.profile21700)⟩
theorem profilesValid3525 : retention3525.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21700
theorem numericValid3525 : retention3525.NumericValid := by decide +kernel
def certificate3525 : RatCutBinCertificate := ⟨⟨retention3525,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(970473177412179709/1000000000000000000)⟩,(199612820902076689/200000000000000000),(382592582242229289/1000000000000000000),(124908044911351027/500000000000000000),(233593242206609507/1000000000000000000)⟩
theorem valid3525 : certificate3525.Valid := by decide +kernel
theorem sound3525 : certificate3525.Sound := rat_cut_bin_certificate_sound certificate3525 profilesValid3525 numericValid3525 valid3525

def retention3526 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(1/2),(27368360873685630529/1000000000000000000),1,(108648190706937578216113864297702409403/109473443494742522116000000000000000000),false,MergedCutProfiles.Batch542.profile21701,(fun _ => MergedCutProfiles.Batch542.profile21701)⟩
theorem profilesValid3526 : retention3526.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21701
theorem numericValid3526 : retention3526.NumericValid := by decide +kernel
def certificate3526 : RatCutBinCertificate := ⟨⟨retention3526,(225169554861169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(48234826380438417/50000000000000000)⟩,(199612820902076689/200000000000000000),(384780578019516723/1000000000000000000),(247720283661431447/1000000000000000000),(115190336205103473/500000000000000000)⟩
theorem valid3526 : certificate3526.Valid := by decide +kernel
theorem sound3526 : certificate3526.Sound := rat_cut_bin_certificate_sound certificate3526 profilesValid3526 numericValid3526 valid3526

def retention3527 : RatCutRetentionCertificate := ⟨(63/1000),(253/4000),(25341419472666297872/55065286028488616857),(35657154427738453/4000000000000000),1,(37405054108073359154042684921182883559/35657154427738453000000000000000000000),false,MergedCutProfiles.Batch542.profile21702,(fun _ => MergedCutProfiles.Batch542.profile21702)⟩
theorem profilesValid3527 : retention3527.ProfilesValid := by
  exact MergedCutProfiles.Batch542.valid21702
theorem numericValid3527 : retention3527.NumericValid := by decide +kernel
def certificate3527 : RatCutBinCertificate := ⟨⟨retention3527,(231018176461169197/100000000000000000),(206867685175350651/1000000000000000000),(838835508587079997/50000000000000000),(462629335143013743249/500000000000000000),(510266428516769097/500000000000000000)⟩,(99801379524132609/100000000000000000),(58874606812924701/500000000000000000),(628174917240787059/1000000000000000000),(574002312049355607/1000000000000000000)⟩
theorem valid3527 : certificate3527.Valid := by decide +kernel
theorem sound3527 : certificate3527.Sound := rat_cut_bin_certificate_sound certificate3527 profilesValid3527 numericValid3527 valid3527

def certificates : List RatCutBinCertificate := [certificate3516,certificate3517,certificate3518,certificate3519,certificate3520,certificate3521,certificate3522,certificate3523,certificate3524,certificate3525,certificate3526,certificate3527]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3516,List.forall_mem_cons.mpr ⟨sound3517,List.forall_mem_cons.mpr ⟨sound3518,List.forall_mem_cons.mpr ⟨sound3519,List.forall_mem_cons.mpr ⟨sound3520,List.forall_mem_cons.mpr ⟨sound3521,List.forall_mem_cons.mpr ⟨sound3522,List.forall_mem_cons.mpr ⟨sound3523,List.forall_mem_cons.mpr ⟨sound3524,List.forall_mem_cons.mpr ⟨sound3525,List.forall_mem_cons.mpr ⟨sound3526,List.forall_mem_cons.mpr ⟨sound3527,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch293
