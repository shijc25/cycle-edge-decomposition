import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch564
import Cycle12.MergedCutProfiles.Batch565
import Cycle12.MergedCutProfiles.Batch566

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch309

def retention3708 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(1287438351000000000/12979510417461775966967),(352655910149024897/500000000000000000),4,(12214981975280493809/5120000000000000000),true,MergedCutProfiles.Batch564.profile22571,![MergedCutProfiles.Batch564.profile22571,MergedCutProfiles.Batch564.profile22573,MergedCutProfiles.Batch564.profile22574,MergedCutProfiles.Batch564.profile22576,MergedCutProfiles.Batch564.profile22577,MergedCutProfiles.Batch564.profile22578,MergedCutProfiles.Batch564.profile22579,MergedCutProfiles.Batch564.profile22580,MergedCutProfiles.Batch564.profile22581,MergedCutProfiles.Batch564.profile22582,MergedCutProfiles.Batch564.profile22582,MergedCutProfiles.Batch564.profile22583,MergedCutProfiles.Batch564.profile22584,MergedCutProfiles.Batch564.profile22585,MergedCutProfiles.Batch564.profile22585,MergedCutProfiles.Batch564.profile22586]⟩
theorem profilesValid3708 : retention3708.ProfilesValid := by
  change ∀ j : Fin 16, (retention3708.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch564.valid22571
  · exact MergedCutProfiles.Batch564.valid22573
  · exact MergedCutProfiles.Batch564.valid22574
  · exact MergedCutProfiles.Batch564.valid22576
  · exact MergedCutProfiles.Batch564.valid22577
  · exact MergedCutProfiles.Batch564.valid22578
  · exact MergedCutProfiles.Batch564.valid22579
  · exact MergedCutProfiles.Batch564.valid22580
  · exact MergedCutProfiles.Batch564.valid22581
  · exact MergedCutProfiles.Batch564.valid22582
  · exact MergedCutProfiles.Batch564.valid22582
  · exact MergedCutProfiles.Batch564.valid22583
  · exact MergedCutProfiles.Batch564.valid22584
  · exact MergedCutProfiles.Batch564.valid22585
  · exact MergedCutProfiles.Batch564.valid22585
  · exact MergedCutProfiles.Batch564.valid22586
theorem numericValid3708 : retention3708.NumericValid := by decide +kernel
def certificate3708 : RatCutBinCertificate := ⟨⟨retention3708,(221054140063555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(1191128229342588893/500000000000000000)⟩,(999981771172697331/1000000000000000000),(499593242530265279/1000000000000000000),(1921355832256487/12500000000000000),(75585279320272177/1000000000000000000)⟩
theorem valid3708 : certificate3708.Valid := by decide +kernel
theorem sound3708 : certificate3708.Sound := rat_cut_bin_certificate_sound certificate3708 profilesValid3708 numericValid3708 valid3708

def retention3709 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(4579303556828937443/12979510417461775966967),(1287438351/1000000000),(5/2),(486391495819329238255474902749008151/205990136160000000000000000000000000),true,MergedCutProfiles.Batch564.profile22575,![MergedCutProfiles.Batch564.profile22575,MergedCutProfiles.Batch564.profile22579,MergedCutProfiles.Batch564.profile22582,MergedCutProfiles.Batch564.profile22585,MergedCutProfiles.Batch564.profile22587,MergedCutProfiles.Batch564.profile22588,MergedCutProfiles.Batch564.profile22589,MergedCutProfiles.Batch564.profile22590,MergedCutProfiles.Batch564.profile22591,MergedCutProfiles.Batch564.profile22592,MergedCutProfiles.Batch564.profile22593,MergedCutProfiles.Batch564.profile22594,MergedCutProfiles.Batch564.profile22595,MergedCutProfiles.Batch564.profile22596,MergedCutProfiles.Batch564.profile22597,MergedCutProfiles.Batch564.profile22598]⟩
theorem profilesValid3709 : retention3709.ProfilesValid := by
  change ∀ j : Fin 16, (retention3709.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch564.valid22575
  · exact MergedCutProfiles.Batch564.valid22579
  · exact MergedCutProfiles.Batch564.valid22582
  · exact MergedCutProfiles.Batch564.valid22585
  · exact MergedCutProfiles.Batch564.valid22587
  · exact MergedCutProfiles.Batch564.valid22588
  · exact MergedCutProfiles.Batch564.valid22589
  · exact MergedCutProfiles.Batch564.valid22590
  · exact MergedCutProfiles.Batch564.valid22591
  · exact MergedCutProfiles.Batch564.valid22592
  · exact MergedCutProfiles.Batch564.valid22593
  · exact MergedCutProfiles.Batch564.valid22594
  · exact MergedCutProfiles.Batch564.valid22595
  · exact MergedCutProfiles.Batch564.valid22596
  · exact MergedCutProfiles.Batch564.valid22597
  · exact MergedCutProfiles.Batch564.valid22598
theorem numericValid3709 : retention3709.NumericValid := by decide +kernel
def certificate3709 : RatCutBinCertificate := ⟨⟨retention3709,(221054140063555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(1179530224164489433/500000000000000000)⟩,(999981771172697331/1000000000000000000),(357572745388943251/1000000000000000000),(274688875093708729/1000000000000000000),(100217265625449401/500000000000000000)⟩
theorem valid3709 : certificate3709.Valid := by decide +kernel
theorem sound3709 : certificate3709.Sound := rat_cut_bin_certificate_sound certificate3709 profilesValid3709 numericValid3709 valid3709

def retention3710 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(64000000000000000000/12979510417461775966967),(4579303556828937443/1000000000000000000),(5/4),(143773106028732846353/64000000000000000000),true,MergedCutProfiles.Batch564.profile22596,![MergedCutProfiles.Batch564.profile22596,MergedCutProfiles.Batch564.profile22599,MergedCutProfiles.Batch565.profile22600,MergedCutProfiles.Batch565.profile22601,MergedCutProfiles.Batch565.profile22602,MergedCutProfiles.Batch565.profile22603,MergedCutProfiles.Batch565.profile22604,MergedCutProfiles.Batch565.profile22605,MergedCutProfiles.Batch565.profile22606,MergedCutProfiles.Batch565.profile22607,MergedCutProfiles.Batch565.profile22608,MergedCutProfiles.Batch565.profile22609,MergedCutProfiles.Batch565.profile22610,MergedCutProfiles.Batch565.profile22611,MergedCutProfiles.Batch565.profile22612,MergedCutProfiles.Batch565.profile22613]⟩
theorem profilesValid3710 : retention3710.ProfilesValid := by
  change ∀ j : Fin 16, (retention3710.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch564.valid22596
  · exact MergedCutProfiles.Batch564.valid22599
  · exact MergedCutProfiles.Batch565.valid22600
  · exact MergedCutProfiles.Batch565.valid22601
  · exact MergedCutProfiles.Batch565.valid22602
  · exact MergedCutProfiles.Batch565.valid22603
  · exact MergedCutProfiles.Batch565.valid22604
  · exact MergedCutProfiles.Batch565.valid22605
  · exact MergedCutProfiles.Batch565.valid22606
  · exact MergedCutProfiles.Batch565.valid22607
  · exact MergedCutProfiles.Batch565.valid22608
  · exact MergedCutProfiles.Batch565.valid22609
  · exact MergedCutProfiles.Batch565.valid22610
  · exact MergedCutProfiles.Batch565.valid22611
  · exact MergedCutProfiles.Batch565.valid22612
  · exact MergedCutProfiles.Batch565.valid22613
theorem numericValid3710 : retention3710.NumericValid := by decide +kernel
def certificate3710 : RatCutBinCertificate := ⟨⟨retention3710,(221054140063555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(112268329579664617/50000000000000000)⟩,(999981771172697331/1000000000000000000),(241223341329438089/1000000000000000000),(415643226376475417/1000000000000000000),(568272484649361269/1000000000000000000)⟩
theorem valid3710 : certificate3710.Valid := by decide +kernel
theorem sound3710 : certificate3710.Sound := rat_cut_bin_certificate_sound certificate3710 profilesValid3710 numericValid3710 valid3710

def retention3711 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(1/2),64,1,(10214764058726808886536973820167101271/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch565.profile22614,(fun _ => MergedCutProfiles.Batch565.profile22614)⟩
theorem profilesValid3711 : retention3711.ProfilesValid := by
  exact MergedCutProfiles.Batch565.valid22614
theorem numericValid3711 : retention3711.NumericValid := by decide +kernel
def certificate3711 : RatCutBinCertificate := ⟨⟨retention3711,(221054140063555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(49833250026537683/50000000000000000)⟩,(999981771172697331/1000000000000000000),(86691235643995611/200000000000000000),(204189335792424317/1000000000000000000),(25048007893471299/125000000000000000)⟩
theorem valid3711 : certificate3711.Valid := by decide +kernel
theorem sound3711 : certificate3711.Sound := rat_cut_bin_certificate_sound certificate3711 profilesValid3711 numericValid3711 valid3711

def retention3712 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(64000000000000000000/12979510417461775966967),(15986693708051214293/1000000000000000000),1,(2233054161579900184044404376649165863/999168356753200893312500000000000000),false,MergedCutProfiles.Batch565.profile22615,(fun _ => MergedCutProfiles.Batch565.profile22615)⟩
theorem profilesValid3712 : retention3712.ProfilesValid := by
  exact MergedCutProfiles.Batch565.valid22615
theorem numericValid3712 : retention3712.NumericValid := by decide +kernel
def certificate3712 : RatCutBinCertificate := ⟨⟨retention3712,(220682097938555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(2234043724816811669/1000000000000000000)⟩,(999981801852475823/1000000000000000000),(6587567680164659/200000000000000000),(167151644746373919/200000000000000000),(1638162127183200659/1000000000000000000)⟩
theorem valid3712 : certificate3712.Valid := by decide +kernel
theorem sound3712 : certificate3712.Sound := rat_cut_bin_certificate_sound certificate3712 profilesValid3712 numericValid3712 valid3712

def retention3713 : RatCutRetentionCertificate := ⟨(9/1000),(19/2000),(1/2),64,1,(10214764058726808886536973820167101271/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch565.profile22614,(fun _ => MergedCutProfiles.Batch565.profile22614)⟩
theorem profilesValid3713 : retention3713.ProfilesValid := by
  exact MergedCutProfiles.Batch565.valid22614
theorem numericValid3713 : retention3713.NumericValid := by decide +kernel
def certificate3713 : RatCutBinCertificate := ⟨⟨retention3713,(220682097938555913/125000000000000000),(3659123537247033/1000000000000000000),(7433116769339109203/1000000000000000000),(48347460048084572699147/500000000000000000),(49833323285071861/50000000000000000)⟩,(999981801852475823/1000000000000000000),(36915344160095673/500000000000000000),(90918009321377149/125000000000000000),(89223793109699453/125000000000000000)⟩
theorem valid3713 : certificate3713.Valid := by decide +kernel
theorem sound3713 : certificate3713.Sound := rat_cut_bin_certificate_sound certificate3713 profilesValid3713 numericValid3713 valid3713

def retention3714 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(631281066439576069/11687681432743611454488),(571490514192422669/1000000000000000000),4,(314956142442121356660140440908608617/142872628548105667250000000000000000),true,MergedCutProfiles.Batch565.profile22616,![MergedCutProfiles.Batch565.profile22616,MergedCutProfiles.Batch565.profile22617,MergedCutProfiles.Batch565.profile22618,MergedCutProfiles.Batch565.profile22619,MergedCutProfiles.Batch565.profile22620,MergedCutProfiles.Batch565.profile22621,MergedCutProfiles.Batch565.profile22621,MergedCutProfiles.Batch565.profile22622,MergedCutProfiles.Batch565.profile22623,MergedCutProfiles.Batch565.profile22623,MergedCutProfiles.Batch565.profile22624,MergedCutProfiles.Batch565.profile22625,MergedCutProfiles.Batch565.profile22625,MergedCutProfiles.Batch565.profile22626,MergedCutProfiles.Batch565.profile22626,MergedCutProfiles.Batch565.profile22627]⟩
theorem profilesValid3714 : retention3714.ProfilesValid := by
  change ∀ j : Fin 16, (retention3714.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch565.valid22616
  · exact MergedCutProfiles.Batch565.valid22617
  · exact MergedCutProfiles.Batch565.valid22618
  · exact MergedCutProfiles.Batch565.valid22619
  · exact MergedCutProfiles.Batch565.valid22620
  · exact MergedCutProfiles.Batch565.valid22621
  · exact MergedCutProfiles.Batch565.valid22621
  · exact MergedCutProfiles.Batch565.valid22622
  · exact MergedCutProfiles.Batch565.valid22623
  · exact MergedCutProfiles.Batch565.valid22623
  · exact MergedCutProfiles.Batch565.valid22624
  · exact MergedCutProfiles.Batch565.valid22625
  · exact MergedCutProfiles.Batch565.valid22625
  · exact MergedCutProfiles.Batch565.valid22626
  · exact MergedCutProfiles.Batch565.valid22626
  · exact MergedCutProfiles.Batch565.valid22627
theorem numericValid3714 : retention3714.NumericValid := by decide +kernel
def certificate3714 : RatCutBinCertificate := ⟨⟨retention3714,(436571528542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(2200660982097504081/1000000000000000000)⟩,(999980139517636921/1000000000000000000),(630421155555292449/1000000000000000000),(78723212148176189/1000000000000000000),(4363539260824033/125000000000000000)⟩
theorem valid3714 : certificate3714.Valid := by decide +kernel
theorem sound3714 : certificate3714.Sound := rat_cut_bin_certificate_sound certificate3714 profilesValid3714 numericValid3714 valid3714

def retention3715 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(160738642375000000/1460960179092951431811),(631281066439576069/1000000000000000000),4,(5834331298726770538375502503696844407/2525124265758304276000000000000000000),true,MergedCutProfiles.Batch565.profile22617,![MergedCutProfiles.Batch565.profile22617,MergedCutProfiles.Batch565.profile22619,MergedCutProfiles.Batch565.profile22621,MergedCutProfiles.Batch565.profile22622,MergedCutProfiles.Batch565.profile22624,MergedCutProfiles.Batch565.profile22625,MergedCutProfiles.Batch565.profile22626,MergedCutProfiles.Batch565.profile22627,MergedCutProfiles.Batch565.profile22628,MergedCutProfiles.Batch565.profile22628,MergedCutProfiles.Batch565.profile22629,MergedCutProfiles.Batch565.profile22630,MergedCutProfiles.Batch565.profile22631,MergedCutProfiles.Batch565.profile22632,MergedCutProfiles.Batch565.profile22632,MergedCutProfiles.Batch565.profile22633]⟩
theorem profilesValid3715 : retention3715.ProfilesValid := by
  change ∀ j : Fin 16, (retention3715.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch565.valid22617
  · exact MergedCutProfiles.Batch565.valid22619
  · exact MergedCutProfiles.Batch565.valid22621
  · exact MergedCutProfiles.Batch565.valid22622
  · exact MergedCutProfiles.Batch565.valid22624
  · exact MergedCutProfiles.Batch565.valid22625
  · exact MergedCutProfiles.Batch565.valid22626
  · exact MergedCutProfiles.Batch565.valid22627
  · exact MergedCutProfiles.Batch565.valid22628
  · exact MergedCutProfiles.Batch565.valid22628
  · exact MergedCutProfiles.Batch565.valid22629
  · exact MergedCutProfiles.Batch565.valid22630
  · exact MergedCutProfiles.Batch565.valid22631
  · exact MergedCutProfiles.Batch565.valid22632
  · exact MergedCutProfiles.Batch565.valid22632
  · exact MergedCutProfiles.Batch565.valid22633
theorem numericValid3715 : retention3715.NumericValid := by decide +kernel
def certificate3715 : RatCutBinCertificate := ⟨⟨retention3715,(436571528542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(576679873612694977/250000000000000000)⟩,(999980139517636921/1000000000000000000),(281057532631585053/500000000000000000),(114079273050245311/1000000000000000000),(53554959311582643/1000000000000000000)⟩
theorem valid3715 : certificate3715.Valid := by decide +kernel
theorem sound3715 : certificate3715.Sound := rat_cut_bin_certificate_sound certificate3715 profilesValid3715 numericValid3715 valid3715

def retention3716 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(23697553280046173/39485410245755444103),(1285909139/1000000000),(5/2),(756742745097970511660063064148279039/321477284750000000000000000000000000),true,MergedCutProfiles.Batch565.profile22624,![MergedCutProfiles.Batch565.profile22624,MergedCutProfiles.Batch565.profile22629,MergedCutProfiles.Batch565.profile22633,MergedCutProfiles.Batch565.profile22634,MergedCutProfiles.Batch565.profile22635,MergedCutProfiles.Batch565.profile22636,MergedCutProfiles.Batch565.profile22637,MergedCutProfiles.Batch565.profile22638,MergedCutProfiles.Batch565.profile22639,MergedCutProfiles.Batch566.profile22640,MergedCutProfiles.Batch566.profile22641,MergedCutProfiles.Batch566.profile22642,MergedCutProfiles.Batch566.profile22643,MergedCutProfiles.Batch566.profile22644,MergedCutProfiles.Batch566.profile22645,MergedCutProfiles.Batch566.profile22646]⟩
theorem profilesValid3716 : retention3716.ProfilesValid := by
  change ∀ j : Fin 16, (retention3716.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch565.valid22624
  · exact MergedCutProfiles.Batch565.valid22629
  · exact MergedCutProfiles.Batch565.valid22633
  · exact MergedCutProfiles.Batch565.valid22634
  · exact MergedCutProfiles.Batch565.valid22635
  · exact MergedCutProfiles.Batch565.valid22636
  · exact MergedCutProfiles.Batch565.valid22637
  · exact MergedCutProfiles.Batch565.valid22638
  · exact MergedCutProfiles.Batch565.valid22639
  · exact MergedCutProfiles.Batch566.valid22640
  · exact MergedCutProfiles.Batch566.valid22641
  · exact MergedCutProfiles.Batch566.valid22642
  · exact MergedCutProfiles.Batch566.valid22643
  · exact MergedCutProfiles.Batch566.valid22644
  · exact MergedCutProfiles.Batch566.valid22645
  · exact MergedCutProfiles.Batch566.valid22646
theorem numericValid3716 : retention3716.NumericValid := by decide +kernel
def certificate3716 : RatCutBinCertificate := ⟨⟨retention3716,(436571528542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(146973959809804809/62500000000000000)⟩,(999980139517636921/1000000000000000000),(18185618548078847/50000000000000000),(268427950950199507/1000000000000000000),(195332762120728459/1000000000000000000)⟩
theorem valid3716 : certificate3716.Valid := by decide +kernel
theorem sound3716 : certificate3716.Sound := rat_cut_bin_certificate_sound certificate3716 profilesValid3716 numericValid3716 valid3716

def retention3717 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(8000000000000000000/1460960179092951431811),(876809471361708401/125000000000000000),(11/10),(389974195476094322365246548375570408151/175361894272341680200000000000000000000),true,MergedCutProfiles.Batch565.profile22639,![MergedCutProfiles.Batch565.profile22639,MergedCutProfiles.Batch566.profile22647,MergedCutProfiles.Batch566.profile22648,MergedCutProfiles.Batch566.profile22649,MergedCutProfiles.Batch566.profile22650,MergedCutProfiles.Batch566.profile22651,MergedCutProfiles.Batch566.profile22652,MergedCutProfiles.Batch566.profile22653,MergedCutProfiles.Batch566.profile22654,MergedCutProfiles.Batch566.profile22655,MergedCutProfiles.Batch566.profile22656,MergedCutProfiles.Batch566.profile22657,MergedCutProfiles.Batch566.profile22658,MergedCutProfiles.Batch566.profile22659,MergedCutProfiles.Batch566.profile22660,MergedCutProfiles.Batch566.profile22661]⟩
theorem profilesValid3717 : retention3717.ProfilesValid := by
  change ∀ j : Fin 16, (retention3717.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch565.valid22639
  · exact MergedCutProfiles.Batch566.valid22647
  · exact MergedCutProfiles.Batch566.valid22648
  · exact MergedCutProfiles.Batch566.valid22649
  · exact MergedCutProfiles.Batch566.valid22650
  · exact MergedCutProfiles.Batch566.valid22651
  · exact MergedCutProfiles.Batch566.valid22652
  · exact MergedCutProfiles.Batch566.valid22653
  · exact MergedCutProfiles.Batch566.valid22654
  · exact MergedCutProfiles.Batch566.valid22655
  · exact MergedCutProfiles.Batch566.valid22656
  · exact MergedCutProfiles.Batch566.valid22657
  · exact MergedCutProfiles.Batch566.valid22658
  · exact MergedCutProfiles.Batch566.valid22659
  · exact MergedCutProfiles.Batch566.valid22660
  · exact MergedCutProfiles.Batch566.valid22661
theorem numericValid3717 : retention3717.NumericValid := by decide +kernel
def certificate3717 : RatCutBinCertificate := ⟨⟨retention3717,(436571528542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(1111391043517610849/500000000000000000)⟩,(999980139517636921/1000000000000000000),(228416725155814249/1000000000000000000),(54270043326670519/125000000000000000),(695223215744371433/1000000000000000000)⟩
theorem valid3717 : certificate3717.Valid := by decide +kernel
theorem sound3717 : certificate3717.Sound := rat_cut_bin_certificate_sound certificate3717 profilesValid3717 numericValid3717 valid3717

def retention3718 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(1/2),64,1,(15960572082716405919661104632746380231/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch566.profile22662,(fun _ => MergedCutProfiles.Batch566.profile22662)⟩
theorem profilesValid3718 : retention3718.ProfilesValid := by
  exact MergedCutProfiles.Batch566.valid22662
theorem numericValid3718 : retention3718.NumericValid := by decide +kernel
def certificate3718 : RatCutBinCertificate := ⟨⟨retention3718,(436571528542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(199317498410669073/200000000000000000)⟩,(999980139517636921/1000000000000000000),(109937591837113067/250000000000000000),(99486591283691061/500000000000000000),(24406230476735371/125000000000000000)⟩
theorem valid3718 : certificate3718.Valid := by decide +kernel
theorem sound3718 : certificate3718.Sound := rat_cut_bin_certificate_sound certificate3718 profilesValid3718 numericValid3718 valid3718

def retention3719 : RatCutRetentionCertificate := ⟨(19/2000),(1/100),(8000000000000000000/1460960179092951431811),(648251116319971077/40000000000000000),1,(180752173587707273091979021628122393/81031389539996384625000000000000000),false,MergedCutProfiles.Batch566.profile22663,(fun _ => MergedCutProfiles.Batch566.profile22663)⟩
theorem profilesValid3719 : retention3719.ProfilesValid := by
  exact MergedCutProfiles.Batch566.valid22663
theorem numericValid3719 : retention3719.NumericValid := by decide +kernel
def certificate3719 : RatCutBinCertificate := ⟨⟨retention3719,(441283115542279867/250000000000000000),(4061079806220747/1000000000000000000),(7478733651448619323/1000000000000000000),(87605946957905369254317/1000000000000000000),(2229685388206440663/1000000000000000000)⟩,(99997992517842491/100000000000000000),(8200632613445411/250000000000000000),(418073744893660419/500000000000000000),(1638833891894105569/1000000000000000000)⟩
theorem valid3719 : certificate3719.Valid := by decide +kernel
theorem sound3719 : certificate3719.Sound := rat_cut_bin_certificate_sound certificate3719 profilesValid3719 numericValid3719 valid3719

def certificates : List RatCutBinCertificate := [certificate3708,certificate3709,certificate3710,certificate3711,certificate3712,certificate3713,certificate3714,certificate3715,certificate3716,certificate3717,certificate3718,certificate3719]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3708,List.forall_mem_cons.mpr ⟨sound3709,List.forall_mem_cons.mpr ⟨sound3710,List.forall_mem_cons.mpr ⟨sound3711,List.forall_mem_cons.mpr ⟨sound3712,List.forall_mem_cons.mpr ⟨sound3713,List.forall_mem_cons.mpr ⟨sound3714,List.forall_mem_cons.mpr ⟨sound3715,List.forall_mem_cons.mpr ⟨sound3716,List.forall_mem_cons.mpr ⟨sound3717,List.forall_mem_cons.mpr ⟨sound3718,List.forall_mem_cons.mpr ⟨sound3719,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch309
