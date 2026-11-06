import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch090
import Cycle12.MergedCutProfiles.Batch091
import Cycle12.MergedCutProfiles.Batch092

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch045

def retention540 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(13060471440245483855/29036633862227320134),(789602619997039899/125000000000000000),1,(33851809450215923529/32000000000000000000),true,MergedCutProfiles.Batch090.profile3606,![MergedCutProfiles.Batch090.profile3606,MergedCutProfiles.Batch090.profile3607,MergedCutProfiles.Batch090.profile3608,MergedCutProfiles.Batch090.profile3609,MergedCutProfiles.Batch090.profile3610,MergedCutProfiles.Batch090.profile3611,MergedCutProfiles.Batch090.profile3612,MergedCutProfiles.Batch090.profile3613,MergedCutProfiles.Batch090.profile3614,MergedCutProfiles.Batch090.profile3615,MergedCutProfiles.Batch090.profile3616,MergedCutProfiles.Batch090.profile3617,MergedCutProfiles.Batch090.profile3618,MergedCutProfiles.Batch090.profile3619,MergedCutProfiles.Batch090.profile3620,MergedCutProfiles.Batch090.profile3621]⟩
theorem profilesValid540 : retention540.ProfilesValid := by
  change ∀ j : Fin 16, (retention540.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch090.valid3606
  · exact MergedCutProfiles.Batch090.valid3607
  · exact MergedCutProfiles.Batch090.valid3608
  · exact MergedCutProfiles.Batch090.valid3609
  · exact MergedCutProfiles.Batch090.valid3610
  · exact MergedCutProfiles.Batch090.valid3611
  · exact MergedCutProfiles.Batch090.valid3612
  · exact MergedCutProfiles.Batch090.valid3613
  · exact MergedCutProfiles.Batch090.valid3614
  · exact MergedCutProfiles.Batch090.valid3615
  · exact MergedCutProfiles.Batch090.valid3616
  · exact MergedCutProfiles.Batch090.valid3617
  · exact MergedCutProfiles.Batch090.valid3618
  · exact MergedCutProfiles.Batch090.valid3619
  · exact MergedCutProfiles.Batch090.valid3620
  · exact MergedCutProfiles.Batch090.valid3621
theorem numericValid540 : retention540.NumericValid := by decide +kernel
def certificate540 : RatCutBinCertificate := ⟨⟨retention540,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(52181442565712511/50000000000000000)⟩,(994289149259070193/1000000000000000000),(486394238473082587/1000000000000000000),(163043942214950893/1000000000000000000),(145133272332190841/1000000000000000000)⟩
theorem valid540 : certificate540.Valid := by decide +kernel
theorem sound540 : certificate540.Sound := rat_cut_bin_certificate_sound certificate540 profilesValid540 numericValid540 valid540

def retention541 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(7213442860598150830/14518316931113660067),(2612094288049096771/200000000000000000),(21/20),(840397035224939240775886843699270524671/835870172175710966720000000000000000000),false,MergedCutProfiles.Batch090.profile3622,(fun _ => MergedCutProfiles.Batch090.profile3622)⟩
theorem profilesValid541 : retention541.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3622
theorem numericValid541 : retention541.NumericValid := by decide +kernel
def certificate541 : RatCutBinCertificate := ⟨⟨retention541,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(7737998797720721/7812500000000000)⟩,(994289149259070193/1000000000000000000),(243651273986387981/500000000000000000),(162390141169140763/1000000000000000000),(142473829444132503/1000000000000000000)⟩
theorem valid541 : certificate541.Valid := by decide +kernel
theorem sound541 : certificate541.Sound := rat_cut_bin_certificate_sound certificate541 profilesValid541 numericValid541 valid541

def retention542 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(1/2),(721344286059815083/50000000000000000),(21/20),(11543305913917554103785231919921525899/11541508576957041328000000000000000000),false,MergedCutProfiles.Batch090.profile3623,(fun _ => MergedCutProfiles.Batch090.profile3623)⟩
theorem profilesValid542 : retention542.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3623
theorem numericValid542 : retention542.NumericValid := by decide +kernel
def certificate542 : RatCutBinCertificate := ⟨⟨retention542,(1037835275846982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(985203849518684257/1000000000000000000)⟩,(994289149259070193/1000000000000000000),(487656631446820171/1000000000000000000),(16213573072917677/100000000000000000),(14241009842448799/100000000000000000)⟩
theorem valid542 : certificate542.Valid := by decide +kernel
theorem sound542 : certificate542.Sound := rat_cut_bin_certificate_sound certificate542 profilesValid542 numericValid542 valid542

def retention543 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(6379278064630586120/14518316931113660067),(3752084006030571863/1000000000000000000),(6/5),(52273444381752166887779082811509572407/46901050075382148287500000000000000000),false,MergedCutProfiles.Batch090.profile3624,(fun _ => MergedCutProfiles.Batch090.profile3624)⟩
theorem profilesValid543 : retention543.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3624
theorem numericValid543 : retention543.NumericValid := by decide +kernel
def certificate543 : RatCutBinCertificate := ⟨⟨retention543,(1234707863346982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(547108661424199649/500000000000000000)⟩,(993205213000348879/1000000000000000000),(184217150440913803/500000000000000000),(52736650047865419/200000000000000000),(198468696481835537/1000000000000000000)⟩
theorem valid543 : certificate543.Valid := by decide +kernel
theorem sound543 : certificate543.Sound := rat_cut_bin_certificate_sound certificate543 profilesValid543 numericValid543 valid543

def retention544 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(14376660394795147381/29036633862227320134),(159481951615764653/12500000000000000),1,(50587851554006493440573378063693138991/51034224517044688960000000000000000000),false,MergedCutProfiles.Batch090.profile3625,(fun _ => MergedCutProfiles.Batch090.profile3625)⟩
theorem profilesValid544 : retention544.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3625
theorem numericValid544 : retention544.NumericValid := by decide +kernel
def certificate544 : RatCutBinCertificate := ⟨⟨retention544,(1234707863346982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(974312284104829017/1000000000000000000)⟩,(993205213000348879/1000000000000000000),(3310209270136303/8000000000000000),(221094409523098771/1000000000000000000),(49681294262394131/250000000000000000)⟩
theorem valid544 : certificate544.Valid := by decide +kernel
theorem sound544 : certificate544.Sound := rat_cut_bin_certificate_sound certificate544 profilesValid544 numericValid544 valid544

def retention545 : RatCutRetentionCertificate := ⟨(41/1000),(83/2000),(1/2),(14376660394795147381/1000000000000000000),1,(1768462051227661828137648385684987139/1797082549349393422625000000000000000),false,MergedCutProfiles.Batch090.profile3623,(fun _ => MergedCutProfiles.Batch090.profile3623)⟩
theorem profilesValid545 : retention545.ProfilesValid := by
  exact MergedCutProfiles.Batch090.valid3623
theorem numericValid545 : retention545.NumericValid := by decide +kernel
def certificate545 : RatCutBinCertificate := ⟨⟨retention545,(1234707863346982131/500000000000000000),(19770779397321387/250000000000000000),(92221564524269007/8000000000000000),(335633625337807551309/1000000000000000000),(19342655419802973/20000000000000000)⟩,(993205213000348879/1000000000000000000),(416847827360553329/1000000000000000000),(43679065961062363/200000000000000000),(196517915176536011/1000000000000000000)⟩
theorem valid545 : certificate545.Valid := by decide +kernel
theorem sound545 : certificate545.Sound := rat_cut_bin_certificate_sound certificate545 profilesValid545 numericValid545 valid545

def retention546 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(806420884500146310/28272455108468384129),(399218259653537777/500000000000000000),(63/20),(10698523196765060457/5000000000000000000),true,MergedCutProfiles.Batch090.profile3626,![MergedCutProfiles.Batch090.profile3626,MergedCutProfiles.Batch090.profile3627,MergedCutProfiles.Batch090.profile3628,MergedCutProfiles.Batch090.profile3629,MergedCutProfiles.Batch090.profile3630,MergedCutProfiles.Batch090.profile3631,MergedCutProfiles.Batch090.profile3632,MergedCutProfiles.Batch090.profile3633,MergedCutProfiles.Batch090.profile3634,MergedCutProfiles.Batch090.profile3635,MergedCutProfiles.Batch090.profile3636,MergedCutProfiles.Batch090.profile3637,MergedCutProfiles.Batch090.profile3638,MergedCutProfiles.Batch090.profile3639,MergedCutProfiles.Batch091.profile3640,MergedCutProfiles.Batch091.profile3641]⟩
theorem profilesValid546 : retention546.ProfilesValid := by
  change ∀ j : Fin 16, (retention546.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch090.valid3626
  · exact MergedCutProfiles.Batch090.valid3627
  · exact MergedCutProfiles.Batch090.valid3628
  · exact MergedCutProfiles.Batch090.valid3629
  · exact MergedCutProfiles.Batch090.valid3630
  · exact MergedCutProfiles.Batch090.valid3631
  · exact MergedCutProfiles.Batch090.valid3632
  · exact MergedCutProfiles.Batch090.valid3633
  · exact MergedCutProfiles.Batch090.valid3634
  · exact MergedCutProfiles.Batch090.valid3635
  · exact MergedCutProfiles.Batch090.valid3636
  · exact MergedCutProfiles.Batch090.valid3637
  · exact MergedCutProfiles.Batch090.valid3638
  · exact MergedCutProfiles.Batch090.valid3639
  · exact MergedCutProfiles.Batch091.valid3640
  · exact MergedCutProfiles.Batch091.valid3641
theorem numericValid546 : retention546.NumericValid := by decide +kernel
def certificate546 : RatCutBinCertificate := ⟨⟨retention546,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(32716792348901419/15625000000000000)⟩,(994176430235862879/1000000000000000000),(199144348597885677/500000000000000000),(235054008477186399/1000000000000000000),(24547214629250539/200000000000000000)⟩
theorem valid546 : certificate546.Valid := by decide +kernel
theorem sound546 : certificate546.Sound := rat_cut_bin_certificate_sound certificate546 profilesValid546 numericValid546 valid546

def retention547 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(890790351412535090/28272455108468384129),(80642088450014631/100000000000000000),(63/20),(272929699021657486823/128000000000000000000),true,MergedCutProfiles.Batch091.profile3642,![MergedCutProfiles.Batch091.profile3642,MergedCutProfiles.Batch091.profile3643,MergedCutProfiles.Batch091.profile3644,MergedCutProfiles.Batch091.profile3645,MergedCutProfiles.Batch091.profile3646,MergedCutProfiles.Batch091.profile3647,MergedCutProfiles.Batch091.profile3648,MergedCutProfiles.Batch091.profile3649,MergedCutProfiles.Batch091.profile3650,MergedCutProfiles.Batch091.profile3651,MergedCutProfiles.Batch091.profile3652,MergedCutProfiles.Batch091.profile3653,MergedCutProfiles.Batch091.profile3654,MergedCutProfiles.Batch091.profile3655,MergedCutProfiles.Batch091.profile3656,MergedCutProfiles.Batch091.profile3657]⟩
theorem profilesValid547 : retention547.ProfilesValid := by
  change ∀ j : Fin 16, (retention547.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch091.valid3642
  · exact MergedCutProfiles.Batch091.valid3643
  · exact MergedCutProfiles.Batch091.valid3644
  · exact MergedCutProfiles.Batch091.valid3645
  · exact MergedCutProfiles.Batch091.valid3646
  · exact MergedCutProfiles.Batch091.valid3647
  · exact MergedCutProfiles.Batch091.valid3648
  · exact MergedCutProfiles.Batch091.valid3649
  · exact MergedCutProfiles.Batch091.valid3650
  · exact MergedCutProfiles.Batch091.valid3651
  · exact MergedCutProfiles.Batch091.valid3652
  · exact MergedCutProfiles.Batch091.valid3653
  · exact MergedCutProfiles.Batch091.valid3654
  · exact MergedCutProfiles.Batch091.valid3655
  · exact MergedCutProfiles.Batch091.valid3656
  · exact MergedCutProfiles.Batch091.valid3657
theorem numericValid547 : retention547.NumericValid := by decide +kernel
def certificate547 : RatCutBinCertificate := ⟨⟨retention547,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(417286677811132591/200000000000000000)⟩,(994176430235862879/1000000000000000000),(3183437691532531/8000000000000000),(235384629317220537/1000000000000000000),(122817356504952053/1000000000000000000)⟩
theorem valid547 : certificate547.Valid := by decide +kernel
theorem sound547 : certificate547.Sound := rat_cut_bin_certificate_sound certificate547 profilesValid547 numericValid547 valid547

def retention548 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(903070886000000000/28272455108468384129),(89079035141253509/100000000000000000),(29/10),(272139002203912148273/128000000000000000000),true,MergedCutProfiles.Batch091.profile3658,![MergedCutProfiles.Batch091.profile3658,MergedCutProfiles.Batch091.profile3659,MergedCutProfiles.Batch091.profile3660,MergedCutProfiles.Batch091.profile3661,MergedCutProfiles.Batch091.profile3662,MergedCutProfiles.Batch091.profile3663,MergedCutProfiles.Batch091.profile3664,MergedCutProfiles.Batch091.profile3665,MergedCutProfiles.Batch091.profile3666,MergedCutProfiles.Batch091.profile3667,MergedCutProfiles.Batch091.profile3668,MergedCutProfiles.Batch091.profile3669,MergedCutProfiles.Batch091.profile3670,MergedCutProfiles.Batch091.profile3671,MergedCutProfiles.Batch091.profile3672,MergedCutProfiles.Batch091.profile3673]⟩
theorem profilesValid548 : retention548.ProfilesValid := by
  change ∀ j : Fin 16, (retention548.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch091.valid3658
  · exact MergedCutProfiles.Batch091.valid3659
  · exact MergedCutProfiles.Batch091.valid3660
  · exact MergedCutProfiles.Batch091.valid3661
  · exact MergedCutProfiles.Batch091.valid3662
  · exact MergedCutProfiles.Batch091.valid3663
  · exact MergedCutProfiles.Batch091.valid3664
  · exact MergedCutProfiles.Batch091.valid3665
  · exact MergedCutProfiles.Batch091.valid3666
  · exact MergedCutProfiles.Batch091.valid3667
  · exact MergedCutProfiles.Batch091.valid3668
  · exact MergedCutProfiles.Batch091.valid3669
  · exact MergedCutProfiles.Batch091.valid3670
  · exact MergedCutProfiles.Batch091.valid3671
  · exact MergedCutProfiles.Batch091.valid3672
  · exact MergedCutProfiles.Batch091.valid3673
theorem numericValid548 : retention548.NumericValid := by decide +kernel
def certificate548 : RatCutBinCertificate := ⟨⟨retention548,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(1041946715423812319/500000000000000000)⟩,(994176430235862879/1000000000000000000),(23846254019690519/62500000000000000),(125414355221534819/500000000000000000),(140054493513136597/1000000000000000000)⟩
theorem valid548 : certificate548.Valid := by decide +kernel
theorem sound548 : certificate548.Sound := rat_cut_bin_certificate_sound certificate548 profilesValid548 numericValid548 valid548

def retention549 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(926960011749193181/28272455108468384129),(451535443/500000000),(57/20),(33914015731239400381/16000000000000000000),true,MergedCutProfiles.Batch091.profile3674,![MergedCutProfiles.Batch091.profile3674,MergedCutProfiles.Batch091.profile3675,MergedCutProfiles.Batch091.profile3676,MergedCutProfiles.Batch091.profile3677,MergedCutProfiles.Batch091.profile3678,MergedCutProfiles.Batch091.profile3679,MergedCutProfiles.Batch092.profile3680,MergedCutProfiles.Batch092.profile3681,MergedCutProfiles.Batch092.profile3682,MergedCutProfiles.Batch092.profile3683,MergedCutProfiles.Batch092.profile3684,MergedCutProfiles.Batch092.profile3685,MergedCutProfiles.Batch091.profile3640,MergedCutProfiles.Batch092.profile3686,MergedCutProfiles.Batch092.profile3687,MergedCutProfiles.Batch092.profile3688]⟩
theorem profilesValid549 : retention549.ProfilesValid := by
  change ∀ j : Fin 16, (retention549.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch091.valid3674
  · exact MergedCutProfiles.Batch091.valid3675
  · exact MergedCutProfiles.Batch091.valid3676
  · exact MergedCutProfiles.Batch091.valid3677
  · exact MergedCutProfiles.Batch091.valid3678
  · exact MergedCutProfiles.Batch091.valid3679
  · exact MergedCutProfiles.Batch092.valid3680
  · exact MergedCutProfiles.Batch092.valid3681
  · exact MergedCutProfiles.Batch092.valid3682
  · exact MergedCutProfiles.Batch092.valid3683
  · exact MergedCutProfiles.Batch092.valid3684
  · exact MergedCutProfiles.Batch092.valid3685
  · exact MergedCutProfiles.Batch091.valid3640
  · exact MergedCutProfiles.Batch092.valid3686
  · exact MergedCutProfiles.Batch092.valid3687
  · exact MergedCutProfiles.Batch092.valid3688
theorem numericValid549 : retention549.NumericValid := by decide +kernel
def certificate549 : RatCutBinCertificate := ⟨⟨retention549,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(519540225493598729/250000000000000000)⟩,(994176430235862879/1000000000000000000),(38039313252708027/100000000000000000),(62983867421392291/250000000000000000),(142174095044309713/1000000000000000000)⟩
theorem valid549 : certificate549.Valid := by decide +kernel
theorem sound549 : certificate549.Sound := rat_cut_bin_certificate_sound certificate549 profilesValid549 numericValid549 valid549

def retention550 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(1188763177168716135/28272455108468384129),(926960011749193181/1000000000000000000),(11/4),(532211277603065089977/256000000000000000000),true,MergedCutProfiles.Batch092.profile3689,![MergedCutProfiles.Batch092.profile3689,MergedCutProfiles.Batch092.profile3690,MergedCutProfiles.Batch091.profile3645,MergedCutProfiles.Batch092.profile3691,MergedCutProfiles.Batch092.profile3692,MergedCutProfiles.Batch091.profile3649,MergedCutProfiles.Batch092.profile3693,MergedCutProfiles.Batch092.profile3694,MergedCutProfiles.Batch091.profile3653,MergedCutProfiles.Batch092.profile3695,MergedCutProfiles.Batch092.profile3696,MergedCutProfiles.Batch091.profile3657,MergedCutProfiles.Batch092.profile3697,MergedCutProfiles.Batch092.profile3698,MergedCutProfiles.Batch092.profile3699,MergedCutProfiles.Batch092.profile3700]⟩
theorem profilesValid550 : retention550.ProfilesValid := by
  change ∀ j : Fin 16, (retention550.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch092.valid3689
  · exact MergedCutProfiles.Batch092.valid3690
  · exact MergedCutProfiles.Batch091.valid3645
  · exact MergedCutProfiles.Batch092.valid3691
  · exact MergedCutProfiles.Batch092.valid3692
  · exact MergedCutProfiles.Batch091.valid3649
  · exact MergedCutProfiles.Batch092.valid3693
  · exact MergedCutProfiles.Batch092.valid3694
  · exact MergedCutProfiles.Batch091.valid3653
  · exact MergedCutProfiles.Batch092.valid3695
  · exact MergedCutProfiles.Batch092.valid3696
  · exact MergedCutProfiles.Batch091.valid3657
  · exact MergedCutProfiles.Batch092.valid3697
  · exact MergedCutProfiles.Batch092.valid3698
  · exact MergedCutProfiles.Batch092.valid3699
  · exact MergedCutProfiles.Batch092.valid3700
theorem numericValid550 : retention550.NumericValid := by decide +kernel
def certificate550 : RatCutBinCertificate := ⟨⟨retention550,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(25486751250529909/12500000000000000)⟩,(994176430235862879/1000000000000000000),(383519734369277593/1000000000000000000),(124463240028744557/500000000000000000),(17750195119956769/125000000000000000)⟩
theorem valid550 : certificate550.Valid := by decide +kernel
theorem sound550 : certificate550.Sound := rat_cut_bin_certificate_sound certificate550 profilesValid550 numericValid550 valid550

def retention551 : RatCutRetentionCertificate := ⟨(83/2000),(21/500),(3623174137711729070/28272455108468384129),(237752635433743227/200000000000000000),(9/4),(742571048280413331/409600000000000000),true,MergedCutProfiles.Batch091.profile3661,![MergedCutProfiles.Batch091.profile3661,MergedCutProfiles.Batch090.profile3634,MergedCutProfiles.Batch092.profile3701,MergedCutProfiles.Batch091.profile3673,MergedCutProfiles.Batch092.profile3702,MergedCutProfiles.Batch092.profile3703,MergedCutProfiles.Batch092.profile3704,MergedCutProfiles.Batch092.profile3705,MergedCutProfiles.Batch092.profile3706,MergedCutProfiles.Batch092.profile3707,MergedCutProfiles.Batch092.profile3708,MergedCutProfiles.Batch092.profile3709,MergedCutProfiles.Batch092.profile3710,MergedCutProfiles.Batch092.profile3711,MergedCutProfiles.Batch092.profile3712,MergedCutProfiles.Batch092.profile3713]⟩
theorem profilesValid551 : retention551.ProfilesValid := by
  change ∀ j : Fin 16, (retention551.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch091.valid3661
  · exact MergedCutProfiles.Batch090.valid3634
  · exact MergedCutProfiles.Batch092.valid3701
  · exact MergedCutProfiles.Batch091.valid3673
  · exact MergedCutProfiles.Batch092.valid3702
  · exact MergedCutProfiles.Batch092.valid3703
  · exact MergedCutProfiles.Batch092.valid3704
  · exact MergedCutProfiles.Batch092.valid3705
  · exact MergedCutProfiles.Batch092.valid3706
  · exact MergedCutProfiles.Batch092.valid3707
  · exact MergedCutProfiles.Batch092.valid3708
  · exact MergedCutProfiles.Batch092.valid3709
  · exact MergedCutProfiles.Batch092.valid3710
  · exact MergedCutProfiles.Batch092.valid3711
  · exact MergedCutProfiles.Batch092.valid3712
  · exact MergedCutProfiles.Batch092.valid3713
theorem numericValid551 : retention551.NumericValid := by decide +kernel
def certificate551 : RatCutBinCertificate := ⟨⟨retention551,(1040799417203044549/500000000000000000),(81190354661587239/1000000000000000000),(11617305499632222731/1000000000000000000),(16467182378646085509/50000000000000000),(1780182126245539233/1000000000000000000)⟩,(994176430235862879/1000000000000000000),(399306963873368379/1000000000000000000),(4682359157563649/20000000000000000),(2839601484715387/20000000000000000)⟩
theorem valid551 : certificate551.Valid := by decide +kernel
theorem sound551 : certificate551.Sound := rat_cut_bin_certificate_sound certificate551 profilesValid551 numericValid551 valid551

def certificates : List RatCutBinCertificate := [certificate540,certificate541,certificate542,certificate543,certificate544,certificate545,certificate546,certificate547,certificate548,certificate549,certificate550,certificate551]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound540,List.forall_mem_cons.mpr ⟨sound541,List.forall_mem_cons.mpr ⟨sound542,List.forall_mem_cons.mpr ⟨sound543,List.forall_mem_cons.mpr ⟨sound544,List.forall_mem_cons.mpr ⟨sound545,List.forall_mem_cons.mpr ⟨sound546,List.forall_mem_cons.mpr ⟨sound547,List.forall_mem_cons.mpr ⟨sound548,List.forall_mem_cons.mpr ⟨sound549,List.forall_mem_cons.mpr ⟨sound550,List.forall_mem_cons.mpr ⟨sound551,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch045
