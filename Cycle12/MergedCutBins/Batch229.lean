import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch304
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch436
import Cycle12.MergedCutProfiles.Batch437
import Cycle12.MergedCutProfiles.Batch438

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch229

def retention2748 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(8736662459596826432/19168601425222358897),(4714334374534769691/1000000000000000000),(21/20),(881775224752210722865007986019915471831/838103888806181278400000000000000000000),false,MergedCutProfiles.Batch436.profile17479,(fun _ => MergedCutProfiles.Batch436.profile17479)⟩
theorem profilesValid2748 : retention2748.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17479
theorem numericValid2748 : retention2748.NumericValid := by decide +kernel
def certificate2748 : RatCutBinCertificate := ⟨⟨retention2748,(2602807746935513181/1000000000000000000),(11895173549139047/50000000000000000),(1793794853076942851/100000000000000000),(86237204490772403387/250000000000000000),(1015856313844620741/1000000000000000000)⟩,(497103254615790661/500000000000000000),(225524528265535829/1000000000000000000),(438438289154719633/1000000000000000000),(352559562161547861/1000000000000000000)⟩
theorem valid2748 : certificate2748.Valid := by decide +kernel
theorem sound2748 : certificate2748.Sound := rat_cut_bin_certificate_sound certificate2748 profilesValid2748 numericValid2748 valid2748

def retention2749 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(9460553529183538933/19168601425222358897),(136510350931200413/15625000000000000),1,(1721364952582266431585711182736545731/1747332491919365286400000000000000000),false,MergedCutProfiles.Batch437.profile17480,(fun _ => MergedCutProfiles.Batch437.profile17480)⟩
theorem profilesValid2749 : retention2749.ProfilesValid := by
  exact MergedCutProfiles.Batch437.valid17480
theorem numericValid2749 : retention2749.NumericValid := by decide +kernel
def certificate2749 : RatCutBinCertificate := ⟨⟨retention2749,(2602807746935513181/1000000000000000000),(11895173549139047/50000000000000000),(1793794853076942851/100000000000000000),(86237204490772403387/250000000000000000),(475308041589372089/500000000000000000)⟩,(497103254615790661/500000000000000000),(48200429178368209/200000000000000000),(1299866495564327/3125000000000000),(354415450056488773/1000000000000000000)⟩
theorem valid2749 : certificate2749.Valid := by decide +kernel
theorem sound2749 : certificate2749.Sound := rat_cut_bin_certificate_sound certificate2749 profilesValid2749 numericValid2749 valid2749

def retention2750 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(9555159064475374323/19168601425222358897),(9460553529183538933/1000000000000000000),1,(231315625607831755655459552380762531/236513838229588473325000000000000000),false,MergedCutProfiles.Batch437.profile17481,(fun _ => MergedCutProfiles.Batch437.profile17481)⟩
theorem profilesValid2750 : retention2750.ProfilesValid := by
  exact MergedCutProfiles.Batch437.valid17481
theorem numericValid2750 : retention2750.NumericValid := by decide +kernel
def certificate2750 : RatCutBinCertificate := ⟨⟨retention2750,(2602807746935513181/1000000000000000000),(11895173549139047/50000000000000000),(1793794853076942851/100000000000000000),(86237204490772403387/250000000000000000),(943499067082237091/1000000000000000000)⟩,(497103254615790661/500000000000000000),(242820076837877137/1000000000000000000),(413382099728678769/1000000000000000000),(88119755067235587/250000000000000000)⟩
theorem valid2750 : certificate2750.Valid := by decide +kernel
theorem sound2750 : certificate2750.Sound := rat_cut_bin_certificate_sound certificate2750 profilesValid2750 numericValid2750 valid2750

def retention2751 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1/2),(9555159064475374323/1000000000000000000),1,(37280380169857222318716579924482105291/38220636257901497292000000000000000000),false,MergedCutProfiles.Batch436.profile17478,(fun _ => MergedCutProfiles.Batch436.profile17478)⟩
theorem profilesValid2751 : retention2751.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17478
theorem numericValid2751 : retention2751.NumericValid := by decide +kernel
def certificate2751 : RatCutBinCertificate := ⟨⟨retention2751,(2602807746935513181/1000000000000000000),(11895173549139047/50000000000000000),(1793794853076942851/100000000000000000),(86237204490772403387/250000000000000000),(188175363873604637/200000000000000000)⟩,(497103254615790661/500000000000000000),(15218551411919851/62500000000000000),(412426887459984153/1000000000000000000),(87772769800829659/250000000000000000)⟩
theorem valid2751 : certificate2751.Valid := by decide +kernel
theorem sound2751 : certificate2751.Sound := rat_cut_bin_certificate_sound certificate2751 profilesValid2751 numericValid2751 valid2751

def retention2752 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(496408796482798920/9412525033197477019),(973255164165863973/1000000000000000000),(5/2),(32676963690628066107/16000000000000000000),true,MergedCutProfiles.Batch437.profile17482,![MergedCutProfiles.Batch437.profile17482,MergedCutProfiles.Batch437.profile17483,MergedCutProfiles.Batch437.profile17484,MergedCutProfiles.Batch437.profile17485,MergedCutProfiles.Batch437.profile17486,MergedCutProfiles.Batch437.profile17487,MergedCutProfiles.Batch437.profile17488,MergedCutProfiles.Batch437.profile17489,MergedCutProfiles.Batch437.profile17490,MergedCutProfiles.Batch437.profile17491,MergedCutProfiles.Batch437.profile17492,MergedCutProfiles.Batch437.profile17493,MergedCutProfiles.Batch437.profile17494,MergedCutProfiles.Batch437.profile17495,MergedCutProfiles.Batch437.profile17496,MergedCutProfiles.Batch437.profile17497]⟩
theorem profilesValid2752 : retention2752.ProfilesValid := by
  change ∀ j : Fin 16, (retention2752.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch437.valid17482
  · exact MergedCutProfiles.Batch437.valid17483
  · exact MergedCutProfiles.Batch437.valid17484
  · exact MergedCutProfiles.Batch437.valid17485
  · exact MergedCutProfiles.Batch437.valid17486
  · exact MergedCutProfiles.Batch437.valid17487
  · exact MergedCutProfiles.Batch437.valid17488
  · exact MergedCutProfiles.Batch437.valid17489
  · exact MergedCutProfiles.Batch437.valid17490
  · exact MergedCutProfiles.Batch437.valid17491
  · exact MergedCutProfiles.Batch437.valid17492
  · exact MergedCutProfiles.Batch437.valid17493
  · exact MergedCutProfiles.Batch437.valid17494
  · exact MergedCutProfiles.Batch437.valid17495
  · exact MergedCutProfiles.Batch437.valid17496
  · exact MergedCutProfiles.Batch437.valid17497
theorem numericValid2752 : retention2752.NumericValid := by decide +kernel
def certificate2752 : RatCutBinCertificate := ⟨⟨retention2752,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(1963204482572188831/1000000000000000000)⟩,(994722529154146931/1000000000000000000),(52367680919812629/200000000000000000),(96807052468730681/250000000000000000),(114208041457015671/500000000000000000)⟩
theorem valid2752 : certificate2752.Valid := by decide +kernel
theorem sound2752 : certificate2752.Sound := rat_cut_bin_certificate_sound certificate2752 profilesValid2752 numericValid2752 valid2752

def retention2753 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(576315201889113270/9412525033197477019),(12410219912069973/12500000000000000),(49/20),(1612202448181604997/800000000000000000),true,MergedCutProfiles.Batch437.profile17498,![MergedCutProfiles.Batch437.profile17498,MergedCutProfiles.Batch437.profile17499,MergedCutProfiles.Batch437.profile17500,MergedCutProfiles.Batch437.profile17501,MergedCutProfiles.Batch437.profile17502,MergedCutProfiles.Batch437.profile17503,MergedCutProfiles.Batch304.profile12194,MergedCutProfiles.Batch437.profile17504,MergedCutProfiles.Batch304.profile12165,MergedCutProfiles.Batch437.profile17505,MergedCutProfiles.Batch437.profile17506,MergedCutProfiles.Batch437.profile17507,MergedCutProfiles.Batch437.profile17508,MergedCutProfiles.Batch304.profile12195,MergedCutProfiles.Batch437.profile17509,MergedCutProfiles.Batch437.profile17510]⟩
theorem profilesValid2753 : retention2753.ProfilesValid := by
  change ∀ j : Fin 16, (retention2753.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch437.valid17498
  · exact MergedCutProfiles.Batch437.valid17499
  · exact MergedCutProfiles.Batch437.valid17500
  · exact MergedCutProfiles.Batch437.valid17501
  · exact MergedCutProfiles.Batch437.valid17502
  · exact MergedCutProfiles.Batch437.valid17503
  · exact MergedCutProfiles.Batch304.valid12194
  · exact MergedCutProfiles.Batch437.valid17504
  · exact MergedCutProfiles.Batch304.valid12165
  · exact MergedCutProfiles.Batch437.valid17505
  · exact MergedCutProfiles.Batch437.valid17506
  · exact MergedCutProfiles.Batch437.valid17507
  · exact MergedCutProfiles.Batch437.valid17508
  · exact MergedCutProfiles.Batch304.valid12195
  · exact MergedCutProfiles.Batch437.valid17509
  · exact MergedCutProfiles.Batch437.valid17510
theorem numericValid2753 : retention2753.NumericValid := by decide +kernel
def certificate2753 : RatCutBinCertificate := ⟨⟨retention2753,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(484432355070458709/250000000000000000)⟩,(994722529154146931/1000000000000000000),(263351518137441461/1000000000000000000),(19260367906972173/50000000000000000),(114218262373388221/500000000000000000)⟩
theorem valid2753 : certificate2753.Valid := by decide +kernel
theorem sound2753 : certificate2753.Sound := rat_cut_bin_certificate_sound certificate2753 profilesValid2753 numericValid2753 valid2753

def retention2754 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(2290154922377153615/18825050066394954038),(57631520188911327/50000000000000000),(43/20),(5892004248902803177/3200000000000000000),true,MergedCutProfiles.Batch437.profile17511,![MergedCutProfiles.Batch437.profile17511,MergedCutProfiles.Batch437.profile17512,MergedCutProfiles.Batch437.profile17513,MergedCutProfiles.Batch437.profile17514,MergedCutProfiles.Batch437.profile17515,MergedCutProfiles.Batch437.profile17516,MergedCutProfiles.Batch437.profile17517,MergedCutProfiles.Batch437.profile17518,MergedCutProfiles.Batch437.profile17519,MergedCutProfiles.Batch438.profile17520,MergedCutProfiles.Batch438.profile17521,MergedCutProfiles.Batch438.profile17522,MergedCutProfiles.Batch438.profile17523,MergedCutProfiles.Batch438.profile17524,MergedCutProfiles.Batch438.profile17525,MergedCutProfiles.Batch438.profile17526]⟩
theorem profilesValid2754 : retention2754.ProfilesValid := by
  change ∀ j : Fin 16, (retention2754.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch437.valid17511
  · exact MergedCutProfiles.Batch437.valid17512
  · exact MergedCutProfiles.Batch437.valid17513
  · exact MergedCutProfiles.Batch437.valid17514
  · exact MergedCutProfiles.Batch437.valid17515
  · exact MergedCutProfiles.Batch437.valid17516
  · exact MergedCutProfiles.Batch437.valid17517
  · exact MergedCutProfiles.Batch437.valid17518
  · exact MergedCutProfiles.Batch437.valid17519
  · exact MergedCutProfiles.Batch438.valid17520
  · exact MergedCutProfiles.Batch438.valid17521
  · exact MergedCutProfiles.Batch438.valid17522
  · exact MergedCutProfiles.Batch438.valid17523
  · exact MergedCutProfiles.Batch438.valid17524
  · exact MergedCutProfiles.Batch438.valid17525
  · exact MergedCutProfiles.Batch438.valid17526
theorem numericValid2754 : retention2754.NumericValid := by decide +kernel
def certificate2754 : RatCutBinCertificate := ⟨⟨retention2754,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(221652593005923787/125000000000000000)⟩,(994722529154146931/1000000000000000000),(54648215365859903/200000000000000000),(74441820079461861/200000000000000000),(28607238039579257/125000000000000000)⟩
theorem valid2754 : certificate2754.Valid := by decide +kernel
theorem sound2754 : certificate2754.Sound := rat_cut_bin_certificate_sound certificate2754 profilesValid2754 numericValid2754 valid2754

def retention2755 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(3159475501972666643/9412525033197477019),(458030984475430723/200000000000000000),(27/20),(337195612430877321459/256000000000000000000),true,MergedCutProfiles.Batch438.profile17527,![MergedCutProfiles.Batch438.profile17527,MergedCutProfiles.Batch438.profile17528,MergedCutProfiles.Batch438.profile17529,MergedCutProfiles.Batch304.profile12182,MergedCutProfiles.Batch438.profile17530,MergedCutProfiles.Batch438.profile17531,MergedCutProfiles.Batch438.profile17532,MergedCutProfiles.Batch438.profile17533,MergedCutProfiles.Batch438.profile17534,MergedCutProfiles.Batch438.profile17535,MergedCutProfiles.Batch438.profile17536,MergedCutProfiles.Batch304.profile12192,MergedCutProfiles.Batch438.profile17537,MergedCutProfiles.Batch438.profile17538,MergedCutProfiles.Batch438.profile17539,MergedCutProfiles.Batch438.profile17540]⟩
theorem profilesValid2755 : retention2755.ProfilesValid := by
  change ∀ j : Fin 16, (retention2755.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch438.valid17527
  · exact MergedCutProfiles.Batch438.valid17528
  · exact MergedCutProfiles.Batch438.valid17529
  · exact MergedCutProfiles.Batch304.valid12182
  · exact MergedCutProfiles.Batch438.valid17530
  · exact MergedCutProfiles.Batch438.valid17531
  · exact MergedCutProfiles.Batch438.valid17532
  · exact MergedCutProfiles.Batch438.valid17533
  · exact MergedCutProfiles.Batch438.valid17534
  · exact MergedCutProfiles.Batch438.valid17535
  · exact MergedCutProfiles.Batch438.valid17536
  · exact MergedCutProfiles.Batch304.valid12192
  · exact MergedCutProfiles.Batch438.valid17537
  · exact MergedCutProfiles.Batch438.valid17538
  · exact MergedCutProfiles.Batch438.valid17539
  · exact MergedCutProfiles.Batch438.valid17540
theorem numericValid2755 : retention2755.NumericValid := by decide +kernel
def certificate2755 : RatCutBinCertificate := ⟨⟨retention2755,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(159306988119450389/125000000000000000)⟩,(994722529154146931/1000000000000000000),(63547910329113041/200000000000000000),(79487603980399433/250000000000000000),(228525378667304013/1000000000000000000)⟩
theorem valid2755 : certificate2755.Valid := by decide +kernel
theorem sound2755 : certificate2755.Sound := rat_cut_bin_certificate_sound certificate2755 profilesValid2755 numericValid2755 valid2755

def retention2756 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(8862815254866837513/18825050066394954038),(3159475501972666643/500000000000000000),1,(130285950954528141323/128000000000000000000),true,MergedCutProfiles.Batch438.profile17541,![MergedCutProfiles.Batch438.profile17541,MergedCutProfiles.Batch438.profile17542,MergedCutProfiles.Batch438.profile17543,MergedCutProfiles.Batch438.profile17544,MergedCutProfiles.Batch438.profile17545,MergedCutProfiles.Batch438.profile17546,MergedCutProfiles.Batch438.profile17547,MergedCutProfiles.Batch438.profile17548,MergedCutProfiles.Batch438.profile17549,MergedCutProfiles.Batch438.profile17550,MergedCutProfiles.Batch438.profile17551,MergedCutProfiles.Batch438.profile17552,MergedCutProfiles.Batch438.profile17553,MergedCutProfiles.Batch438.profile17554,MergedCutProfiles.Batch438.profile17555,MergedCutProfiles.Batch438.profile17556]⟩
theorem profilesValid2756 : retention2756.ProfilesValid := by
  change ∀ j : Fin 16, (retention2756.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch438.valid17541
  · exact MergedCutProfiles.Batch438.valid17542
  · exact MergedCutProfiles.Batch438.valid17543
  · exact MergedCutProfiles.Batch438.valid17544
  · exact MergedCutProfiles.Batch438.valid17545
  · exact MergedCutProfiles.Batch438.valid17546
  · exact MergedCutProfiles.Batch438.valid17547
  · exact MergedCutProfiles.Batch438.valid17548
  · exact MergedCutProfiles.Batch438.valid17549
  · exact MergedCutProfiles.Batch438.valid17550
  · exact MergedCutProfiles.Batch438.valid17551
  · exact MergedCutProfiles.Batch438.valid17552
  · exact MergedCutProfiles.Batch438.valid17553
  · exact MergedCutProfiles.Batch438.valid17554
  · exact MergedCutProfiles.Batch438.valid17555
  · exact MergedCutProfiles.Batch438.valid17556
theorem numericValid2756 : retention2756.NumericValid := by decide +kernel
def certificate2756 : RatCutBinCertificate := ⟨⟨retention2756,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(308194485914391/312500000000000)⟩,(994722529154146931/1000000000000000000),(358477501001461657/1000000000000000000),(68439918245821823/250000000000000000),(232190247757247003/1000000000000000000)⟩
theorem valid2756 : certificate2756.Valid := by decide +kernel
theorem sound2756 : certificate2756.Sound := rat_cut_bin_certificate_sound certificate2756 profilesValid2756 numericValid2756 valid2756

def retention2757 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4657453952522319583/9412525033197477019),(8862815254866837513/1000000000000000000),(21/20),(14221910058998798326195346154242458822391/14180504407786940020800000000000000000000),false,MergedCutProfiles.Batch438.profile17557,(fun _ => MergedCutProfiles.Batch438.profile17557)⟩
theorem profilesValid2757 : retention2757.ProfilesValid := by
  exact MergedCutProfiles.Batch438.valid17557
theorem numericValid2757 : retention2757.NumericValid := by decide +kernel
def certificate2757 : RatCutBinCertificate := ⟨⟨retention2757,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(484851312964534217/500000000000000000)⟩,(994722529154146931/1000000000000000000),(355934968279233941/1000000000000000000),(138188361996194529/500000000000000000),(4617801102447021/20000000000000000)⟩
theorem valid2757 : certificate2757.Valid := by decide +kernel
theorem sound2757 : certificate2757.Sound := rat_cut_bin_certificate_sound certificate2757 profilesValid2757 numericValid2757 valid2757

def retention2758 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4704028492047542779/9412525033197477019),(4657453952522319583/500000000000000000),(21/20),(3705123336256089891682144034412512145911/3725963162017855666400000000000000000000),false,MergedCutProfiles.Batch438.profile17558,(fun _ => MergedCutProfiles.Batch438.profile17558)⟩
theorem profilesValid2758 : retention2758.ProfilesValid := by
  exact MergedCutProfiles.Batch438.valid17558
theorem numericValid2758 : retention2758.NumericValid := by decide +kernel
def certificate2758 : RatCutBinCertificate := ⟨⟨retention2758,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(961189710975251743/1000000000000000000)⟩,(994722529154146931/1000000000000000000),(358035345122712759/1000000000000000000),(274213490635442433/1000000000000000000),(228247525554859757/1000000000000000000)⟩
theorem valid2758 : certificate2758.Valid := by decide +kernel
theorem sound2758 : certificate2758.Sound := rat_cut_bin_certificate_sound certificate2758 profilesValid2758 numericValid2758 valid2758

def retention2759 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(4704028492047542779/500000000000000000),(21/20),(3741220897599311042844433048053430512039/3763222793638034223200000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid2759 : retention2759.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid2759 : retention2759.NumericValid := by decide +kernel
def certificate2759 : RatCutBinCertificate := ⟨⟨retention2759,(2364970645655384873/1000000000000000000),(121143195939341811/500000000000000000),(4528487254489889107/250000000000000000),(171047067277992696389/500000000000000000),(960936315825471633/1000000000000000000)⟩,(994722529154146931/1000000000000000000),(357925509440071281/1000000000000000000),(274326307744907933/1000000000000000000),(228480649899760363/1000000000000000000)⟩
theorem valid2759 : certificate2759.Valid := by decide +kernel
theorem sound2759 : certificate2759.Sound := rat_cut_bin_certificate_sound certificate2759 profilesValid2759 numericValid2759 valid2759

def certificates : List RatCutBinCertificate := [certificate2748,certificate2749,certificate2750,certificate2751,certificate2752,certificate2753,certificate2754,certificate2755,certificate2756,certificate2757,certificate2758,certificate2759]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2748,List.forall_mem_cons.mpr ⟨sound2749,List.forall_mem_cons.mpr ⟨sound2750,List.forall_mem_cons.mpr ⟨sound2751,List.forall_mem_cons.mpr ⟨sound2752,List.forall_mem_cons.mpr ⟨sound2753,List.forall_mem_cons.mpr ⟨sound2754,List.forall_mem_cons.mpr ⟨sound2755,List.forall_mem_cons.mpr ⟨sound2756,List.forall_mem_cons.mpr ⟨sound2757,List.forall_mem_cons.mpr ⟨sound2758,List.forall_mem_cons.mpr ⟨sound2759,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch229
