import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch187
import Cycle12.MergedCutProfiles.Batch188
import Cycle12.MergedCutProfiles.Batch189

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch094

def retention1128 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(1424705613379522169/3128544938784732214),(3657321140320232363/1000000000000000000),(6/5),(395958208205488077037008248090555045991/365732114032023236300000000000000000000),false,MergedCutProfiles.Batch187.profile7512,(fun _ => MergedCutProfiles.Batch187.profile7512)⟩
theorem profilesValid1128 : retention1128.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7512
theorem numericValid1128 : retention1128.NumericValid := by decide +kernel
def certificate1128 : RatCutBinCertificate := ⟨⟨retention1128,(2582368555916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(1051093355570307759/1000000000000000000)⟩,(495065514061387401/500000000000000000),(76516555607692997/200000000000000000),(249825509020302023/1000000000000000000),(7217647436408077/40000000000000000)⟩
theorem valid1128 : certificate1128.Valid := by decide +kernel
theorem sound1128 : certificate1128.Sound := rat_cut_bin_certificate_sound certificate1128 profilesValid1128 numericValid1128 valid1128

def retention1129 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(7713760134969912677/15642724693923661070),(1424705613379522169/200000000000000000),(21/20),(455958936351834414386039026153331619671/455905796281447094080000000000000000000),false,MergedCutProfiles.Batch187.profile7513,(fun _ => MergedCutProfiles.Batch187.profile7513)⟩
theorem profilesValid1129 : retention1129.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7513
theorem numericValid1129 : retention1129.NumericValid := by decide +kernel
def certificate1129 : RatCutBinCertificate := ⟨⟨retention1129,(2582368555916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(243127542017186743/250000000000000000)⟩,(495065514061387401/500000000000000000),(413497184045312447/1000000000000000000),(8853626866183503/40000000000000000),(11281650005853707/62500000000000000)⟩
theorem valid1129 : certificate1129.Valid := by decide +kernel
theorem sound1129 : certificate1129.Sound := rat_cut_bin_certificate_sound certificate1129 profilesValid1129 numericValid1129 valid1129

def retention1130 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(354131715287255082/711032940632893685),(7713760134969912677/1000000000000000000),(21/20),(12255957089194438477771227733605973936071/12342016215951860283200000000000000000000),false,MergedCutProfiles.Batch187.profile7514,(fun _ => MergedCutProfiles.Batch187.profile7514)⟩
theorem profilesValid1130 : retention1130.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7514
theorem numericValid1130 : retention1130.NumericValid := by decide +kernel
def certificate1130 : RatCutBinCertificate := ⟨⟨retention1130,(2582368555916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(120677616779418741/125000000000000000)⟩,(495065514061387401/500000000000000000),(26033347326259997/62500000000000000),(218670437515224577/1000000000000000000),(178675142551773129/1000000000000000000)⟩
theorem valid1130 : certificate1130.Valid := by decide +kernel
theorem sound1130 : certificate1130.Sound := rat_cut_bin_certificate_sound certificate1130 profilesValid1130 numericValid1130 valid1130

def retention1131 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(1/2),(1947724434079902951/250000000000000000),(21/20),(770952119933819587259923417245145044479/779089773631961180400000000000000000000),false,MergedCutProfiles.Batch187.profile7511,(fun _ => MergedCutProfiles.Batch187.profile7511)⟩
theorem profilesValid1131 : retention1131.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7511
theorem numericValid1131 : retention1131.NumericValid := by decide +kernel
def certificate1131 : RatCutBinCertificate := ⟨⟨retention1131,(2582368555916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(961948735871404361/1000000000000000000)⟩,(495065514061387401/500000000000000000),(104509263580345863/250000000000000000),(108678219790024977/500000000000000000),(177206784680670759/1000000000000000000)⟩
theorem valid1131 : certificate1131.Valid := by decide +kernel
theorem sound1131 : certificate1131.Sound := rat_cut_bin_certificate_sound certificate1131 profilesValid1131 numericValid1131 valid1131

def retention1132 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(868813452970865859/15477341277444565996),(843261777840520253/1000000000000000000),(57/20),(81356775744004666323/40000000000000000000),true,MergedCutProfiles.Batch187.profile7515,![MergedCutProfiles.Batch187.profile7515,MergedCutProfiles.Batch187.profile7516,MergedCutProfiles.Batch187.profile7517,MergedCutProfiles.Batch187.profile7518,MergedCutProfiles.Batch187.profile7519,MergedCutProfiles.Batch188.profile7520,MergedCutProfiles.Batch188.profile7521,MergedCutProfiles.Batch188.profile7522,MergedCutProfiles.Batch188.profile7523,MergedCutProfiles.Batch188.profile7524,MergedCutProfiles.Batch188.profile7525,MergedCutProfiles.Batch188.profile7526,MergedCutProfiles.Batch188.profile7527,MergedCutProfiles.Batch188.profile7528,MergedCutProfiles.Batch188.profile7529,MergedCutProfiles.Batch188.profile7530]⟩
theorem profilesValid1132 : retention1132.ProfilesValid := by
  change ∀ j : Fin 16, (retention1132.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch187.valid7515
  · exact MergedCutProfiles.Batch187.valid7516
  · exact MergedCutProfiles.Batch187.valid7517
  · exact MergedCutProfiles.Batch187.valid7518
  · exact MergedCutProfiles.Batch187.valid7519
  · exact MergedCutProfiles.Batch188.valid7520
  · exact MergedCutProfiles.Batch188.valid7521
  · exact MergedCutProfiles.Batch188.valid7522
  · exact MergedCutProfiles.Batch188.valid7523
  · exact MergedCutProfiles.Batch188.valid7524
  · exact MergedCutProfiles.Batch188.valid7525
  · exact MergedCutProfiles.Batch188.valid7526
  · exact MergedCutProfiles.Batch188.valid7527
  · exact MergedCutProfiles.Batch188.valid7528
  · exact MergedCutProfiles.Batch188.valid7529
  · exact MergedCutProfiles.Batch188.valid7530
theorem numericValid1132 : retention1132.NumericValid := by decide +kernel
def certificate1132 : RatCutBinCertificate := ⟨⟨retention1132,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(984493495637075183/500000000000000000)⟩,(991466091293777911/1000000000000000000),(364822237954165229/1000000000000000000),(66826813973237769/250000000000000000),(35494628570025811/250000000000000000)⟩
theorem valid1132 : certificate1132.Valid := by decide +kernel
theorem sound1132 : certificate1132.Sound := rat_cut_bin_certificate_sound certificate1132 profilesValid1132 numericValid1132 valid1132

def retention1133 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(524810654399926643/7738670638722282998),(868813452970865859/1000000000000000000),(11/4),(510466918721585488407/256000000000000000000),true,MergedCutProfiles.Batch188.profile7531,![MergedCutProfiles.Batch188.profile7531,MergedCutProfiles.Batch188.profile7532,MergedCutProfiles.Batch188.profile7533,MergedCutProfiles.Batch188.profile7534,MergedCutProfiles.Batch188.profile7535,MergedCutProfiles.Batch188.profile7536,MergedCutProfiles.Batch188.profile7537,MergedCutProfiles.Batch188.profile7538,MergedCutProfiles.Batch188.profile7539,MergedCutProfiles.Batch188.profile7540,MergedCutProfiles.Batch188.profile7541,MergedCutProfiles.Batch188.profile7542,MergedCutProfiles.Batch188.profile7543,MergedCutProfiles.Batch188.profile7544,MergedCutProfiles.Batch188.profile7545,MergedCutProfiles.Batch188.profile7546]⟩
theorem profilesValid1133 : retention1133.ProfilesValid := by
  change ∀ j : Fin 16, (retention1133.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch188.valid7531
  · exact MergedCutProfiles.Batch188.valid7532
  · exact MergedCutProfiles.Batch188.valid7533
  · exact MergedCutProfiles.Batch188.valid7534
  · exact MergedCutProfiles.Batch188.valid7535
  · exact MergedCutProfiles.Batch188.valid7536
  · exact MergedCutProfiles.Batch188.valid7537
  · exact MergedCutProfiles.Batch188.valid7538
  · exact MergedCutProfiles.Batch188.valid7539
  · exact MergedCutProfiles.Batch188.valid7540
  · exact MergedCutProfiles.Batch188.valid7541
  · exact MergedCutProfiles.Batch188.valid7542
  · exact MergedCutProfiles.Batch188.valid7543
  · exact MergedCutProfiles.Batch188.valid7544
  · exact MergedCutProfiles.Batch188.valid7545
  · exact MergedCutProfiles.Batch188.valid7546
theorem numericValid1133 : retention1133.NumericValid := by decide +kernel
def certificate1133 : RatCutBinCertificate := ⟨⟨retention1133,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(965678613740452799/500000000000000000)⟩,(991466091293777911/1000000000000000000),(183718547085745109/500000000000000000),(66170051067825647/250000000000000000),(35548764466825563/250000000000000000)⟩
theorem valid1133 : certificate1133.Valid := by decide +kernel
theorem sound1133 : certificate1133.Sound := rat_cut_bin_certificate_sound certificate1133 profilesValid1133 numericValid1133 valid1133

def retention1134 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(531851252279658121/3869335319361141499),(524810654399926643/500000000000000000),(47/20),(1147266842174259660259/640000000000000000000),true,MergedCutProfiles.Batch188.profile7547,![MergedCutProfiles.Batch188.profile7547,MergedCutProfiles.Batch188.profile7548,MergedCutProfiles.Batch188.profile7549,MergedCutProfiles.Batch188.profile7550,MergedCutProfiles.Batch188.profile7551,MergedCutProfiles.Batch188.profile7552,MergedCutProfiles.Batch188.profile7553,MergedCutProfiles.Batch188.profile7554,MergedCutProfiles.Batch188.profile7555,MergedCutProfiles.Batch188.profile7556,MergedCutProfiles.Batch188.profile7557,MergedCutProfiles.Batch188.profile7558,MergedCutProfiles.Batch188.profile7559,MergedCutProfiles.Batch189.profile7560,MergedCutProfiles.Batch189.profile7561,MergedCutProfiles.Batch189.profile7562]⟩
theorem profilesValid1134 : retention1134.ProfilesValid := by
  change ∀ j : Fin 16, (retention1134.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch188.valid7547
  · exact MergedCutProfiles.Batch188.valid7548
  · exact MergedCutProfiles.Batch188.valid7549
  · exact MergedCutProfiles.Batch188.valid7550
  · exact MergedCutProfiles.Batch188.valid7551
  · exact MergedCutProfiles.Batch188.valid7552
  · exact MergedCutProfiles.Batch188.valid7553
  · exact MergedCutProfiles.Batch188.valid7554
  · exact MergedCutProfiles.Batch188.valid7555
  · exact MergedCutProfiles.Batch188.valid7556
  · exact MergedCutProfiles.Batch188.valid7557
  · exact MergedCutProfiles.Batch188.valid7558
  · exact MergedCutProfiles.Batch188.valid7559
  · exact MergedCutProfiles.Batch189.valid7560
  · exact MergedCutProfiles.Batch189.valid7561
  · exact MergedCutProfiles.Batch189.valid7562
theorem numericValid1134 : retention1134.NumericValid := by decide +kernel
def certificate1134 : RatCutBinCertificate := ⟨⟨retention1134,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(1739064065921697861/1000000000000000000)⟩,(991466091293777911/1000000000000000000),(379697592279009651/1000000000000000000),(126304165194831189/500000000000000000),(142338418368286897/1000000000000000000)⟩
theorem valid1134 : certificate1134.Valid := by decide +kernel
theorem sound1134 : certificate1134.Sound := rat_cut_bin_certificate_sound certificate1134 profilesValid1134 numericValid1134 valid1134

def retention1135 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1341769599830892896/3869335319361141499),(531851252279658121/250000000000000000),(7/5),(414426168296215065877/320000000000000000000),true,MergedCutProfiles.Batch189.profile7563,![MergedCutProfiles.Batch189.profile7563,MergedCutProfiles.Batch189.profile7564,MergedCutProfiles.Batch189.profile7565,MergedCutProfiles.Batch189.profile7566,MergedCutProfiles.Batch189.profile7567,MergedCutProfiles.Batch189.profile7568,MergedCutProfiles.Batch189.profile7569,MergedCutProfiles.Batch189.profile7570,MergedCutProfiles.Batch189.profile7571,MergedCutProfiles.Batch189.profile7572,MergedCutProfiles.Batch189.profile7573,MergedCutProfiles.Batch189.profile7574,MergedCutProfiles.Batch189.profile7575,MergedCutProfiles.Batch189.profile7576,MergedCutProfiles.Batch189.profile7577,MergedCutProfiles.Batch189.profile7578]⟩
theorem profilesValid1135 : retention1135.ProfilesValid := by
  change ∀ j : Fin 16, (retention1135.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch189.valid7563
  · exact MergedCutProfiles.Batch189.valid7564
  · exact MergedCutProfiles.Batch189.valid7565
  · exact MergedCutProfiles.Batch189.valid7566
  · exact MergedCutProfiles.Batch189.valid7567
  · exact MergedCutProfiles.Batch189.valid7568
  · exact MergedCutProfiles.Batch189.valid7569
  · exact MergedCutProfiles.Batch189.valid7570
  · exact MergedCutProfiles.Batch189.valid7571
  · exact MergedCutProfiles.Batch189.valid7572
  · exact MergedCutProfiles.Batch189.valid7573
  · exact MergedCutProfiles.Batch189.valid7574
  · exact MergedCutProfiles.Batch189.valid7575
  · exact MergedCutProfiles.Batch189.valid7576
  · exact MergedCutProfiles.Batch189.valid7577
  · exact MergedCutProfiles.Batch189.valid7578
theorem numericValid1135 : retention1135.NumericValid := by decide +kernel
def certificate1135 : RatCutBinCertificate := ⟨⟨retention1135,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(631593425181016767/500000000000000000)⟩,(991466091293777911/1000000000000000000),(427664732723409007/1000000000000000000),(209069546694509321/1000000000000000000),(35837914454934291/250000000000000000)⟩
theorem valid1135 : certificate1135.Valid := by decide +kernel
theorem sound1135 : certificate1135.Sound := rat_cut_bin_certificate_sound certificate1135 profilesValid1135 numericValid1135 valid1135

def retention1136 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(7234010799034943435/15477341277444565996),(41930299994715403/7812500000000000),1,(8162929249439685007/8000000000000000000),true,MergedCutProfiles.Batch189.profile7579,![MergedCutProfiles.Batch189.profile7579,MergedCutProfiles.Batch189.profile7580,MergedCutProfiles.Batch189.profile7581,MergedCutProfiles.Batch189.profile7582,MergedCutProfiles.Batch189.profile7583,MergedCutProfiles.Batch189.profile7584,MergedCutProfiles.Batch189.profile7585,MergedCutProfiles.Batch189.profile7586,MergedCutProfiles.Batch189.profile7587,MergedCutProfiles.Batch189.profile7588,MergedCutProfiles.Batch189.profile7589,MergedCutProfiles.Batch189.profile7590,MergedCutProfiles.Batch189.profile7591,MergedCutProfiles.Batch189.profile7592,MergedCutProfiles.Batch189.profile7593,MergedCutProfiles.Batch189.profile7594]⟩
theorem profilesValid1136 : retention1136.ProfilesValid := by
  change ∀ j : Fin 16, (retention1136.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch189.valid7579
  · exact MergedCutProfiles.Batch189.valid7580
  · exact MergedCutProfiles.Batch189.valid7581
  · exact MergedCutProfiles.Batch189.valid7582
  · exact MergedCutProfiles.Batch189.valid7583
  · exact MergedCutProfiles.Batch189.valid7584
  · exact MergedCutProfiles.Batch189.valid7585
  · exact MergedCutProfiles.Batch189.valid7586
  · exact MergedCutProfiles.Batch189.valid7587
  · exact MergedCutProfiles.Batch189.valid7588
  · exact MergedCutProfiles.Batch189.valid7589
  · exact MergedCutProfiles.Batch189.valid7590
  · exact MergedCutProfiles.Batch189.valid7591
  · exact MergedCutProfiles.Batch189.valid7592
  · exact MergedCutProfiles.Batch189.valid7593
  · exact MergedCutProfiles.Batch189.valid7594
theorem numericValid1136 : retention1136.NumericValid := by decide +kernel
def certificate1136 : RatCutBinCertificate := ⟨⟨retention1136,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(498793157959605171/500000000000000000)⟩,(991466091293777911/1000000000000000000),(235378746172155093/500000000000000000),(174567931772139117/1000000000000000000),(29095880987751551/200000000000000000)⟩
theorem valid1136 : certificate1136.Valid := by decide +kernel
theorem sound1136 : certificate1136.Sound := rat_cut_bin_certificate_sound certificate1136 profilesValid1136 numericValid1136 valid1136

def retention1137 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(7679048232840833503/15477341277444565996),(1446802159806988687/200000000000000000),(21/20),(460570708592288833946148389903603357399/462976691138236379840000000000000000000),false,MergedCutProfiles.Batch189.profile7595,(fun _ => MergedCutProfiles.Batch189.profile7595)⟩
theorem profilesValid1137 : retention1137.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7595
theorem numericValid1137 : retention1137.NumericValid := by decide +kernel
def certificate1137 : RatCutBinCertificate := ⟨⟨retention1137,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(970885263590051757/1000000000000000000)⟩,(991466091293777911/1000000000000000000),(94276150696100697/200000000000000000),(17409877455383499/100000000000000000),(142199558903846719/1000000000000000000)⟩
theorem valid1137 : certificate1137.Valid := by decide +kernel
theorem sound1137 : certificate1137.Sound := rat_cut_bin_certificate_sound certificate1137 profilesValid1137 numericValid1137 valid1137

def retention1138 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1/2),(7679048232840833503/1000000000000000000),(21/20),(12153257728538209276791505918804351034231/12286477172545333604800000000000000000000),false,MergedCutProfiles.Batch189.profile7596,(fun _ => MergedCutProfiles.Batch189.profile7596)⟩
theorem profilesValid1138 : retention1138.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7596
theorem numericValid1138 : retention1138.NumericValid := by decide +kernel
def certificate1138 : RatCutBinCertificate := ⟨⟨retention1138,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(482619691278202629/500000000000000000)⟩,(991466091293777911/1000000000000000000),(472072756483812753/1000000000000000000),(86789418746926221/500000000000000000),(35482973781249711/250000000000000000)⟩
theorem valid1138 : certificate1138.Valid := by decide +kernel
theorem sound1138 : certificate1138.Sound := rat_cut_bin_certificate_sound certificate1138 profilesValid1138 numericValid1138 valid1138

def retention1139 : RatCutRetentionCertificate := ⟨(109/2000),(219/4000),(1/2),64,1,(255400315015348816056059995758943668471/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch189.profile7596,(fun _ => MergedCutProfiles.Batch189.profile7596)⟩
theorem profilesValid1139 : retention1139.ProfilesValid := by
  exact MergedCutProfiles.Batch189.valid7596
theorem numericValid1139 : retention1139.NumericValid := by decide +kernel
def certificate1139 : RatCutBinCertificate := ⟨⟨retention1139,(2223477582207165147/1000000000000000000),(73656633113325057/500000000000000000),(287612269959572801/20000000000000000),(222902312226657076333/1000000000000000000),(194976041952981597/200000000000000000)⟩,(991466091293777911/1000000000000000000),(438154828209835789/1000000000000000000),(200286872245386607/1000000000000000000),(190669588985237801/1000000000000000000)⟩
theorem valid1139 : certificate1139.Valid := by decide +kernel
theorem sound1139 : certificate1139.Sound := rat_cut_bin_certificate_sound certificate1139 profilesValid1139 numericValid1139 valid1139

def certificates : List RatCutBinCertificate := [certificate1128,certificate1129,certificate1130,certificate1131,certificate1132,certificate1133,certificate1134,certificate1135,certificate1136,certificate1137,certificate1138,certificate1139]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1128,List.forall_mem_cons.mpr ⟨sound1129,List.forall_mem_cons.mpr ⟨sound1130,List.forall_mem_cons.mpr ⟨sound1131,List.forall_mem_cons.mpr ⟨sound1132,List.forall_mem_cons.mpr ⟨sound1133,List.forall_mem_cons.mpr ⟨sound1134,List.forall_mem_cons.mpr ⟨sound1135,List.forall_mem_cons.mpr ⟨sound1136,List.forall_mem_cons.mpr ⟨sound1137,List.forall_mem_cons.mpr ⟨sound1138,List.forall_mem_cons.mpr ⟨sound1139,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch094
