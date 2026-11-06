import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch685
import Cycle12.MergedCutProfiles.Batch686
import Cycle12.MergedCutProfiles.Batch687

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch407

def retention4884 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1/40),(11463579346599132937/200000000000000000),(21/20),(2207453869476447549/1000000000000000000),false,MergedCutProfiles.Batch685.profile27435,(fun _ => MergedCutProfiles.Batch685.profile27435)⟩
theorem profilesValid4884 : retention4884.ProfilesValid := by
  exact MergedCutProfiles.Batch685.valid27435
theorem numericValid4884 : retention4884.NumericValid := by decide +kernel
def certificate4884 : RatCutBinCertificate := ⟨⟨retention4884,(926794816391658239/500000000000000000),(23060041821265367/250000000000000000),(12083399313703635401/1000000000000000000),(30100436419524438813219/1000000000000000000),(2192596775609374973/1000000000000000000)⟩,(62496497457666677/62500000000000000),(8776481783704133/12500000000000000),(24787555392049727/500000000000000000),(50022507149955103/500000000000000000)⟩
theorem valid4884 : certificate4884.Valid := by decide +kernel
theorem sound4884 : certificate4884.Sound := rat_cut_bin_certificate_sound certificate4884 profilesValid4884 numericValid4884 valid4884

def retention4885 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(608242939700856749/2422573656693449252979),(9224290700315623/15625000000000000),4,(4517339557094596493/2000000000000000000),true,MergedCutProfiles.Batch685.profile27436,![MergedCutProfiles.Batch685.profile27436,MergedCutProfiles.Batch685.profile27437,MergedCutProfiles.Batch685.profile27438,MergedCutProfiles.Batch685.profile27439,MergedCutProfiles.Batch686.profile27440,MergedCutProfiles.Batch686.profile27441,MergedCutProfiles.Batch686.profile27442,MergedCutProfiles.Batch686.profile27443,MergedCutProfiles.Batch686.profile27444,MergedCutProfiles.Batch686.profile27445,MergedCutProfiles.Batch686.profile27446,MergedCutProfiles.Batch686.profile27447,MergedCutProfiles.Batch686.profile27448,MergedCutProfiles.Batch686.profile27449,MergedCutProfiles.Batch686.profile27450,MergedCutProfiles.Batch686.profile27451]⟩
theorem profilesValid4885 : retention4885.ProfilesValid := by
  change ∀ j : Fin 16, (retention4885.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch685.valid27436
  · exact MergedCutProfiles.Batch685.valid27437
  · exact MergedCutProfiles.Batch685.valid27438
  · exact MergedCutProfiles.Batch685.valid27439
  · exact MergedCutProfiles.Batch686.valid27440
  · exact MergedCutProfiles.Batch686.valid27441
  · exact MergedCutProfiles.Batch686.valid27442
  · exact MergedCutProfiles.Batch686.valid27443
  · exact MergedCutProfiles.Batch686.valid27444
  · exact MergedCutProfiles.Batch686.valid27445
  · exact MergedCutProfiles.Batch686.valid27446
  · exact MergedCutProfiles.Batch686.valid27447
  · exact MergedCutProfiles.Batch686.valid27448
  · exact MergedCutProfiles.Batch686.valid27449
  · exact MergedCutProfiles.Batch686.valid27450
  · exact MergedCutProfiles.Batch686.valid27451
theorem numericValid4885 : retention4885.NumericValid := by decide +kernel
def certificate4885 : RatCutBinCertificate := ⟨⟨retention4885,(475743403786706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(439915287244828891/200000000000000000)⟩,(999941616952369829/1000000000000000000),(702584069494468773/1000000000000000000),(9882126023856631/200000000000000000),(11018505839848397/500000000000000000)⟩
theorem valid4885 : certificate4885.Valid := by decide +kernel
theorem sound4885 : certificate4885.Sound := rat_cut_bin_certificate_sound certificate4885 profilesValid4885 numericValid4885 valid4885

def retention4886 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1120974698000000000/2422573656693449252979),(608242939700856749/1000000000000000000),4,(9157162704299083679/4000000000000000000),true,MergedCutProfiles.Batch685.profile27437,![MergedCutProfiles.Batch685.profile27437,MergedCutProfiles.Batch686.profile27452,MergedCutProfiles.Batch686.profile27441,MergedCutProfiles.Batch686.profile27443,MergedCutProfiles.Batch686.profile27444,MergedCutProfiles.Batch686.profile27446,MergedCutProfiles.Batch686.profile27448,MergedCutProfiles.Batch686.profile27450,MergedCutProfiles.Batch686.profile27453,MergedCutProfiles.Batch686.profile27454,MergedCutProfiles.Batch686.profile27455,MergedCutProfiles.Batch686.profile27456,MergedCutProfiles.Batch686.profile27457,MergedCutProfiles.Batch686.profile27458,MergedCutProfiles.Batch686.profile27459,MergedCutProfiles.Batch686.profile27460]⟩
theorem profilesValid4886 : retention4886.ProfilesValid := by
  change ∀ j : Fin 16, (retention4886.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch685.valid27437
  · exact MergedCutProfiles.Batch686.valid27452
  · exact MergedCutProfiles.Batch686.valid27441
  · exact MergedCutProfiles.Batch686.valid27443
  · exact MergedCutProfiles.Batch686.valid27444
  · exact MergedCutProfiles.Batch686.valid27446
  · exact MergedCutProfiles.Batch686.valid27448
  · exact MergedCutProfiles.Batch686.valid27450
  · exact MergedCutProfiles.Batch686.valid27453
  · exact MergedCutProfiles.Batch686.valid27454
  · exact MergedCutProfiles.Batch686.valid27455
  · exact MergedCutProfiles.Batch686.valid27456
  · exact MergedCutProfiles.Batch686.valid27457
  · exact MergedCutProfiles.Batch686.valid27458
  · exact MergedCutProfiles.Batch686.valid27459
  · exact MergedCutProfiles.Batch686.valid27460
theorem numericValid4886 : retention4886.NumericValid := by decide +kernel
def certificate4886 : RatCutBinCertificate := ⟨⟨retention4886,(475743403786706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(2230197336103541519/1000000000000000000)⟩,(999941616952369829/1000000000000000000),(135871430876973389/200000000000000000),(362485865115043/6250000000000000),(263059402579509/10000000000000000)⟩
theorem valid4886 : certificate4886.Valid := by decide +kernel
theorem sound4886 : certificate4886.Sound := rat_cut_bin_certificate_sound certificate4886 profilesValid4886 numericValid4886 valid4886

def retention4887 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1910007451132048616/2422573656693449252979),(560487349/500000000),(57/20),(19237008654349390041/8000000000000000000),true,MergedCutProfiles.Batch685.profile27438,![MergedCutProfiles.Batch685.profile27438,MergedCutProfiles.Batch686.profile27461,MergedCutProfiles.Batch686.profile27444,MergedCutProfiles.Batch686.profile27447,MergedCutProfiles.Batch686.profile27451,MergedCutProfiles.Batch686.profile27462,MergedCutProfiles.Batch686.profile27456,MergedCutProfiles.Batch686.profile27463,MergedCutProfiles.Batch686.profile27464,MergedCutProfiles.Batch686.profile27465,MergedCutProfiles.Batch686.profile27466,MergedCutProfiles.Batch686.profile27467,MergedCutProfiles.Batch686.profile27468,MergedCutProfiles.Batch686.profile27469,MergedCutProfiles.Batch686.profile27470,MergedCutProfiles.Batch686.profile27471]⟩
theorem profilesValid4887 : retention4887.ProfilesValid := by
  change ∀ j : Fin 16, (retention4887.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch685.valid27438
  · exact MergedCutProfiles.Batch686.valid27461
  · exact MergedCutProfiles.Batch686.valid27444
  · exact MergedCutProfiles.Batch686.valid27447
  · exact MergedCutProfiles.Batch686.valid27451
  · exact MergedCutProfiles.Batch686.valid27462
  · exact MergedCutProfiles.Batch686.valid27456
  · exact MergedCutProfiles.Batch686.valid27463
  · exact MergedCutProfiles.Batch686.valid27464
  · exact MergedCutProfiles.Batch686.valid27465
  · exact MergedCutProfiles.Batch686.valid27466
  · exact MergedCutProfiles.Batch686.valid27467
  · exact MergedCutProfiles.Batch686.valid27468
  · exact MergedCutProfiles.Batch686.valid27469
  · exact MergedCutProfiles.Batch686.valid27470
  · exact MergedCutProfiles.Batch686.valid27471
theorem numericValid4887 : retention4887.NumericValid := by decide +kernel
def certificate4887 : RatCutBinCertificate := ⟨⟨retention4887,(475743403786706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(1181261045125723809/500000000000000000)⟩,(999941616952369829/1000000000000000000),(111947735424465209/250000000000000000),(19244061800647837/100000000000000000),(63325689973662439/500000000000000000)⟩
theorem valid4887 : certificate4887.Valid := by decide +kernel
theorem sound4887 : certificate4887.Sound := rat_cut_bin_certificate_sound certificate4887 profilesValid4887 numericValid4887 valid4887

def retention4888 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(64000000000000000000/2422573656693449252979),(238750931391506077/125000000000000000),(39/20),(349373274473978429487/160000000000000000000),true,MergedCutProfiles.Batch686.profile27472,![MergedCutProfiles.Batch686.profile27472,MergedCutProfiles.Batch686.profile27473,MergedCutProfiles.Batch686.profile27474,MergedCutProfiles.Batch686.profile27475,MergedCutProfiles.Batch686.profile27476,MergedCutProfiles.Batch686.profile27477,MergedCutProfiles.Batch686.profile27478,MergedCutProfiles.Batch686.profile27479,MergedCutProfiles.Batch687.profile27480,MergedCutProfiles.Batch687.profile27481,MergedCutProfiles.Batch687.profile27482,MergedCutProfiles.Batch687.profile27483,MergedCutProfiles.Batch687.profile27484,MergedCutProfiles.Batch687.profile27485,MergedCutProfiles.Batch687.profile27486,MergedCutProfiles.Batch687.profile27487]⟩
theorem profilesValid4888 : retention4888.ProfilesValid := by
  change ∀ j : Fin 16, (retention4888.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch686.valid27472
  · exact MergedCutProfiles.Batch686.valid27473
  · exact MergedCutProfiles.Batch686.valid27474
  · exact MergedCutProfiles.Batch686.valid27475
  · exact MergedCutProfiles.Batch686.valid27476
  · exact MergedCutProfiles.Batch686.valid27477
  · exact MergedCutProfiles.Batch686.valid27478
  · exact MergedCutProfiles.Batch686.valid27479
  · exact MergedCutProfiles.Batch687.valid27480
  · exact MergedCutProfiles.Batch687.valid27481
  · exact MergedCutProfiles.Batch687.valid27482
  · exact MergedCutProfiles.Batch687.valid27483
  · exact MergedCutProfiles.Batch687.valid27484
  · exact MergedCutProfiles.Batch687.valid27485
  · exact MergedCutProfiles.Batch687.valid27486
  · exact MergedCutProfiles.Batch687.valid27487
theorem numericValid4888 : retention4888.NumericValid := by decide +kernel
def certificate4888 : RatCutBinCertificate := ⟨⟨retention4888,(475743403786706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(2154774975347789639/1000000000000000000)⟩,(999941616952369829/1000000000000000000),(386986764480402113/1000000000000000000),(245619641802789549/1000000000000000000),(209298813658799311/1000000000000000000)⟩
theorem valid4888 : certificate4888.Valid := by decide +kernel
theorem sound4888 : certificate4888.Sound := rat_cut_bin_certificate_sound certificate4888 profilesValid4888 numericValid4888 valid4888

def retention4889 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1/2),64,1,(255388469165804010637126414638867959079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch687.profile27488,(fun _ => MergedCutProfiles.Batch687.profile27488)⟩
theorem profilesValid4889 : retention4889.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27488
theorem numericValid4889 : retention4889.NumericValid := by decide +kernel
def certificate4889 : RatCutBinCertificate := ⟨⟨retention4889,(475743403786706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(982837891353118573/1000000000000000000)⟩,(999941616952369829/1000000000000000000),(133558884206584361/250000000000000000),(26168466067123751/200000000000000000),(63322180755527867/500000000000000000)⟩
theorem valid4889 : certificate4889.Valid := by decide +kernel
theorem sound4889 : certificate4889.Sound := rat_cut_bin_certificate_sound certificate4889 profilesValid4889 numericValid4889 valid4889

def retention4890 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(64000000000000000000/2422573656693449252979),(16675172123435855551/500000000000000000),1,(288686555779247556101462485407937326991/133401376987486844408000000000000000000),false,MergedCutProfiles.Batch687.profile27489,(fun _ => MergedCutProfiles.Batch687.profile27489)⟩
theorem profilesValid4890 : retention4890.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27489
theorem numericValid4890 : retention4890.NumericValid := by decide +kernel
def certificate4890 : RatCutBinCertificate := ⟨⟨retention4890,(437070060286706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(1075236203974411449/500000000000000000)⟩,(999946362956084183/1000000000000000000),(9820574670444683/500000000000000000),(875092329820265119/1000000000000000000),(883885452896334459/500000000000000000)⟩
theorem valid4890 : certificate4890.Valid := by decide +kernel
theorem sound4890 : certificate4890.Sound := rat_cut_bin_certificate_sound certificate4890 profilesValid4890 numericValid4890 valid4890

def retention4891 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1/2),64,1,(255388469165804010637126414638867959079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch687.profile27488,(fun _ => MergedCutProfiles.Batch687.profile27488)⟩
theorem profilesValid4891 : retention4891.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27488
theorem numericValid4891 : retention4891.NumericValid := by decide +kernel
def certificate4891 : RatCutBinCertificate := ⟨⟨retention4891,(437070060286706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(39361552770970033/40000000000000000)⟩,(999946362956084183/1000000000000000000),(5365356133655379/125000000000000000),(403812698346820709/500000000000000000),(78265782339032679/100000000000000000)⟩
theorem valid4891 : certificate4891.Valid := by decide +kernel
theorem sound4891 : certificate4891.Sound := rat_cut_bin_certificate_sound certificate4891 profilesValid4891 numericValid4891 valid4891

def retention4892 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(700093952363544008/2422573656693449252979),(693162329072815849/1000000000000000000),4,(415863824695710425209547678293068301/173290582268203962250000000000000000),false,MergedCutProfiles.Batch687.profile27490,(fun _ => MergedCutProfiles.Batch687.profile27490)⟩
theorem profilesValid4892 : retention4892.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27490
theorem numericValid4892 : retention4892.NumericValid := by decide +kernel
def certificate4892 : RatCutBinCertificate := ⟨⟨retention4892,(464424978036706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(2342118824041303773/1000000000000000000)⟩,(499971502976635513/500000000000000000),(54242734907950027/62500000000000000),(2284822377426049/250000000000000000),(2208985853208679/500000000000000000)⟩
theorem valid4892 : certificate4892.Valid := by decide +kernel
theorem sound4892 : certificate4892.Sound := rat_cut_bin_certificate_sound certificate4892 profilesValid4892 numericValid4892 valid4892

def retention4893 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(871418045822608994/2422573656693449252979),(87511744045443001/125000000000000000),4,(6729786835527750328096172491340268999/2800375809454176032000000000000000000),false,MergedCutProfiles.Batch687.profile27491,(fun _ => MergedCutProfiles.Batch687.profile27491)⟩
theorem profilesValid4893 : retention4893.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27491
theorem numericValid4893 : retention4893.NumericValid := by decide +kernel
def certificate4893 : RatCutBinCertificate := ⟨⟨retention4893,(464424978036706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(58637132789699877/25000000000000000)⟩,(499971502976635513/500000000000000000),(172903786541092481/200000000000000000),(4811304064618259/500000000000000000),(4665192560245481/1000000000000000000)⟩
theorem valid4893 : certificate4893.Valid := by decide +kernel
theorem sound4893 : certificate4893.Sound := rat_cut_bin_certificate_sound certificate4893 profilesValid4893 numericValid4893 valid4893

def retention4894 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1485287735460507072/807524552231149750993),(435709022911304497/500000000000000000),(73/20),(837686464595776205339126461986419298679/348567218329043597600000000000000000000),false,MergedCutProfiles.Batch687.profile27492,(fun _ => MergedCutProfiles.Batch687.profile27492)⟩
theorem profilesValid4894 : retention4894.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27492
theorem numericValid4894 : retention4894.NumericValid := by decide +kernel
def certificate4894 : RatCutBinCertificate := ⟨⟨retention4894,(464424978036706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(470117624171044863/200000000000000000)⟩,(499971502976635513/500000000000000000),(82106937757776651/100000000000000000),(17058708257178717/1000000000000000000),(1827073439205023/200000000000000000)⟩
theorem valid4894 : certificate4894.Valid := by decide +kernel
theorem sound4894 : certificate4894.Sound := rat_cut_bin_certificate_sound certificate4894 profilesValid4894 numericValid4894 valid4894

def retention4895 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(56911959399635768456/2422573656693449252979),(69622862599711269/15625000000000000),(29/20),(109622556453669293809557780155426999831/49509591182016902400000000000000000000),false,MergedCutProfiles.Batch687.profile27493,(fun _ => MergedCutProfiles.Batch687.profile27493)⟩
theorem profilesValid4895 : retention4895.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27493
theorem numericValid4895 : retention4895.NumericValid := by decide +kernel
def certificate4895 : RatCutBinCertificate := ⟨⟨retention4895,(464424978036706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(2193256397125833837/1000000000000000000)⟩,(499971502976635513/500000000000000000),(183376602272245789/250000000000000000),(39166059366840103/1000000000000000000),(48001006101631971/1000000000000000000)⟩
theorem valid4895 : certificate4895.Valid := by decide +kernel
theorem sound4895 : certificate4895.Sound := rat_cut_bin_certificate_sound certificate4895 profilesValid4895 numericValid4895 valid4895

def certificates : List RatCutBinCertificate := [certificate4884,certificate4885,certificate4886,certificate4887,certificate4888,certificate4889,certificate4890,certificate4891,certificate4892,certificate4893,certificate4894,certificate4895]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4884,List.forall_mem_cons.mpr ⟨sound4885,List.forall_mem_cons.mpr ⟨sound4886,List.forall_mem_cons.mpr ⟨sound4887,List.forall_mem_cons.mpr ⟨sound4888,List.forall_mem_cons.mpr ⟨sound4889,List.forall_mem_cons.mpr ⟨sound4890,List.forall_mem_cons.mpr ⟨sound4891,List.forall_mem_cons.mpr ⟨sound4892,List.forall_mem_cons.mpr ⟨sound4893,List.forall_mem_cons.mpr ⟨sound4894,List.forall_mem_cons.mpr ⟨sound4895,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch407
