import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch313
import Cycle12.MergedCutProfiles.Batch568
import Cycle12.MergedCutProfiles.Batch569
import Cycle12.MergedCutProfiles.Batch570

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch311

def retention3732 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(1/2),64,1,(255369275099586074223962287322657158471/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch568.profile22754,(fun _ => MergedCutProfiles.Batch568.profile22754)⟩
theorem profilesValid3732 : retention3732.ProfilesValid := by
  exact MergedCutProfiles.Batch568.valid22754
theorem numericValid3732 : retention3732.NumericValid := by decide +kernel
def certificate3732 : RatCutBinCertificate := ⟨⟨retention3732,(897833486860996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(996366954377688933/1000000000000000000)⟩,(999975501371161171/1000000000000000000),(437645438842212577/1000000000000000000),(100353750569610257/500000000000000000),(9845393614825959/50000000000000000)⟩
theorem valid3732 : certificate3732.Valid := by decide +kernel
theorem sound3732 : certificate3732.Sound := rat_cut_bin_certificate_sound certificate3732 profilesValid3732 numericValid3732 valid3732

def retention3733 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(64000000000000000000/9615687695137442862049),(16389297360015867223/1000000000000000000),1,(36395463357777330851989256303170469773/16389297360015867223000000000000000000),false,MergedCutProfiles.Batch568.profile22755,(fun _ => MergedCutProfiles.Batch568.profile22755)⟩
theorem profilesValid3733 : retention3733.ProfilesValid := by
  exact MergedCutProfiles.Batch568.valid22755
theorem numericValid3733 : retention3733.NumericValid := by decide +kernel
def certificate3733 : RatCutBinCertificate := ⟨⟨retention3733,(883994246360996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(443906707255493837/200000000000000000)⟩,(999975878994025793/1000000000000000000),(16390587009470551/500000000000000000),(16724178999355267/20000000000000000),(1634582975583203129/1000000000000000000)⟩
theorem valid3733 : certificate3733.Valid := by decide +kernel
theorem sound3733 : certificate3733.Sound := rat_cut_bin_certificate_sound certificate3733 profilesValid3733 numericValid3733 valid3733

def retention3734 : RatCutRetentionCertificate := ⟨(21/2000),(11/1000),(1/2),64,1,(255369275099586074223962287322657158471/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch568.profile22754,(fun _ => MergedCutProfiles.Batch568.profile22754)⟩
theorem profilesValid3734 : retention3734.ProfilesValid := by
  exact MergedCutProfiles.Batch568.valid22754
theorem numericValid3734 : retention3734.NumericValid := by decide +kernel
def certificate3734 : RatCutBinCertificate := ⟨⟨retention3734,(883994246360996359/500000000000000000),(246507623072377/50000000000000000),(7571273441896334563/1000000000000000000),(72967924963157851309997/1000000000000000000),(996384977651108201/1000000000000000000)⟩,(999975878994025793/1000000000000000000),(73022894489146473/1000000000000000000),(729322037469555917/1000000000000000000),(22360254032274877/31250000000000000)⟩
theorem valid3734 : certificate3734.Valid := by decide +kernel
theorem sound3734 : certificate3734.Sound := rat_cut_bin_certificate_sound certificate3734 profilesValid3734 numericValid3734 valid3734

def retention3735 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(612664887465086327/8043209882764221631265),(565785744578021111/1000000000000000000),4,(140249210328507589103/64000000000000000000),true,MergedCutProfiles.Batch568.profile22756,![MergedCutProfiles.Batch568.profile22756,MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch568.profile22758,MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22761,MergedCutProfiles.Batch569.profile22762,MergedCutProfiles.Batch569.profile22763,MergedCutProfiles.Batch569.profile22764,MergedCutProfiles.Batch313.profile12522,MergedCutProfiles.Batch313.profile12522,MergedCutProfiles.Batch569.profile22765,MergedCutProfiles.Batch569.profile22766,MergedCutProfiles.Batch569.profile22766,MergedCutProfiles.Batch569.profile22767,MergedCutProfiles.Batch569.profile22767]⟩
theorem profilesValid3735 : retention3735.ProfilesValid := by
  change ∀ j : Fin 16, (retention3735.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch568.valid22756
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch568.valid22758
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22761
  · exact MergedCutProfiles.Batch569.valid22762
  · exact MergedCutProfiles.Batch569.valid22763
  · exact MergedCutProfiles.Batch569.valid22764
  · exact MergedCutProfiles.Batch313.valid12522
  · exact MergedCutProfiles.Batch313.valid12522
  · exact MergedCutProfiles.Batch569.valid22765
  · exact MergedCutProfiles.Batch569.valid22766
  · exact MergedCutProfiles.Batch569.valid22766
  · exact MergedCutProfiles.Batch569.valid22767
  · exact MergedCutProfiles.Batch569.valid22767
theorem numericValid3735 : retention3735.NumericValid := by decide +kernel
def certificate3735 : RatCutBinCertificate := ⟨⟨retention3735,(1799499920472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(437166349710165901/200000000000000000)⟩,(999970909616596387/1000000000000000000),(640688073894349413/1000000000000000000),(74069545410043219/1000000000000000000),(16301164061021499/500000000000000000)⟩
theorem valid3735 : certificate3735.Valid := by decide +kernel
theorem sound3735 : certificate3735.Sound := rat_cut_bin_certificate_sound certificate3735 profilesValid3735 numericValid3735 valid3735

def retention3736 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(255053986800000000/1608641976552844326253),(612664887465086327/1000000000000000000),4,(1118137412424734432023081819183381179/490131909972069061600000000000000000),true,MergedCutProfiles.Batch568.profile22757,![MergedCutProfiles.Batch568.profile22757,MergedCutProfiles.Batch569.profile22760,MergedCutProfiles.Batch569.profile22762,MergedCutProfiles.Batch569.profile22763,MergedCutProfiles.Batch313.profile12522,MergedCutProfiles.Batch569.profile22765,MergedCutProfiles.Batch569.profile22767,MergedCutProfiles.Batch569.profile22768,MergedCutProfiles.Batch012.profile510,MergedCutProfiles.Batch313.profile12530,MergedCutProfiles.Batch569.profile22769,MergedCutProfiles.Batch313.profile12540,MergedCutProfiles.Batch569.profile22770,MergedCutProfiles.Batch313.profile12523,MergedCutProfiles.Batch313.profile12523,MergedCutProfiles.Batch569.profile22771]⟩
theorem profilesValid3736 : retention3736.ProfilesValid := by
  change ∀ j : Fin 16, (retention3736.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch568.valid22757
  · exact MergedCutProfiles.Batch569.valid22760
  · exact MergedCutProfiles.Batch569.valid22762
  · exact MergedCutProfiles.Batch569.valid22763
  · exact MergedCutProfiles.Batch313.valid12522
  · exact MergedCutProfiles.Batch569.valid22765
  · exact MergedCutProfiles.Batch569.valid22767
  · exact MergedCutProfiles.Batch569.valid22768
  · exact MergedCutProfiles.Batch012.valid510
  · exact MergedCutProfiles.Batch313.valid12530
  · exact MergedCutProfiles.Batch569.valid22769
  · exact MergedCutProfiles.Batch313.valid12540
  · exact MergedCutProfiles.Batch569.valid22770
  · exact MergedCutProfiles.Batch313.valid12523
  · exact MergedCutProfiles.Batch313.valid12523
  · exact MergedCutProfiles.Batch569.valid22771
theorem numericValid3736 : retention3736.NumericValid := by decide +kernel
def certificate3736 : RatCutBinCertificate := ⟨⟨retention3736,(1799499920472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(455147357781556991/200000000000000000)⟩,(999970909616596387/1000000000000000000),(116554681185156119/200000000000000000),(51277053454244359/500000000000000000),(1183789777175183/25000000000000000)⟩
theorem valid3736 : certificate3736.Valid := by decide +kernel
theorem sound3736 : certificate3736.Sound := rat_cut_bin_certificate_sound certificate3736 profilesValid3736 numericValid3736 valid3736

def retention3737 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(2370990563865711238/8043209882764221631265),(637634967/500000000),(5/2),(18885044124298000069/8000000000000000000),true,MergedCutProfiles.Batch568.profile22759,![MergedCutProfiles.Batch568.profile22759,MergedCutProfiles.Batch569.profile22763,MergedCutProfiles.Batch569.profile22765,MergedCutProfiles.Batch569.profile22767,MergedCutProfiles.Batch012.profile510,MergedCutProfiles.Batch569.profile22769,MergedCutProfiles.Batch569.profile22770,MergedCutProfiles.Batch313.profile12523,MergedCutProfiles.Batch569.profile22772,MergedCutProfiles.Batch569.profile22773,MergedCutProfiles.Batch569.profile22774,MergedCutProfiles.Batch569.profile22775,MergedCutProfiles.Batch313.profile12524,MergedCutProfiles.Batch313.profile12541,MergedCutProfiles.Batch012.profile512,MergedCutProfiles.Batch313.profile12531]⟩
theorem profilesValid3737 : retention3737.ProfilesValid := by
  change ∀ j : Fin 16, (retention3737.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch568.valid22759
  · exact MergedCutProfiles.Batch569.valid22763
  · exact MergedCutProfiles.Batch569.valid22765
  · exact MergedCutProfiles.Batch569.valid22767
  · exact MergedCutProfiles.Batch012.valid510
  · exact MergedCutProfiles.Batch569.valid22769
  · exact MergedCutProfiles.Batch569.valid22770
  · exact MergedCutProfiles.Batch313.valid12523
  · exact MergedCutProfiles.Batch569.valid22772
  · exact MergedCutProfiles.Batch569.valid22773
  · exact MergedCutProfiles.Batch569.valid22774
  · exact MergedCutProfiles.Batch569.valid22775
  · exact MergedCutProfiles.Batch313.valid12524
  · exact MergedCutProfiles.Batch313.valid12541
  · exact MergedCutProfiles.Batch012.valid512
  · exact MergedCutProfiles.Batch313.valid12531
theorem numericValid3737 : retention3737.NumericValid := by decide +kernel
def certificate3737 : RatCutBinCertificate := ⟨⟨retention3737,(1799499920472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(73661067619056581/31250000000000000)⟩,(999970909616596387/1000000000000000000),(73050744998536729/200000000000000000),(13343623512272713/50000000000000000),(194187155223387399/1000000000000000000)⟩
theorem valid3737 : certificate3737.Valid := by decide +kernel
theorem sound3737 : certificate3737.Sound := rat_cut_bin_certificate_sound certificate3737 profilesValid3737 numericValid3737 valid3737

def retention3738 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(12800000000000000000/1608641976552844326253),(1185495281932855619/500000000000000000),(17/10),(360266299669686371287/160000000000000000000),true,MergedCutProfiles.Batch313.profile12532,![MergedCutProfiles.Batch313.profile12532,MergedCutProfiles.Batch313.profile12535,MergedCutProfiles.Batch013.profile525,MergedCutProfiles.Batch313.profile12548,MergedCutProfiles.Batch013.profile535,MergedCutProfiles.Batch013.profile547,MergedCutProfiles.Batch569.profile22776,MergedCutProfiles.Batch569.profile22777,MergedCutProfiles.Batch569.profile22778,MergedCutProfiles.Batch569.profile22779,MergedCutProfiles.Batch569.profile22780,MergedCutProfiles.Batch569.profile22781,MergedCutProfiles.Batch569.profile22782,MergedCutProfiles.Batch569.profile22783,MergedCutProfiles.Batch569.profile22784,MergedCutProfiles.Batch569.profile22785]⟩
theorem profilesValid3738 : retention3738.ProfilesValid := by
  change ∀ j : Fin 16, (retention3738.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch313.valid12532
  · exact MergedCutProfiles.Batch313.valid12535
  · exact MergedCutProfiles.Batch013.valid525
  · exact MergedCutProfiles.Batch313.valid12548
  · exact MergedCutProfiles.Batch013.valid535
  · exact MergedCutProfiles.Batch013.valid547
  · exact MergedCutProfiles.Batch569.valid22776
  · exact MergedCutProfiles.Batch569.valid22777
  · exact MergedCutProfiles.Batch569.valid22778
  · exact MergedCutProfiles.Batch569.valid22779
  · exact MergedCutProfiles.Batch569.valid22780
  · exact MergedCutProfiles.Batch569.valid22781
  · exact MergedCutProfiles.Batch569.valid22782
  · exact MergedCutProfiles.Batch569.valid22783
  · exact MergedCutProfiles.Batch569.valid22784
  · exact MergedCutProfiles.Batch569.valid22785
theorem numericValid3738 : retention3738.NumericValid := by decide +kernel
def certificate3738 : RatCutBinCertificate := ⟨⟨retention3738,(1799499920472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(8786329897561341/3906250000000000)⟩,(999970909616596387/1000000000000000000),(18398579506228507/62500000000000000),(69120812335854277/200000000000000000),(68850940178694397/200000000000000000)⟩
theorem valid3738 : certificate3738.Valid := by decide +kernel
theorem sound3738 : certificate3738.Sound := rat_cut_bin_certificate_sound certificate3738 profilesValid3738 numericValid3738 valid3738

def retention3739 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid3739 : retention3739.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid3739 : retention3739.NumericValid := by decide +kernel
def certificate3739 : RatCutBinCertificate := ⟨⟨retention3739,(1799499920472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(996145753673134423/1000000000000000000)⟩,(999970909616596387/1000000000000000000),(6890935705022553/15625000000000000),(197932059003583567/1000000000000000000),(7765664945442371/40000000000000000)⟩
theorem valid3739 : certificate3739.Valid := by decide +kernel
theorem sound3739 : certificate3739.Sound := rat_cut_bin_certificate_sound certificate3739 profilesValid3739 numericValid3739 valid3739

def retention3740 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(12800000000000000000/1608641976552844326253),(16601584521584192803/1000000000000000000),1,(573376526295710046741601118530934277/259399758149753012546875000000000000),false,MergedCutProfiles.Batch569.profile22786,(fun _ => MergedCutProfiles.Batch569.profile22786)⟩
theorem profilesValid3740 : retention3740.ProfilesValid := by
  exact MergedCutProfiles.Batch569.valid22786
theorem numericValid3740 : retention3740.NumericValid := by decide +kernel
def certificate3740 : RatCutBinCertificate := ⟨⟨retention3740,(1768379872472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(2209030811824301357/1000000000000000000)⟩,(999971412697616721/1000000000000000000),(31982512533833/976562500000000),(104537300762621299/125000000000000000),(326081968302558751/200000000000000000)⟩
theorem valid3740 : certificate3740.Valid := by decide +kernel
theorem sound3740 : certificate3740.Sound := rat_cut_bin_certificate_sound certificate3740 profilesValid3740 numericValid3740 valid3740

def retention3741 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid3741 : retention3741.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid3741 : retention3741.NumericValid := by decide +kernel
def certificate3741 : RatCutBinCertificate := ⟨⟨retention3741,(1768379872472659019/1000000000000000000),(5886872707676009/1000000000000000000),(952275916467377169/125000000000000000),(61553962516360105273289/1000000000000000000),(249042450323497293/250000000000000000)⟩,(999971412697616721/1000000000000000000),(9078016125848001/125000000000000000),(36515034515029599/50000000000000000),(716332685318162013/1000000000000000000)⟩
theorem valid3741 : certificate3741.Valid := by decide +kernel
theorem sound3741 : certificate3741.Sound := rat_cut_bin_certificate_sound certificate3741 profilesValid3741 numericValid3741 valid3741

def retention3742 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(576650254688633864/7395724679333802015673),(70660995820095317/125000000000000000),4,(76194901910451584747015361116189919/34786951788354617600000000000000000),true,MergedCutProfiles.Batch569.profile22787,![MergedCutProfiles.Batch569.profile22787,MergedCutProfiles.Batch569.profile22788,MergedCutProfiles.Batch569.profile22789,MergedCutProfiles.Batch569.profile22790,MergedCutProfiles.Batch569.profile22791,MergedCutProfiles.Batch569.profile22792,MergedCutProfiles.Batch569.profile22792,MergedCutProfiles.Batch569.profile22793,MergedCutProfiles.Batch569.profile22794,MergedCutProfiles.Batch569.profile22795,MergedCutProfiles.Batch569.profile22795,MergedCutProfiles.Batch569.profile22796,MergedCutProfiles.Batch569.profile22797,MergedCutProfiles.Batch569.profile22797,MergedCutProfiles.Batch569.profile22798,MergedCutProfiles.Batch569.profile22799]⟩
theorem profilesValid3742 : retention3742.ProfilesValid := by
  change ∀ j : Fin 16, (retention3742.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch569.valid22787
  · exact MergedCutProfiles.Batch569.valid22788
  · exact MergedCutProfiles.Batch569.valid22789
  · exact MergedCutProfiles.Batch569.valid22790
  · exact MergedCutProfiles.Batch569.valid22791
  · exact MergedCutProfiles.Batch569.valid22792
  · exact MergedCutProfiles.Batch569.valid22792
  · exact MergedCutProfiles.Batch569.valid22793
  · exact MergedCutProfiles.Batch569.valid22794
  · exact MergedCutProfiles.Batch569.valid22795
  · exact MergedCutProfiles.Batch569.valid22795
  · exact MergedCutProfiles.Batch569.valid22796
  · exact MergedCutProfiles.Batch569.valid22797
  · exact MergedCutProfiles.Batch569.valid22797
  · exact MergedCutProfiles.Batch569.valid22798
  · exact MergedCutProfiles.Batch569.valid22799
theorem numericValid3742 : retention3742.NumericValid := by decide +kernel
def certificate3742 : RatCutBinCertificate := ⟨⟨retention3742,(903871676627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(43686634950120097/20000000000000000)⟩,(249992142340777621/250000000000000000),(25793356275801057/40000000000000000),(36118576652531623/500000000000000000),(31772679996185223/1000000000000000000)⟩
theorem valid3742 : certificate3742.Valid := by decide +kernel
theorem sound3742 : certificate3742.Sound := rat_cut_bin_certificate_sound certificate3742 profilesValid3742 numericValid3742 valid3742

def retention3743 : RatCutRetentionCertificate := ⟨(3/250),(1/80),(1274340723000000000/7395724679333802015673),(72081281836079233/125000000000000000),4,(5107199987470885514625398094066762807/2306601018754535456000000000000000000),true,MergedCutProfiles.Batch569.profile22788,![MergedCutProfiles.Batch569.profile22788,MergedCutProfiles.Batch569.profile22790,MergedCutProfiles.Batch569.profile22792,MergedCutProfiles.Batch569.profile22794,MergedCutProfiles.Batch569.profile22796,MergedCutProfiles.Batch569.profile22797,MergedCutProfiles.Batch569.profile22798,MergedCutProfiles.Batch570.profile22800,MergedCutProfiles.Batch570.profile22801,MergedCutProfiles.Batch570.profile22802,MergedCutProfiles.Batch570.profile22803,MergedCutProfiles.Batch570.profile22804,MergedCutProfiles.Batch570.profile22805,MergedCutProfiles.Batch570.profile22806,MergedCutProfiles.Batch570.profile22807,MergedCutProfiles.Batch570.profile22807]⟩
theorem profilesValid3743 : retention3743.ProfilesValid := by
  change ∀ j : Fin 16, (retention3743.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch569.valid22788
  · exact MergedCutProfiles.Batch569.valid22790
  · exact MergedCutProfiles.Batch569.valid22792
  · exact MergedCutProfiles.Batch569.valid22794
  · exact MergedCutProfiles.Batch569.valid22796
  · exact MergedCutProfiles.Batch569.valid22797
  · exact MergedCutProfiles.Batch569.valid22798
  · exact MergedCutProfiles.Batch570.valid22800
  · exact MergedCutProfiles.Batch570.valid22801
  · exact MergedCutProfiles.Batch570.valid22802
  · exact MergedCutProfiles.Batch570.valid22803
  · exact MergedCutProfiles.Batch570.valid22804
  · exact MergedCutProfiles.Batch570.valid22805
  · exact MergedCutProfiles.Batch570.valid22806
  · exact MergedCutProfiles.Batch570.valid22807
  · exact MergedCutProfiles.Batch570.valid22807
theorem numericValid3743 : retention3743.NumericValid := by decide +kernel
def certificate3743 : RatCutBinCertificate := ⟨⟨retention3743,(903871676627028339/500000000000000000),(6398394180380671/1000000000000000000),(1928357816880769413/250000000000000000),(28588376033724291777339/500000000000000000),(2208168866934967697/1000000000000000000)⟩,(249992142340777621/250000000000000000),(39323169778907989/62500000000000000),(39650682318126109/500000000000000000),(35322314172692503/1000000000000000000)⟩
theorem valid3743 : certificate3743.Valid := by decide +kernel
theorem sound3743 : certificate3743.Sound := rat_cut_bin_certificate_sound certificate3743 profilesValid3743 numericValid3743 valid3743

def certificates : List RatCutBinCertificate := [certificate3732,certificate3733,certificate3734,certificate3735,certificate3736,certificate3737,certificate3738,certificate3739,certificate3740,certificate3741,certificate3742,certificate3743]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3732,List.forall_mem_cons.mpr ⟨sound3733,List.forall_mem_cons.mpr ⟨sound3734,List.forall_mem_cons.mpr ⟨sound3735,List.forall_mem_cons.mpr ⟨sound3736,List.forall_mem_cons.mpr ⟨sound3737,List.forall_mem_cons.mpr ⟨sound3738,List.forall_mem_cons.mpr ⟨sound3739,List.forall_mem_cons.mpr ⟨sound3740,List.forall_mem_cons.mpr ⟨sound3741,List.forall_mem_cons.mpr ⟨sound3742,List.forall_mem_cons.mpr ⟨sound3743,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch311
