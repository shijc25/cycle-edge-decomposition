import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch116
import Cycle12.MergedCutProfiles.Batch117
import Cycle12.MergedCutProfiles.Batch118
import Cycle12.MergedCutProfiles.Batch688
import Cycle12.MergedCutProfiles.Batch689
import Cycle12.MergedCutProfiles.Batch690

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch409

def retention4908 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(1/40),(13987282053713070283/250000000000000000),(21/20),(1104425177119200843/500000000000000000),false,MergedCutProfiles.Batch688.profile27555,(fun _ => MergedCutProfiles.Batch688.profile27555)⟩
theorem profilesValid4908 : retention4908.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27555
theorem numericValid4908 : retention4908.NumericValid := by decide +kernel
def certificate4908 : RatCutBinCertificate := ⟨⟨retention4908,(465453011275959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(2193420212697480161/1000000000000000000)⟩,(499971027495810487/500000000000000000),(349728658181377649/500000000000000000),(50521311307567421/1000000000000000000),(50953833694284703/500000000000000000)⟩
theorem valid4908 : certificate4908.Valid := by decide +kernel
theorem sound4908 : certificate4908.Sound := rat_cut_bin_certificate_sound certificate4908 profilesValid4908 numericValid4908 valid4908

def retention4909 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(628753803903477176/2305523233828859471285),(148078631278807129/250000000000000000),4,(144832775065134193901/64000000000000000000),true,MergedCutProfiles.Batch688.profile27556,![MergedCutProfiles.Batch688.profile27556,MergedCutProfiles.Batch688.profile27557,MergedCutProfiles.Batch688.profile27558,MergedCutProfiles.Batch688.profile27559,MergedCutProfiles.Batch689.profile27560,MergedCutProfiles.Batch689.profile27561,MergedCutProfiles.Batch689.profile27562,MergedCutProfiles.Batch689.profile27563,MergedCutProfiles.Batch689.profile27564,MergedCutProfiles.Batch689.profile27565,MergedCutProfiles.Batch689.profile27566,MergedCutProfiles.Batch689.profile27567,MergedCutProfiles.Batch689.profile27568,MergedCutProfiles.Batch689.profile27569,MergedCutProfiles.Batch689.profile27570,MergedCutProfiles.Batch689.profile27571]⟩
theorem profilesValid4909 : retention4909.ProfilesValid := by
  change ∀ j : Fin 16, (retention4909.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch688.valid27556
  · exact MergedCutProfiles.Batch688.valid27557
  · exact MergedCutProfiles.Batch688.valid27558
  · exact MergedCutProfiles.Batch688.valid27559
  · exact MergedCutProfiles.Batch689.valid27560
  · exact MergedCutProfiles.Batch689.valid27561
  · exact MergedCutProfiles.Batch689.valid27562
  · exact MergedCutProfiles.Batch689.valid27563
  · exact MergedCutProfiles.Batch689.valid27564
  · exact MergedCutProfiles.Batch689.valid27565
  · exact MergedCutProfiles.Batch689.valid27566
  · exact MergedCutProfiles.Batch689.valid27567
  · exact MergedCutProfiles.Batch689.valid27568
  · exact MergedCutProfiles.Batch689.valid27569
  · exact MergedCutProfiles.Batch689.valid27570
  · exact MergedCutProfiles.Batch689.valid27571
theorem numericValid4909 : retention4909.NumericValid := by decide +kernel
def certificate4909 : RatCutBinCertificate := ⟨⟨retention4909,(476627747505100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2201828961365275569/1000000000000000000)⟩,(999939825862281553/1000000000000000000),(175482008224449449/250000000000000000),(24821255499481259/500000000000000000),(11086318387495221/500000000000000000)⟩
theorem valid4909 : certificate4909.Valid := by decide +kernel
theorem sound4909 : certificate4909.Sound := rat_cut_bin_certificate_sound certificate4909 profilesValid4909 numericValid4909 valid4909

def retention4910 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(224837247200000000/461104646765771894257),(78594225487934647/125000000000000000),4,(74356235777256041809/32000000000000000000),true,MergedCutProfiles.Batch688.profile27557,![MergedCutProfiles.Batch688.profile27557,MergedCutProfiles.Batch689.profile27572,MergedCutProfiles.Batch689.profile27573,MergedCutProfiles.Batch689.profile27562,MergedCutProfiles.Batch689.profile27564,MergedCutProfiles.Batch689.profile27574,MergedCutProfiles.Batch689.profile27567,MergedCutProfiles.Batch689.profile27569,MergedCutProfiles.Batch689.profile27571,MergedCutProfiles.Batch689.profile27575,MergedCutProfiles.Batch689.profile27576,MergedCutProfiles.Batch689.profile27577,MergedCutProfiles.Batch689.profile27578,MergedCutProfiles.Batch689.profile27579,MergedCutProfiles.Batch689.profile27580,MergedCutProfiles.Batch689.profile27581]⟩
theorem profilesValid4910 : retention4910.ProfilesValid := by
  change ∀ j : Fin 16, (retention4910.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch688.valid27557
  · exact MergedCutProfiles.Batch689.valid27572
  · exact MergedCutProfiles.Batch689.valid27573
  · exact MergedCutProfiles.Batch689.valid27562
  · exact MergedCutProfiles.Batch689.valid27564
  · exact MergedCutProfiles.Batch689.valid27574
  · exact MergedCutProfiles.Batch689.valid27567
  · exact MergedCutProfiles.Batch689.valid27569
  · exact MergedCutProfiles.Batch689.valid27571
  · exact MergedCutProfiles.Batch689.valid27575
  · exact MergedCutProfiles.Batch689.valid27576
  · exact MergedCutProfiles.Batch689.valid27577
  · exact MergedCutProfiles.Batch689.valid27578
  · exact MergedCutProfiles.Batch689.valid27579
  · exact MergedCutProfiles.Batch689.valid27580
  · exact MergedCutProfiles.Batch689.valid27581
theorem numericValid4910 : retention4910.NumericValid := by decide +kernel
def certificate4910 : RatCutBinCertificate := ⟨⟨retention4910,(476627747505100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2262449224205303609/1000000000000000000)⟩,(999939825862281553/1000000000000000000),(131357723750954681/200000000000000000),(13420402196020649/200000000000000000),(6196611327462781/200000000000000000)⟩
theorem valid4910 : certificate4910.Valid := by decide +kernel
theorem sound4910 : certificate4910.Sound := rat_cut_bin_certificate_sound certificate4910 profilesValid4910 numericValid4910 valid4910

def retention4911 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(2969032390992847676/2305523233828859471285),(281046559/250000000),(14/5),(10736067259950547338029580278168921271/4496744944000000000000000000000000000),true,MergedCutProfiles.Batch689.profile27560,![MergedCutProfiles.Batch689.profile27560,MergedCutProfiles.Batch689.profile27564,MergedCutProfiles.Batch689.profile27569,MergedCutProfiles.Batch689.profile27582,MergedCutProfiles.Batch689.profile27583,MergedCutProfiles.Batch689.profile27581,MergedCutProfiles.Batch689.profile27584,MergedCutProfiles.Batch689.profile27585,MergedCutProfiles.Batch689.profile27586,MergedCutProfiles.Batch689.profile27587,MergedCutProfiles.Batch689.profile27588,MergedCutProfiles.Batch689.profile27589,MergedCutProfiles.Batch689.profile27590,MergedCutProfiles.Batch689.profile27591,MergedCutProfiles.Batch689.profile27592,MergedCutProfiles.Batch689.profile27593]⟩
theorem profilesValid4911 : retention4911.ProfilesValid := by
  change ∀ j : Fin 16, (retention4911.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch689.valid27560
  · exact MergedCutProfiles.Batch689.valid27564
  · exact MergedCutProfiles.Batch689.valid27569
  · exact MergedCutProfiles.Batch689.valid27582
  · exact MergedCutProfiles.Batch689.valid27583
  · exact MergedCutProfiles.Batch689.valid27581
  · exact MergedCutProfiles.Batch689.valid27584
  · exact MergedCutProfiles.Batch689.valid27585
  · exact MergedCutProfiles.Batch689.valid27586
  · exact MergedCutProfiles.Batch689.valid27587
  · exact MergedCutProfiles.Batch689.valid27588
  · exact MergedCutProfiles.Batch689.valid27589
  · exact MergedCutProfiles.Batch689.valid27590
  · exact MergedCutProfiles.Batch689.valid27591
  · exact MergedCutProfiles.Batch689.valid27592
  · exact MergedCutProfiles.Batch689.valid27593
theorem numericValid4911 : retention4911.NumericValid := by decide +kernel
def certificate4911 : RatCutBinCertificate := ⟨⟨retention4911,(476627747505100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(1172345768970740951/500000000000000000)⟩,(999939825862281553/1000000000000000000),(451737464674381271/1000000000000000000),(94643622077201389/500000000000000000),(125191416133310329/1000000000000000000)⟩
theorem valid4911 : certificate4911.Valid := by decide +kernel
theorem sound4911 : certificate4911.Sound := rat_cut_bin_certificate_sound certificate4911 profilesValid4911 numericValid4911 valid4911

def retention4912 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(12800000000000000000/461104646765771894257),(742258097748211919/250000000000000000),(3/2),(1603162529465510943693354468183869877/742258097748211919000000000000000000),true,MergedCutProfiles.Batch689.profile27594,![MergedCutProfiles.Batch689.profile27594,MergedCutProfiles.Batch689.profile27595,MergedCutProfiles.Batch689.profile27596,MergedCutProfiles.Batch689.profile27597,MergedCutProfiles.Batch689.profile27598,MergedCutProfiles.Batch689.profile27599,MergedCutProfiles.Batch690.profile27600,MergedCutProfiles.Batch690.profile27601,MergedCutProfiles.Batch690.profile27602,MergedCutProfiles.Batch690.profile27603,MergedCutProfiles.Batch116.profile4674,MergedCutProfiles.Batch690.profile27604,MergedCutProfiles.Batch116.profile4645,MergedCutProfiles.Batch117.profile4703,MergedCutProfiles.Batch116.profile4677,MergedCutProfiles.Batch690.profile27605]⟩
theorem profilesValid4912 : retention4912.ProfilesValid := by
  change ∀ j : Fin 16, (retention4912.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch689.valid27594
  · exact MergedCutProfiles.Batch689.valid27595
  · exact MergedCutProfiles.Batch689.valid27596
  · exact MergedCutProfiles.Batch689.valid27597
  · exact MergedCutProfiles.Batch689.valid27598
  · exact MergedCutProfiles.Batch689.valid27599
  · exact MergedCutProfiles.Batch690.valid27600
  · exact MergedCutProfiles.Batch690.valid27601
  · exact MergedCutProfiles.Batch690.valid27602
  · exact MergedCutProfiles.Batch690.valid27603
  · exact MergedCutProfiles.Batch116.valid4674
  · exact MergedCutProfiles.Batch690.valid27604
  · exact MergedCutProfiles.Batch116.valid4645
  · exact MergedCutProfiles.Batch117.valid4703
  · exact MergedCutProfiles.Batch116.valid4677
  · exact MergedCutProfiles.Batch690.valid27605
theorem numericValid4912 : retention4912.NumericValid := by decide +kernel
def certificate4912 : RatCutBinCertificate := ⟨⟨retention4912,(476627747505100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(427380290769967263/200000000000000000)⟩,(999939825862281553/1000000000000000000),(169088127944923787/500000000000000000),(295168982144026677/1000000000000000000),(159283411199452607/500000000000000000)⟩
theorem valid4912 : certificate4912.Valid := by decide +kernel
theorem sound4912 : certificate4912.Sound := rat_cut_bin_certificate_sound certificate4912 profilesValid4912 numericValid4912 valid4912

def retention4913 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1/2),64,1,(249403819990079998474269137177007319/250000000000000000000000000000000000),false,MergedCutProfiles.Batch118.profile4748,(fun _ => MergedCutProfiles.Batch118.profile4748)⟩
theorem profilesValid4913 : retention4913.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4748
theorem numericValid4913 : retention4913.NumericValid := by decide +kernel
def certificate4913 : RatCutBinCertificate := ⟨⟨retention4913,(476627747505100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(98231951427734023/100000000000000000)⟩,(999939825862281553/1000000000000000000),(268288251450756599/500000000000000000),(129379858186629099/1000000000000000000),(62581766899402039/500000000000000000)⟩
theorem valid4913 : certificate4913.Valid := by decide +kernel
theorem sound4913 : certificate4913.Sound := rat_cut_bin_certificate_sound certificate4913 profilesValid4913 numericValid4913 valid4913

def retention4914 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(12800000000000000000/461104646765771894257),(3402928242502243139/100000000000000000),1,(293894155934223867625719860971928355031/136117129700089725560000000000000000000),false,MergedCutProfiles.Batch690.profile27606,(fun _ => MergedCutProfiles.Batch690.profile27606)⟩
theorem profilesValid4914 : retention4914.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27606
theorem numericValid4914 : retention4914.NumericValid := by decide +kernel
def certificate4914 : RatCutBinCertificate := ⟨⟨retention4914,(436898751755100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2145106099656739533/1000000000000000000)⟩,(124993105208507819/125000000000000000),(3873309105534761/200000000000000000),(875928378989531673/1000000000000000000),(883719737574478473/500000000000000000)⟩
theorem valid4914 : certificate4914.Valid := by decide +kernel
theorem sound4914 : certificate4914.Sound := rat_cut_bin_certificate_sound certificate4914 profilesValid4914 numericValid4914 valid4914

def retention4915 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(1/2),64,1,(249403819990079998474269137177007319/250000000000000000000000000000000000),false,MergedCutProfiles.Batch118.profile4748,(fun _ => MergedCutProfiles.Batch118.profile4748)⟩
theorem profilesValid4915 : retention4915.ProfilesValid := by
  exact MergedCutProfiles.Batch118.valid4748
theorem numericValid4915 : retention4915.NumericValid := by decide +kernel
def certificate4915 : RatCutBinCertificate := ⟨⟨retention4915,(436898751755100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(122949310359104817/125000000000000000)⟩,(124993105208507819/125000000000000000),(21118100835293037/500000000000000000),(404761663934698283/500000000000000000),(784146997316874777/1000000000000000000)⟩
theorem valid4915 : certificate4915.Valid := by decide +kernel
theorem sound4915 : certificate4915.Sound := rat_cut_bin_certificate_sound certificate4915 profilesValid4915 numericValid4915 valid4915

def retention4916 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(704075462118074066/2305523233828859471285),(348552208969343597/500000000000000000),4,(6703028616101215794452213224714339207/2788417671754748776000000000000000000),false,MergedCutProfiles.Batch690.profile27607,(fun _ => MergedCutProfiles.Batch690.profile27607)⟩
theorem profilesValid4916 : retention4916.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27607
theorem numericValid4916 : retention4916.NumericValid := by decide +kernel
def certificate4916 : RatCutBinCertificate := ⟨⟨retention4916,(466481940255100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2344001810118096809/1000000000000000000)⟩,(39997644271043399/40000000000000000),(172267756964707041/200000000000000000),(10091436953057937/1000000000000000000),(1221572873494871/250000000000000000)⟩
theorem valid4916 : certificate4916.Valid := by decide +kernel
theorem sound4916 : certificate4916.Sound := rat_cut_bin_certificate_sound certificate4916 profilesValid4916 numericValid4916 valid4916

def retention4917 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(876373894159825554/2305523233828859471285),(352037731059037033/500000000000000000),4,(6778707567810242319427922152381764247/2816301848472296264000000000000000000),false,MergedCutProfiles.Batch690.profile27608,(fun _ => MergedCutProfiles.Batch690.profile27608)⟩
theorem profilesValid4917 : retention4917.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27608
theorem numericValid4917 : retention4917.NumericValid := by decide +kernel
def certificate4917 : RatCutBinCertificate := ⟨⟨retention4917,(466481940255100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(1173536370376921441/500000000000000000)⟩,(39997644271043399/40000000000000000),(171625894711219927/200000000000000000),(10576468734558849/1000000000000000000),(5135527753100359/1000000000000000000)⟩
theorem valid4917 : certificate4917.Valid := by decide +kernel
theorem sound4917 : certificate4917.Sound := rat_cut_bin_certificate_sound certificate4917 profilesValid4917 numericValid4917 valid4917

def retention4918 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(4392906754861146593/2305523233828859471285),(438186947079912777/500000000000000000),(73/20),(842834659722136788596506567824601101119/350549557663930221600000000000000000000),false,MergedCutProfiles.Batch690.profile27609,(fun _ => MergedCutProfiles.Batch690.profile27609)⟩
theorem profilesValid4918 : retention4918.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27609
theorem numericValid4918 : retention4918.NumericValid := by decide +kernel
def certificate4918 : RatCutBinCertificate := ⟨⟨retention4918,(466481940255100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2349682666049821313/1000000000000000000)⟩,(39997644271043399/40000000000000000),(816282415559966951/1000000000000000000),(9008214113193929/500000000000000000),(2413581898291787/250000000000000000)⟩
theorem valid4918 : certificate4918.Valid := by decide +kernel
theorem sound4918 : certificate4918.Sound := rat_cut_bin_certificate_sound certificate4918 profilesValid4918 numericValid4918 valid4918

def retention4919 : RatCutRetentionCertificate := ⟨(91/2000),(23/500),(55002309520223979938/2305523233828859471285),(4392906754861146593/1000000000000000000),(29/20),(15552714736705418812251719807730435715591/7028650807777834548800000000000000000000),false,MergedCutProfiles.Batch690.profile27610,(fun _ => MergedCutProfiles.Batch690.profile27610)⟩
theorem profilesValid4919 : retention4919.ProfilesValid := by
  exact MergedCutProfiles.Batch690.valid27610
theorem numericValid4919 : retention4919.NumericValid := by decide +kernel
def certificate4919 : RatCutBinCertificate := ⟨⟨retention4919,(466481940255100343/250000000000000000),(19858540071699249/200000000000000000),(12376146356452482367/1000000000000000000),(894160117241170598371/31250000000000000),(2191052869278894643/1000000000000000000)⟩,(39997644271043399/40000000000000000),(365962741572407477/500000000000000000),(39657723175219917/1000000000000000000),(48432334560488959/1000000000000000000)⟩
theorem valid4919 : certificate4919.Valid := by decide +kernel
theorem sound4919 : certificate4919.Sound := rat_cut_bin_certificate_sound certificate4919 profilesValid4919 numericValid4919 valid4919

def certificates : List RatCutBinCertificate := [certificate4908,certificate4909,certificate4910,certificate4911,certificate4912,certificate4913,certificate4914,certificate4915,certificate4916,certificate4917,certificate4918,certificate4919]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4908,List.forall_mem_cons.mpr ⟨sound4909,List.forall_mem_cons.mpr ⟨sound4910,List.forall_mem_cons.mpr ⟨sound4911,List.forall_mem_cons.mpr ⟨sound4912,List.forall_mem_cons.mpr ⟨sound4913,List.forall_mem_cons.mpr ⟨sound4914,List.forall_mem_cons.mpr ⟨sound4915,List.forall_mem_cons.mpr ⟨sound4916,List.forall_mem_cons.mpr ⟨sound4917,List.forall_mem_cons.mpr ⟨sound4918,List.forall_mem_cons.mpr ⟨sound4919,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch409
