import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch029
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch323
import Cycle12.MergedCutProfiles.Batch457
import Cycle12.MergedCutProfiles.Batch458
import Cycle12.MergedCutProfiles.Batch650
import Cycle12.MergedCutProfiles.Batch651

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch375

def retention4500 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(64000000000000000000/11416785527815779703113),(3649348139249986293/200000000000000000),1,(6562443709393762698433427569048034987/2919478511399989034400000000000000000),false,MergedCutProfiles.Batch650.profile26017,(fun _ => MergedCutProfiles.Batch650.profile26017)⟩
theorem profilesValid4500 : retention4500.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26017
theorem numericValid4500 : retention4500.NumericValid := by decide +kernel
def certificate4500 : RatCutBinCertificate := ⟨⟨retention4500,(179542291632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(560891079148857733/250000000000000000)⟩,(999982263187576019/1000000000000000000),(6671034902492083/250000000000000000),(42699103505641271/50000000000000000),(853073079666280447/500000000000000000)⟩
theorem valid4500 : certificate4500.Valid := by decide +kernel
theorem sound4500 : certificate4500.Sound := rat_cut_bin_certificate_sound certificate4500 profilesValid4500 numericValid4500 valid4500

def retention4501 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid4501 : retention4501.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid4501 : retention4501.NumericValid := by decide +kernel
def certificate4501 : RatCutBinCertificate := ⟨⟨retention4501,(179542291632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(993297418201149077/1000000000000000000)⟩,(999982263187576019/1000000000000000000),(6027155849895917/100000000000000000),(380684556353840551/500000000000000000),(186173644535777271/250000000000000000)⟩
theorem valid4501 : certificate4501.Valid := by decide +kernel
theorem sound4501 : certificate4501.Sound := rat_cut_bin_certificate_sound certificate4501 profilesValid4501 numericValid4501 valid4501

def retention4502 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(677110354556920307/11416785527815779703113),(134081258328103031/200000000000000000),4,(6344415402234517908861074293500290191/2681625166562060620000000000000000000),false,MergedCutProfiles.Batch650.profile26018,(fun _ => MergedCutProfiles.Batch650.profile26018)⟩
theorem profilesValid4502 : retention4502.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26018
theorem numericValid4502 : retention4502.NumericValid := by decide +kernel
def certificate4502 : RatCutBinCertificate := ⟨⟨retention4502,(176989929632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(146820544450579273/62500000000000000)⟩,(49999125766653841/50000000000000000),(824840627155869991/1000000000000000000),(8161931408130527/500000000000000000),(3932115496925257/500000000000000000)⟩
theorem valid4502 : certificate4502.Valid := by decide +kernel
theorem sound4502 : certificate4502.Sound := rat_cut_bin_certificate_sound certificate4502 profilesValid4502 numericValid4502 valid4502

def retention4503 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(466657754146546945/3805595175938593234371),(677110354556920307/1000000000000000000),4,(1283124258511633832420008024463429339/541688283645536245600000000000000000),false,MergedCutProfiles.Batch650.profile26019,(fun _ => MergedCutProfiles.Batch650.profile26019)⟩
theorem profilesValid4503 : retention4503.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26019
theorem numericValid4503 : retention4503.NumericValid := by decide +kernel
def certificate4503 : RatCutBinCertificate := ⟨⟨retention4503,(176989929632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(73499827147490913/31250000000000000)⟩,(49999125766653841/50000000000000000),(821376104402183001/1000000000000000000),(8499147531721419/500000000000000000),(8211963075231387/1000000000000000000)⟩
theorem valid4503 : certificate4503.Valid := by decide +kernel
theorem sound4503 : certificate4503.Sound := rat_cut_bin_certificate_sound certificate4503 profilesValid4503 numericValid4503 valid4503

def retention4504 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(64000000000000000000/11416785527815779703113),(279994652487928167/200000000000000000),(13/5),(12994395093607862408773478176636990859/5599893049758563340000000000000000000),false,MergedCutProfiles.Batch650.profile26017,(fun _ => MergedCutProfiles.Batch650.profile26017)⟩
theorem profilesValid4504 : retention4504.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26017
theorem numericValid4504 : retention4504.NumericValid := by decide +kernel
def certificate4504 : RatCutBinCertificate := ⟨⟨retention4504,(176989929632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(1154790376597016899/500000000000000000)⟩,(49999125766653841/50000000000000000),(353566816636305557/500000000000000000),(23909688614008563/500000000000000000),(34144415163939189/1000000000000000000)⟩
theorem valid4504 : certificate4504.Valid := by decide +kernel
theorem sound4504 : certificate4504.Sound := rat_cut_bin_certificate_sound certificate4504 profilesValid4504 numericValid4504 valid4504

def retention4505 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/40),64,1,(2163423956780994486113237086399372599/1000000000000000000000000000000000000),false,MergedCutProfiles.Batch650.profile26020,(fun _ => MergedCutProfiles.Batch650.profile26020)⟩
theorem profilesValid4505 : retention4505.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26020
theorem numericValid4505 : retention4505.NumericValid := by decide +kernel
def certificate4505 : RatCutBinCertificate := ⟨⟨retention4505,(176989929632895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(1079617505605370897/500000000000000000)⟩,(49999125766653841/50000000000000000),(15740733492152563/25000000000000000),(19772256867027123/250000000000000000),(16519541405623933/100000000000000000)⟩
theorem valid4505 : certificate4505.Valid := by decide +kernel
theorem sound4505 : certificate4505.Sound := rat_cut_bin_certificate_sound certificate4505 profilesValid4505 numericValid4505 valid4505

def retention4506 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(74343030924939515/1155016623011647602451),(6303104825147587/10000000000000000),4,(5843436067847183179540641224626938471/2521241930059034800000000000000000000),true,MergedCutProfiles.Batch650.profile26021,![MergedCutProfiles.Batch650.profile26021,MergedCutProfiles.Batch650.profile26022,MergedCutProfiles.Batch650.profile26023,MergedCutProfiles.Batch650.profile26024,MergedCutProfiles.Batch650.profile26025,MergedCutProfiles.Batch650.profile26026,MergedCutProfiles.Batch650.profile26026,MergedCutProfiles.Batch650.profile26027,MergedCutProfiles.Batch650.profile26028,MergedCutProfiles.Batch650.profile26028,MergedCutProfiles.Batch650.profile26029,MergedCutProfiles.Batch650.profile26030,MergedCutProfiles.Batch650.profile26030,MergedCutProfiles.Batch650.profile26031,MergedCutProfiles.Batch650.profile26031,MergedCutProfiles.Batch650.profile26032]⟩
theorem profilesValid4506 : retention4506.ProfilesValid := by
  change ∀ j : Fin 16, (retention4506.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch650.valid26021
  · exact MergedCutProfiles.Batch650.valid26022
  · exact MergedCutProfiles.Batch650.valid26023
  · exact MergedCutProfiles.Batch650.valid26024
  · exact MergedCutProfiles.Batch650.valid26025
  · exact MergedCutProfiles.Batch650.valid26026
  · exact MergedCutProfiles.Batch650.valid26026
  · exact MergedCutProfiles.Batch650.valid26027
  · exact MergedCutProfiles.Batch650.valid26028
  · exact MergedCutProfiles.Batch650.valid26028
  · exact MergedCutProfiles.Batch650.valid26029
  · exact MergedCutProfiles.Batch650.valid26030
  · exact MergedCutProfiles.Batch650.valid26030
  · exact MergedCutProfiles.Batch650.valid26031
  · exact MergedCutProfiles.Batch650.valid26031
  · exact MergedCutProfiles.Batch650.valid26032
theorem numericValid4506 : retention4506.NumericValid := by decide +kernel
def certificate4506 : RatCutBinCertificate := ⟨⟨retention4506,(1902011081711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(1149094377284723/500000000000000)⟩,(999979676236103069/1000000000000000000),(496742881322839251/1000000000000000000),(19461830921769051/125000000000000000),(72850434514499153/1000000000000000000)⟩
theorem valid4506 : certificate4506.Valid := by decide +kernel
theorem sound4506 : certificate4506.Sound := rat_cut_bin_certificate_sound certificate4506 profilesValid4506 numericValid4506 valid4506

def retention4507 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(139370587000000000/1155016623011647602451),(133817455664891127/200000000000000000),4,(604913788867269900619/256000000000000000000),true,MergedCutProfiles.Batch650.profile26022,![MergedCutProfiles.Batch650.profile26022,MergedCutProfiles.Batch650.profile26023,MergedCutProfiles.Batch650.profile26025,MergedCutProfiles.Batch650.profile26027,MergedCutProfiles.Batch650.profile26028,MergedCutProfiles.Batch650.profile26029,MergedCutProfiles.Batch650.profile26030,MergedCutProfiles.Batch650.profile26031,MergedCutProfiles.Batch650.profile26032,MergedCutProfiles.Batch457.profile18312,MergedCutProfiles.Batch650.profile26033,MergedCutProfiles.Batch650.profile26034,MergedCutProfiles.Batch650.profile26035,MergedCutProfiles.Batch650.profile26036,MergedCutProfiles.Batch650.profile26036,MergedCutProfiles.Batch650.profile26037]⟩
theorem profilesValid4507 : retention4507.ProfilesValid := by
  change ∀ j : Fin 16, (retention4507.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch650.valid26022
  · exact MergedCutProfiles.Batch650.valid26023
  · exact MergedCutProfiles.Batch650.valid26025
  · exact MergedCutProfiles.Batch650.valid26027
  · exact MergedCutProfiles.Batch650.valid26028
  · exact MergedCutProfiles.Batch650.valid26029
  · exact MergedCutProfiles.Batch650.valid26030
  · exact MergedCutProfiles.Batch650.valid26031
  · exact MergedCutProfiles.Batch650.valid26032
  · exact MergedCutProfiles.Batch457.valid18312
  · exact MergedCutProfiles.Batch650.valid26033
  · exact MergedCutProfiles.Batch650.valid26034
  · exact MergedCutProfiles.Batch650.valid26035
  · exact MergedCutProfiles.Batch650.valid26036
  · exact MergedCutProfiles.Batch650.valid26036
  · exact MergedCutProfiles.Batch650.valid26037
theorem numericValid4507 : retention4507.NumericValid := by decide +kernel
def certificate4507 : RatCutBinCertificate := ⟨⟨retention4507,(1902011081711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(585862906901954913/250000000000000000)⟩,(999979676236103069/1000000000000000000),(468737503732929207/1000000000000000000),(687867757734267/3906250000000000),(16927436179838721/200000000000000000)⟩
theorem valid4507 : certificate4507.Valid := by decide +kernel
theorem sound4507 : certificate4507.Sound := rat_cut_bin_certificate_sound certificate4507 profilesValid4507 numericValid4507 valid4507

def retention4508 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(2721425663011490872/10395149607104828422059),(1254335283/1000000000),(5/2),(82349364255550907820046688579390991/34842646750000000000000000000000000),true,MergedCutProfiles.Batch650.profile26024,![MergedCutProfiles.Batch650.profile26024,MergedCutProfiles.Batch650.profile26027,MergedCutProfiles.Batch650.profile26030,MergedCutProfiles.Batch650.profile26032,MergedCutProfiles.Batch650.profile26033,MergedCutProfiles.Batch650.profile26035,MergedCutProfiles.Batch650.profile26036,MergedCutProfiles.Batch650.profile26038,MergedCutProfiles.Batch457.profile18313,MergedCutProfiles.Batch650.profile26039,MergedCutProfiles.Batch651.profile26040,MergedCutProfiles.Batch323.profile12934,MergedCutProfiles.Batch651.profile26041,MergedCutProfiles.Batch457.profile18314,MergedCutProfiles.Batch651.profile26042,MergedCutProfiles.Batch651.profile26043]⟩
theorem profilesValid4508 : retention4508.ProfilesValid := by
  change ∀ j : Fin 16, (retention4508.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch650.valid26024
  · exact MergedCutProfiles.Batch650.valid26027
  · exact MergedCutProfiles.Batch650.valid26030
  · exact MergedCutProfiles.Batch650.valid26032
  · exact MergedCutProfiles.Batch650.valid26033
  · exact MergedCutProfiles.Batch650.valid26035
  · exact MergedCutProfiles.Batch650.valid26036
  · exact MergedCutProfiles.Batch650.valid26038
  · exact MergedCutProfiles.Batch457.valid18313
  · exact MergedCutProfiles.Batch650.valid26039
  · exact MergedCutProfiles.Batch651.valid26040
  · exact MergedCutProfiles.Batch323.valid12934
  · exact MergedCutProfiles.Batch651.valid26041
  · exact MergedCutProfiles.Batch457.valid18314
  · exact MergedCutProfiles.Batch651.valid26042
  · exact MergedCutProfiles.Batch651.valid26043
theorem numericValid4508 : retention4508.NumericValid := by decide +kernel
def certificate4508 : RatCutBinCertificate := ⟨⟨retention4508,(1902011081711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(2351281622597243067/1000000000000000000)⟩,(999979676236103069/1000000000000000000),(328009285510013947/1000000000000000000),(9573238489325943/31250000000000000),(11081934445783567/50000000000000000)⟩
theorem valid4508 : certificate4508.Valid := by decide +kernel
theorem sound4508 : certificate4508.Sound := rat_cut_bin_certificate_sound certificate4508 profilesValid4508 numericValid4508 valid4508

def retention4509 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(64000000000000000000/10395149607104828422059),(340178207876436359/125000000000000000),(31/20),(45201420886569005039/20000000000000000000),true,MergedCutProfiles.Batch323.profile12935,![MergedCutProfiles.Batch323.profile12935,MergedCutProfiles.Batch458.profile18332,MergedCutProfiles.Batch323.profile12938,MergedCutProfiles.Batch323.profile12939,MergedCutProfiles.Batch458.profile18330,MergedCutProfiles.Batch323.profile12941,MergedCutProfiles.Batch029.profile1168,MergedCutProfiles.Batch651.profile26044,MergedCutProfiles.Batch029.profile1181,MergedCutProfiles.Batch029.profile1195,MergedCutProfiles.Batch028.profile1158,MergedCutProfiles.Batch323.profile12955,MergedCutProfiles.Batch323.profile12956,MergedCutProfiles.Batch029.profile1170,MergedCutProfiles.Batch651.profile26045,MergedCutProfiles.Batch028.profile1149]⟩
theorem profilesValid4509 : retention4509.ProfilesValid := by
  change ∀ j : Fin 16, (retention4509.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12935
  · exact MergedCutProfiles.Batch458.valid18332
  · exact MergedCutProfiles.Batch323.valid12938
  · exact MergedCutProfiles.Batch323.valid12939
  · exact MergedCutProfiles.Batch458.valid18330
  · exact MergedCutProfiles.Batch323.valid12941
  · exact MergedCutProfiles.Batch029.valid1168
  · exact MergedCutProfiles.Batch651.valid26044
  · exact MergedCutProfiles.Batch029.valid1181
  · exact MergedCutProfiles.Batch029.valid1195
  · exact MergedCutProfiles.Batch028.valid1158
  · exact MergedCutProfiles.Batch323.valid12955
  · exact MergedCutProfiles.Batch323.valid12956
  · exact MergedCutProfiles.Batch029.valid1170
  · exact MergedCutProfiles.Batch651.valid26045
  · exact MergedCutProfiles.Batch028.valid1149
theorem numericValid4509 : retention4509.NumericValid := by decide +kernel
def certificate4509 : RatCutBinCertificate := ⟨⟨retention4509,(1902011081711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(1126258780635723257/500000000000000000)⟩,(999979676236103069/1000000000000000000),(126429754470904777/500000000000000000),(199699836159983053/500000000000000000),(53960855519475403/125000000000000000)⟩
theorem valid4509 : certificate4509.Valid := by decide +kernel
theorem sound4509 : certificate4509.Sound := rat_cut_bin_certificate_sound certificate4509 profilesValid4509 numericValid4509 valid4509

def retention4510 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid4510 : retention4510.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid4510 : retention4510.NumericValid := by decide +kernel
def certificate4510 : RatCutBinCertificate := ⟨⟨retention4510,(1902011081711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(248168784041160859/250000000000000000)⟩,(999979676236103069/1000000000000000000),(203730701194367763/500000000000000000),(226714984407023737/1000000000000000000),(55403096418405673/250000000000000000)⟩
theorem valid4510 : certificate4510.Valid := by decide +kernel
theorem sound4510 : certificate4510.Sound := rat_cut_bin_certificate_sound certificate4510 profilesValid4510 numericValid4510 valid4510

def retention4511 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(64000000000000000000/10395149607104828422059),(2308776454547314993/125000000000000000),1,(10362119802286609524361158905257345263/4617552909094629986000000000000000000),false,MergedCutProfiles.Batch651.profile26046,(fun _ => MergedCutProfiles.Batch651.profile26046)⟩
theorem profilesValid4511 : retention4511.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26046
theorem numericValid4511 : retention4511.NumericValid := by decide +kernel
def certificate4511 : RatCutBinCertificate := ⟨⟨retention4511,(1796238348711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(139966843046640073/62500000000000000)⟩,(124997600807666849/125000000000000000),(13187954280119459/500000000000000000),(854892757260062661/1000000000000000000),(1707444821335148379/1000000000000000000)⟩
theorem valid4511 : certificate4511.Valid := by decide +kernel
theorem sound4511 : certificate4511.Sound := rat_cut_bin_certificate_sound certificate4511 profilesValid4511 numericValid4511 valid4511

def certificates : List RatCutBinCertificate := [certificate4500,certificate4501,certificate4502,certificate4503,certificate4504,certificate4505,certificate4506,certificate4507,certificate4508,certificate4509,certificate4510,certificate4511]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4500,List.forall_mem_cons.mpr ⟨sound4501,List.forall_mem_cons.mpr ⟨sound4502,List.forall_mem_cons.mpr ⟨sound4503,List.forall_mem_cons.mpr ⟨sound4504,List.forall_mem_cons.mpr ⟨sound4505,List.forall_mem_cons.mpr ⟨sound4506,List.forall_mem_cons.mpr ⟨sound4507,List.forall_mem_cons.mpr ⟨sound4508,List.forall_mem_cons.mpr ⟨sound4509,List.forall_mem_cons.mpr ⟨sound4510,List.forall_mem_cons.mpr ⟨sound4511,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch375
