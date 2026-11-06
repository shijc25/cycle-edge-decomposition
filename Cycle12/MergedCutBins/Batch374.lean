import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch026
import Cycle12.MergedCutProfiles.Batch027
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch322
import Cycle12.MergedCutProfiles.Batch457
import Cycle12.MergedCutProfiles.Batch583
import Cycle12.MergedCutProfiles.Batch650

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch374

def retention4488 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid4488 : retention4488.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid4488 : retention4488.NumericValid := by decide +kernel
def certificate4488 : RatCutBinCertificate := ⟨⟨retention4488,(188929242828945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(993432007458159371/1000000000000000000)⟩,(199996563745740623/200000000000000000),(51047030428541503/125000000000000000),(22589468767083067/100000000000000000),(55244259099518359/250000000000000000)⟩
theorem valid4488 : certificate4488.Valid := by decide +kernel
theorem sound4488 : certificate4488.Sound := rat_cut_bin_certificate_sound certificate4488 profilesValid4488 numericValid4488 valid4488

def retention4489 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(64000000000000000000/12590448292418869216701),(9013932638405853357/500000000000000000),1,(126844256032531108833953624539958899/56337078990036583481250000000000000),false,MergedCutProfiles.Batch650.profile26001,(fun _ => MergedCutProfiles.Batch650.profile26001)⟩
theorem profilesValid4489 : retention4489.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26001
theorem numericValid4489 : retention4489.NumericValid := by decide +kernel
def certificate4489 : RatCutBinCertificate := ⟨⟨retention4489,(179450427528945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(2247616562547733451/1000000000000000000)⟩,(999983680734712649/1000000000000000000),(26994941937396767/1000000000000000000),(853064988221766929/1000000000000000000),(852393593096048781/500000000000000000)⟩
theorem valid4489 : certificate4489.Valid := by decide +kernel
theorem sound4489 : certificate4489.Sound := rat_cut_bin_certificate_sound certificate4489 profilesValid4489 numericValid4489 valid4489

def retention4490 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid4490 : retention4490.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid4490 : retention4490.NumericValid := by decide +kernel
def certificate4490 : RatCutBinCertificate := ⟨⟨retention4490,(179450427528945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(993638376041292881/1000000000000000000)⟩,(999983680734712649/1000000000000000000),(61062736772745093/1000000000000000000),(759334397763963287/1000000000000000000),(74295652992126173/100000000000000000)⟩
theorem valid4490 : certificate4490.Valid := by decide +kernel
theorem sound4490 : certificate4490.Sound := rat_cut_bin_certificate_sound certificate4490 profilesValid4490 numericValid4490 valid4490

def retention4491 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(676739478649117208/12590448292418869216701),(83754885971425397/125000000000000000),4,(1267817910828492736068769404643235451/536031270217122540800000000000000000),false,MergedCutProfiles.Batch650.profile26002,(fun _ => MergedCutProfiles.Batch650.profile26002)⟩
theorem profilesValid4491 : retention4491.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26002
theorem numericValid4491 : retention4491.NumericValid := by decide +kernel
def certificate4491 : RatCutBinCertificate := ⟨⟨retention4491,(172547808128945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(2350167398058701877/1000000000000000000)⟩,(999984308460759039/1000000000000000000),(166350589696440583/200000000000000000),(3755418437355473/250000000000000000),(226212853051939/31250000000000000)⟩
theorem valid4491 : certificate4491.Valid := by decide +kernel
theorem sound4491 : certificate4491.Sound := rat_cut_bin_certificate_sound certificate4491 profilesValid4491 numericValid4491 valid4491

def retention4492 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(485339947710298894/4196816097472956405567),(84592434831139651/125000000000000000),4,(320506499445070713065633004761091459/135347895729823441600000000000000000),false,MergedCutProfiles.Batch650.profile26003,(fun _ => MergedCutProfiles.Batch650.profile26003)⟩
theorem profilesValid4492 : retention4492.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26003
theorem numericValid4492 : retention4492.NumericValid := by decide +kernel
def certificate4492 : RatCutBinCertificate := ⟨⟨retention4492,(172547808128945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(235299327843243731/100000000000000000)⟩,(999984308460759039/1000000000000000000),(41410963063752291/50000000000000000),(1568016602343203/100000000000000000),(3788542843864743/500000000000000000)⟩
theorem valid4492 : certificate4492.Valid := by decide +kernel
theorem sound4492 : certificate4492.Sound := rat_cut_bin_certificate_sound certificate4492 profilesValid4492 numericValid4492 valid4492

def retention4493 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(64000000000000000000/12590448292418869216701),(728009921565448341/500000000000000000),(5/2),(13529910276880251439491909710673885551/5824079372523586728000000000000000000),false,MergedCutProfiles.Batch650.profile26001,(fun _ => MergedCutProfiles.Batch650.profile26001)⟩
theorem profilesValid4493 : retention4493.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26001
theorem numericValid4493 : retention4493.NumericValid := by decide +kernel
def certificate4493 : RatCutBinCertificate := ⟨⟨retention4493,(172547808128945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(144606684438152849/62500000000000000)⟩,(999984308460759039/1000000000000000000),(352157173194412439/500000000000000000),(48801988168255417/1000000000000000000),(36009245462421553/1000000000000000000)⟩
theorem valid4493 : certificate4493.Valid := by decide +kernel
theorem sound4493 : certificate4493.Sound := rat_cut_bin_certificate_sound certificate4493 profilesValid4493 numericValid4493 valid4493

def retention4494 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/40),64,1,(138406025264738026274516158729001450799/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch650.profile26004,(fun _ => MergedCutProfiles.Batch650.profile26004)⟩
theorem profilesValid4494 : retention4494.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26004
theorem numericValid4494 : retention4494.NumericValid := by decide +kernel
def certificate4494 : RatCutBinCertificate := ⟨⟨retention4494,(172547808128945551/100000000000000000),(1860584005120499/100000000000000000),(4272969246167985191/500000000000000000),(108113375975837050826623/1000000000000000000),(86353500401551903/40000000000000000)⟩,(999984308460759039/1000000000000000000),(629352718199315219/1000000000000000000),(123776656207777/1562500000000000),(41358417788547903/250000000000000000)⟩
theorem valid4494 : certificate4494.Valid := by decide +kernel
theorem sound4494 : certificate4494.Sound := rat_cut_bin_certificate_sound certificate4494 profilesValid4494 numericValid4494 valid4494

def retention4495 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(76948908438978181/1268531725312864411457),(313473793444522917/500000000000000000),4,(295940945742696445893/128000000000000000000),true,MergedCutProfiles.Batch650.profile26005,![MergedCutProfiles.Batch650.profile26005,MergedCutProfiles.Batch650.profile26006,MergedCutProfiles.Batch650.profile26007,MergedCutProfiles.Batch650.profile26008,MergedCutProfiles.Batch583.profile23342,MergedCutProfiles.Batch650.profile26009,MergedCutProfiles.Batch650.profile26010,MergedCutProfiles.Batch583.profile23343,MergedCutProfiles.Batch583.profile23343,MergedCutProfiles.Batch650.profile26011,MergedCutProfiles.Batch650.profile26012,MergedCutProfiles.Batch650.profile26012,MergedCutProfiles.Batch583.profile23344,MergedCutProfiles.Batch583.profile23344,MergedCutProfiles.Batch650.profile26013,MergedCutProfiles.Batch650.profile26013]⟩
theorem profilesValid4495 : retention4495.ProfilesValid := by
  change ∀ j : Fin 16, (retention4495.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch650.valid26005
  · exact MergedCutProfiles.Batch650.valid26006
  · exact MergedCutProfiles.Batch650.valid26007
  · exact MergedCutProfiles.Batch650.valid26008
  · exact MergedCutProfiles.Batch583.valid23342
  · exact MergedCutProfiles.Batch650.valid26009
  · exact MergedCutProfiles.Batch650.valid26010
  · exact MergedCutProfiles.Batch583.valid23343
  · exact MergedCutProfiles.Batch583.valid23343
  · exact MergedCutProfiles.Batch650.valid26011
  · exact MergedCutProfiles.Batch650.valid26012
  · exact MergedCutProfiles.Batch650.valid26012
  · exact MergedCutProfiles.Batch583.valid23344
  · exact MergedCutProfiles.Batch583.valid23344
  · exact MergedCutProfiles.Batch650.valid26013
  · exact MergedCutProfiles.Batch650.valid26013
theorem numericValid4495 : retention4495.NumericValid := by decide +kernel
def certificate4495 : RatCutBinCertificate := ⟨⟨retention4495,(190367860332895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(1147008177600677821/500000000000000000)⟩,(999981193739547211/1000000000000000000),(500137694773973779/1000000000000000000),(19166366936523453/125000000000000000),(71567313541877273/1000000000000000000)⟩
theorem valid4495 : certificate4495.Valid := by decide +kernel
theorem sound4495 : certificate4495.Sound := rat_cut_bin_certificate_sound certificate4495 profilesValid4495 numericValid4495 valid4495

def retention4496 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1279741531000000000/11416785527815779703113),(692540175950803629/1000000000000000000),4,(38145045418293519657/16000000000000000000),true,MergedCutProfiles.Batch650.profile26006,![MergedCutProfiles.Batch650.profile26006,MergedCutProfiles.Batch650.profile26008,MergedCutProfiles.Batch650.profile26009,MergedCutProfiles.Batch650.profile26010,MergedCutProfiles.Batch650.profile26011,MergedCutProfiles.Batch650.profile26012,MergedCutProfiles.Batch583.profile23344,MergedCutProfiles.Batch650.profile26013,MergedCutProfiles.Batch457.profile18294,MergedCutProfiles.Batch650.profile26014,MergedCutProfiles.Batch650.profile26014,MergedCutProfiles.Batch583.profile23345,MergedCutProfiles.Batch583.profile23346,MergedCutProfiles.Batch583.profile23354,MergedCutProfiles.Batch583.profile23354,MergedCutProfiles.Batch583.profile23347]⟩
theorem profilesValid4496 : retention4496.ProfilesValid := by
  change ∀ j : Fin 16, (retention4496.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch650.valid26006
  · exact MergedCutProfiles.Batch650.valid26008
  · exact MergedCutProfiles.Batch650.valid26009
  · exact MergedCutProfiles.Batch650.valid26010
  · exact MergedCutProfiles.Batch650.valid26011
  · exact MergedCutProfiles.Batch650.valid26012
  · exact MergedCutProfiles.Batch583.valid23344
  · exact MergedCutProfiles.Batch650.valid26013
  · exact MergedCutProfiles.Batch457.valid18294
  · exact MergedCutProfiles.Batch650.valid26014
  · exact MergedCutProfiles.Batch650.valid26014
  · exact MergedCutProfiles.Batch583.valid23345
  · exact MergedCutProfiles.Batch583.valid23346
  · exact MergedCutProfiles.Batch583.valid23354
  · exact MergedCutProfiles.Batch583.valid23354
  · exact MergedCutProfiles.Batch583.valid23347
theorem numericValid4496 : retention4496.NumericValid := by decide +kernel
def certificate4496 : RatCutBinCertificate := ⟨⟨retention4496,(190367860332895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(2366043055370311467/1000000000000000000)⟩,(999981193739547211/1000000000000000000),(45487855494847231/100000000000000000),(37360417014621731/200000000000000000),(45525484598195281/500000000000000000)⟩
theorem valid4496 : certificate4496.Valid := by decide +kernel
theorem sound4496 : certificate4496.Sound := rat_cut_bin_certificate_sound certificate4496 profilesValid4496 numericValid4496 valid4496

def retention4497 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(15138081727331752294/11416785527815779703113),(1279741531/1000000000),(49/20),(18669274898210096187/8000000000000000000),true,MergedCutProfiles.Batch583.profile23345,![MergedCutProfiles.Batch583.profile23345,MergedCutProfiles.Batch583.profile23355,MergedCutProfiles.Batch583.profile23353,MergedCutProfiles.Batch322.profile12908,MergedCutProfiles.Batch457.profile18298,MergedCutProfiles.Batch583.profile23358,MergedCutProfiles.Batch650.profile26015,MergedCutProfiles.Batch322.profile12909,MergedCutProfiles.Batch026.profile1070,MergedCutProfiles.Batch457.profile18303,MergedCutProfiles.Batch457.profile18304,MergedCutProfiles.Batch322.profile12910,MergedCutProfiles.Batch457.profile18306,MergedCutProfiles.Batch650.profile26016,MergedCutProfiles.Batch027.profile1086,MergedCutProfiles.Batch322.profile12911]⟩
theorem profilesValid4497 : retention4497.ProfilesValid := by
  change ∀ j : Fin 16, (retention4497.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch583.valid23345
  · exact MergedCutProfiles.Batch583.valid23355
  · exact MergedCutProfiles.Batch583.valid23353
  · exact MergedCutProfiles.Batch322.valid12908
  · exact MergedCutProfiles.Batch457.valid18298
  · exact MergedCutProfiles.Batch583.valid23358
  · exact MergedCutProfiles.Batch650.valid26015
  · exact MergedCutProfiles.Batch322.valid12909
  · exact MergedCutProfiles.Batch026.valid1070
  · exact MergedCutProfiles.Batch457.valid18303
  · exact MergedCutProfiles.Batch457.valid18304
  · exact MergedCutProfiles.Batch322.valid12910
  · exact MergedCutProfiles.Batch457.valid18306
  · exact MergedCutProfiles.Batch650.valid26016
  · exact MergedCutProfiles.Batch027.valid1086
  · exact MergedCutProfiles.Batch322.valid12911
theorem numericValid4497 : retention4497.NumericValid := by decide +kernel
def certificate4497 : RatCutBinCertificate := ⟨⟨retention4497,(190367860332895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(2322620713867288583/1000000000000000000)⟩,(999981193739547211/1000000000000000000),(13167966880122809/40000000000000000),(305019752427394741/1000000000000000000),(222024027171648271/1000000000000000000)⟩
theorem valid4497 : certificate4497.Valid := by decide +kernel
theorem sound4497 : certificate4497.Sound := rat_cut_bin_certificate_sound certificate4497 profilesValid4497 numericValid4497 valid4497

def retention4498 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(64000000000000000000/11416785527815779703113),(7569040863665876147/500000000000000000),1,(27038408799108696467391261139890668763/12110465381865401835200000000000000000),false,MergedCutProfiles.Batch650.profile26017,(fun _ => MergedCutProfiles.Batch650.profile26017)⟩
theorem profilesValid4498 : retention4498.ProfilesValid := by
  exact MergedCutProfiles.Batch650.valid26017
theorem numericValid4498 : retention4498.NumericValid := by decide +kernel
def certificate4498 : RatCutBinCertificate := ⟨⟨retention4498,(190367860332895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(1114071317334147319/500000000000000000)⟩,(999981193739547211/1000000000000000000),(38427702498696947/200000000000000000),(490561399128604279/1000000000000000000),(952781627776978717/1000000000000000000)⟩
theorem valid4498 : certificate4498.Valid := by decide +kernel
theorem sound4498 : certificate4498.Sound := rat_cut_bin_certificate_sound certificate4498 profilesValid4498 numericValid4498 valid4498

def retention4499 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid4499 : retention4499.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid4499 : retention4499.NumericValid := by decide +kernel
def certificate4499 : RatCutBinCertificate := ⟨⟨retention4499,(190367860332895587/100000000000000000),(10247703429141591/500000000000000000),(541228181487186109/62500000000000000),(49671218117945647540743/500000000000000000),(993041201826887619/1000000000000000000)⟩,(999981193739547211/1000000000000000000),(203611182969465803/500000000000000000),(226929655762279473/1000000000000000000),(221903116078457459/1000000000000000000)⟩
theorem valid4499 : certificate4499.Valid := by decide +kernel
theorem sound4499 : certificate4499.Sound := rat_cut_bin_certificate_sound certificate4499 profilesValid4499 numericValid4499 valid4499

def certificates : List RatCutBinCertificate := [certificate4488,certificate4489,certificate4490,certificate4491,certificate4492,certificate4493,certificate4494,certificate4495,certificate4496,certificate4497,certificate4498,certificate4499]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4488,List.forall_mem_cons.mpr ⟨sound4489,List.forall_mem_cons.mpr ⟨sound4490,List.forall_mem_cons.mpr ⟨sound4491,List.forall_mem_cons.mpr ⟨sound4492,List.forall_mem_cons.mpr ⟨sound4493,List.forall_mem_cons.mpr ⟨sound4494,List.forall_mem_cons.mpr ⟨sound4495,List.forall_mem_cons.mpr ⟨sound4496,List.forall_mem_cons.mpr ⟨sound4497,List.forall_mem_cons.mpr ⟨sound4498,List.forall_mem_cons.mpr ⟨sound4499,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch374
