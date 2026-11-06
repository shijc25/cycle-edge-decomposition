import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch186
import Cycle12.MergedCutProfiles.Batch187

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch093

def retention1116 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(1/2),64,1,(63849911830755860292934404689492983111/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch186.profile7443,(fun _ => MergedCutProfiles.Batch186.profile7443)⟩
theorem profilesValid1116 : retention1116.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7443
theorem numericValid1116 : retention1116.NumericValid := by decide +kernel
def certificate1116 : RatCutBinCertificate := ⟨⟨retention1116,(1115141502066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(97509127745482499/100000000000000000)⟩,(39660699087471147/40000000000000000),(439645867670463323/1000000000000000000),(199059045183512161/1000000000000000000),(23693898183024053/125000000000000000)⟩
theorem valid1116 : certificate1116.Valid := by decide +kernel
theorem sound1116 : certificate1116.Sound := rat_cut_bin_certificate_sound certificate1116 profilesValid1116 numericValid1116 valid1116

def retention1117 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(1814054873059968295/3952625591985861747),(114126274841736759/31250000000000000),(6/5),(32737776104800670998931502550564690053/30433673291129802400000000000000000000),false,MergedCutProfiles.Batch186.profile7444,(fun _ => MergedCutProfiles.Batch186.profile7444)⟩
theorem profilesValid1117 : retention1117.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7444
theorem numericValid1117 : retention1117.NumericValid := by decide +kernel
def certificate1117 : RatCutBinCertificate := ⟨⟨retention1117,(1290238765066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(41775078330880103/40000000000000000)⟩,(990183392882904167/1000000000000000000),(193195925047086857/500000000000000000),(123092427317477163/500000000000000000),(176831462030898719/1000000000000000000)⟩
theorem valid1117 : certificate1117.Valid := by decide +kernel
theorem sound1117 : certificate1117.Sound := rat_cut_bin_certificate_sound certificate1117 profilesValid1117 numericValid1117 valid1117

def retention1118 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(3928722967340564605/7905251183971723494),(362810974611993659/50000000000000000),(21/20),(1801913673581823420838231375164699329/1814054873059968295000000000000000000),false,MergedCutProfiles.Batch186.profile7445,(fun _ => MergedCutProfiles.Batch186.profile7445)⟩
theorem profilesValid1118 : retention1118.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7445
theorem numericValid1118 : retention1118.NumericValid := by decide +kernel
def certificate1118 : RatCutBinCertificate := ⟨⟨retention1118,(1290238765066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(482946657222730967/500000000000000000)⟩,(990183392882904167/1000000000000000000),(417788112897462333/1000000000000000000),(339958798029339/1562500000000000),(176725048252228769/1000000000000000000)⟩
theorem valid1118 : certificate1118.Valid := by decide +kernel
theorem sound1118 : certificate1118.Sound := rat_cut_bin_certificate_sound certificate1118 profilesValid1118 numericValid1118 valid1118

def retention1119 : RatCutRetentionCertificate := ⟨(27/500),(217/4000),(1/2),(785744593468112921/100000000000000000),(21/20),(124434876258613389852658739616392668839/125719134954898067360000000000000000000),false,MergedCutProfiles.Batch186.profile7443,(fun _ => MergedCutProfiles.Batch186.profile7443)⟩
theorem profilesValid1119 : retention1119.ProfilesValid := by
  exact MergedCutProfiles.Batch186.valid7443
theorem numericValid1119 : retention1119.NumericValid := by decide +kernel
def certificate1119 : RatCutBinCertificate := ⟨⟨retention1119,(1290238765066766229/500000000000000000),(5769223604251667/40000000000000000),(14256515711461654539/1000000000000000000),(225734409531058096999/1000000000000000000),(962371041483406527/1000000000000000000)⟩,(990183392882904167/1000000000000000000),(83863443039688069/200000000000000000),(216241890524605423/1000000000000000000),(176529201506482489/1000000000000000000)⟩
theorem valid1119 : certificate1119.Valid := by decide +kernel
theorem sound1119 : certificate1119.Sound := rat_cut_bin_certificate_sound certificate1119 profilesValid1119 numericValid1119 valid1119

def retention1120 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(40038423329774504/711032940632893685),(846475032567901681/1000000000000000000),(57/20),(2603936721526604447289/1280000000000000000000),true,MergedCutProfiles.Batch186.profile7446,![MergedCutProfiles.Batch186.profile7446,MergedCutProfiles.Batch186.profile7447,MergedCutProfiles.Batch186.profile7448,MergedCutProfiles.Batch186.profile7449,MergedCutProfiles.Batch186.profile7450,MergedCutProfiles.Batch186.profile7451,MergedCutProfiles.Batch186.profile7452,MergedCutProfiles.Batch186.profile7453,MergedCutProfiles.Batch186.profile7454,MergedCutProfiles.Batch186.profile7455,MergedCutProfiles.Batch186.profile7456,MergedCutProfiles.Batch186.profile7457,MergedCutProfiles.Batch186.profile7458,MergedCutProfiles.Batch186.profile7459,MergedCutProfiles.Batch186.profile7460,MergedCutProfiles.Batch186.profile7461]⟩
theorem profilesValid1120 : retention1120.ProfilesValid := by
  change ∀ j : Fin 16, (retention1120.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch186.valid7446
  · exact MergedCutProfiles.Batch186.valid7447
  · exact MergedCutProfiles.Batch186.valid7448
  · exact MergedCutProfiles.Batch186.valid7449
  · exact MergedCutProfiles.Batch186.valid7450
  · exact MergedCutProfiles.Batch186.valid7451
  · exact MergedCutProfiles.Batch186.valid7452
  · exact MergedCutProfiles.Batch186.valid7453
  · exact MergedCutProfiles.Batch186.valid7454
  · exact MergedCutProfiles.Batch186.valid7455
  · exact MergedCutProfiles.Batch186.valid7456
  · exact MergedCutProfiles.Batch186.valid7457
  · exact MergedCutProfiles.Batch186.valid7458
  · exact MergedCutProfiles.Batch186.valid7459
  · exact MergedCutProfiles.Batch186.valid7460
  · exact MergedCutProfiles.Batch186.valid7461
theorem numericValid1120 : retention1120.NumericValid := by decide +kernel
def certificate1120 : RatCutBinCertificate := ⟨⟨retention1120,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(984740802061069123/500000000000000000)⟩,(495731555071820573/500000000000000000),(181637789580823219/500000000000000000),(26886993126301473/100000000000000000),(28591934977262189/200000000000000000)⟩
theorem valid1120 : certificate1120.Valid := by decide +kernel
theorem sound1120 : certificate1120.Sound := rat_cut_bin_certificate_sound certificate1120 profilesValid1120 numericValid1120 valid1120

def retention1121 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(564812106189619942/7821362346961830535),(55052832078439943/62500000000000000),(11/4),(15887931127208498377/8000000000000000000),true,MergedCutProfiles.Batch186.profile7462,![MergedCutProfiles.Batch186.profile7462,MergedCutProfiles.Batch186.profile7463,MergedCutProfiles.Batch186.profile7464,MergedCutProfiles.Batch186.profile7465,MergedCutProfiles.Batch186.profile7466,MergedCutProfiles.Batch186.profile7467,MergedCutProfiles.Batch186.profile7454,MergedCutProfiles.Batch186.profile7468,MergedCutProfiles.Batch186.profile7469,MergedCutProfiles.Batch186.profile7470,MergedCutProfiles.Batch186.profile7471,MergedCutProfiles.Batch186.profile7472,MergedCutProfiles.Batch186.profile7473,MergedCutProfiles.Batch186.profile7474,MergedCutProfiles.Batch186.profile7475,MergedCutProfiles.Batch186.profile7476]⟩
theorem profilesValid1121 : retention1121.ProfilesValid := by
  change ∀ j : Fin 16, (retention1121.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch186.valid7462
  · exact MergedCutProfiles.Batch186.valid7463
  · exact MergedCutProfiles.Batch186.valid7464
  · exact MergedCutProfiles.Batch186.valid7465
  · exact MergedCutProfiles.Batch186.valid7466
  · exact MergedCutProfiles.Batch186.valid7467
  · exact MergedCutProfiles.Batch186.valid7454
  · exact MergedCutProfiles.Batch186.valid7468
  · exact MergedCutProfiles.Batch186.valid7469
  · exact MergedCutProfiles.Batch186.valid7470
  · exact MergedCutProfiles.Batch186.valid7471
  · exact MergedCutProfiles.Batch186.valid7472
  · exact MergedCutProfiles.Batch186.valid7473
  · exact MergedCutProfiles.Batch186.valid7474
  · exact MergedCutProfiles.Batch186.valid7475
  · exact MergedCutProfiles.Batch186.valid7476
theorem numericValid1121 : retention1121.NumericValid := by decide +kernel
def certificate1121 : RatCutBinCertificate := ⟨⟨retention1121,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(384684545328694537/200000000000000000)⟩,(495731555071820573/500000000000000000),(366045977985646027/1000000000000000000),(266075485971452001/1000000000000000000),(7146809108189479/50000000000000000)⟩
theorem valid1121 : certificate1121.Valid := by decide +kernel
theorem sound1121 : certificate1121.Sound := rat_cut_bin_certificate_sound certificate1121 profilesValid1121 numericValid1121 valid1121

def retention1122 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(1277193345218054994/7821362346961830535),(282406053094809971/250000000000000000),(11/5),(551516783749546988671/320000000000000000000),true,MergedCutProfiles.Batch186.profile7477,![MergedCutProfiles.Batch186.profile7477,MergedCutProfiles.Batch186.profile7478,MergedCutProfiles.Batch186.profile7479,MergedCutProfiles.Batch187.profile7480,MergedCutProfiles.Batch187.profile7481,MergedCutProfiles.Batch187.profile7482,MergedCutProfiles.Batch187.profile7483,MergedCutProfiles.Batch187.profile7484,MergedCutProfiles.Batch187.profile7485,MergedCutProfiles.Batch187.profile7486,MergedCutProfiles.Batch187.profile7487,MergedCutProfiles.Batch187.profile7488,MergedCutProfiles.Batch187.profile7489,MergedCutProfiles.Batch187.profile7490,MergedCutProfiles.Batch187.profile7491,MergedCutProfiles.Batch187.profile7492]⟩
theorem profilesValid1122 : retention1122.ProfilesValid := by
  change ∀ j : Fin 16, (retention1122.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch186.valid7477
  · exact MergedCutProfiles.Batch186.valid7478
  · exact MergedCutProfiles.Batch186.valid7479
  · exact MergedCutProfiles.Batch187.valid7480
  · exact MergedCutProfiles.Batch187.valid7481
  · exact MergedCutProfiles.Batch187.valid7482
  · exact MergedCutProfiles.Batch187.valid7483
  · exact MergedCutProfiles.Batch187.valid7484
  · exact MergedCutProfiles.Batch187.valid7485
  · exact MergedCutProfiles.Batch187.valid7486
  · exact MergedCutProfiles.Batch187.valid7487
  · exact MergedCutProfiles.Batch187.valid7488
  · exact MergedCutProfiles.Batch187.valid7489
  · exact MergedCutProfiles.Batch187.valid7490
  · exact MergedCutProfiles.Batch187.valid7491
  · exact MergedCutProfiles.Batch187.valid7492
theorem numericValid1122 : retention1122.NumericValid := by decide +kernel
def certificate1122 : RatCutBinCertificate := ⟨⟨retention1122,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(418358839329732829/250000000000000000)⟩,(495731555071820573/500000000000000000),(383767621870385081/1000000000000000000),(12434450487302701/50000000000000000),(143371505461543257/1000000000000000000)⟩
theorem valid1122 : certificate1122.Valid := by decide +kernel
theorem sound1122 : certificate1122.Sound := rat_cut_bin_certificate_sound certificate1122 profilesValid1122 numericValid1122 valid1122

def retention1123 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(601069633960861852/1564272469392366107),(638596672609027497/250000000000000000),(5/4),(15485953986008424813/12800000000000000000),true,MergedCutProfiles.Batch187.profile7493,![MergedCutProfiles.Batch187.profile7493,MergedCutProfiles.Batch187.profile7494,MergedCutProfiles.Batch187.profile7495,MergedCutProfiles.Batch187.profile7496,MergedCutProfiles.Batch187.profile7497,MergedCutProfiles.Batch187.profile7498,MergedCutProfiles.Batch187.profile7499,MergedCutProfiles.Batch187.profile7500,MergedCutProfiles.Batch187.profile7501,MergedCutProfiles.Batch187.profile7502,MergedCutProfiles.Batch187.profile7503,MergedCutProfiles.Batch187.profile7504,MergedCutProfiles.Batch187.profile7505,MergedCutProfiles.Batch187.profile7506,MergedCutProfiles.Batch187.profile7507,MergedCutProfiles.Batch187.profile7508]⟩
theorem profilesValid1123 : retention1123.ProfilesValid := by
  change ∀ j : Fin 16, (retention1123.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch187.valid7493
  · exact MergedCutProfiles.Batch187.valid7494
  · exact MergedCutProfiles.Batch187.valid7495
  · exact MergedCutProfiles.Batch187.valid7496
  · exact MergedCutProfiles.Batch187.valid7497
  · exact MergedCutProfiles.Batch187.valid7498
  · exact MergedCutProfiles.Batch187.valid7499
  · exact MergedCutProfiles.Batch187.valid7500
  · exact MergedCutProfiles.Batch187.valid7501
  · exact MergedCutProfiles.Batch187.valid7502
  · exact MergedCutProfiles.Batch187.valid7503
  · exact MergedCutProfiles.Batch187.valid7504
  · exact MergedCutProfiles.Batch187.valid7505
  · exact MergedCutProfiles.Batch187.valid7506
  · exact MergedCutProfiles.Batch187.valid7507
  · exact MergedCutProfiles.Batch187.valid7508
theorem numericValid1123 : retention1123.NumericValid := by decide +kernel
def certificate1123 : RatCutBinCertificate := ⟨⟨retention1123,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(73837605891308801/62500000000000000)⟩,(495731555071820573/500000000000000000),(440207567421304917/1000000000000000000),(198597814001033789/1000000000000000000),(71707404866461027/500000000000000000)⟩
theorem valid1123 : certificate1123.Valid := by decide +kernel
theorem sound1123 : certificate1123.Sound := rat_cut_bin_certificate_sound certificate1123 profilesValid1123 numericValid1123 valid1123

def retention1124 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(755642515267823174/1564272469392366107),(150267408490215463/25000000000000000),(11/10),(24709411394739039885552426427319883439/24042785358434474080000000000000000000),false,MergedCutProfiles.Batch187.profile7509,(fun _ => MergedCutProfiles.Batch187.profile7509)⟩
theorem profilesValid1124 : retention1124.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7509
theorem numericValid1124 : retention1124.NumericValid := by decide +kernel
def certificate1124 : RatCutBinCertificate := ⟨⟨retention1124,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(1002703443418845829/1000000000000000000)⟩,(495731555071820573/500000000000000000),(4631212600473521/10000000000000000),(9019169663619371/50000000000000000),(1145392122480871/8000000000000000)⟩
theorem valid1124 : certificate1124.Valid := by decide +kernel
theorem sound1124 : certificate1124.Sound := rat_cut_bin_certificate_sound certificate1124 profilesValid1124 numericValid1124 valid1124

def retention1125 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(7785392391229534841/15642724693923661070),(377821257633911587/50000000000000000),(21/20),(117256747961160891619494982924510259/118069143010597370937500000000000000),false,MergedCutProfiles.Batch187.profile7510,(fun _ => MergedCutProfiles.Batch187.profile7510)⟩
theorem profilesValid1125 : retention1125.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7510
theorem numericValid1125 : retention1125.NumericValid := by decide +kernel
def certificate1125 : RatCutBinCertificate := ⟨⟨retention1125,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(3786070021559241/3906250000000000)⟩,(495731555071820573/500000000000000000),(58803442767457961/125000000000000000),(87408317183611901/500000000000000000),(28647016011094183/200000000000000000)⟩
theorem valid1125 : certificate1125.Valid := by decide +kernel
theorem sound1125 : certificate1125.Sound := rat_cut_bin_certificate_sound certificate1125 profilesValid1125 numericValid1125 valid1125

def retention1126 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(1/2),(7785392391229534841/1000000000000000000),(21/20),(12326276687935107268550597108064037069839/12456627825967255745600000000000000000000),false,MergedCutProfiles.Batch187.profile7511,(fun _ => MergedCutProfiles.Batch187.profile7511)⟩
theorem profilesValid1126 : retention1126.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7511
theorem numericValid1126 : retention1126.NumericValid := by decide +kernel
def certificate1126 : RatCutBinCertificate := ⟨⟨retention1126,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(965650254930032561/1000000000000000000)⟩,(495731555071820573/500000000000000000),(117794076443134787/250000000000000000),(17425258084164989/100000000000000000),(71369030699147247/500000000000000000)⟩
theorem valid1126 : certificate1126.Valid := by decide +kernel
theorem sound1126 : certificate1126.Sound := rat_cut_bin_certificate_sound certificate1126 profilesValid1126 numericValid1126 valid1126

def retention1127 : RatCutRetentionCertificate := ⟨(217/4000),(109/2000),(1/2),64,1,(3990624689426514337093969724446591519/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch187.profile7511,(fun _ => MergedCutProfiles.Batch187.profile7511)⟩
theorem profilesValid1127 : retention1127.ProfilesValid := by
  exact MergedCutProfiles.Batch187.valid7511
theorem numericValid1127 : retention1127.NumericValid := by decide +kernel
def certificate1127 : RatCutBinCertificate := ⟨⟨retention1127,(2234309390916781739/1000000000000000000),(36441619022305257/250000000000000000),(894897485822997303/62500000000000000),(224308339632153902779/1000000000000000000),(974909802062878467/1000000000000000000)⟩,(495731555071820573/500000000000000000),(438073209905931521/1000000000000000000),(4007084576136521/20000000000000000),(190738956171489233/1000000000000000000)⟩
theorem valid1127 : certificate1127.Valid := by decide +kernel
theorem sound1127 : certificate1127.Sound := rat_cut_bin_certificate_sound certificate1127 profilesValid1127 numericValid1127 valid1127

def certificates : List RatCutBinCertificate := [certificate1116,certificate1117,certificate1118,certificate1119,certificate1120,certificate1121,certificate1122,certificate1123,certificate1124,certificate1125,certificate1126,certificate1127]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1116,List.forall_mem_cons.mpr ⟨sound1117,List.forall_mem_cons.mpr ⟨sound1118,List.forall_mem_cons.mpr ⟨sound1119,List.forall_mem_cons.mpr ⟨sound1120,List.forall_mem_cons.mpr ⟨sound1121,List.forall_mem_cons.mpr ⟨sound1122,List.forall_mem_cons.mpr ⟨sound1123,List.forall_mem_cons.mpr ⟨sound1124,List.forall_mem_cons.mpr ⟨sound1125,List.forall_mem_cons.mpr ⟨sound1126,List.forall_mem_cons.mpr ⟨sound1127,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch093
