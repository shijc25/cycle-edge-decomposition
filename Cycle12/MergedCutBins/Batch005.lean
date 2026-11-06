import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch011
import Cycle12.MergedCutProfiles.Batch012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch005

def retention60 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(11851216605896948442/146096017909295143181),(341597024769496123/200000000000000000),2,(531028622287773511149358612656116791/273277619815596898400000000000000000),false,MergedCutProfiles.Batch011.profile459,(fun _ => MergedCutProfiles.Batch011.profile459)⟩
theorem profilesValid60 : retention60.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid459
theorem numericValid60 : retention60.NumericValid := by decide +kernel
def certificate60 : RatCutBinCertificate := ⟨⟨retention60,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(970580836778577147/500000000000000000)⟩,(249894322084639273/250000000000000000),(35760529204477873/100000000000000000),(274655409418716941/1000000000000000000),(103746714005401737/500000000000000000)⟩
theorem valid60 : certificate60.Valid := by decide +kernel
theorem sound60 : certificate60.Sound := rat_cut_bin_certificate_sound certificate60 profilesValid60 numericValid60 valid60

def retention61 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(16000000000000000000/146096017909295143181),(5925608302948474221/125000000000000000),1,(350450287390944950525036972575433319407/189619465694351175072000000000000000000),false,MergedCutProfiles.Batch011.profile460,(fun _ => MergedCutProfiles.Batch011.profile460)⟩
theorem profilesValid61 : retention61.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid460
theorem numericValid61 : retention61.NumericValid := by decide +kernel
def certificate61 : RatCutBinCertificate := ⟨⟨retention61,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(461791430968677219/250000000000000000)⟩,(249894322084639273/250000000000000000),(2306967579991341/10000000000000000),(21540659155537/50000000000000),(76561065426861381/100000000000000000)⟩
theorem valid61 : certificate61.Valid := by decide +kernel
theorem sound61 : certificate61.Sound := rat_cut_bin_certificate_sound certificate61 profilesValid61 numericValid61 valid61

def retention62 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid62 : retention62.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid62 : retention62.NumericValid := by decide +kernel
def certificate62 : RatCutBinCertificate := ⟨⟨retention62,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(996524315725316599/1000000000000000000)⟩,(249894322084639273/250000000000000000),(425014660313435263/1000000000000000000),(211328737872405487/1000000000000000000),(207277013068638887/1000000000000000000)⟩
theorem valid62 : certificate62.Valid := by decide +kernel
theorem sound62 : certificate62.Sound := rat_cut_bin_certificate_sound certificate62 profilesValid62 numericValid62 valid62

def retention63 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(16000000000000000000/146096017909295143181),(3326990168860181551/1000000000000000000),(27/20),(9738812018659883394177347579002987505591/5323184270176290481600000000000000000000),false,MergedCutProfiles.Batch011.profile460,(fun _ => MergedCutProfiles.Batch011.profile460)⟩
theorem profilesValid63 : retention63.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid460
theorem numericValid63 : retention63.NumericValid := by decide +kernel
def certificate63 : RatCutBinCertificate := ⟨⟨retention63,(68659147355699667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(1827888201184600421/1000000000000000000)⟩,(499749058710866579/500000000000000000),(13314153334083611/62500000000000000),(57168412379026633/125000000000000000),(118887401654777261/250000000000000000)⟩
theorem valid63 : certificate63.Valid := by decide +kernel
theorem sound63 : certificate63.Sound := rat_cut_bin_certificate_sound certificate63 profilesValid63 numericValid63 valid63

def retention64 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1/2),64,1,(62345958716102427160851921466530999/62500000000000000000000000000000000),false,MergedCutProfiles.Batch011.profile461,(fun _ => MergedCutProfiles.Batch011.profile461)⟩
theorem profilesValid64 : retention64.ProfilesValid := by
  exact MergedCutProfiles.Batch011.valid461
theorem numericValid64 : retention64.NumericValid := by decide +kernel
def certificate64 : RatCutBinCertificate := ⟨⟨retention64,(68659147355699667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(996334958414005783/1000000000000000000)⟩,(499749058710866579/500000000000000000),(39082091551819519/100000000000000000),(60499694970002843/250000000000000000),(237295822648693351/1000000000000000000)⟩
theorem valid64 : certificate64.Valid := by decide +kernel
theorem sound64 : certificate64.Sound := rat_cut_bin_certificate_sound certificate64 profilesValid64 numericValid64 valid64

def retention65 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(26621417760547951/20903668902472701874),(594285173451838707/1000000000000000000),4,(8941006469122168731/4000000000000000000),true,MergedCutProfiles.Batch011.profile462,![MergedCutProfiles.Batch011.profile462,MergedCutProfiles.Batch011.profile463,MergedCutProfiles.Batch011.profile464,MergedCutProfiles.Batch011.profile465,MergedCutProfiles.Batch011.profile466,MergedCutProfiles.Batch011.profile467,MergedCutProfiles.Batch011.profile468,MergedCutProfiles.Batch011.profile469,MergedCutProfiles.Batch011.profile470,MergedCutProfiles.Batch011.profile471,MergedCutProfiles.Batch011.profile472,MergedCutProfiles.Batch011.profile473,MergedCutProfiles.Batch011.profile474,MergedCutProfiles.Batch011.profile475,MergedCutProfiles.Batch011.profile476,MergedCutProfiles.Batch011.profile477]⟩
theorem profilesValid65 : retention65.ProfilesValid := by
  change ∀ j : Fin 16, (retention65.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid462
  · exact MergedCutProfiles.Batch011.valid463
  · exact MergedCutProfiles.Batch011.valid464
  · exact MergedCutProfiles.Batch011.valid465
  · exact MergedCutProfiles.Batch011.valid466
  · exact MergedCutProfiles.Batch011.valid467
  · exact MergedCutProfiles.Batch011.valid468
  · exact MergedCutProfiles.Batch011.valid469
  · exact MergedCutProfiles.Batch011.valid470
  · exact MergedCutProfiles.Batch011.valid471
  · exact MergedCutProfiles.Batch011.valid472
  · exact MergedCutProfiles.Batch011.valid473
  · exact MergedCutProfiles.Batch011.valid474
  · exact MergedCutProfiles.Batch011.valid475
  · exact MergedCutProfiles.Batch011.valid476
  · exact MergedCutProfiles.Batch011.valid477
theorem numericValid65 : retention65.NumericValid := by decide +kernel
def certificate65 : RatCutBinCertificate := ⟨⟨retention65,(232312513054981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(5575952349186203/2500000000000000)⟩,(499745340778328803/500000000000000000),(542319126842920369/1000000000000000000),(15729429148505359/125000000000000000),(5679965133382869/100000000000000000)⟩
theorem valid65 : certificate65.Valid := by decide +kernel
theorem sound65 : certificate65.Sound := rat_cut_bin_certificate_sound certificate65 profilesValid65 numericValid65 valid65

def retention66 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(637575968000000000/240392192378436071551),(612292608492602873/1000000000000000000),4,(344799530853933955905364097720476833/153073152123150718250000000000000000),true,MergedCutProfiles.Batch011.profile478,![MergedCutProfiles.Batch011.profile478,MergedCutProfiles.Batch011.profile479,MergedCutProfiles.Batch012.profile480,MergedCutProfiles.Batch012.profile481,MergedCutProfiles.Batch012.profile482,MergedCutProfiles.Batch012.profile483,MergedCutProfiles.Batch012.profile484,MergedCutProfiles.Batch012.profile485,MergedCutProfiles.Batch012.profile486,MergedCutProfiles.Batch012.profile487,MergedCutProfiles.Batch012.profile488,MergedCutProfiles.Batch012.profile489,MergedCutProfiles.Batch012.profile490,MergedCutProfiles.Batch012.profile491,MergedCutProfiles.Batch012.profile492,MergedCutProfiles.Batch012.profile493]⟩
theorem profilesValid66 : retention66.ProfilesValid := by
  change ∀ j : Fin 16, (retention66.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid478
  · exact MergedCutProfiles.Batch011.valid479
  · exact MergedCutProfiles.Batch012.valid480
  · exact MergedCutProfiles.Batch012.valid481
  · exact MergedCutProfiles.Batch012.valid482
  · exact MergedCutProfiles.Batch012.valid483
  · exact MergedCutProfiles.Batch012.valid484
  · exact MergedCutProfiles.Batch012.valid485
  · exact MergedCutProfiles.Batch012.valid486
  · exact MergedCutProfiles.Batch012.valid487
  · exact MergedCutProfiles.Batch012.valid488
  · exact MergedCutProfiles.Batch012.valid489
  · exact MergedCutProfiles.Batch012.valid490
  · exact MergedCutProfiles.Batch012.valid491
  · exact MergedCutProfiles.Batch012.valid492
  · exact MergedCutProfiles.Batch012.valid493
theorem numericValid66 : retention66.NumericValid := by decide +kernel
def certificate66 : RatCutBinCertificate := ⟨⟨retention66,(232312513054981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(561911014636180459/250000000000000000)⟩,(499745340778328803/500000000000000000),(10556117110583151/20000000000000000),(134912059970232721/1000000000000000000),(30812268654018959/500000000000000000)⟩
theorem valid66 : certificate66.Valid := by decide +kernel
theorem sound66 : certificate66.Sound := rat_cut_bin_certificate_sound certificate66 profilesValid66 numericValid66 valid66

def retention67 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(2617457200350841443/480784384756872143102),(19924249/15625000),(12/5),(1132766071914565151/500000000000000000),true,MergedCutProfiles.Batch011.profile479,![MergedCutProfiles.Batch011.profile479,MergedCutProfiles.Batch012.profile494,MergedCutProfiles.Batch011.profile474,MergedCutProfiles.Batch012.profile495,MergedCutProfiles.Batch012.profile496,MergedCutProfiles.Batch012.profile497,MergedCutProfiles.Batch012.profile498,MergedCutProfiles.Batch012.profile499,MergedCutProfiles.Batch012.profile500,MergedCutProfiles.Batch012.profile501,MergedCutProfiles.Batch012.profile502,MergedCutProfiles.Batch012.profile503,MergedCutProfiles.Batch012.profile504,MergedCutProfiles.Batch012.profile505,MergedCutProfiles.Batch012.profile506,MergedCutProfiles.Batch012.profile507]⟩
theorem profilesValid67 : retention67.ProfilesValid := by
  change ∀ j : Fin 16, (retention67.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid479
  · exact MergedCutProfiles.Batch012.valid494
  · exact MergedCutProfiles.Batch011.valid474
  · exact MergedCutProfiles.Batch012.valid495
  · exact MergedCutProfiles.Batch012.valid496
  · exact MergedCutProfiles.Batch012.valid497
  · exact MergedCutProfiles.Batch012.valid498
  · exact MergedCutProfiles.Batch012.valid499
  · exact MergedCutProfiles.Batch012.valid500
  · exact MergedCutProfiles.Batch012.valid501
  · exact MergedCutProfiles.Batch012.valid502
  · exact MergedCutProfiles.Batch012.valid503
  · exact MergedCutProfiles.Batch012.valid504
  · exact MergedCutProfiles.Batch012.valid505
  · exact MergedCutProfiles.Batch012.valid506
  · exact MergedCutProfiles.Batch012.valid507
theorem numericValid67 : retention67.NumericValid := by decide +kernel
def certificate67 : RatCutBinCertificate := ⟨⟨retention67,(232312513054981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(2262609737637824511/1000000000000000000)⟩,(499745340778328803/500000000000000000),(347964779087247559/1000000000000000000),(71174662147323/250000000000000),(51268105360647397/250000000000000000)⟩
theorem valid67 : certificate67.Valid := by decide +kernel
theorem sound67 : certificate67.Sound := rat_cut_bin_certificate_sound certificate67 profilesValid67 numericValid67 valid67

def retention68 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(32000000000000000000/240392192378436071551),(2617457200350841443/1000000000000000000),(31/20),(7494190471027301734313105612408299813511/4187931520561346308800000000000000000000),false,MergedCutProfiles.Batch012.profile508,(fun _ => MergedCutProfiles.Batch012.profile508)⟩
theorem profilesValid68 : retention68.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid508
theorem numericValid68 : retention68.NumericValid := by decide +kernel
def certificate68 : RatCutBinCertificate := ⟨⟨retention68,(232312513054981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(1787585634157149781/1000000000000000000)⟩,(499745340778328803/500000000000000000),(334694062112921739/1000000000000000000),(298961498672447487/1000000000000000000),(268318956388627187/1000000000000000000)⟩
theorem valid68 : certificate68.Valid := by decide +kernel
theorem sound68 : certificate68.Sound := rat_cut_bin_certificate_sound certificate68 profilesValid68 numericValid68 valid68

def retention69 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid69 : retention69.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid69 : retention69.NumericValid := by decide +kernel
def certificate69 : RatCutBinCertificate := ⟨⟨retention69,(232312513054981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(996318101092730647/1000000000000000000)⟩,(499745340778328803/500000000000000000),(427654273795482177/1000000000000000000),(209078430611583049/1000000000000000000),(20501015382846799/100000000000000000)⟩
theorem valid69 : certificate69.Valid := by decide +kernel
theorem sound69 : certificate69.Sound := rat_cut_bin_certificate_sound certificate69 profilesValid69 numericValid69 valid69

def retention70 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(32000000000000000000/240392192378436071551),(3361589830246311363/1000000000000000000),(27/20),(9535752733001767998139251404244527521199/5378543728394098180800000000000000000000),false,MergedCutProfiles.Batch012.profile508,(fun _ => MergedCutProfiles.Batch012.profile508)⟩
theorem profilesValid70 : retention70.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid508
theorem numericValid70 : retention70.NumericValid := by decide +kernel
def certificate70 : RatCutBinCertificate := ⟨⟨retention70,(276093541929981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(354194199166820209/200000000000000000)⟩,(499697348226789897/500000000000000000),(109132092141539389/500000000000000000),(89867626726152267/200000000000000000),(456974340830862949/1000000000000000000)⟩
theorem valid70 : certificate70.Valid := by decide +kernel
theorem sound70 : certificate70.Sound := rat_cut_bin_certificate_sound certificate70 profilesValid70 numericValid70 valid70

def retention71 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid71 : retention71.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid71 : retention71.NumericValid := by decide +kernel
def certificate71 : RatCutBinCertificate := ⟨⟨retention71,(276093541929981793/125000000000000000),(246507623072377/50000000000000000),(3762389890941862633/500000000000000000),(454272876767597821347/125000000000000000),(31127769447560759/31250000000000000)⟩,(499697348226789897/500000000000000000),(388057378763823399/1000000000000000000),(244604780198961847/1000000000000000000),(239767802484432961/1000000000000000000)⟩
theorem valid71 : certificate71.Valid := by decide +kernel
theorem sound71 : certificate71.Sound := rat_cut_bin_certificate_sound certificate71 profilesValid71 numericValid71 valid71

def certificates : List RatCutBinCertificate := [certificate60,certificate61,certificate62,certificate63,certificate64,certificate65,certificate66,certificate67,certificate68,certificate69,certificate70,certificate71]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound60,List.forall_mem_cons.mpr ⟨sound61,List.forall_mem_cons.mpr ⟨sound62,List.forall_mem_cons.mpr ⟨sound63,List.forall_mem_cons.mpr ⟨sound64,List.forall_mem_cons.mpr ⟨sound65,List.forall_mem_cons.mpr ⟨sound66,List.forall_mem_cons.mpr ⟨sound67,List.forall_mem_cons.mpr ⟨sound68,List.forall_mem_cons.mpr ⟨sound69,List.forall_mem_cons.mpr ⟨sound70,List.forall_mem_cons.mpr ⟨sound71,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch005
