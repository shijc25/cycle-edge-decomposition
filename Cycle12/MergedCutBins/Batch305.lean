import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch004
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch441
import Cycle12.MergedCutProfiles.Batch561
import Cycle12.MergedCutProfiles.Batch562

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch305

def retention3660 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(32247563888319242817/47800972580928223399921),(134310811/100000000),(12/5),(7493644347829641763/3200000000000000000),true,MergedCutProfiles.Batch307.profile12316,![MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch003.profile130,MergedCutProfiles.Batch003.profile133,MergedCutProfiles.Batch003.profile135,MergedCutProfiles.Batch003.profile138,MergedCutProfiles.Batch003.profile140,MergedCutProfiles.Batch561.profile22456,MergedCutProfiles.Batch003.profile144,MergedCutProfiles.Batch003.profile145,MergedCutProfiles.Batch003.profile152,MergedCutProfiles.Batch003.profile148,MergedCutProfiles.Batch003.profile149,MergedCutProfiles.Batch003.profile153,MergedCutProfiles.Batch441.profile17652,MergedCutProfiles.Batch561.profile22457,MergedCutProfiles.Batch561.profile22458]⟩
theorem profilesValid3660 : retention3660.ProfilesValid := by
  change ∀ j : Fin 16, (retention3660.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch003.valid130
  · exact MergedCutProfiles.Batch003.valid133
  · exact MergedCutProfiles.Batch003.valid135
  · exact MergedCutProfiles.Batch003.valid138
  · exact MergedCutProfiles.Batch003.valid140
  · exact MergedCutProfiles.Batch561.valid22456
  · exact MergedCutProfiles.Batch003.valid144
  · exact MergedCutProfiles.Batch003.valid145
  · exact MergedCutProfiles.Batch003.valid152
  · exact MergedCutProfiles.Batch003.valid148
  · exact MergedCutProfiles.Batch003.valid149
  · exact MergedCutProfiles.Batch003.valid153
  · exact MergedCutProfiles.Batch441.valid17652
  · exact MergedCutProfiles.Batch561.valid22457
  · exact MergedCutProfiles.Batch561.valid22458
theorem numericValid3660 : retention3660.NumericValid := by decide +kernel
def certificate3660 : RatCutBinCertificate := ⟨⟨retention3660,(924644786538216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(2341130352265645021/1000000000000000000)⟩,(999994500574185357/1000000000000000000),(332915978196359473/1000000000000000000),(75227989721018823/250000000000000000),(56334526266399019/250000000000000000)⟩
theorem valid3660 : certificate3660.Valid := by decide +kernel
theorem sound3660 : certificate3660.Sound := rat_cut_bin_certificate_sound certificate3660 profilesValid3660 numericValid3660 valid3660

def retention3661 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(64000000000000000000/47800972580928223399921),(32247563888319242817/1000000000000000000),1,(100045279704535309626915657876770404809/42996751851092323756000000000000000000),false,MergedCutProfiles.Batch561.profile22459,(fun _ => MergedCutProfiles.Batch561.profile22459)⟩
theorem profilesValid3661 : retention3661.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22459
theorem numericValid3661 : retention3661.NumericValid := by decide +kernel
def certificate3661 : RatCutBinCertificate := ⟨⟨retention3661,(924644786538216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(2326546214114323473/1000000000000000000)⟩,(999994500574185357/1000000000000000000),(44198785374346211/250000000000000000),(516336691860984393/1000000000000000000),(1120438818778812187/1000000000000000000)⟩
theorem valid3661 : certificate3661.Valid := by decide +kernel
theorem sound3661 : certificate3661.Sound := rat_cut_bin_certificate_sound certificate3661 profilesValid3661 numericValid3661 valid3661

def retention3662 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid3662 : retention3662.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid3662 : retention3662.NumericValid := by decide +kernel
def certificate3662 : RatCutBinCertificate := ⟨⟨retention3662,(924644786538216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(997270633312581629/1000000000000000000)⟩,(999994500574185357/1000000000000000000),(404489615916628471/1000000000000000000),(229393843142108567/1000000000000000000),(225256449003899123/1000000000000000000)⟩
theorem valid3662 : certificate3662.Valid := by decide +kernel
theorem sound3662 : certificate3662.Sound := rat_cut_bin_certificate_sound certificate3662 profilesValid3662 numericValid3662 valid3662

def retention3663 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(64000000000000000000/47800972580928223399921),(741274775824710977/50000000000000000),1,(134948924251925711885792391190588511439/59301982065976878160000000000000000000),false,MergedCutProfiles.Batch561.profile22459,(fun _ => MergedCutProfiles.Batch561.profile22459)⟩
theorem profilesValid3663 : retention3663.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22459
theorem numericValid3663 : retention3663.NumericValid := by decide +kernel
def certificate3663 : RatCutBinCertificate := ⟨⟨retention3663,(877839029038216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(568842973369217693/250000000000000000)⟩,(249998694739134741/250000000000000000),(33625047236645457/1000000000000000000),(833784584064795949/1000000000000000000),(1644731405814508541/1000000000000000000)⟩
theorem valid3663 : certificate3663.Valid := by decide +kernel
theorem sound3663 : certificate3663.Sound := rat_cut_bin_certificate_sound certificate3663 profilesValid3663 numericValid3663 valid3663

def retention3664 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid3664 : retention3664.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid3664 : retention3664.NumericValid := by decide +kernel
def certificate3664 : RatCutBinCertificate := ⟨⟨retention3664,(877839029038216869/500000000000000000),(249776479000013/250000000000000000),(1399931098764986143/200000000000000000),(336055224918426238233403/1000000000000000000),(31165124846472017/31250000000000000)⟩,(249998694739134741/250000000000000000),(38358926733007843/500000000000000000),(720323741441999367/1000000000000000000),(353670682056175301/500000000000000000)⟩
theorem valid3664 : certificate3664.Valid := by decide +kernel
theorem sound3664 : certificate3664.Sound := rat_cut_bin_certificate_sound certificate3664 profilesValid3664 numericValid3664 valid3664

def retention3665 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(386477652810232769/19709187927742654406726),(573473255664974163/1000000000000000000),4,(527792962858319860352499513517839/238947189860405901250000000000000),true,MergedCutProfiles.Batch561.profile22460,![MergedCutProfiles.Batch561.profile22460,MergedCutProfiles.Batch561.profile22461,MergedCutProfiles.Batch561.profile22461,MergedCutProfiles.Batch561.profile22462,MergedCutProfiles.Batch561.profile22463,MergedCutProfiles.Batch561.profile22463,MergedCutProfiles.Batch561.profile22463,MergedCutProfiles.Batch561.profile22464,MergedCutProfiles.Batch561.profile22464,MergedCutProfiles.Batch561.profile22465,MergedCutProfiles.Batch561.profile22465,MergedCutProfiles.Batch561.profile22465,MergedCutProfiles.Batch561.profile22466,MergedCutProfiles.Batch561.profile22466,MergedCutProfiles.Batch561.profile22466,MergedCutProfiles.Batch561.profile22467]⟩
theorem profilesValid3665 : retention3665.ProfilesValid := by
  change ∀ j : Fin 16, (retention3665.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22460
  · exact MergedCutProfiles.Batch561.valid22461
  · exact MergedCutProfiles.Batch561.valid22461
  · exact MergedCutProfiles.Batch561.valid22462
  · exact MergedCutProfiles.Batch561.valid22463
  · exact MergedCutProfiles.Batch561.valid22463
  · exact MergedCutProfiles.Batch561.valid22463
  · exact MergedCutProfiles.Batch561.valid22464
  · exact MergedCutProfiles.Batch561.valid22464
  · exact MergedCutProfiles.Batch561.valid22465
  · exact MergedCutProfiles.Batch561.valid22465
  · exact MergedCutProfiles.Batch561.valid22465
  · exact MergedCutProfiles.Batch561.valid22466
  · exact MergedCutProfiles.Batch561.valid22466
  · exact MergedCutProfiles.Batch561.valid22466
  · exact MergedCutProfiles.Batch561.valid22467
theorem numericValid3665 : retention3665.NumericValid := by decide +kernel
def certificate3665 : RatCutBinCertificate := ⟨⟨retention3665,(1800088859878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(1103797986235213539/500000000000000000)⟩,(24999839335035547/25000000000000000),(74465767104648199/125000000000000000),(95703081232505391/1000000000000000000),(83153824383473/1953125000000000)⟩
theorem valid3665 : certificate3665.Valid := by decide +kernel
theorem sound3665 : certificate3665.Sound := rat_cut_bin_certificate_sound certificate3665 profilesValid3665 numericValid3665 valid3665

def retention3666 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(331863363500000000/9854593963871327203363),(386477652810232769/500000000000000000),(15/4),(5918386758937600993886314490843098083/2473456977985489721600000000000000000),false,MergedCutProfiles.Batch561.profile22468,(fun _ => MergedCutProfiles.Batch561.profile22468)⟩
theorem profilesValid3666 : retention3666.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22468
theorem numericValid3666 : retention3666.NumericValid := by decide +kernel
def certificate3666 : RatCutBinCertificate := ⟨⟨retention3666,(1800088859878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(1195802601033013803/500000000000000000)⟩,(24999839335035547/25000000000000000),(451548310000039637/1000000000000000000),(94718797330191417/500000000000000000),(24756676565449923/250000000000000000)⟩
theorem valid3666 : certificate3666.Valid := by decide +kernel
theorem sound3666 : certificate3666.Sound := rat_cut_bin_certificate_sound certificate3666 profilesValid3666 numericValid3666 valid3666

def retention3667 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(25661258645731423865/39418375855485308813452),(663726727/500000000),(12/5),(37412665199678683391/16000000000000000000),true,MergedCutProfiles.Batch561.profile22469,![MergedCutProfiles.Batch561.profile22469,MergedCutProfiles.Batch561.profile22470,MergedCutProfiles.Batch561.profile22471,MergedCutProfiles.Batch561.profile22472,MergedCutProfiles.Batch561.profile22473,MergedCutProfiles.Batch561.profile22474,MergedCutProfiles.Batch561.profile22475,MergedCutProfiles.Batch561.profile22476,MergedCutProfiles.Batch561.profile22477,MergedCutProfiles.Batch561.profile22478,MergedCutProfiles.Batch561.profile22479,MergedCutProfiles.Batch562.profile22480,MergedCutProfiles.Batch562.profile22481,MergedCutProfiles.Batch562.profile22482,MergedCutProfiles.Batch562.profile22483,MergedCutProfiles.Batch562.profile22484]⟩
theorem profilesValid3667 : retention3667.ProfilesValid := by
  change ∀ j : Fin 16, (retention3667.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch561.valid22469
  · exact MergedCutProfiles.Batch561.valid22470
  · exact MergedCutProfiles.Batch561.valid22471
  · exact MergedCutProfiles.Batch561.valid22472
  · exact MergedCutProfiles.Batch561.valid22473
  · exact MergedCutProfiles.Batch561.valid22474
  · exact MergedCutProfiles.Batch561.valid22475
  · exact MergedCutProfiles.Batch561.valid22476
  · exact MergedCutProfiles.Batch561.valid22477
  · exact MergedCutProfiles.Batch561.valid22478
  · exact MergedCutProfiles.Batch561.valid22479
  · exact MergedCutProfiles.Batch562.valid22480
  · exact MergedCutProfiles.Batch562.valid22481
  · exact MergedCutProfiles.Batch562.valid22482
  · exact MergedCutProfiles.Batch562.valid22483
  · exact MergedCutProfiles.Batch562.valid22484
theorem numericValid3667 : retention3667.NumericValid := by decide +kernel
def certificate3667 : RatCutBinCertificate := ⟨⟨retention3667,(1800088859878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(1168776531560172269/500000000000000000)⟩,(24999839335035547/25000000000000000),(341163451256772057/1000000000000000000),(291944105290855269/1000000000000000000),(8710792954892147/40000000000000000)⟩
theorem valid3667 : certificate3667.Valid := by decide +kernel
theorem sound3667 : certificate3667.Sound := rat_cut_bin_certificate_sound certificate3667 profilesValid3667 numericValid3667 valid3667

def retention3668 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(16000000000000000000/9854593963871327203363),(5132251729146284773/200000000000000000),1,(237163568551065427656741473881120255899/102645034582925695460000000000000000000),false,MergedCutProfiles.Batch562.profile22485,(fun _ => MergedCutProfiles.Batch562.profile22485)⟩
theorem profilesValid3668 : retention3668.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22485
theorem numericValid3668 : retention3668.NumericValid := by decide +kernel
def certificate3668 : RatCutBinCertificate := ⟨⟨retention3668,(1800088859878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(2310213877124189221/1000000000000000000)⟩,(24999839335035547/25000000000000000),(183595085263340061/1000000000000000000),(504763186558230443/1000000000000000000),(267448180658016459/250000000000000000)⟩
theorem valid3668 : certificate3668.Valid := by decide +kernel
theorem sound3668 : certificate3668.Sound := rat_cut_bin_certificate_sound certificate3668 profilesValid3668 numericValid3668 valid3668

def retention3669 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(1/2),64,1,(25536890277765986994245943214600551/25600000000000000000000000000000000),false,MergedCutProfiles.Batch562.profile22486,(fun _ => MergedCutProfiles.Batch562.profile22486)⟩
theorem profilesValid3669 : retention3669.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22486
theorem numericValid3669 : retention3669.NumericValid := by decide +kernel
def certificate3669 : RatCutBinCertificate := ⟨⟨retention3669,(1800088859878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(62326691450050553/62500000000000000)⟩,(24999839335035547/25000000000000000),(82617785546996897/200000000000000000),(22170139499116951/100000000000000000),(217693174204018213/1000000000000000000)⟩
theorem valid3669 : certificate3669.Valid := by decide +kernel
theorem sound3669 : certificate3669.Sound := rat_cut_bin_certificate_sound certificate3669 profilesValid3669 numericValid3669 valid3669

def retention3670 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(16000000000000000000/9854593963871327203363),(3022679692638752243/200000000000000000),1,(137380256760187317272089279594523617299/60453593852775044860000000000000000000),false,MergedCutProfiles.Batch562.profile22485,(fun _ => MergedCutProfiles.Batch562.profile22485)⟩
theorem profilesValid3670 : retention3670.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22485
theorem numericValid3670 : retention3670.NumericValid := by decide +kernel
def certificate3670 : RatCutBinCertificate := ⟨⟨retention3670,(1756237572878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(142011933036193929/62500000000000000)⟩,(999993729957371273/1000000000000000000),(4157878000282761/125000000000000000),(208705899479292077/250000000000000000),(1648957416030378749/1000000000000000000)⟩
theorem valid3670 : certificate3670.Valid := by decide +kernel
theorem sound3670 : certificate3670.Sound := rat_cut_bin_certificate_sound certificate3670 profilesValid3670 numericValid3670 valid3670

def retention3671 : RatCutRetentionCertificate := ⟨(1/200),(11/2000),(1/2),64,1,(25536890277765986994245943214600551/25600000000000000000000000000000000),false,MergedCutProfiles.Batch562.profile22486,(fun _ => MergedCutProfiles.Batch562.profile22486)⟩
theorem profilesValid3671 : retention3671.ProfilesValid := by
  exact MergedCutProfiles.Batch562.valid22486
theorem numericValid3671 : retention3671.NumericValid := by decide +kernel
def certificate3671 : RatCutBinCertificate := ⟨⟨retention3671,(1756237572878810893/1000000000000000000),(302704992384261/250000000000000000),(885395480054642677/125000000000000000),(69954983579123564145781/250000000000000000),(997234559288036137/1000000000000000000)⟩,(999993729957371273/1000000000000000000),(37894766427373059/500000000000000000),(722572678620102031/1000000000000000000),(354757192439199327/500000000000000000)⟩
theorem valid3671 : certificate3671.Valid := by decide +kernel
theorem sound3671 : certificate3671.Sound := rat_cut_bin_certificate_sound certificate3671 profilesValid3671 numericValid3671 valid3671

def certificates : List RatCutBinCertificate := [certificate3660,certificate3661,certificate3662,certificate3663,certificate3664,certificate3665,certificate3666,certificate3667,certificate3668,certificate3669,certificate3670,certificate3671]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3660,List.forall_mem_cons.mpr ⟨sound3661,List.forall_mem_cons.mpr ⟨sound3662,List.forall_mem_cons.mpr ⟨sound3663,List.forall_mem_cons.mpr ⟨sound3664,List.forall_mem_cons.mpr ⟨sound3665,List.forall_mem_cons.mpr ⟨sound3666,List.forall_mem_cons.mpr ⟨sound3667,List.forall_mem_cons.mpr ⟨sound3668,List.forall_mem_cons.mpr ⟨sound3669,List.forall_mem_cons.mpr ⟨sound3670,List.forall_mem_cons.mpr ⟨sound3671,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch305
