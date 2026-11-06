import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch677
import Cycle12.MergedCutProfiles.Batch678

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch400

def retention4800 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(1/2),64,1,(10215375598638441852214962015610919319/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch677.profile27102,(fun _ => MergedCutProfiles.Batch677.profile27102)⟩
theorem profilesValid4800 : retention4800.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27102
theorem numericValid4800 : retention4800.NumericValid := by decide +kernel
def certificate4800 : RatCutBinCertificate := ⟨⟨retention4800,(944169306222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(123146645021219759/125000000000000000)⟩,(999950010581339193/1000000000000000000),(262121384812137211/500000000000000000),(27440203701323203/200000000000000000),(41597162424311/312500000000000)⟩
theorem valid4800 : certificate4800.Valid := by decide +kernel
theorem sound4800 : certificate4800.Sound := rat_cut_bin_certificate_sound certificate4800 profilesValid4800 numericValid4800 valid4800

def retention4801 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(512000000000000000/24522918443256535917),(6132091401067662353/200000000000000000),1,(8377250834076775062745677720976169217/3832557125667288970625000000000000000),false,MergedCutProfiles.Batch677.profile27103,(fun _ => MergedCutProfiles.Batch677.profile27103)⟩
theorem profilesValid4801 : retention4801.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27103
theorem numericValid4801 : retention4801.NumericValid := by decide +kernel
def certificate4801 : RatCutBinCertificate := ⟨⟨retention4801,(876440639222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(1087140677529806731/500000000000000000)⟩,(249988399128946289/250000000000000000),(20789673823921811/1000000000000000000),(21790156498636413/25000000000000000),(1769540824586319983/1000000000000000000)⟩
theorem valid4801 : certificate4801.Valid := by decide +kernel
theorem sound4801 : certificate4801.Sound := rat_cut_bin_certificate_sound certificate4801 profilesValid4801 numericValid4801 valid4801

def retention4802 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(1/2),64,1,(10215375598638441852214962015610919319/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch677.profile27102,(fun _ => MergedCutProfiles.Batch677.profile27102)⟩
theorem profilesValid4802 : retention4802.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27102
theorem numericValid4802 : retention4802.NumericValid := by decide +kernel
def certificate4802 : RatCutBinCertificate := ⟨⟨retention4802,(876440639222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(493032121556306121/500000000000000000)⟩,(249988399128946289/250000000000000000),(45841435270421609/1000000000000000000),(79961707909582611/100000000000000000),(77647352444238123/100000000000000000)⟩
theorem valid4802 : certificate4802.Valid := by decide +kernel
theorem sound4802 : certificate4802.Sound := rat_cut_bin_certificate_sound certificate4802 profilesValid4802 numericValid4802 valid4802

def retention4803 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(230849663633610872/1021788268469022329875),(342846035099422087/500000000000000000),4,(6556094065318362940149518160755872191/2742768280795376696000000000000000000),false,MergedCutProfiles.Batch677.profile27104,(fun _ => MergedCutProfiles.Batch677.profile27104)⟩
theorem profilesValid4803 : retention4803.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27104
theorem numericValid4803 : retention4803.NumericValid := by decide +kernel
def certificate4803 : RatCutBinCertificate := ⟨⟨retention4803,(919085830222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(2341951638876254287/1000000000000000000)⟩,(999951338641093171/1000000000000000000),(434270102194648413/500000000000000000),(9046520974545079/1000000000000000000),(872924629890293/200000000000000000)⟩
theorem valid4803 : certificate4803.Valid := by decide +kernel
theorem sound4803 : certificate4803.Sound := rat_cut_bin_certificate_sound certificate4803 profilesValid4803 numericValid4803 valid4803

def retention4804 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(299009484629536008/1021788268469022329875),(86568623862604077/125000000000000000),4,(6631712158101120251480852291406691967/2770195963603330464000000000000000000),false,MergedCutProfiles.Batch677.profile27105,(fun _ => MergedCutProfiles.Batch677.profile27105)⟩
theorem profilesValid4804 : retention4804.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27105
theorem numericValid4804 : retention4804.NumericValid := by decide +kernel
def certificate4804 : RatCutBinCertificate := ⟨⟨retention4804,(919085830222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(469116424650584453/200000000000000000)⟩,(999951338641093171/1000000000000000000),(864982492730617547/1000000000000000000),(9555246358957153/1000000000000000000),(578002139261139/125000000000000000)⟩
theorem valid4804 : certificate4804.Valid := by decide +kernel
theorem sound4804 : certificate4804.Sound := rat_cut_bin_certificate_sound certificate4804 profilesValid4804 numericValid4804 valid4804

def retention4805 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(6244161206283470893/3065364805407066989625),(112128556736076003/125000000000000000),(18/5),(53690824404864858820991389313910458879/22425711347215200600000000000000000000),false,MergedCutProfiles.Batch677.profile27106,(fun _ => MergedCutProfiles.Batch677.profile27106)⟩
theorem profilesValid4805 : retention4805.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27106
theorem numericValid4805 : retention4805.NumericValid := by decide +kernel
def certificate4805 : RatCutBinCertificate := ⟨⟨retention4805,(919085830222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(2350632133940807253/1000000000000000000)⟩,(999951338641093171/1000000000000000000),(81277796208315277/100000000000000000),(2341918473535903/125000000000000000),(10175222806472499/1000000000000000000)⟩
theorem valid4805 : certificate4805.Valid := by decide +kernel
theorem sound4805 : certificate4805.Sound := rat_cut_bin_certificate_sound certificate4805 profilesValid4805 numericValid4805 valid4805

def retention4806 : RatCutRetentionCertificate := ⟨(161/4000),(81/2000),(1/40),(6244161206283470893/1000000000000000000),(13/10),(5490149673657535937676784082457851475759/2497664482513388357200000000000000000000),false,MergedCutProfiles.Batch677.profile27107,(fun _ => MergedCutProfiles.Batch677.profile27107)⟩
theorem profilesValid4806 : retention4806.ProfilesValid := by
  exact MergedCutProfiles.Batch677.valid27107
theorem numericValid4806 : retention4806.NumericValid := by decide +kernel
def certificate4806 : RatCutBinCertificate := ⟨⟨retention4806,(919085830222870061/500000000000000000),(14993777272926573/200000000000000000),(11396341834837657161/1000000000000000000),(17490523395247794866119/500000000000000000),(1091196815394164021/500000000000000000)⟩,(999951338641093171/1000000000000000000),(143631363313412751/200000000000000000),(22042463150608343/500000000000000000),(30661142488556611/500000000000000000)⟩
theorem valid4806 : certificate4806.Valid := by decide +kernel
theorem sound4806 : certificate4806.Sound := rat_cut_bin_certificate_sound certificate4806 profilesValid4806 numericValid4806 valid4806

def retention4807 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(594336762033289571/3023785039358298996097),(72828247479816877/125000000000000000),4,(261075882542947662707493133393999427/116525195967707003200000000000000000),true,MergedCutProfiles.Batch677.profile27108,![MergedCutProfiles.Batch677.profile27108,MergedCutProfiles.Batch677.profile27109,MergedCutProfiles.Batch677.profile27110,MergedCutProfiles.Batch677.profile27111,MergedCutProfiles.Batch677.profile27112,MergedCutProfiles.Batch677.profile27113,MergedCutProfiles.Batch677.profile27114,MergedCutProfiles.Batch677.profile27115,MergedCutProfiles.Batch677.profile27116,MergedCutProfiles.Batch677.profile27117,MergedCutProfiles.Batch677.profile27118,MergedCutProfiles.Batch677.profile27119,MergedCutProfiles.Batch678.profile27120,MergedCutProfiles.Batch678.profile27121,MergedCutProfiles.Batch678.profile27122,MergedCutProfiles.Batch678.profile27123]⟩
theorem profilesValid4807 : retention4807.ProfilesValid := by
  change ∀ j : Fin 16, (retention4807.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch677.valid27108
  · exact MergedCutProfiles.Batch677.valid27109
  · exact MergedCutProfiles.Batch677.valid27110
  · exact MergedCutProfiles.Batch677.valid27111
  · exact MergedCutProfiles.Batch677.valid27112
  · exact MergedCutProfiles.Batch677.valid27113
  · exact MergedCutProfiles.Batch677.valid27114
  · exact MergedCutProfiles.Batch677.valid27115
  · exact MergedCutProfiles.Batch677.valid27116
  · exact MergedCutProfiles.Batch677.valid27117
  · exact MergedCutProfiles.Batch677.valid27118
  · exact MergedCutProfiles.Batch677.valid27119
  · exact MergedCutProfiles.Batch678.valid27120
  · exact MergedCutProfiles.Batch678.valid27121
  · exact MergedCutProfiles.Batch678.valid27122
  · exact MergedCutProfiles.Batch678.valid27123
theorem numericValid4807 : retention4807.NumericValid := by decide +kernel
def certificate4807 : RatCutBinCertificate := ⟨⟨retention4807,(118086989583703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(1095156755766832517/500000000000000000)⟩,(199989908927676709/200000000000000000),(1101693579223377/1562500000000000),(48532659664068717/1000000000000000000),(21517926110733121/1000000000000000000)⟩
theorem valid4807 : certificate4807.Valid := by decide +kernel
theorem sound4807 : certificate4807.Sound := rat_cut_bin_certificate_sound certificate4807 profilesValid4807 numericValid4807 valid4807

def retention4808 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(1132083610000000000/3023785039358298996097),(594336762033289571/1000000000000000000),4,(1075318024637211739540935961926899691/475469409626631656800000000000000000),true,MergedCutProfiles.Batch678.profile27124,![MergedCutProfiles.Batch678.profile27124,MergedCutProfiles.Batch677.profile27111,MergedCutProfiles.Batch677.profile27113,MergedCutProfiles.Batch678.profile27125,MergedCutProfiles.Batch677.profile27117,MergedCutProfiles.Batch677.profile27119,MergedCutProfiles.Batch678.profile27121,MergedCutProfiles.Batch678.profile27123,MergedCutProfiles.Batch678.profile27126,MergedCutProfiles.Batch678.profile27127,MergedCutProfiles.Batch678.profile27128,MergedCutProfiles.Batch678.profile27129,MergedCutProfiles.Batch678.profile27130,MergedCutProfiles.Batch678.profile27131,MergedCutProfiles.Batch678.profile27132,MergedCutProfiles.Batch678.profile27133]⟩
theorem profilesValid4808 : retention4808.ProfilesValid := by
  change ∀ j : Fin 16, (retention4808.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch678.valid27124
  · exact MergedCutProfiles.Batch677.valid27111
  · exact MergedCutProfiles.Batch677.valid27113
  · exact MergedCutProfiles.Batch678.valid27125
  · exact MergedCutProfiles.Batch677.valid27117
  · exact MergedCutProfiles.Batch677.valid27119
  · exact MergedCutProfiles.Batch678.valid27121
  · exact MergedCutProfiles.Batch678.valid27123
  · exact MergedCutProfiles.Batch678.valid27126
  · exact MergedCutProfiles.Batch678.valid27127
  · exact MergedCutProfiles.Batch678.valid27128
  · exact MergedCutProfiles.Batch678.valid27129
  · exact MergedCutProfiles.Batch678.valid27130
  · exact MergedCutProfiles.Batch678.valid27131
  · exact MergedCutProfiles.Batch678.valid27132
  · exact MergedCutProfiles.Batch678.valid27133
theorem numericValid4808 : retention4808.NumericValid := by decide +kernel
def certificate4808 : RatCutBinCertificate := ⟨⟨retention4808,(118086989583703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(552848955626516611/250000000000000000)⟩,(199989908927676709/200000000000000000),(43070222870505447/62500000000000000),(54291829538121919/1000000000000000000),(24350639252153947/1000000000000000000)⟩
theorem valid4808 : certificate4808.Valid := by decide +kernel
theorem sound4808 : certificate4808.Sound := rat_cut_bin_certificate_sound certificate4808 profilesValid4808 numericValid4808 valid4808

def retention4809 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(1317475344537154837/3023785039358298996097),(113208361/100000000),(14/5),(10880674541466668428811796752662900311/4528334440000000000000000000000000000),true,MergedCutProfiles.Batch677.profile27109,![MergedCutProfiles.Batch677.profile27109,MergedCutProfiles.Batch678.profile27134,MergedCutProfiles.Batch677.profile27114,MergedCutProfiles.Batch677.profile27116,MergedCutProfiles.Batch677.profile27118,MergedCutProfiles.Batch678.profile27121,MergedCutProfiles.Batch678.profile27123,MergedCutProfiles.Batch678.profile27135,MergedCutProfiles.Batch678.profile27128,MergedCutProfiles.Batch678.profile27136,MergedCutProfiles.Batch678.profile27130,MergedCutProfiles.Batch678.profile27131,MergedCutProfiles.Batch678.profile27132,MergedCutProfiles.Batch678.profile27133,MergedCutProfiles.Batch678.profile27137,MergedCutProfiles.Batch678.profile27138]⟩
theorem profilesValid4809 : retention4809.ProfilesValid := by
  change ∀ j : Fin 16, (retention4809.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch677.valid27109
  · exact MergedCutProfiles.Batch678.valid27134
  · exact MergedCutProfiles.Batch677.valid27114
  · exact MergedCutProfiles.Batch677.valid27116
  · exact MergedCutProfiles.Batch677.valid27118
  · exact MergedCutProfiles.Batch678.valid27121
  · exact MergedCutProfiles.Batch678.valid27123
  · exact MergedCutProfiles.Batch678.valid27135
  · exact MergedCutProfiles.Batch678.valid27128
  · exact MergedCutProfiles.Batch678.valid27136
  · exact MergedCutProfiles.Batch678.valid27130
  · exact MergedCutProfiles.Batch678.valid27131
  · exact MergedCutProfiles.Batch678.valid27132
  · exact MergedCutProfiles.Batch678.valid27133
  · exact MergedCutProfiles.Batch678.valid27137
  · exact MergedCutProfiles.Batch678.valid27138
theorem numericValid4809 : retention4809.NumericValid := by decide +kernel
def certificate4809 : RatCutBinCertificate := ⟨⟨retention4809,(118086989583703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(2367660726954659789/1000000000000000000)⟩,(199989908927676709/200000000000000000),(439727209323396271/1000000000000000000),(49748052079503763/250000000000000000),(8301508755674807/62500000000000000)⟩
theorem valid4809 : certificate4809.Valid := by decide +kernel
theorem sound4809 : certificate4809.Sound := rat_cut_bin_certificate_sound certificate4809 profilesValid4809 numericValid4809 valid4809

def retention4810 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(64000000000000000000/3023785039358298996097),(1317475344537154837/1000000000000000000),(5/2),(113377299523700770889/51200000000000000000),true,MergedCutProfiles.Batch678.profile27139,![MergedCutProfiles.Batch678.profile27139,MergedCutProfiles.Batch678.profile27140,MergedCutProfiles.Batch678.profile27141,MergedCutProfiles.Batch678.profile27142,MergedCutProfiles.Batch678.profile27143,MergedCutProfiles.Batch678.profile27144,MergedCutProfiles.Batch678.profile27145,MergedCutProfiles.Batch678.profile27146,MergedCutProfiles.Batch678.profile27147,MergedCutProfiles.Batch678.profile27148,MergedCutProfiles.Batch678.profile27149,MergedCutProfiles.Batch678.profile27150,MergedCutProfiles.Batch678.profile27151,MergedCutProfiles.Batch678.profile27152,MergedCutProfiles.Batch678.profile27153,MergedCutProfiles.Batch678.profile27154]⟩
theorem profilesValid4810 : retention4810.ProfilesValid := by
  change ∀ j : Fin 16, (retention4810.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch678.valid27139
  · exact MergedCutProfiles.Batch678.valid27140
  · exact MergedCutProfiles.Batch678.valid27141
  · exact MergedCutProfiles.Batch678.valid27142
  · exact MergedCutProfiles.Batch678.valid27143
  · exact MergedCutProfiles.Batch678.valid27144
  · exact MergedCutProfiles.Batch678.valid27145
  · exact MergedCutProfiles.Batch678.valid27146
  · exact MergedCutProfiles.Batch678.valid27147
  · exact MergedCutProfiles.Batch678.valid27148
  · exact MergedCutProfiles.Batch678.valid27149
  · exact MergedCutProfiles.Batch678.valid27150
  · exact MergedCutProfiles.Batch678.valid27151
  · exact MergedCutProfiles.Batch678.valid27152
  · exact MergedCutProfiles.Batch678.valid27153
  · exact MergedCutProfiles.Batch678.valid27154
theorem numericValid4810 : retention4810.NumericValid := by decide +kernel
def certificate4810 : RatCutBinCertificate := ⟨⟨retention4810,(118086989583703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(54575687508028131/25000000000000000)⟩,(199989908927676709/200000000000000000),(17700866192807271/40000000000000000),(196705183928074921/1000000000000000000),(67881174924873229/500000000000000000)⟩
theorem valid4810 : certificate4810.Valid := by decide +kernel
theorem sound4810 : certificate4810.Sound := rat_cut_bin_certificate_sound certificate4810 profilesValid4810 numericValid4810 valid4810

def retention4811 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(1/2),64,1,(255384616602882347994592673071332382551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch678.profile27155,(fun _ => MergedCutProfiles.Batch678.profile27155)⟩
theorem profilesValid4811 : retention4811.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27155
theorem numericValid4811 : retention4811.NumericValid := by decide +kernel
def certificate4811 : RatCutBinCertificate := ⟨⟨retention4811,(118086989583703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(39401880565285023/40000000000000000)⟩,(199989908927676709/200000000000000000),(524803390976130833/1000000000000000000),(136839269101804437/1000000000000000000),(132743150417840677/1000000000000000000)⟩
theorem valid4811 : certificate4811.Valid := by decide +kernel
theorem sound4811 : certificate4811.Sound := rat_cut_bin_certificate_sound certificate4811 profilesValid4811 numericValid4811 valid4811

def certificates : List RatCutBinCertificate := [certificate4800,certificate4801,certificate4802,certificate4803,certificate4804,certificate4805,certificate4806,certificate4807,certificate4808,certificate4809,certificate4810,certificate4811]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4800,List.forall_mem_cons.mpr ⟨sound4801,List.forall_mem_cons.mpr ⟨sound4802,List.forall_mem_cons.mpr ⟨sound4803,List.forall_mem_cons.mpr ⟨sound4804,List.forall_mem_cons.mpr ⟨sound4805,List.forall_mem_cons.mpr ⟨sound4806,List.forall_mem_cons.mpr ⟨sound4807,List.forall_mem_cons.mpr ⟨sound4808,List.forall_mem_cons.mpr ⟨sound4809,List.forall_mem_cons.mpr ⟨sound4810,List.forall_mem_cons.mpr ⟨sound4811,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch400
