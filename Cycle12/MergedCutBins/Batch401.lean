import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch678
import Cycle12.MergedCutProfiles.Batch679
import Cycle12.MergedCutProfiles.Batch680

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch401

def retention4812 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(64000000000000000000/3023785039358298996097),(30810454878883848783/1000000000000000000),1,(67310614273969142948024933010487896893/30810454878883848783000000000000000000),false,MergedCutProfiles.Batch678.profile27156,(fun _ => MergedCutProfiles.Batch678.profile27156)⟩
theorem profilesValid4812 : retention4812.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27156
theorem numericValid4812 : retention4812.NumericValid := by decide +kernel
def certificate4812 : RatCutBinCertificate := ⟨⟨retention4812,(109557496896203739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(2173025268830849217/1000000000000000000)⟩,(499976594536322361/500000000000000000),(20716459844309227/1000000000000000000),(435913985077154787/500000000000000000),(353921107446949113/200000000000000000)⟩
theorem valid4812 : certificate4812.Valid := by decide +kernel
theorem sound4812 : certificate4812.Sound := rat_cut_bin_certificate_sound certificate4812 profilesValid4812 numericValid4812 valid4812

def retention4813 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(1/2),64,1,(255384616602882347994592673071332382551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch678.profile27155,(fun _ => MergedCutProfiles.Batch678.profile27155)⟩
theorem profilesValid4813 : retention4813.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27155
theorem numericValid4813 : retention4813.NumericValid := by decide +kernel
def certificate4813 : RatCutBinCertificate := ⟨⟨retention4813,(109557496896203739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(197190689243147543/200000000000000000)⟩,(499976594536322361/500000000000000000),(5707342331322563/125000000000000000),(800115607484787637/1000000000000000000),(388435663335620119/500000000000000000)⟩
theorem valid4813 : certificate4813.Valid := by decide +kernel
theorem sound4813 : certificate4813.Sound := rat_cut_bin_certificate_sound certificate4813 profilesValid4813 numericValid4813 valid4813

def retention4814 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(693476651452595892/3023785039358298996097),(1716526364981673/2500000000000000),4,(2189210089537071465374351496354167253/915480727990225600000000000000000000),false,MergedCutProfiles.Batch678.profile27157,(fun _ => MergedCutProfiles.Batch678.profile27157)⟩
theorem profilesValid4814 : retention4814.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27157
theorem numericValid4814 : retention4814.NumericValid := by decide +kernel
def certificate4814 : RatCutBinCertificate := ⟨⟨retention4814,(115049555458703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(468483501417657911/200000000000000000)⟩,(499975421228306419/500000000000000000),(86688444889684759/100000000000000000),(1856292943572951/200000000000000000),(4479760885777509/1000000000000000000)⟩
theorem valid4814 : certificate4814.Valid := by decide +kernel
theorem sound4814 : certificate4814.Sound := rat_cut_bin_certificate_sound certificate4814 profilesValid4814 numericValid4814 valid4814

def retention4815 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(898230012076425556/3023785039358298996097),(173369162863148973/250000000000000000),4,(1328634910171673309067993013314975763/554781321162076713600000000000000000),false,MergedCutProfiles.Batch678.profile27158,(fun _ => MergedCutProfiles.Batch678.profile27158)⟩
theorem profilesValid4815 : retention4815.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27158
theorem numericValid4815 : retention4815.NumericValid := by decide +kernel
def certificate4815 : RatCutBinCertificate := ⟨⟨retention4815,(115049555458703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(2345974937829884617/1000000000000000000)⟩,(499975421228306419/500000000000000000),(863365855408245391/1000000000000000000),(1958248966174379/200000000000000000),(947996499309397/200000000000000000)⟩
theorem valid4815 : certificate4815.Valid := by decide +kernel
theorem sound4815 : certificate4815.Sound := rat_cut_bin_certificate_sound certificate4815 profilesValid4815 numericValid4815 valid4815

def retention4816 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(6190618990774683532/3023785039358298996097),(224557503019106389/250000000000000000),(18/5),(53769481253713409784869789887692933119/22455750301910638900000000000000000000),false,MergedCutProfiles.Batch678.profile27159,(fun _ => MergedCutProfiles.Batch678.profile27159)⟩
theorem profilesValid4816 : retention4816.ProfilesValid := by
  exact MergedCutProfiles.Batch678.valid27159
theorem numericValid4816 : retention4816.NumericValid := by decide +kernel
def certificate4816 : RatCutBinCertificate := ⟨⟨retention4816,(115049555458703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(1175224447455393527/500000000000000000)⟩,(499975421228306419/500000000000000000),(202894075479762391/250000000000000000),(2373167182106847/125000000000000000),(2062527695674143/200000000000000000)⟩
theorem valid4816 : certificate4816.Valid := by decide +kernel
theorem sound4816 : certificate4816.Sound := rat_cut_bin_certificate_sound certificate4816 profilesValid4816 numericValid4816 valid4816

def retention4817 : RatCutRetentionCertificate := ⟨(81/2000),(163/4000),(1/40),(1547654747693670883/250000000000000000),(13/10),(42520875249608628813026115552377249673/19345684346170886037500000000000000000),false,MergedCutProfiles.Batch679.profile27160,(fun _ => MergedCutProfiles.Batch679.profile27160)⟩
theorem profilesValid4817 : retention4817.ProfilesValid := by
  exact MergedCutProfiles.Batch679.valid27160
theorem numericValid4817 : retention4817.NumericValid := by decide +kernel
def certificate4817 : RatCutBinCertificate := ⟨⟨retention4817,(115049555458703739/62500000000000000),(75985007536902399/1000000000000000000),(5720129285599643441/500000000000000000),(34639596741050693742707/1000000000000000000),(2182057199274997579/1000000000000000000)⟩,(499975421228306419/500000000000000000),(71780497197233803/100000000000000000),(22100748376813157/500000000000000000),(61385574992820863/1000000000000000000)⟩
theorem valid4817 : certificate4817.Valid := by decide +kernel
theorem sound4817 : certificate4817.Sound := rat_cut_bin_certificate_sound certificate4817 profilesValid4817 numericValid4817 valid4817

def retention4818 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(588913487696149412/3003289735309396365599),(583082661085296447/1000000000000000000),4,(4084617503809887394755980544475099/1822133315891551396875000000000000),true,MergedCutProfiles.Batch679.profile27161,![MergedCutProfiles.Batch679.profile27161,MergedCutProfiles.Batch679.profile27162,MergedCutProfiles.Batch679.profile27163,MergedCutProfiles.Batch679.profile27164,MergedCutProfiles.Batch679.profile27165,MergedCutProfiles.Batch679.profile27166,MergedCutProfiles.Batch679.profile27167,MergedCutProfiles.Batch679.profile27168,MergedCutProfiles.Batch679.profile27169,MergedCutProfiles.Batch679.profile27170,MergedCutProfiles.Batch679.profile27171,MergedCutProfiles.Batch679.profile27172,MergedCutProfiles.Batch679.profile27173,MergedCutProfiles.Batch679.profile27174,MergedCutProfiles.Batch679.profile27175,MergedCutProfiles.Batch679.profile27176]⟩
theorem profilesValid4818 : retention4818.ProfilesValid := by
  change ∀ j : Fin 16, (retention4818.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch679.valid27161
  · exact MergedCutProfiles.Batch679.valid27162
  · exact MergedCutProfiles.Batch679.valid27163
  · exact MergedCutProfiles.Batch679.valid27164
  · exact MergedCutProfiles.Batch679.valid27165
  · exact MergedCutProfiles.Batch679.valid27166
  · exact MergedCutProfiles.Batch679.valid27167
  · exact MergedCutProfiles.Batch679.valid27168
  · exact MergedCutProfiles.Batch679.valid27169
  · exact MergedCutProfiles.Batch679.valid27170
  · exact MergedCutProfiles.Batch679.valid27171
  · exact MergedCutProfiles.Batch679.valid27172
  · exact MergedCutProfiles.Batch679.valid27173
  · exact MergedCutProfiles.Batch679.valid27174
  · exact MergedCutProfiles.Batch679.valid27175
  · exact MergedCutProfiles.Batch679.valid27176
theorem numericValid4818 : retention4818.NumericValid := by decide +kernel
def certificate4818 : RatCutBinCertificate := ⟨⟨retention4818,(472608207551894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(2191300110211496811/1000000000000000000)⟩,(999949389362287809/1000000000000000000),(704806035416737661/1000000000000000000),(48629807750439879/1000000000000000000),(1348254604277351/62500000000000000)⟩
theorem valid4818 : certificate4818.Valid := by decide +kernel
theorem sound4818 : certificate4818.Sound := rat_cut_bin_certificate_sound certificate4818 profilesValid4818 numericValid4818 valid4818

def retention4819 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(87141961000000000/231022287331492028123),(147228371924037353/250000000000000000),4,(144058204177734462549/64000000000000000000),true,MergedCutProfiles.Batch679.profile27177,![MergedCutProfiles.Batch679.profile27177,MergedCutProfiles.Batch679.profile27164,MergedCutProfiles.Batch679.profile27166,MergedCutProfiles.Batch679.profile27178,MergedCutProfiles.Batch679.profile27170,MergedCutProfiles.Batch679.profile27172,MergedCutProfiles.Batch679.profile27174,MergedCutProfiles.Batch679.profile27176,MergedCutProfiles.Batch679.profile27179,MergedCutProfiles.Batch679.profile27180,MergedCutProfiles.Batch679.profile27181,MergedCutProfiles.Batch679.profile27182,MergedCutProfiles.Batch679.profile27183,MergedCutProfiles.Batch679.profile27184,MergedCutProfiles.Batch679.profile27185,MergedCutProfiles.Batch679.profile27186]⟩
theorem profilesValid4819 : retention4819.ProfilesValid := by
  change ∀ j : Fin 16, (retention4819.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch679.valid27177
  · exact MergedCutProfiles.Batch679.valid27164
  · exact MergedCutProfiles.Batch679.valid27166
  · exact MergedCutProfiles.Batch679.valid27178
  · exact MergedCutProfiles.Batch679.valid27170
  · exact MergedCutProfiles.Batch679.valid27172
  · exact MergedCutProfiles.Batch679.valid27174
  · exact MergedCutProfiles.Batch679.valid27176
  · exact MergedCutProfiles.Batch679.valid27179
  · exact MergedCutProfiles.Batch679.valid27180
  · exact MergedCutProfiles.Batch679.valid27181
  · exact MergedCutProfiles.Batch679.valid27182
  · exact MergedCutProfiles.Batch679.valid27183
  · exact MergedCutProfiles.Batch679.valid27184
  · exact MergedCutProfiles.Batch679.valid27185
  · exact MergedCutProfiles.Batch679.valid27186
theorem numericValid4819 : retention4819.NumericValid := by decide +kernel
def certificate4819 : RatCutBinCertificate := ⟨⟨retention4819,(472608207551894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(2200541793622063899/1000000000000000000)⟩,(999949389362287809/1000000000000000000),(348591383004486699/500000000000000000),(51338052779921987/1000000000000000000),(4578884962948241/200000000000000000)⟩
theorem valid4819 : certificate4819.Valid := by decide +kernel
theorem sound4819 : certificate4819.Sound := rat_cut_bin_certificate_sound certificate4819 profilesValid4819 numericValid4819 valid4819

def retention4820 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(1577130045399414620/3003289735309396365599),(1132845493/1000000000),(14/5),(6799131727872200011274399751238879/2832113732500000000000000000000000),true,MergedCutProfiles.Batch679.profile27187,![MergedCutProfiles.Batch679.profile27187,MergedCutProfiles.Batch679.profile27165,MergedCutProfiles.Batch679.profile27168,MergedCutProfiles.Batch679.profile27171,MergedCutProfiles.Batch679.profile27174,MergedCutProfiles.Batch679.profile27176,MergedCutProfiles.Batch679.profile27180,MergedCutProfiles.Batch679.profile27188,MergedCutProfiles.Batch679.profile27183,MergedCutProfiles.Batch679.profile27184,MergedCutProfiles.Batch679.profile27185,MergedCutProfiles.Batch679.profile27189,MergedCutProfiles.Batch679.profile27190,MergedCutProfiles.Batch679.profile27191,MergedCutProfiles.Batch679.profile27192,MergedCutProfiles.Batch679.profile27193]⟩
theorem profilesValid4820 : retention4820.ProfilesValid := by
  change ∀ j : Fin 16, (retention4820.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch679.valid27187
  · exact MergedCutProfiles.Batch679.valid27165
  · exact MergedCutProfiles.Batch679.valid27168
  · exact MergedCutProfiles.Batch679.valid27171
  · exact MergedCutProfiles.Batch679.valid27174
  · exact MergedCutProfiles.Batch679.valid27176
  · exact MergedCutProfiles.Batch679.valid27180
  · exact MergedCutProfiles.Batch679.valid27188
  · exact MergedCutProfiles.Batch679.valid27183
  · exact MergedCutProfiles.Batch679.valid27184
  · exact MergedCutProfiles.Batch679.valid27185
  · exact MergedCutProfiles.Batch679.valid27189
  · exact MergedCutProfiles.Batch679.valid27190
  · exact MergedCutProfiles.Batch679.valid27191
  · exact MergedCutProfiles.Batch679.valid27192
  · exact MergedCutProfiles.Batch679.valid27193
theorem numericValid4820 : retention4820.NumericValid := by decide +kernel
def certificate4820 : RatCutBinCertificate := ⟨⟨retention4820,(472608207551894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(118273479672380289/50000000000000000)⟩,(999949389362287809/1000000000000000000),(220139442603290681/500000000000000000),(99269651888705113/500000000000000000),(132443719397669129/1000000000000000000)⟩
theorem valid4820 : certificate4820.Valid := by decide +kernel
theorem sound4820 : certificate4820.Sound := rat_cut_bin_certificate_sound certificate4820 profilesValid4820 numericValid4820 valid4820

def retention4821 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(64000000000000000000/3003289735309396365599),(78856502269970731/50000000000000000),(11/5),(141420840834593220191/64000000000000000000),true,MergedCutProfiles.Batch679.profile27194,![MergedCutProfiles.Batch679.profile27194,MergedCutProfiles.Batch679.profile27195,MergedCutProfiles.Batch679.profile27196,MergedCutProfiles.Batch679.profile27197,MergedCutProfiles.Batch679.profile27198,MergedCutProfiles.Batch679.profile27199,MergedCutProfiles.Batch680.profile27200,MergedCutProfiles.Batch680.profile27201,MergedCutProfiles.Batch680.profile27202,MergedCutProfiles.Batch680.profile27203,MergedCutProfiles.Batch680.profile27204,MergedCutProfiles.Batch680.profile27205,MergedCutProfiles.Batch680.profile27206,MergedCutProfiles.Batch680.profile27207,MergedCutProfiles.Batch680.profile27208,MergedCutProfiles.Batch680.profile27209]⟩
theorem profilesValid4821 : retention4821.ProfilesValid := by
  change ∀ j : Fin 16, (retention4821.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch679.valid27194
  · exact MergedCutProfiles.Batch679.valid27195
  · exact MergedCutProfiles.Batch679.valid27196
  · exact MergedCutProfiles.Batch679.valid27197
  · exact MergedCutProfiles.Batch679.valid27198
  · exact MergedCutProfiles.Batch679.valid27199
  · exact MergedCutProfiles.Batch680.valid27200
  · exact MergedCutProfiles.Batch680.valid27201
  · exact MergedCutProfiles.Batch680.valid27202
  · exact MergedCutProfiles.Batch680.valid27203
  · exact MergedCutProfiles.Batch680.valid27204
  · exact MergedCutProfiles.Batch680.valid27205
  · exact MergedCutProfiles.Batch680.valid27206
  · exact MergedCutProfiles.Batch680.valid27207
  · exact MergedCutProfiles.Batch680.valid27208
  · exact MergedCutProfiles.Batch680.valid27209
theorem numericValid4821 : retention4821.NumericValid := by decide +kernel
def certificate4821 : RatCutBinCertificate := ⟨⟨retention4821,(472608207551894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(1090999220374391347/500000000000000000)⟩,(999949389362287809/1000000000000000000),(8168552463870731/20000000000000000),(225848678552597841/1000000000000000000),(34838803321219929/200000000000000000)⟩
theorem valid4821 : certificate4821.Valid := by decide +kernel
theorem sound4821 : certificate4821.Sound := rat_cut_bin_certificate_sound certificate4821 profilesValid4821 numericValid4821 valid4821

def retention4822 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(1/2),64,1,(255384855766391590003702603419612725079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch680.profile27210,(fun _ => MergedCutProfiles.Batch680.profile27210)⟩
theorem profilesValid4822 : retention4822.ProfilesValid := by
  exact MergedCutProfiles.Batch680.valid27210
theorem numericValid4822 : retention4822.NumericValid := by decide +kernel
def certificate4822 : RatCutBinCertificate := ⟨⟨retention4822,(472608207551894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(985005192584937467/1000000000000000000)⟩,(999949389362287809/1000000000000000000),(16416460265829583/31250000000000000),(136502118117378707/1000000000000000000),(66205267062222093/500000000000000000)⟩
theorem valid4822 : certificate4822.Valid := by decide +kernel
theorem sound4822 : certificate4822.Sound := rat_cut_bin_certificate_sound certificate4822 profilesValid4822 numericValid4822 valid4822

def retention4823 : RatCutRetentionCertificate := ⟨(163/4000),(327/8000),(64000000000000000000/3003289735309396365599),(30961511562218037573/1000000000000000000),1,(2817952306018882273509678352693644297/1290062981759084898875000000000000000),false,MergedCutProfiles.Batch680.profile27211,(fun _ => MergedCutProfiles.Batch680.profile27211)⟩
theorem profilesValid4823 : retention4823.ProfilesValid := by
  exact MergedCutProfiles.Batch680.valid27211
theorem numericValid4823 : retention4823.NumericValid := by decide +kernel
def certificate4823 : RatCutBinCertificate := ⟨⟨retention4823,(438216848051894219/250000000000000000),(19124041420776849/250000000000000000),(11484435637206276463/1000000000000000000),(17257197573927185931247/500000000000000000),(1086338454002171177/500000000000000000)⟩,(124994134034527747/125000000000000000),(10317907977912969/500000000000000000),(174414452137186711/200000000000000000),(885202542073571443/500000000000000000)⟩
theorem valid4823 : certificate4823.Valid := by decide +kernel
theorem sound4823 : certificate4823.Sound := rat_cut_bin_certificate_sound certificate4823 profilesValid4823 numericValid4823 valid4823

def certificates : List RatCutBinCertificate := [certificate4812,certificate4813,certificate4814,certificate4815,certificate4816,certificate4817,certificate4818,certificate4819,certificate4820,certificate4821,certificate4822,certificate4823]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4812,List.forall_mem_cons.mpr ⟨sound4813,List.forall_mem_cons.mpr ⟨sound4814,List.forall_mem_cons.mpr ⟨sound4815,List.forall_mem_cons.mpr ⟨sound4816,List.forall_mem_cons.mpr ⟨sound4817,List.forall_mem_cons.mpr ⟨sound4818,List.forall_mem_cons.mpr ⟨sound4819,List.forall_mem_cons.mpr ⟨sound4820,List.forall_mem_cons.mpr ⟨sound4821,List.forall_mem_cons.mpr ⟨sound4822,List.forall_mem_cons.mpr ⟨sound4823,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch401
