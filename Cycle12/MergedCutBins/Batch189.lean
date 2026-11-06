import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch349
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch351

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch189

def retention2268 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(346664680978726413/13329703287103710401),(219344325192120139/200000000000000000),(51/20),(551609656953198559051/256000000000000000000),true,MergedCutProfiles.Batch350.profile14004,![MergedCutProfiles.Batch350.profile14004,MergedCutProfiles.Batch350.profile14005,MergedCutProfiles.Batch350.profile14006,MergedCutProfiles.Batch350.profile14007,MergedCutProfiles.Batch350.profile14008,MergedCutProfiles.Batch350.profile14009,MergedCutProfiles.Batch349.profile13960,MergedCutProfiles.Batch350.profile14010,MergedCutProfiles.Batch350.profile14011,MergedCutProfiles.Batch350.profile14012,MergedCutProfiles.Batch350.profile14013,MergedCutProfiles.Batch350.profile14014,MergedCutProfiles.Batch350.profile14015,MergedCutProfiles.Batch350.profile14016,MergedCutProfiles.Batch350.profile14017,MergedCutProfiles.Batch350.profile14018]⟩
theorem profilesValid2268 : retention2268.ProfilesValid := by
  change ∀ j : Fin 16, (retention2268.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch350.valid14004
  · exact MergedCutProfiles.Batch350.valid14005
  · exact MergedCutProfiles.Batch350.valid14006
  · exact MergedCutProfiles.Batch350.valid14007
  · exact MergedCutProfiles.Batch350.valid14008
  · exact MergedCutProfiles.Batch350.valid14009
  · exact MergedCutProfiles.Batch349.valid13960
  · exact MergedCutProfiles.Batch350.valid14010
  · exact MergedCutProfiles.Batch350.valid14011
  · exact MergedCutProfiles.Batch350.valid14012
  · exact MergedCutProfiles.Batch350.valid14013
  · exact MergedCutProfiles.Batch350.valid14014
  · exact MergedCutProfiles.Batch350.valid14015
  · exact MergedCutProfiles.Batch350.valid14016
  · exact MergedCutProfiles.Batch350.valid14017
  · exact MergedCutProfiles.Batch350.valid14018
theorem numericValid2268 : retention2268.NumericValid := by decide +kernel
def certificate2268 : RatCutBinCertificate := ⟨⟨retention2268,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(2122119676263549609/1000000000000000000)⟩,(498708035098880483/500000000000000000),(368607708120218097/1000000000000000000),(131755081172250887/500000000000000000),(168499237262230363/1000000000000000000)⟩
theorem valid2268 : certificate2268.Valid := by decide +kernel
theorem sound2268 : certificate2268.Sound := rat_cut_bin_certificate_sound certificate2268 profilesValid2268 numericValid2268 valid2268

def retention2269 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(11594766145174407959/66648516435518552005),(346664680978726413/200000000000000000),(37/20),(20948635912030092163090578676206923351/12325855323688050240000000000000000000),false,MergedCutProfiles.Batch350.profile14019,(fun _ => MergedCutProfiles.Batch350.profile14019)⟩
theorem profilesValid2269 : retention2269.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14019
theorem numericValid2269 : retention2269.NumericValid := by decide +kernel
def certificate2269 : RatCutBinCertificate := ⟨⟨retention2269,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(418978408769347401/250000000000000000)⟩,(498708035098880483/500000000000000000),(98342573902821377/250000000000000000),(59903012410080019/250000000000000000),(168753183616972731/1000000000000000000)⟩
theorem valid2269 : certificate2269.Valid := by decide +kernel
theorem sound2269 : certificate2269.Sound := rat_cut_bin_certificate_sound certificate2269 profilesValid2269 numericValid2269 valid2269

def retention2270 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(31051172097402234478/66648516435518552005),(11594766145174407959/1000000000000000000),(21/20),(19755706613525590864194335302918232087519/18551625832279052734400000000000000000000),false,MergedCutProfiles.Batch350.profile14020,(fun _ => MergedCutProfiles.Batch350.profile14020)⟩
theorem profilesValid2270 : retention2270.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14020
theorem numericValid2270 : retention2270.NumericValid := by decide +kernel
def certificate2270 : RatCutBinCertificate := ⟨⟨retention2270,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(1051478859423094239/1000000000000000000)⟩,(498708035098880483/500000000000000000),(455612997519061477/1000000000000000000),(93112072359658137/500000000000000000),(171848721601050893/1000000000000000000)⟩
theorem valid2270 : certificate2270.Valid := by decide +kernel
theorem sound2270 : certificate2270.Sound := rat_cut_bin_certificate_sound certificate2270 profilesValid2270 numericValid2270 valid2270

def retention2271 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(32961444881171988986/66648516435518552005),(15525586048701117239/500000000000000000),1,(124721781596768191609229638758708925807/124204688389608937912000000000000000000),false,MergedCutProfiles.Batch350.profile14021,(fun _ => MergedCutProfiles.Batch350.profile14021)⟩
theorem profilesValid2271 : retention2271.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14021
theorem numericValid2271 : retention2271.NumericValid := by decide +kernel
def certificate2271 : RatCutBinCertificate := ⟨⟨retention2271,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(495688567384178183/500000000000000000)⟩,(498708035098880483/500000000000000000),(2895105287941337/6250000000000000),(180309824807329591/1000000000000000000),(86384516936762249/500000000000000000)⟩
theorem valid2271 : certificate2271.Valid := by decide +kernel
theorem sound2271 : certificate2271.Sound := rat_cut_bin_certificate_sound certificate2271 profilesValid2271 numericValid2271 valid2271

def retention2272 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(33291059329983708876/66648516435518552005),(16480722440585994493/500000000000000000),1,(64048242098320779385571819591687111/64377822033539040988281250000000000),false,MergedCutProfiles.Batch350.profile14022,(fun _ => MergedCutProfiles.Batch350.profile14022)⟩
theorem profilesValid2272 : retention2272.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14022
theorem numericValid2272 : retention2272.NumericValid := by decide +kernel
def certificate2272 : RatCutBinCertificate := ⟨⟨retention2272,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(196418887781216963/200000000000000000)⟩,(498708035098880483/500000000000000000),(466897259441391439/1000000000000000000),(177492129353699351/1000000000000000000),(168825967578766531/1000000000000000000)⟩
theorem valid2272 : certificate2272.Valid := by decide +kernel
theorem sound2272 : certificate2272.Sound := rat_cut_bin_certificate_sound certificate2272 profilesValid2272 numericValid2272 valid2272

def retention2273 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),(8322764832495927219/250000000000000000),1,(11030140616561046985913558246824003029/11097019776661236292000000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid2273 : retention2273.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid2273 : retention2273.NumericValid := by decide +kernel
def certificate2273 : RatCutBinCertificate := ⟨⟨retention2273,(509833898978535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(981187135478549201/1000000000000000000)⟩,(498708035098880483/500000000000000000),(233608289327897269/500000000000000000),(35449806401395423/200000000000000000),(33698355952523537/200000000000000000)⟩
theorem valid2273 : certificate2273.Valid := by decide +kernel
theorem sound2273 : certificate2273.Sound := rat_cut_bin_certificate_sound certificate2273 profilesValid2273 numericValid2273 valid2273

def retention2274 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(28767695372761399977/66648516435518552005),(351625034862064007/62500000000000000),(21/20),(304065496312912561229256594303340807/274707058485987505468750000000000000),false,MergedCutProfiles.Batch350.profile14024,(fun _ => MergedCutProfiles.Batch350.profile14024)⟩
theorem profilesValid2274 : retention2274.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14024
theorem numericValid2274 : retention2274.NumericValid := by decide +kernel
def certificate2274 : RatCutBinCertificate := ⟨⟨retention2274,(583011207478535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(1091519228073696717/1000000000000000000)⟩,(249261279486994771/250000000000000000),(108866833786281461/500000000000000000),(225071869679323469/500000000000000000),(396660453594783451/1000000000000000000)⟩
theorem valid2274 : certificate2274.Valid := by decide +kernel
theorem sound2274 : certificate2274.Sound := rat_cut_bin_certificate_sound certificate2274 profilesValid2274 numericValid2274 valid2274

def retention2275 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(33067724005264498169/66648516435518552005),(28767695372761399977/1000000000000000000),1,(179864093495770170654704817014913689/179798096079758749856250000000000000),false,MergedCutProfiles.Batch350.profile14025,(fun _ => MergedCutProfiles.Batch350.profile14025)⟩
theorem profilesValid2275 : retention2275.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14025
theorem numericValid2275 : retention2275.NumericValid := by decide +kernel
def certificate2275 : RatCutBinCertificate := ⟨⟨retention2275,(583011207478535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(985745750964675653/1000000000000000000)⟩,(249261279486994771/250000000000000000),(2410971434793183/10000000000000000),(415822377004129259/1000000000000000000),(395124760906758657/1000000000000000000)⟩
theorem valid2275 : certificate2275.Valid := by decide +kernel
theorem sound2275 : certificate2275.Sound := rat_cut_bin_certificate_sound certificate2275 profilesValid2275 numericValid2275 valid2275

def retention2276 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1/2),(33067724005264498169/1000000000000000000),1,(6573350063975749057228784776005844077/6613544801052899633800000000000000000),false,MergedCutProfiles.Batch350.profile14023,(fun _ => MergedCutProfiles.Batch350.profile14023)⟩
theorem profilesValid2276 : retention2276.ProfilesValid := by
  exact MergedCutProfiles.Batch350.valid14023
theorem numericValid2276 : retention2276.NumericValid := by decide +kernel
def certificate2276 : RatCutBinCertificate := ⟨⟨retention2276,(583011207478535091/250000000000000000),(69043717129131353/1000000000000000000),(5506125422214505869/500000000000000000),(737870866433231862963/1000000000000000000),(979301054217288937/1000000000000000000)⟩,(249261279486994771/250000000000000000),(121341891612896329/500000000000000000),(206787349887746199/500000000000000000),(392185559523848593/1000000000000000000)⟩
theorem valid2276 : certificate2276.Valid := by decide +kernel
theorem sound2276 : certificate2276.Sound := rat_cut_bin_certificate_sound certificate2276 profilesValid2276 numericValid2276 valid2276

def retention2277 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(255699004067297208/21006340554727543465),(759501992279100617/1000000000000000000),(7/2),(575343719318235748217/256000000000000000000),true,MergedCutProfiles.Batch350.profile14026,![MergedCutProfiles.Batch350.profile14026,MergedCutProfiles.Batch350.profile14027,MergedCutProfiles.Batch350.profile14028,MergedCutProfiles.Batch350.profile14029,MergedCutProfiles.Batch350.profile14030,MergedCutProfiles.Batch350.profile14031,MergedCutProfiles.Batch350.profile14032,MergedCutProfiles.Batch350.profile14033,MergedCutProfiles.Batch350.profile14034,MergedCutProfiles.Batch350.profile14035,MergedCutProfiles.Batch350.profile14036,MergedCutProfiles.Batch350.profile14037,MergedCutProfiles.Batch350.profile14038,MergedCutProfiles.Batch350.profile14039,MergedCutProfiles.Batch351.profile14040,MergedCutProfiles.Batch351.profile14041]⟩
theorem profilesValid2277 : retention2277.ProfilesValid := by
  change ∀ j : Fin 16, (retention2277.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch350.valid14026
  · exact MergedCutProfiles.Batch350.valid14027
  · exact MergedCutProfiles.Batch350.valid14028
  · exact MergedCutProfiles.Batch350.valid14029
  · exact MergedCutProfiles.Batch350.valid14030
  · exact MergedCutProfiles.Batch350.valid14031
  · exact MergedCutProfiles.Batch350.valid14032
  · exact MergedCutProfiles.Batch350.valid14033
  · exact MergedCutProfiles.Batch350.valid14034
  · exact MergedCutProfiles.Batch350.valid14035
  · exact MergedCutProfiles.Batch350.valid14036
  · exact MergedCutProfiles.Batch350.valid14037
  · exact MergedCutProfiles.Batch350.valid14038
  · exact MergedCutProfiles.Batch350.valid14039
  · exact MergedCutProfiles.Batch351.valid14040
  · exact MergedCutProfiles.Batch351.valid14041
theorem numericValid2277 : retention2277.NumericValid := by decide +kernel
def certificate2277 : RatCutBinCertificate := ⟨⟨retention2277,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(1100429147658783633/500000000000000000)⟩,(99731946768931759/100000000000000000),(420343099446205313/1000000000000000000),(53837885885794123/250000000000000000),(109167476270110303/1000000000000000000)⟩
theorem valid2277 : certificate2277.Valid := by decide +kernel
theorem sound2277 : certificate2277.Sound := rat_cut_bin_certificate_sound certificate2277 profilesValid2277 numericValid2277 valid2277

def retention2278 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(185347353259919237/12603804332836526079),(95887126525236453/125000000000000000),(69/20),(356775825132389025789/160000000000000000000),true,MergedCutProfiles.Batch351.profile14042,![MergedCutProfiles.Batch351.profile14042,MergedCutProfiles.Batch351.profile14043,MergedCutProfiles.Batch351.profile14044,MergedCutProfiles.Batch351.profile14045,MergedCutProfiles.Batch350.profile14031,MergedCutProfiles.Batch351.profile14046,MergedCutProfiles.Batch351.profile14047,MergedCutProfiles.Batch351.profile14048,MergedCutProfiles.Batch351.profile14049,MergedCutProfiles.Batch351.profile14050,MergedCutProfiles.Batch351.profile14051,MergedCutProfiles.Batch351.profile14052,MergedCutProfiles.Batch351.profile14053,MergedCutProfiles.Batch351.profile14054,MergedCutProfiles.Batch351.profile14055,MergedCutProfiles.Batch351.profile14056]⟩
theorem profilesValid2278 : retention2278.ProfilesValid := by
  change ∀ j : Fin 16, (retention2278.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch351.valid14042
  · exact MergedCutProfiles.Batch351.valid14043
  · exact MergedCutProfiles.Batch351.valid14044
  · exact MergedCutProfiles.Batch351.valid14045
  · exact MergedCutProfiles.Batch350.valid14031
  · exact MergedCutProfiles.Batch351.valid14046
  · exact MergedCutProfiles.Batch351.valid14047
  · exact MergedCutProfiles.Batch351.valid14048
  · exact MergedCutProfiles.Batch351.valid14049
  · exact MergedCutProfiles.Batch351.valid14050
  · exact MergedCutProfiles.Batch351.valid14051
  · exact MergedCutProfiles.Batch351.valid14052
  · exact MergedCutProfiles.Batch351.valid14053
  · exact MergedCutProfiles.Batch351.valid14054
  · exact MergedCutProfiles.Batch351.valid14055
  · exact MergedCutProfiles.Batch351.valid14056
theorem numericValid2278 : retention2278.NumericValid := by decide +kernel
def certificate2278 : RatCutBinCertificate := ⟨⟨retention2278,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(545984048110429803/250000000000000000)⟩,(99731946768931759/100000000000000000),(421438052904273633/1000000000000000000),(107202006985225291/500000000000000000),(54590552418519949/500000000000000000)⟩
theorem valid2278 : certificate2278.Valid := by decide +kernel
theorem sound2278 : certificate2278.Sound := rat_cut_bin_certificate_sound certificate2278 profilesValid2278 numericValid2278 valid2278

def retention2279 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(69744900200000000/4201268110945508693),(185347353259919237/200000000000000000),(29/10),(35250175638039465767/16000000000000000000),true,MergedCutProfiles.Batch351.profile14057,![MergedCutProfiles.Batch351.profile14057,MergedCutProfiles.Batch351.profile14058,MergedCutProfiles.Batch351.profile14059,MergedCutProfiles.Batch351.profile14060,MergedCutProfiles.Batch351.profile14061,MergedCutProfiles.Batch351.profile14062,MergedCutProfiles.Batch351.profile14063,MergedCutProfiles.Batch351.profile14049,MergedCutProfiles.Batch351.profile14064,MergedCutProfiles.Batch351.profile14065,MergedCutProfiles.Batch351.profile14040,MergedCutProfiles.Batch351.profile14066,MergedCutProfiles.Batch351.profile14067,MergedCutProfiles.Batch351.profile14068,MergedCutProfiles.Batch351.profile14069,MergedCutProfiles.Batch351.profile14070]⟩
theorem profilesValid2279 : retention2279.ProfilesValid := by
  change ∀ j : Fin 16, (retention2279.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch351.valid14057
  · exact MergedCutProfiles.Batch351.valid14058
  · exact MergedCutProfiles.Batch351.valid14059
  · exact MergedCutProfiles.Batch351.valid14060
  · exact MergedCutProfiles.Batch351.valid14061
  · exact MergedCutProfiles.Batch351.valid14062
  · exact MergedCutProfiles.Batch351.valid14063
  · exact MergedCutProfiles.Batch351.valid14049
  · exact MergedCutProfiles.Batch351.valid14064
  · exact MergedCutProfiles.Batch351.valid14065
  · exact MergedCutProfiles.Batch351.valid14040
  · exact MergedCutProfiles.Batch351.valid14066
  · exact MergedCutProfiles.Batch351.valid14067
  · exact MergedCutProfiles.Batch351.valid14068
  · exact MergedCutProfiles.Batch351.valid14069
  · exact MergedCutProfiles.Batch351.valid14070
theorem numericValid2279 : retention2279.NumericValid := by decide +kernel
def certificate2279 : RatCutBinCertificate := ⟨⟨retention2279,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(270567837994950587/125000000000000000)⟩,(99731946768931759/100000000000000000),(387636788530088397/1000000000000000000),(61250778884340973/250000000000000000),(35668507524227443/250000000000000000)⟩
theorem valid2279 : certificate2279.Valid := by decide +kernel
theorem sound2279 : certificate2279.Sound := rat_cut_bin_certificate_sound certificate2279 profilesValid2279 numericValid2279 valid2279

def certificates : List RatCutBinCertificate := [certificate2268,certificate2269,certificate2270,certificate2271,certificate2272,certificate2273,certificate2274,certificate2275,certificate2276,certificate2277,certificate2278,certificate2279]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2268,List.forall_mem_cons.mpr ⟨sound2269,List.forall_mem_cons.mpr ⟨sound2270,List.forall_mem_cons.mpr ⟨sound2271,List.forall_mem_cons.mpr ⟨sound2272,List.forall_mem_cons.mpr ⟨sound2273,List.forall_mem_cons.mpr ⟨sound2274,List.forall_mem_cons.mpr ⟨sound2275,List.forall_mem_cons.mpr ⟨sound2276,List.forall_mem_cons.mpr ⟨sound2277,List.forall_mem_cons.mpr ⟨sound2278,List.forall_mem_cons.mpr ⟨sound2279,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch189
