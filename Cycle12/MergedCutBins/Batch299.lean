import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch429
import Cycle12.MergedCutProfiles.Batch430
import Cycle12.MergedCutProfiles.Batch431
import Cycle12.MergedCutProfiles.Batch551
import Cycle12.MergedCutProfiles.Batch552

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch299

def retention3588 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(23203409259936831117/50624096366191786564),(4332173086668278667/500000000000000000),1,(36447057058367548316120066280758553983/34657384693346229336000000000000000000),false,MergedCutProfiles.Batch551.profile22050,(fun _ => MergedCutProfiles.Batch551.profile22050)⟩
theorem profilesValid3588 : retention3588.ProfilesValid := by
  exact MergedCutProfiles.Batch551.valid22050
theorem numericValid3588 : retention3588.NumericValid := by decide +kernel
def certificate3588 : RatCutBinCertificate := ⟨⟨retention3588,(2330395604009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(102153628338783477/100000000000000000)⟩,(199589496770949581/200000000000000000),(290673907419993/2500000000000000),(15781743659522681/25000000000000000),(575586892307287869/1000000000000000000)⟩
theorem valid3588 : certificate3588.Valid := by decide +kernel
theorem sound3588 : certificate3588.Sound := rat_cut_bin_certificate_sound certificate3588 profilesValid3588 numericValid3588 valid3588

def retention3589 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1092433361328490655/2201047668095295068),(23203409259936831117/1000000000000000000),1,(18526298867633217358209463886114554231/18562727407949464893600000000000000000),false,MergedCutProfiles.Batch551.profile22051,(fun _ => MergedCutProfiles.Batch551.profile22051)⟩
theorem profilesValid3589 : retention3589.ProfilesValid := by
  exact MergedCutProfiles.Batch551.valid22051
theorem numericValid3589 : retention3589.NumericValid := by decide +kernel
def certificate3589 : RatCutBinCertificate := ⟨⟨retention3589,(2330395604009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(967935390162627027/1000000000000000000)⟩,(199589496770949581/200000000000000000),(122708166715032521/1000000000000000000),(24716678305755569/40000000000000000),(572941456036900271/1000000000000000000)⟩
theorem valid3589 : certificate3589.Valid := by decide +kernel
theorem sound3589 : certificate3589.Sound := rat_cut_bin_certificate_sound certificate3589 profilesValid3589 numericValid3589 valid3589

def retention3590 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),(5025193462111057013/200000000000000000),1,(24916332827236915553460308375667297229/25125967310555285065000000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid3590 : retention3590.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid3590 : retention3590.NumericValid := by decide +kernel
def certificate3590 : RatCutBinCertificate := ⟨⟨retention3590,(2330395604009882821/1000000000000000000),(225107070921290071/1000000000000000000),(17427134482546462459/1000000000000000000),(885034598884324527611/1000000000000000000),(961554531845419577/1000000000000000000)⟩,(199589496770949581/200000000000000000),(123522455868940609/1000000000000000000),(77031141391471399/125000000000000000),(142378632525350531/250000000000000000)⟩
theorem valid3590 : certificate3590.Valid := by decide +kernel
theorem sound3590 : certificate3590.Sound := rat_cut_bin_certificate_sound certificate3590 profilesValid3590 numericValid3590 valid3590

def retention3591 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(947807990246920539/49701584545203616610),(187684750543944661/200000000000000000),(14/5),(35361929711233310321/16000000000000000000),true,MergedCutProfiles.Batch551.profile22052,![MergedCutProfiles.Batch551.profile22052,MergedCutProfiles.Batch551.profile22053,MergedCutProfiles.Batch551.profile22054,MergedCutProfiles.Batch551.profile22055,MergedCutProfiles.Batch551.profile22056,MergedCutProfiles.Batch551.profile22057,MergedCutProfiles.Batch551.profile22058,MergedCutProfiles.Batch551.profile22059,MergedCutProfiles.Batch551.profile22060,MergedCutProfiles.Batch551.profile22061,MergedCutProfiles.Batch551.profile22062,MergedCutProfiles.Batch551.profile22063,MergedCutProfiles.Batch430.profile17204,MergedCutProfiles.Batch551.profile22064,MergedCutProfiles.Batch551.profile22065,MergedCutProfiles.Batch551.profile22066]⟩
theorem profilesValid3591 : retention3591.ProfilesValid := by
  change ∀ j : Fin 16, (retention3591.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch551.valid22052
  · exact MergedCutProfiles.Batch551.valid22053
  · exact MergedCutProfiles.Batch551.valid22054
  · exact MergedCutProfiles.Batch551.valid22055
  · exact MergedCutProfiles.Batch551.valid22056
  · exact MergedCutProfiles.Batch551.valid22057
  · exact MergedCutProfiles.Batch551.valid22058
  · exact MergedCutProfiles.Batch551.valid22059
  · exact MergedCutProfiles.Batch551.valid22060
  · exact MergedCutProfiles.Batch551.valid22061
  · exact MergedCutProfiles.Batch551.valid22062
  · exact MergedCutProfiles.Batch551.valid22063
  · exact MergedCutProfiles.Batch430.valid17204
  · exact MergedCutProfiles.Batch551.valid22064
  · exact MergedCutProfiles.Batch551.valid22065
  · exact MergedCutProfiles.Batch551.valid22066
theorem numericValid3591 : retention3591.NumericValid := by decide +kernel
def certificate3591 : RatCutBinCertificate := ⟨⟨retention3591,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(2126560531375219819/1000000000000000000)⟩,(124747056383452567/125000000000000000),(71178377546489137/250000000000000000),(357574401588094097/1000000000000000000),(210164350003631841/1000000000000000000)⟩
theorem valid3591 : certificate3591.Valid := by decide +kernel
theorem sound3591 : certificate3591.Sound := rat_cut_bin_certificate_sound certificate3591 profilesValid3591 numericValid3591 valid3591

def retention3592 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(42322140474165581/1911599405584754485),(947807990246920539/1000000000000000000),(11/4),(1751841984361819899/800000000000000000),true,MergedCutProfiles.Batch551.profile22067,![MergedCutProfiles.Batch551.profile22067,MergedCutProfiles.Batch551.profile22068,MergedCutProfiles.Batch551.profile22069,MergedCutProfiles.Batch551.profile22070,MergedCutProfiles.Batch551.profile22071,MergedCutProfiles.Batch551.profile22072,MergedCutProfiles.Batch551.profile22073,MergedCutProfiles.Batch551.profile22074,MergedCutProfiles.Batch551.profile22075,MergedCutProfiles.Batch551.profile22076,MergedCutProfiles.Batch429.profile17188,MergedCutProfiles.Batch551.profile22077,MergedCutProfiles.Batch551.profile22078,MergedCutProfiles.Batch551.profile22079,MergedCutProfiles.Batch552.profile22080,MergedCutProfiles.Batch552.profile22081]⟩
theorem profilesValid3592 : retention3592.ProfilesValid := by
  change ∀ j : Fin 16, (retention3592.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch551.valid22067
  · exact MergedCutProfiles.Batch551.valid22068
  · exact MergedCutProfiles.Batch551.valid22069
  · exact MergedCutProfiles.Batch551.valid22070
  · exact MergedCutProfiles.Batch551.valid22071
  · exact MergedCutProfiles.Batch551.valid22072
  · exact MergedCutProfiles.Batch551.valid22073
  · exact MergedCutProfiles.Batch551.valid22074
  · exact MergedCutProfiles.Batch551.valid22075
  · exact MergedCutProfiles.Batch551.valid22076
  · exact MergedCutProfiles.Batch429.valid17188
  · exact MergedCutProfiles.Batch551.valid22077
  · exact MergedCutProfiles.Batch551.valid22078
  · exact MergedCutProfiles.Batch551.valid22079
  · exact MergedCutProfiles.Batch552.valid22080
  · exact MergedCutProfiles.Batch552.valid22081
theorem numericValid3592 : retention3592.NumericValid := by decide +kernel
def certificate3592 : RatCutBinCertificate := ⟨⟨retention3592,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(2107734482955684583/1000000000000000000)⟩,(124747056383452567/125000000000000000),(143007703302125757/500000000000000000),(355943002545244907/1000000000000000000),(210305285000798081/1000000000000000000)⟩
theorem valid3592 : certificate3592.Valid := by decide +kernel
theorem sound3592 : certificate3592.Sound := rat_cut_bin_certificate_sound certificate3592 profilesValid3592 numericValid3592 valid3592

def retention3593 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(8572080900000000/382319881116950897),(550187826164152553/500000000000000000),(49/20),(43644516361113777991/20000000000000000000),true,MergedCutProfiles.Batch551.profile22067,![MergedCutProfiles.Batch551.profile22067,MergedCutProfiles.Batch552.profile22082,MergedCutProfiles.Batch552.profile22083,MergedCutProfiles.Batch552.profile22084,MergedCutProfiles.Batch552.profile22085,MergedCutProfiles.Batch551.profile22058,MergedCutProfiles.Batch430.profile17218,MergedCutProfiles.Batch552.profile22086,MergedCutProfiles.Batch552.profile22087,MergedCutProfiles.Batch552.profile22088,MergedCutProfiles.Batch430.profile17204,MergedCutProfiles.Batch552.profile22089,MergedCutProfiles.Batch429.profile17189,MergedCutProfiles.Batch430.profile17221,MergedCutProfiles.Batch552.profile22090,MergedCutProfiles.Batch552.profile22091]⟩
theorem profilesValid3593 : retention3593.ProfilesValid := by
  change ∀ j : Fin 16, (retention3593.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch551.valid22067
  · exact MergedCutProfiles.Batch552.valid22082
  · exact MergedCutProfiles.Batch552.valid22083
  · exact MergedCutProfiles.Batch552.valid22084
  · exact MergedCutProfiles.Batch552.valid22085
  · exact MergedCutProfiles.Batch551.valid22058
  · exact MergedCutProfiles.Batch430.valid17218
  · exact MergedCutProfiles.Batch552.valid22086
  · exact MergedCutProfiles.Batch552.valid22087
  · exact MergedCutProfiles.Batch552.valid22088
  · exact MergedCutProfiles.Batch430.valid17204
  · exact MergedCutProfiles.Batch552.valid22089
  · exact MergedCutProfiles.Batch429.valid17189
  · exact MergedCutProfiles.Batch430.valid17221
  · exact MergedCutProfiles.Batch552.valid22090
  · exact MergedCutProfiles.Batch552.valid22091
theorem numericValid3593 : retention3593.NumericValid := by decide +kernel
def certificate3593 : RatCutBinCertificate := ⟨⟨retention3593,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(2109110936261431329/1000000000000000000)⟩,(124747056383452567/125000000000000000),(268631605928436189/1000000000000000000),(189111298135730543/500000000000000000),(30774399735955031/125000000000000000)⟩
theorem valid3593 : certificate3593.Valid := by decide +kernel
theorem sound3593 : certificate3593.Sound := rat_cut_bin_certificate_sound certificate3593 profilesValid3593 numericValid3593 valid3593

def retention3594 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(258055398262830963/9940316909040723322),(1114370517/1000000000),(12/5),(8640827109514818999/4000000000000000000),true,MergedCutProfiles.Batch552.profile22092,![MergedCutProfiles.Batch552.profile22092,MergedCutProfiles.Batch430.profile17216,MergedCutProfiles.Batch552.profile22093,MergedCutProfiles.Batch552.profile22094,MergedCutProfiles.Batch552.profile22095,MergedCutProfiles.Batch430.profile17218,MergedCutProfiles.Batch552.profile22096,MergedCutProfiles.Batch430.profile17219,MergedCutProfiles.Batch552.profile22097,MergedCutProfiles.Batch552.profile22098,MergedCutProfiles.Batch551.profile22065,MergedCutProfiles.Batch551.profile22079,MergedCutProfiles.Batch552.profile22099,MergedCutProfiles.Batch552.profile22100,MergedCutProfiles.Batch429.profile17191,MergedCutProfiles.Batch552.profile22101]⟩
theorem profilesValid3594 : retention3594.ProfilesValid := by
  change ∀ j : Fin 16, (retention3594.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch552.valid22092
  · exact MergedCutProfiles.Batch430.valid17216
  · exact MergedCutProfiles.Batch552.valid22093
  · exact MergedCutProfiles.Batch552.valid22094
  · exact MergedCutProfiles.Batch552.valid22095
  · exact MergedCutProfiles.Batch430.valid17218
  · exact MergedCutProfiles.Batch552.valid22096
  · exact MergedCutProfiles.Batch430.valid17219
  · exact MergedCutProfiles.Batch552.valid22097
  · exact MergedCutProfiles.Batch552.valid22098
  · exact MergedCutProfiles.Batch551.valid22065
  · exact MergedCutProfiles.Batch551.valid22079
  · exact MergedCutProfiles.Batch552.valid22099
  · exact MergedCutProfiles.Batch552.valid22100
  · exact MergedCutProfiles.Batch429.valid17191
  · exact MergedCutProfiles.Batch552.valid22101
theorem numericValid3594 : retention3594.NumericValid := by decide +kernel
def certificate3594 : RatCutBinCertificate := ⟨⟨retention3594,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(2088583980390257951/1000000000000000000)⟩,(124747056383452567/125000000000000000),(134958441572335441/500000000000000000),(94134500983660947/250000000000000000),(1973082541099441/8000000000000000)⟩
theorem valid3594 : certificate3594.Valid := by decide +kernel
theorem sound3594 : certificate3594.Sound := rat_cut_bin_certificate_sound certificate3594 profilesValid3594 numericValid3594 valid3594

def retention3595 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(3704661856231536867/49701584545203616610),(258055398262830963/200000000000000000),(11/5),(511697738873117204223/256000000000000000000),true,MergedCutProfiles.Batch552.profile22102,![MergedCutProfiles.Batch552.profile22102,MergedCutProfiles.Batch430.profile17202,MergedCutProfiles.Batch552.profile22088,MergedCutProfiles.Batch552.profile22103,MergedCutProfiles.Batch552.profile22104,MergedCutProfiles.Batch552.profile22105,MergedCutProfiles.Batch430.profile17225,MergedCutProfiles.Batch552.profile22106,MergedCutProfiles.Batch552.profile22107,MergedCutProfiles.Batch552.profile22108,MergedCutProfiles.Batch552.profile22109,MergedCutProfiles.Batch552.profile22110,MergedCutProfiles.Batch552.profile22111,MergedCutProfiles.Batch552.profile22112,MergedCutProfiles.Batch552.profile22113,MergedCutProfiles.Batch552.profile22114]⟩
theorem profilesValid3595 : retention3595.ProfilesValid := by
  change ∀ j : Fin 16, (retention3595.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch552.valid22102
  · exact MergedCutProfiles.Batch430.valid17202
  · exact MergedCutProfiles.Batch552.valid22088
  · exact MergedCutProfiles.Batch552.valid22103
  · exact MergedCutProfiles.Batch552.valid22104
  · exact MergedCutProfiles.Batch552.valid22105
  · exact MergedCutProfiles.Batch430.valid17225
  · exact MergedCutProfiles.Batch552.valid22106
  · exact MergedCutProfiles.Batch552.valid22107
  · exact MergedCutProfiles.Batch552.valid22108
  · exact MergedCutProfiles.Batch552.valid22109
  · exact MergedCutProfiles.Batch552.valid22110
  · exact MergedCutProfiles.Batch552.valid22111
  · exact MergedCutProfiles.Batch552.valid22112
  · exact MergedCutProfiles.Batch552.valid22113
  · exact MergedCutProfiles.Batch552.valid22114
theorem numericValid3595 : retention3595.NumericValid := by decide +kernel
def certificate3595 : RatCutBinCertificate := ⟨⟨retention3595,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(966582716422552501/500000000000000000)⟩,(124747056383452567/125000000000000000),(275925940996104427/1000000000000000000),(368742057087426137/1000000000000000000),(246831703251452321/1000000000000000000)⟩
theorem valid3595 : certificate3595.Valid := by decide +kernel
theorem sound3595 : certificate3595.Sound := rat_cut_bin_certificate_sound certificate3595 profilesValid3595 numericValid3595 valid3595

def retention3596 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(9102032531164944853/24850792272601808305),(3704661856231536867/1000000000000000000),(6/5),(116445689316587982911917148785424901989/92616546405788421675000000000000000000),false,MergedCutProfiles.Batch552.profile22115,(fun _ => MergedCutProfiles.Batch552.profile22115)⟩
theorem profilesValid3596 : retention3596.ProfilesValid := by
  exact MergedCutProfiles.Batch552.valid22115
theorem numericValid3596 : retention3596.NumericValid := by decide +kernel
def certificate3596 : RatCutBinCertificate := ⟨⟨retention3596,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(1221478178388314873/1000000000000000000)⟩,(124747056383452567/125000000000000000),(334164304120745033/1000000000000000000),(299541626059486327/1000000000000000000),(12376557023863711/50000000000000000)⟩
theorem valid3596 : certificate3596.Valid := by decide +kernel
theorem sound3596 : certificate3596.Sound := rat_cut_bin_certificate_sound certificate3596 profilesValid3596 numericValid3596 valid3596

def retention3597 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(24293395394961371633/49701584545203616610),(9102032531164944853/500000000000000000),1,(18381437194388096859388411226008064211/18204065062329889706000000000000000000),false,MergedCutProfiles.Batch552.profile22116,(fun _ => MergedCutProfiles.Batch552.profile22116)⟩
theorem profilesValid3597 : retention3597.ProfilesValid := by
  exact MergedCutProfiles.Batch552.valid22116
theorem numericValid3597 : retention3597.NumericValid := by decide +kernel
def certificate3597 : RatCutBinCertificate := ⟨⟨retention3597,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(489951600513721783/500000000000000000)⟩,(124747056383452567/125000000000000000),(362144936752993213/1000000000000000000),(135008221083431151/500000000000000000),(125274259429576263/500000000000000000)⟩
theorem valid3597 : certificate3597.Valid := by decide +kernel
theorem sound3597 : certificate3597.Sound := rat_cut_bin_certificate_sound certificate3597 profilesValid3597 numericValid3597 valid3597

def retention3598 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(12390846321200047602/24850792272601808305),(24293395394961371633/1000000000000000000),1,(24148755151183611386441297415323027793/24293395394961371633000000000000000000),false,MergedCutProfiles.Batch552.profile22117,(fun _ => MergedCutProfiles.Batch552.profile22117)⟩
theorem profilesValid3598 : retention3598.ProfilesValid := by
  exact MergedCutProfiles.Batch552.valid22117
theorem numericValid3598 : retention3598.NumericValid := by decide +kernel
def certificate3598 : RatCutBinCertificate := ⟨⟨retention3598,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(482102935754940277/500000000000000000)⟩,(124747056383452567/125000000000000000),(36449990841148157/100000000000000000),(66908095542570597/250000000000000000),(247685571597338239/1000000000000000000)⟩
theorem valid3598 : certificate3598.Valid := by decide +kernel
theorem sound3598 : certificate3598.Sound := rat_cut_bin_certificate_sound certificate3598 profilesValid3598 numericValid3598 valid3598

def retention3599 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),(6195423160600023801/250000000000000000),1,(19657261314915061101261175338096212179/19825354113920076163200000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid3599 : retention3599.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid3599 : retention3599.NumericValid := by decide +kernel
def certificate3599 : RatCutBinCertificate := ⟨⟨retention3599,(1144832734436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(961681091212993373/1000000000000000000)⟩,(124747056383452567/125000000000000000),(22827983958036803/62500000000000000),(266878494156093713/1000000000000000000),(9862040184663709/40000000000000000)⟩
theorem valid3599 : certificate3599.Valid := by decide +kernel
theorem sound3599 : certificate3599.Sound := rat_cut_bin_certificate_sound certificate3599 profilesValid3599 numericValid3599 valid3599

def certificates : List RatCutBinCertificate := [certificate3588,certificate3589,certificate3590,certificate3591,certificate3592,certificate3593,certificate3594,certificate3595,certificate3596,certificate3597,certificate3598,certificate3599]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3588,List.forall_mem_cons.mpr ⟨sound3589,List.forall_mem_cons.mpr ⟨sound3590,List.forall_mem_cons.mpr ⟨sound3591,List.forall_mem_cons.mpr ⟨sound3592,List.forall_mem_cons.mpr ⟨sound3593,List.forall_mem_cons.mpr ⟨sound3594,List.forall_mem_cons.mpr ⟨sound3595,List.forall_mem_cons.mpr ⟨sound3596,List.forall_mem_cons.mpr ⟨sound3597,List.forall_mem_cons.mpr ⟨sound3598,List.forall_mem_cons.mpr ⟨sound3599,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch299
