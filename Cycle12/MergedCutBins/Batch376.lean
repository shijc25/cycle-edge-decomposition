import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch324
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch458
import Cycle12.MergedCutProfiles.Batch459
import Cycle12.MergedCutProfiles.Batch651

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch376

def retention4512 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid4512 : retention4512.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid4512 : retention4512.NumericValid := by decide +kernel
def certificate4512 : RatCutBinCertificate := ⟨⟨retention4512,(1796238348711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(198589228097774867/200000000000000000)⟩,(124997600807666849/125000000000000000),(14871915013822871/250000000000000000),(190847829267924801/250000000000000000),(373205686125082213/500000000000000000)⟩
theorem valid4512 : certificate4512.Valid := by decide +kernel
theorem sound4512 : certificate4512.Sound := rat_cut_bin_certificate_sound certificate4512 profilesValid4512 numericValid4512 valid4512

def retention4513 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(226781713816305874/3465049869034942807353),(336804525469761199/500000000000000000),4,(6384390304815555324306279204344371303/2694436203758089592000000000000000000),false,MergedCutProfiles.Batch651.profile26047,(fun _ => MergedCutProfiles.Batch651.profile26047)⟩
theorem profilesValid4513 : retention4513.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26047
theorem numericValid4513 : retention4513.NumericValid := by decide +kernel
def certificate4513 : RatCutBinCertificate := ⟨⟨retention4513,(1776633976711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(2351263763495556313/1000000000000000000)⟩,(999981015942120973/1000000000000000000),(163841368958419267/200000000000000000),(17428016360376807/1000000000000000000),(8409604318422569/1000000000000000000)⟩
theorem valid4513 : certificate4513.Valid := by decide +kernel
theorem sound4513 : certificate4513.Sound := rat_cut_bin_certificate_sound certificate4513 profilesValid4513 numericValid4513 valid4513

def retention4514 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(450591322681671208/3465049869034942807353),(340172570724458811/500000000000000000),4,(537969567352022729812588599269248437/226781713816305874000000000000000000),false,MergedCutProfiles.Batch651.profile26048,(fun _ => MergedCutProfiles.Batch651.profile26048)⟩
theorem profilesValid4514 : retention4514.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26048
theorem numericValid4514 : retention4514.NumericValid := by decide +kernel
def certificate4514 : RatCutBinCertificate := ⟨⟨retention4514,(1776633976711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(2353983192192240347/1000000000000000000)⟩,(999981015942120973/1000000000000000000),(163166729154133021/200000000000000000),(2263456197760991/125000000000000000),(8761394723169121/1000000000000000000)⟩
theorem valid4514 : certificate4514.Valid := by decide +kernel
theorem sound4514 : certificate4514.Sound := rat_cut_bin_certificate_sound certificate4514 profilesValid4514 numericValid4514 valid4514

def retention4515 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(64000000000000000000/10395149607104828422059),(168971746005626703/125000000000000000),(53/20),(26081814832279997377935767489734358493/11264783067041780200000000000000000000),false,MergedCutProfiles.Batch651.profile26046,(fun _ => MergedCutProfiles.Batch651.profile26046)⟩
theorem profilesValid4515 : retention4515.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26046
theorem numericValid4515 : retention4515.NumericValid := by decide +kernel
def certificate4515 : RatCutBinCertificate := ⟨⟨retention4515,(1776633976711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(2303278314870843687/1000000000000000000)⟩,(999981015942120973/1000000000000000000),(710599654328698101/1000000000000000000),(46626758005854771/1000000000000000000),(6522489715285779/200000000000000000)⟩
theorem valid4515 : certificate4515.Valid := by decide +kernel
theorem sound4515 : certificate4515.Sound := rat_cut_bin_certificate_sound certificate4515 profilesValid4515 numericValid4515 valid4515

def retention4516 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/40),64,1,(138513500667774696958015671392173208919/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch651.profile26049,(fun _ => MergedCutProfiles.Batch651.profile26049)⟩
theorem profilesValid4516 : retention4516.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26049
theorem numericValid4516 : retention4516.NumericValid := by decide +kernel
def certificate4516 : RatCutBinCertificate := ⟨⟨retention4516,(1776633976711687279/1000000000000000000),(702642711920787/31250000000000000),(1755141062535292033/200000000000000000),(45833768599724083707897/500000000000000000),(431944293350245239/200000000000000000)⟩,(999981015942120973/1000000000000000000),(313758878916307783/500000000000000000),(80069440608532543/1000000000000000000),(167279425105295601/1000000000000000000)⟩
theorem valid4516 : certificate4516.Valid := by decide +kernel
theorem sound4516 : certificate4516.Sound := rat_cut_bin_certificate_sound certificate4516 profilesValid4516 numericValid4516 valid4516

def retention4517 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(709236797187936828/9500551814030085163711),(317852881327956603/500000000000000000),4,(1478450208382159733699781152492984903/635705762655913206000000000000000000),true,MergedCutProfiles.Batch651.profile26050,![MergedCutProfiles.Batch651.profile26050,MergedCutProfiles.Batch651.profile26051,MergedCutProfiles.Batch651.profile26052,MergedCutProfiles.Batch651.profile26053,MergedCutProfiles.Batch651.profile26054,MergedCutProfiles.Batch651.profile26055,MergedCutProfiles.Batch651.profile26056,MergedCutProfiles.Batch651.profile26057,MergedCutProfiles.Batch651.profile26058,MergedCutProfiles.Batch651.profile26058,MergedCutProfiles.Batch651.profile26059,MergedCutProfiles.Batch651.profile26060,MergedCutProfiles.Batch651.profile26060,MergedCutProfiles.Batch651.profile26061,MergedCutProfiles.Batch651.profile26062,MergedCutProfiles.Batch651.profile26062]⟩
theorem profilesValid4517 : retention4517.ProfilesValid := by
  change ∀ j : Fin 16, (retention4517.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch651.valid26050
  · exact MergedCutProfiles.Batch651.valid26051
  · exact MergedCutProfiles.Batch651.valid26052
  · exact MergedCutProfiles.Batch651.valid26053
  · exact MergedCutProfiles.Batch651.valid26054
  · exact MergedCutProfiles.Batch651.valid26055
  · exact MergedCutProfiles.Batch651.valid26056
  · exact MergedCutProfiles.Batch651.valid26057
  · exact MergedCutProfiles.Batch651.valid26058
  · exact MergedCutProfiles.Batch651.valid26058
  · exact MergedCutProfiles.Batch651.valid26059
  · exact MergedCutProfiles.Batch651.valid26060
  · exact MergedCutProfiles.Batch651.valid26060
  · exact MergedCutProfiles.Batch651.valid26061
  · exact MergedCutProfiles.Batch651.valid26062
  · exact MergedCutProfiles.Batch651.valid26062
theorem numericValid4517 : retention4517.NumericValid := by decide +kernel
def certificate4517 : RatCutBinCertificate := ⟨⟨retention4517,(1894019162043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(72023452251416723/31250000000000000)⟩,(499989097929063821/500000000000000000),(491951259789180709/1000000000000000000),(159070436575488087/1000000000000000000),(9340100235392789/125000000000000000)⟩
theorem valid4517 : certificate4517.Valid := by decide +kernel
theorem sound4517 : certificate4517.Sound := rat_cut_bin_certificate_sound certificate4517 profilesValid4517 numericValid4517 valid4517

def retention4518 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1268116581000000000/9500551814030085163711),(177309199296984207/250000000000000000),4,(153399186884829412143/64000000000000000000),true,MergedCutProfiles.Batch651.profile26063,![MergedCutProfiles.Batch651.profile26063,MergedCutProfiles.Batch651.profile26053,MergedCutProfiles.Batch651.profile26055,MergedCutProfiles.Batch651.profile26056,MergedCutProfiles.Batch651.profile26058,MergedCutProfiles.Batch651.profile26059,MergedCutProfiles.Batch651.profile26060,MergedCutProfiles.Batch651.profile26061,MergedCutProfiles.Batch651.profile26062,MergedCutProfiles.Batch458.profile18342,MergedCutProfiles.Batch651.profile26064,MergedCutProfiles.Batch651.profile26065,MergedCutProfiles.Batch651.profile26066,MergedCutProfiles.Batch651.profile26067,MergedCutProfiles.Batch651.profile26067,MergedCutProfiles.Batch651.profile26068]⟩
theorem profilesValid4518 : retention4518.ProfilesValid := by
  change ∀ j : Fin 16, (retention4518.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch651.valid26063
  · exact MergedCutProfiles.Batch651.valid26053
  · exact MergedCutProfiles.Batch651.valid26055
  · exact MergedCutProfiles.Batch651.valid26056
  · exact MergedCutProfiles.Batch651.valid26058
  · exact MergedCutProfiles.Batch651.valid26059
  · exact MergedCutProfiles.Batch651.valid26060
  · exact MergedCutProfiles.Batch651.valid26061
  · exact MergedCutProfiles.Batch651.valid26062
  · exact MergedCutProfiles.Batch458.valid18342
  · exact MergedCutProfiles.Batch651.valid26064
  · exact MergedCutProfiles.Batch651.valid26065
  · exact MergedCutProfiles.Batch651.valid26066
  · exact MergedCutProfiles.Batch651.valid26067
  · exact MergedCutProfiles.Batch651.valid26067
  · exact MergedCutProfiles.Batch651.valid26068
theorem numericValid4518 : retention4518.NumericValid := by decide +kernel
def certificate4518 : RatCutBinCertificate := ⟨⟨retention4518,(1894019162043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(2375929573612646639/1000000000000000000)⟩,(499989097929063821/500000000000000000),(44509928375252853/100000000000000000),(4865281302913027/25000000000000000),(95580647590315433/1000000000000000000)⟩
theorem valid4518 : certificate4518.Valid := by decide +kernel
theorem sound4518 : certificate4518.Sound := rat_cut_bin_certificate_sound certificate4518 profilesValid4518 numericValid4518 valid4518

def retention4519 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(9907299963320852771/9500551814030085163711),(1268116581/1000000000),(5/2),(18791295498439451713/8000000000000000000),true,MergedCutProfiles.Batch651.profile26061,![MergedCutProfiles.Batch651.profile26061,MergedCutProfiles.Batch651.profile26068,MergedCutProfiles.Batch651.profile26069,MergedCutProfiles.Batch651.profile26070,MergedCutProfiles.Batch458.profile18351,MergedCutProfiles.Batch324.profile12996,MergedCutProfiles.Batch030.profile1211,MergedCutProfiles.Batch651.profile26071,MergedCutProfiles.Batch030.profile1227,MergedCutProfiles.Batch324.profile12985,MergedCutProfiles.Batch651.profile26072,MergedCutProfiles.Batch325.profile13003,MergedCutProfiles.Batch459.profile18361,MergedCutProfiles.Batch030.profile1212,MergedCutProfiles.Batch458.profile18348,MergedCutProfiles.Batch459.profile18362]⟩
theorem profilesValid4519 : retention4519.ProfilesValid := by
  change ∀ j : Fin 16, (retention4519.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch651.valid26061
  · exact MergedCutProfiles.Batch651.valid26068
  · exact MergedCutProfiles.Batch651.valid26069
  · exact MergedCutProfiles.Batch651.valid26070
  · exact MergedCutProfiles.Batch458.valid18351
  · exact MergedCutProfiles.Batch324.valid12996
  · exact MergedCutProfiles.Batch030.valid1211
  · exact MergedCutProfiles.Batch651.valid26071
  · exact MergedCutProfiles.Batch030.valid1227
  · exact MergedCutProfiles.Batch324.valid12985
  · exact MergedCutProfiles.Batch651.valid26072
  · exact MergedCutProfiles.Batch325.valid13003
  · exact MergedCutProfiles.Batch459.valid18361
  · exact MergedCutProfiles.Batch030.valid1212
  · exact MergedCutProfiles.Batch458.valid18348
  · exact MergedCutProfiles.Batch459.valid18362
theorem numericValid4519 : retention4519.NumericValid := by decide +kernel
def certificate4519 : RatCutBinCertificate := ⟨⟨retention4519,(1894019162043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(2335828986531008247/1000000000000000000)⟩,(499989097929063821/500000000000000000),(41035058504854089/125000000000000000),(306041533109202739/1000000000000000000),(220849575052170843/1000000000000000000)⟩
theorem valid4519 : certificate4519.Valid := by decide +kernel
theorem sound4519 : certificate4519.Sound := rat_cut_bin_certificate_sound certificate4519 profilesValid4519 numericValid4519 valid4519

def retention4520 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(64000000000000000000/9500551814030085163711),(9907299963320852771/1000000000000000000),(21/20),(35325402429526527003427065189104890060919/15851679941313364433600000000000000000000),false,MergedCutProfiles.Batch651.profile26073,(fun _ => MergedCutProfiles.Batch651.profile26073)⟩
theorem profilesValid4520 : retention4520.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26073
theorem numericValid4520 : retention4520.NumericValid := by decide +kernel
def certificate4520 : RatCutBinCertificate := ⟨⟨retention4520,(1894019162043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(1111500488629772601/500000000000000000)⟩,(499989097929063821/500000000000000000),(200224537433406033/1000000000000000000),(477455905890660709/1000000000000000000),(83988660098353987/100000000000000000)⟩
theorem valid4520 : certificate4520.Valid := by decide +kernel
theorem sound4520 : certificate4520.Sound := rat_cut_bin_certificate_sound certificate4520 profilesValid4520 numericValid4520 valid4520

def retention4521 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid4521 : retention4521.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid4521 : retention4521.NumericValid := by decide +kernel
def certificate4521 : RatCutBinCertificate := ⟨⟨retention4521,(1894019162043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(992316847520880669/1000000000000000000)⟩,(499989097929063821/500000000000000000),(204162136364814633/500000000000000000),(225941232526984343/1000000000000000000),(110388610706866513/500000000000000000)⟩
theorem valid4521 : certificate4521.Valid := by decide +kernel
theorem sound4521 : certificate4521.Sound := rat_cut_bin_certificate_sound certificate4521 profilesValid4521 numericValid4521 valid4521

def retention4522 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(64000000000000000000/9500551814030085163711),(18698418081753556621/1000000000000000000),1,(1047250010329052397686488285186530057/467460452043838915525000000000000000),false,MergedCutProfiles.Batch651.profile26073,(fun _ => MergedCutProfiles.Batch651.profile26073)⟩
theorem profilesValid4522 : retention4522.ProfilesValid := by
  exact MergedCutProfiles.Batch651.valid26073
theorem numericValid4522 : retention4522.NumericValid := by decide +kernel
def certificate4522 : RatCutBinCertificate := ⟨⟨retention4522,(1797002244043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(2235331368944817261/1000000000000000000)⟩,(199995862545463879/200000000000000000),(26069553492611497/1000000000000000000),(855799080665023833/1000000000000000000),(854343150590254369/500000000000000000)⟩
theorem valid4522 : certificate4522.Valid := by decide +kernel
theorem sound4522 : certificate4522.Sound := rat_cut_bin_certificate_sound certificate4522 profilesValid4522 numericValid4522 valid4522

def retention4523 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid4523 : retention4523.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid4523 : retention4523.NumericValid := by decide +kernel
def certificate4523 : RatCutBinCertificate := ⟨⟨retention4523,(1797002244043966987/1000000000000000000),(12287303118992409/500000000000000000),(4447083476021343527/500000000000000000),(1326750426848419357023/15625000000000000),(992584905516858203/1000000000000000000)⟩,(199995862545463879/200000000000000000),(14677356660505267/250000000000000000),(191351263315439347/250000000000000000),(748111085765978861/1000000000000000000)⟩
theorem valid4523 : certificate4523.Valid := by decide +kernel
theorem sound4523 : certificate4523.Sound := rat_cut_bin_certificate_sound certificate4523 profilesValid4523 numericValid4523 valid4523

def certificates : List RatCutBinCertificate := [certificate4512,certificate4513,certificate4514,certificate4515,certificate4516,certificate4517,certificate4518,certificate4519,certificate4520,certificate4521,certificate4522,certificate4523]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4512,List.forall_mem_cons.mpr ⟨sound4513,List.forall_mem_cons.mpr ⟨sound4514,List.forall_mem_cons.mpr ⟨sound4515,List.forall_mem_cons.mpr ⟨sound4516,List.forall_mem_cons.mpr ⟨sound4517,List.forall_mem_cons.mpr ⟨sound4518,List.forall_mem_cons.mpr ⟨sound4519,List.forall_mem_cons.mpr ⟨sound4520,List.forall_mem_cons.mpr ⟨sound4521,List.forall_mem_cons.mpr ⟨sound4522,List.forall_mem_cons.mpr ⟨sound4523,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch376
