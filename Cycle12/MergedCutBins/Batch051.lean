import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch101
import Cycle12.MergedCutProfiles.Batch102
import Cycle12.MergedCutProfiles.Batch103
import Cycle12.MergedCutProfiles.Batch104

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch051

def retention612 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(44737146200000000/1290374107000689903),(81873141872315687/100000000000000000),(31/10),(271471690285721982619/128000000000000000000),true,MergedCutProfiles.Batch101.profile4079,![MergedCutProfiles.Batch101.profile4079,MergedCutProfiles.Batch102.profile4080,MergedCutProfiles.Batch102.profile4081,MergedCutProfiles.Batch102.profile4082,MergedCutProfiles.Batch102.profile4083,MergedCutProfiles.Batch102.profile4084,MergedCutProfiles.Batch102.profile4085,MergedCutProfiles.Batch102.profile4086,MergedCutProfiles.Batch102.profile4087,MergedCutProfiles.Batch102.profile4088,MergedCutProfiles.Batch102.profile4089,MergedCutProfiles.Batch102.profile4090,MergedCutProfiles.Batch102.profile4091,MergedCutProfiles.Batch102.profile4092,MergedCutProfiles.Batch102.profile4093,MergedCutProfiles.Batch102.profile4094]⟩
theorem profilesValid612 : retention612.ProfilesValid := by
  change ∀ j : Fin 16, (retention612.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch101.valid4079
  · exact MergedCutProfiles.Batch102.valid4080
  · exact MergedCutProfiles.Batch102.valid4081
  · exact MergedCutProfiles.Batch102.valid4082
  · exact MergedCutProfiles.Batch102.valid4083
  · exact MergedCutProfiles.Batch102.valid4084
  · exact MergedCutProfiles.Batch102.valid4085
  · exact MergedCutProfiles.Batch102.valid4086
  · exact MergedCutProfiles.Batch102.valid4087
  · exact MergedCutProfiles.Batch102.valid4088
  · exact MergedCutProfiles.Batch102.valid4089
  · exact MergedCutProfiles.Batch102.valid4090
  · exact MergedCutProfiles.Batch102.valid4091
  · exact MergedCutProfiles.Batch102.valid4092
  · exact MergedCutProfiles.Batch102.valid4093
  · exact MergedCutProfiles.Batch102.valid4094
theorem numericValid612 : retention612.NumericValid := by decide +kernel
def certificate612 : RatCutBinCertificate := ⟨⟨retention612,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(1036299027548126809/500000000000000000)⟩,(3975234993582157/4000000000000000),(390500948747510119/1000000000000000000),(60574876128288049/250000000000000000),(127286446880179481/1000000000000000000)⟩
theorem valid612 : certificate612.Valid := by decide +kernel
theorem sound612 : certificate612.Sound := rat_cut_bin_certificate_sound certificate612 profilesValid612 numericValid612 valid612

def retention613 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(969627247298085067/25807482140013798060),(223685731/250000000),(57/20),(33615040269726693023/16000000000000000000),true,MergedCutProfiles.Batch102.profile4095,![MergedCutProfiles.Batch102.profile4095,MergedCutProfiles.Batch102.profile4096,MergedCutProfiles.Batch102.profile4097,MergedCutProfiles.Batch102.profile4098,MergedCutProfiles.Batch102.profile4099,MergedCutProfiles.Batch102.profile4100,MergedCutProfiles.Batch102.profile4101,MergedCutProfiles.Batch102.profile4102,MergedCutProfiles.Batch102.profile4103,MergedCutProfiles.Batch102.profile4104,MergedCutProfiles.Batch102.profile4105,MergedCutProfiles.Batch102.profile4091,MergedCutProfiles.Batch102.profile4106,MergedCutProfiles.Batch102.profile4107,MergedCutProfiles.Batch102.profile4108,MergedCutProfiles.Batch102.profile4109]⟩
theorem profilesValid613 : retention613.ProfilesValid := by
  change ∀ j : Fin 16, (retention613.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch102.valid4095
  · exact MergedCutProfiles.Batch102.valid4096
  · exact MergedCutProfiles.Batch102.valid4097
  · exact MergedCutProfiles.Batch102.valid4098
  · exact MergedCutProfiles.Batch102.valid4099
  · exact MergedCutProfiles.Batch102.valid4100
  · exact MergedCutProfiles.Batch102.valid4101
  · exact MergedCutProfiles.Batch102.valid4102
  · exact MergedCutProfiles.Batch102.valid4103
  · exact MergedCutProfiles.Batch102.valid4104
  · exact MergedCutProfiles.Batch102.valid4105
  · exact MergedCutProfiles.Batch102.valid4091
  · exact MergedCutProfiles.Batch102.valid4106
  · exact MergedCutProfiles.Batch102.valid4107
  · exact MergedCutProfiles.Batch102.valid4108
  · exact MergedCutProfiles.Batch102.valid4109
theorem numericValid613 : retention613.NumericValid := by decide +kernel
def certificate613 : RatCutBinCertificate := ⟨⟨retention613,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(51413965549242319/25000000000000000)⟩,(3975234993582157/4000000000000000),(47370182117406389/125000000000000000),(126660924648348317/500000000000000000),(35360906528092021/250000000000000000)⟩
theorem valid613 : certificate613.Valid := by decide +kernel
theorem sound613 : certificate613.Sound := rat_cut_bin_certificate_sound certificate613 profilesValid613 numericValid613 valid613

def retention614 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(1692784769303568119/25807482140013798060),(969627247298085067/1000000000000000000),(53/20),(641233632386012812957/320000000000000000000),true,MergedCutProfiles.Batch102.profile4110,![MergedCutProfiles.Batch102.profile4110,MergedCutProfiles.Batch102.profile4111,MergedCutProfiles.Batch102.profile4112,MergedCutProfiles.Batch102.profile4101,MergedCutProfiles.Batch102.profile4113,MergedCutProfiles.Batch102.profile4114,MergedCutProfiles.Batch102.profile4115,MergedCutProfiles.Batch102.profile4116,MergedCutProfiles.Batch102.profile4117,MergedCutProfiles.Batch102.profile4118,MergedCutProfiles.Batch102.profile4119,MergedCutProfiles.Batch103.profile4120,MergedCutProfiles.Batch103.profile4121,MergedCutProfiles.Batch103.profile4122,MergedCutProfiles.Batch103.profile4123,MergedCutProfiles.Batch103.profile4124]⟩
theorem profilesValid614 : retention614.ProfilesValid := by
  change ∀ j : Fin 16, (retention614.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch102.valid4110
  · exact MergedCutProfiles.Batch102.valid4111
  · exact MergedCutProfiles.Batch102.valid4112
  · exact MergedCutProfiles.Batch102.valid4101
  · exact MergedCutProfiles.Batch102.valid4113
  · exact MergedCutProfiles.Batch102.valid4114
  · exact MergedCutProfiles.Batch102.valid4115
  · exact MergedCutProfiles.Batch102.valid4116
  · exact MergedCutProfiles.Batch102.valid4117
  · exact MergedCutProfiles.Batch102.valid4118
  · exact MergedCutProfiles.Batch102.valid4119
  · exact MergedCutProfiles.Batch103.valid4120
  · exact MergedCutProfiles.Batch103.valid4121
  · exact MergedCutProfiles.Batch103.valid4122
  · exact MergedCutProfiles.Batch103.valid4123
  · exact MergedCutProfiles.Batch103.valid4124
theorem numericValid614 : retention614.NumericValid := by decide +kernel
def certificate614 : RatCutBinCertificate := ⟨⟨retention614,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(1962588225375958959/1000000000000000000)⟩,(3975234993582157/4000000000000000),(384392849859087959/1000000000000000000),(248090766753418183/1000000000000000000),(2831856371661637/20000000000000000)⟩
theorem valid614 : certificate614.Valid := by decide +kernel
theorem sound614 : certificate614.Sound := rat_cut_bin_certificate_sound certificate614 profilesValid614 numericValid614 valid614

def retention615 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(2140644626388348829/8602494046671266020),(1692784769303568119/1000000000000000000),(7/4),(164739487625717785008048229195699854823/108338225235428359616000000000000000000),false,MergedCutProfiles.Batch103.profile4125,(fun _ => MergedCutProfiles.Batch103.profile4125)⟩
theorem profilesValid615 : retention615.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4125
theorem numericValid615 : retention615.NumericValid := by decide +kernel
def certificate615 : RatCutBinCertificate := ⟨⟨retention615,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(1493352221915303483/1000000000000000000)⟩,(3975234993582157/4000000000000000),(419890153734898043/1000000000000000000),(53936084558613281/250000000000000000),(141914849752622251/1000000000000000000)⟩
theorem valid615 : certificate615.Valid := by decide +kernel
theorem sound615 : certificate615.Sound := rat_cut_bin_certificate_sound certificate615 profilesValid615 numericValid615 valid615

def retention616 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(392779104581426053/860249404667126602),(6421933879165046487/1000000000000000000),1,(267726297742665677127/256000000000000000000),true,MergedCutProfiles.Batch103.profile4126,![MergedCutProfiles.Batch103.profile4126,MergedCutProfiles.Batch103.profile4127,MergedCutProfiles.Batch103.profile4128,MergedCutProfiles.Batch103.profile4129,MergedCutProfiles.Batch103.profile4130,MergedCutProfiles.Batch103.profile4131,MergedCutProfiles.Batch103.profile4132,MergedCutProfiles.Batch103.profile4133,MergedCutProfiles.Batch103.profile4134,MergedCutProfiles.Batch103.profile4135,MergedCutProfiles.Batch103.profile4136,MergedCutProfiles.Batch103.profile4137,MergedCutProfiles.Batch103.profile4138,MergedCutProfiles.Batch103.profile4139,MergedCutProfiles.Batch103.profile4140,MergedCutProfiles.Batch103.profile4141]⟩
theorem profilesValid616 : retention616.ProfilesValid := by
  change ∀ j : Fin 16, (retention616.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch103.valid4126
  · exact MergedCutProfiles.Batch103.valid4127
  · exact MergedCutProfiles.Batch103.valid4128
  · exact MergedCutProfiles.Batch103.valid4129
  · exact MergedCutProfiles.Batch103.valid4130
  · exact MergedCutProfiles.Batch103.valid4131
  · exact MergedCutProfiles.Batch103.valid4132
  · exact MergedCutProfiles.Batch103.valid4133
  · exact MergedCutProfiles.Batch103.valid4134
  · exact MergedCutProfiles.Batch103.valid4135
  · exact MergedCutProfiles.Batch103.valid4136
  · exact MergedCutProfiles.Batch103.valid4137
  · exact MergedCutProfiles.Batch103.valid4138
  · exact MergedCutProfiles.Batch103.valid4139
  · exact MergedCutProfiles.Batch103.valid4140
  · exact MergedCutProfiles.Batch103.valid4141
theorem numericValid616 : retention616.NumericValid := by decide +kernel
def certificate616 : RatCutBinCertificate := ⟨⟨retention616,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(257558621762841533/250000000000000000)⟩,(3975234993582157/4000000000000000),(486577407549280877/1000000000000000000),(162911960710004219/1000000000000000000),(35917746704149611/250000000000000000)⟩
theorem valid616 : certificate616.Valid := by decide +kernel
theorem sound616 : certificate616.Sound := rat_cut_bin_certificate_sound certificate616 profilesValid616 numericValid616 valid616

def retention617 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(12759704616797704781/25807482140013798060),(1178337313744278159/100000000000000000),(21/20),(63404362816181554122044893994364697653/62844656733028168480000000000000000000),false,MergedCutProfiles.Batch103.profile4142,(fun _ => MergedCutProfiles.Batch103.profile4142)⟩
theorem profilesValid617 : retention617.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4142
theorem numericValid617 : retention617.NumericValid := by decide +kernel
def certificate617 : RatCutBinCertificate := ⟨⟨retention617,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(992556603560786609/1000000000000000000)⟩,(3975234993582157/4000000000000000),(242206638980673121/500000000000000000),(164475725001342553/1000000000000000000),(143509510941696731/1000000000000000000)⟩
theorem valid617 : certificate617.Valid := by decide +kernel
theorem sound617 : certificate617.Sound := rat_cut_bin_certificate_sound certificate617 profilesValid617 numericValid617 valid617

def retention618 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(12887301662965681829/25807482140013798060),(12759704616797704781/1000000000000000000),(21/20),(20419486159802621701227592959145648661199/20415527386876327649600000000000000000000),false,MergedCutProfiles.Batch103.profile4143,(fun _ => MergedCutProfiles.Batch103.profile4143)⟩
theorem profilesValid618 : retention618.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4143
theorem numericValid618 : retention618.NumericValid := by decide +kernel
def certificate618 : RatCutBinCertificate := ⟨⟨retention618,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(983844358349613033/1000000000000000000)⟩,(3975234993582157/4000000000000000),(486794940613749639/1000000000000000000),(3255106159603283/20000000000000000),(141615167733910117/1000000000000000000)⟩
theorem valid618 : certificate618.Valid := by decide +kernel
theorem sound618 : certificate618.Sound := rat_cut_bin_certificate_sound certificate618 profilesValid618 numericValid618 valid618

def retention619 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(1/2),(12887301662965681829/1000000000000000000),(21/20),(20600112793473087220899717788639640907959/20619682660745090926400000000000000000000),false,MergedCutProfiles.Batch103.profile4144,(fun _ => MergedCutProfiles.Batch103.profile4144)⟩
theorem profilesValid619 : retention619.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4144
theorem numericValid619 : retention619.NumericValid := by decide +kernel
def certificate619 : RatCutBinCertificate := ⟨⟨retention619,(525250416165231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(491350682588961847/500000000000000000)⟩,(3975234993582157/4000000000000000),(48713288009180759/100000000000000000),(162512139406792763/1000000000000000000),(141341727800782273/1000000000000000000)⟩
theorem valid619 : certificate619.Valid := by decide +kernel
theorem sound619 : certificate619.Sound := rat_cut_bin_certificate_sound certificate619 profilesValid619 numericValid619 valid619

def retention620 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(5696324373225133079/12903741070006899030),(3737927244300435437/1000000000000000000),(6/5),(415073121812774527787211372740982054471/373792724430043543700000000000000000000),false,MergedCutProfiles.Batch103.profile4145,(fun _ => MergedCutProfiles.Batch103.profile4145)⟩
theorem profilesValid620 : retention620.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4145
theorem numericValid620 : retention620.NumericValid := by decide +kernel
def certificate620 : RatCutBinCertificate := ⟨⟨retention620,(620193623415231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(1088372959958967003/1000000000000000000)⟩,(496344421814255063/500000000000000000),(186391125213844897/500000000000000000),(259367815812831931/1000000000000000000),(7764679568510689/40000000000000000)⟩
theorem valid620 : certificate620.Valid := by decide +kernel
theorem sound620 : certificate620.Sound := rat_cut_bin_certificate_sound certificate620 profilesValid620 numericValid620 valid620

def retention621 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(12837521767001768237/25807482140013798060),(5696324373225133079/500000000000000000),(21/20),(4568339942501887835039071404630918610439/4557059498580106463200000000000000000000),false,MergedCutProfiles.Batch103.profile4146,(fun _ => MergedCutProfiles.Batch103.profile4146)⟩
theorem profilesValid621 : retention621.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4146
theorem numericValid621 : retention621.NumericValid := by decide +kernel
def certificate621 : RatCutBinCertificate := ⟨⟨retention621,(620193623415231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(491585232329512407/500000000000000000)⟩,(496344421814255063/500000000000000000),(206335592810378141/500000000000000000),(44414183444050637/200000000000000000),(23922442496322041/125000000000000000)⟩
theorem valid621 : certificate621.Valid := by decide +kernel
theorem sound621 : certificate621.Sound := rat_cut_bin_certificate_sound certificate621 profilesValid621 numericValid621 valid621

def retention622 : RatCutRetentionCertificate := ⟨(87/2000),(7/160),(1/2),(12837521767001768237/1000000000000000000),(21/20),(20519629801854818984515414383908842411431/20540034827202829179200000000000000000000),false,MergedCutProfiles.Batch103.profile4144,(fun _ => MergedCutProfiles.Batch103.profile4144)⟩
theorem profilesValid622 : retention622.ProfilesValid := by
  exact MergedCutProfiles.Batch103.valid4144
theorem numericValid622 : retention622.NumericValid := by decide +kernel
def certificate622 : RatCutBinCertificate := ⟨⟨retention622,(620193623415231327/250000000000000000),(22208520138960273/250000000000000000),(5993337883701644691/500000000000000000),(30977154396792592491/100000000000000000),(979701711936587367/1000000000000000000)⟩,(496344421814255063/500000000000000000),(414132297999302519/1000000000000000000),(220780304410844337/1000000000000000000),(19120717357185673/100000000000000000)⟩
theorem valid622 : certificate622.Valid := by decide +kernel
theorem sound622 : certificate622.Sound := rat_cut_bin_certificate_sound certificate622 profilesValid622 numericValid622 valid622

def retention623 : RatCutRetentionCertificate := ⟨(7/160),(11/250),(817291728763740003/25479936054786540268),(809199731449247527/1000000000000000000),(31/10),(170087853076368322949/80000000000000000000),true,MergedCutProfiles.Batch103.profile4147,![MergedCutProfiles.Batch103.profile4147,MergedCutProfiles.Batch103.profile4148,MergedCutProfiles.Batch103.profile4149,MergedCutProfiles.Batch103.profile4150,MergedCutProfiles.Batch103.profile4151,MergedCutProfiles.Batch103.profile4152,MergedCutProfiles.Batch103.profile4153,MergedCutProfiles.Batch103.profile4154,MergedCutProfiles.Batch103.profile4155,MergedCutProfiles.Batch103.profile4156,MergedCutProfiles.Batch103.profile4157,MergedCutProfiles.Batch103.profile4158,MergedCutProfiles.Batch103.profile4159,MergedCutProfiles.Batch104.profile4160,MergedCutProfiles.Batch104.profile4161,MergedCutProfiles.Batch104.profile4162]⟩
theorem profilesValid623 : retention623.ProfilesValid := by
  change ∀ j : Fin 16, (retention623.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch103.valid4147
  · exact MergedCutProfiles.Batch103.valid4148
  · exact MergedCutProfiles.Batch103.valid4149
  · exact MergedCutProfiles.Batch103.valid4150
  · exact MergedCutProfiles.Batch103.valid4151
  · exact MergedCutProfiles.Batch103.valid4152
  · exact MergedCutProfiles.Batch103.valid4153
  · exact MergedCutProfiles.Batch103.valid4154
  · exact MergedCutProfiles.Batch103.valid4155
  · exact MergedCutProfiles.Batch103.valid4156
  · exact MergedCutProfiles.Batch103.valid4157
  · exact MergedCutProfiles.Batch103.valid4158
  · exact MergedCutProfiles.Batch103.valid4159
  · exact MergedCutProfiles.Batch104.valid4160
  · exact MergedCutProfiles.Batch104.valid4161
  · exact MergedCutProfiles.Batch104.valid4162
theorem numericValid623 : retention623.NumericValid := by decide +kernel
def certificate623 : RatCutBinCertificate := ⟨⟨retention623,(2102826811312011789/1000000000000000000),(5622540848385301/62500000000000000),(12034105757834079189/1000000000000000000),(38381348920839597449/125000000000000000),(207736162294316353/100000000000000000)⟩,(993756035613194971/1000000000000000000),(39148389737102261/100000000000000000),(30172062671758221/125000000000000000),(126710995738469051/1000000000000000000)⟩
theorem valid623 : certificate623.Valid := by decide +kernel
theorem sound623 : certificate623.Sound := rat_cut_bin_certificate_sound certificate623 profilesValid623 numericValid623 valid623

def certificates : List RatCutBinCertificate := [certificate612,certificate613,certificate614,certificate615,certificate616,certificate617,certificate618,certificate619,certificate620,certificate621,certificate622,certificate623]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound612,List.forall_mem_cons.mpr ⟨sound613,List.forall_mem_cons.mpr ⟨sound614,List.forall_mem_cons.mpr ⟨sound615,List.forall_mem_cons.mpr ⟨sound616,List.forall_mem_cons.mpr ⟨sound617,List.forall_mem_cons.mpr ⟨sound618,List.forall_mem_cons.mpr ⟨sound619,List.forall_mem_cons.mpr ⟨sound620,List.forall_mem_cons.mpr ⟨sound621,List.forall_mem_cons.mpr ⟨sound622,List.forall_mem_cons.mpr ⟨sound623,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch051
