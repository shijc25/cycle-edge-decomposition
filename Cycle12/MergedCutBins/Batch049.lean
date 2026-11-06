import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch097
import Cycle12.MergedCutProfiles.Batch098
import Cycle12.MergedCutProfiles.Batch099
import Cycle12.MergedCutProfiles.Batch100

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch049

def retention588 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(994248408727596299/26825845523449284044),(180016022829070039/200000000000000000),(57/20),(538637952012747287631/256000000000000000000),true,MergedCutProfiles.Batch098.profile3943,![MergedCutProfiles.Batch098.profile3943,MergedCutProfiles.Batch098.profile3944,MergedCutProfiles.Batch098.profile3945,MergedCutProfiles.Batch098.profile3946,MergedCutProfiles.Batch098.profile3947,MergedCutProfiles.Batch098.profile3948,MergedCutProfiles.Batch098.profile3949,MergedCutProfiles.Batch098.profile3950,MergedCutProfiles.Batch097.profile3907,MergedCutProfiles.Batch098.profile3937,MergedCutProfiles.Batch098.profile3951,MergedCutProfiles.Batch098.profile3952,MergedCutProfiles.Batch098.profile3953,MergedCutProfiles.Batch098.profile3954,MergedCutProfiles.Batch098.profile3955,MergedCutProfiles.Batch098.profile3956]⟩
theorem profilesValid588 : retention588.ProfilesValid := by
  change ∀ j : Fin 16, (retention588.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch098.valid3943
  · exact MergedCutProfiles.Batch098.valid3944
  · exact MergedCutProfiles.Batch098.valid3945
  · exact MergedCutProfiles.Batch098.valid3946
  · exact MergedCutProfiles.Batch098.valid3947
  · exact MergedCutProfiles.Batch098.valid3948
  · exact MergedCutProfiles.Batch098.valid3949
  · exact MergedCutProfiles.Batch098.valid3950
  · exact MergedCutProfiles.Batch097.valid3907
  · exact MergedCutProfiles.Batch098.valid3937
  · exact MergedCutProfiles.Batch098.valid3951
  · exact MergedCutProfiles.Batch098.valid3952
  · exact MergedCutProfiles.Batch098.valid3953
  · exact MergedCutProfiles.Batch098.valid3954
  · exact MergedCutProfiles.Batch098.valid3955
  · exact MergedCutProfiles.Batch098.valid3956
theorem numericValid588 : retention588.NumericValid := by decide +kernel
def certificate588 : RatCutBinCertificate := ⟨⟨retention588,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(515231181215287407/250000000000000000)⟩,(993966059501501379/1000000000000000000),(380362566896032503/1000000000000000000),(62991252986877851/250000000000000000),(141130798208841607/1000000000000000000)⟩
theorem valid588 : certificate588.Valid := by decide +kernel
theorem sound588 : certificate588.Sound := rat_cut_bin_certificate_sound certificate588 profilesValid588 numericValid588 valid588

def retention589 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(484135530713825722/6706461380862321011),(994248408727596299/1000000000000000000),(13/5),(2537022459930495140567/1280000000000000000000),true,MergedCutProfiles.Batch098.profile3957,![MergedCutProfiles.Batch098.profile3957,MergedCutProfiles.Batch098.profile3958,MergedCutProfiles.Batch098.profile3959,MergedCutProfiles.Batch099.profile3960,MergedCutProfiles.Batch099.profile3961,MergedCutProfiles.Batch098.profile3924,MergedCutProfiles.Batch098.profile3941,MergedCutProfiles.Batch099.profile3962,MergedCutProfiles.Batch099.profile3963,MergedCutProfiles.Batch099.profile3964,MergedCutProfiles.Batch099.profile3965,MergedCutProfiles.Batch099.profile3966,MergedCutProfiles.Batch099.profile3967,MergedCutProfiles.Batch099.profile3968,MergedCutProfiles.Batch099.profile3969,MergedCutProfiles.Batch099.profile3970]⟩
theorem profilesValid589 : retention589.ProfilesValid := by
  change ∀ j : Fin 16, (retention589.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch098.valid3957
  · exact MergedCutProfiles.Batch098.valid3958
  · exact MergedCutProfiles.Batch098.valid3959
  · exact MergedCutProfiles.Batch099.valid3960
  · exact MergedCutProfiles.Batch099.valid3961
  · exact MergedCutProfiles.Batch098.valid3924
  · exact MergedCutProfiles.Batch098.valid3941
  · exact MergedCutProfiles.Batch099.valid3962
  · exact MergedCutProfiles.Batch099.valid3963
  · exact MergedCutProfiles.Batch099.valid3964
  · exact MergedCutProfiles.Batch099.valid3965
  · exact MergedCutProfiles.Batch099.valid3966
  · exact MergedCutProfiles.Batch099.valid3967
  · exact MergedCutProfiles.Batch099.valid3968
  · exact MergedCutProfiles.Batch099.valid3969
  · exact MergedCutProfiles.Batch099.valid3970
theorem numericValid589 : retention589.NumericValid := by decide +kernel
def certificate589 : RatCutBinCertificate := ⟨⟨retention589,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(388540473383788437/200000000000000000)⟩,(993966059501501379/1000000000000000000),(387643632739763893/1000000000000000000),(244996629829743963/1000000000000000000),(70504803108130843/500000000000000000)⟩
theorem valid589 : certificate589.Valid := by decide +kernel
theorem sound589 : certificate589.Sound := rat_cut_bin_certificate_sound certificate589 profilesValid589 numericValid589 valid589

def retention590 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(7569290203661053719/26825845523449284044),(242067765356912861/125000000000000000),(8/5),(231142276047602879383/160000000000000000000),true,MergedCutProfiles.Batch099.profile3971,![MergedCutProfiles.Batch099.profile3971,MergedCutProfiles.Batch099.profile3972,MergedCutProfiles.Batch099.profile3973,MergedCutProfiles.Batch099.profile3974,MergedCutProfiles.Batch099.profile3975,MergedCutProfiles.Batch099.profile3976,MergedCutProfiles.Batch099.profile3977,MergedCutProfiles.Batch099.profile3978,MergedCutProfiles.Batch099.profile3979,MergedCutProfiles.Batch099.profile3980,MergedCutProfiles.Batch099.profile3981,MergedCutProfiles.Batch099.profile3982,MergedCutProfiles.Batch099.profile3983,MergedCutProfiles.Batch099.profile3984,MergedCutProfiles.Batch099.profile3985,MergedCutProfiles.Batch099.profile3986]⟩
theorem profilesValid590 : retention590.ProfilesValid := by
  change ∀ j : Fin 16, (retention590.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch099.valid3971
  · exact MergedCutProfiles.Batch099.valid3972
  · exact MergedCutProfiles.Batch099.valid3973
  · exact MergedCutProfiles.Batch099.valid3974
  · exact MergedCutProfiles.Batch099.valid3975
  · exact MergedCutProfiles.Batch099.valid3976
  · exact MergedCutProfiles.Batch099.valid3977
  · exact MergedCutProfiles.Batch099.valid3978
  · exact MergedCutProfiles.Batch099.valid3979
  · exact MergedCutProfiles.Batch099.valid3980
  · exact MergedCutProfiles.Batch099.valid3981
  · exact MergedCutProfiles.Batch099.valid3982
  · exact MergedCutProfiles.Batch099.valid3983
  · exact MergedCutProfiles.Batch099.valid3984
  · exact MergedCutProfiles.Batch099.valid3985
  · exact MergedCutProfiles.Batch099.valid3986
theorem numericValid590 : retention590.NumericValid := by decide +kernel
def certificate590 : RatCutBinCertificate := ⟨⟨retention590,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(1109708168544959/781250000000000)⟩,(993966059501501379/1000000000000000000),(13414206994955977/31250000000000000),(207722047824118293/1000000000000000000),(142351664576892881/1000000000000000000)⟩
theorem valid590 : certificate590.Valid := by decide +kernel
theorem sound590 : certificate590.Sound := rat_cut_bin_certificate_sound certificate590 profilesValid590 numericValid590 valid590

def retention591 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(3174728579505035105/6706461380862321011),(7569290203661053719/1000000000000000000),(21/20),(1399327172721953760843379444911487988031/1345651591761965105600000000000000000000),false,MergedCutProfiles.Batch099.profile3987,(fun _ => MergedCutProfiles.Batch099.profile3987)⟩
theorem profilesValid591 : retention591.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3987
theorem numericValid591 : retention591.NumericValid := by decide +kernel
def certificate591 : RatCutBinCertificate := ⟨⟨retention591,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(255999845985390001/250000000000000000)⟩,(993966059501501379/1000000000000000000),(121378649929686667/250000000000000000),(163678722700381363/1000000000000000000),(70633507362341311/500000000000000000)⟩
theorem valid591 : certificate591.Valid := by decide +kernel
theorem sound591 : certificate591.Sound := rat_cut_bin_certificate_sound certificate591 profilesValid591 numericValid591 valid591

def retention592 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(6673343286798977559/13412922761724642022),(634945715901007021/50000000000000000),(21/20),(12746552490015289901179428262818096371/12698914318020140420000000000000000000),false,MergedCutProfiles.Batch099.profile3988,(fun _ => MergedCutProfiles.Batch099.profile3988)⟩
theorem profilesValid592 : retention592.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3988
theorem numericValid592 : retention592.NumericValid := by decide +kernel
def certificate592 : RatCutBinCertificate := ⟨⟨retention592,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(987862788216453499/1000000000000000000)⟩,(993966059501501379/1000000000000000000),(121862852405020979/250000000000000000),(8114157606330371/50000000000000000),(141721962281562199/1000000000000000000)⟩
theorem valid592 : certificate592.Valid := by decide +kernel
theorem sound592 : certificate592.Sound := rat_cut_bin_certificate_sound certificate592 profilesValid592 numericValid592 valid592

def retention593 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(1/2),(6673343286798977559/500000000000000000),(21/20),(5335629624878170249375723512348566011079/5338674629439182047200000000000000000000),false,MergedCutProfiles.Batch099.profile3989,(fun _ => MergedCutProfiles.Batch099.profile3989)⟩
theorem profilesValid593 : retention593.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3989
theorem numericValid593 : retention593.NumericValid := by decide +kernel
def certificate593 : RatCutBinCertificate := ⟨⟨retention593,(522035734245703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(983541078803061333/1000000000000000000)⟩,(993966059501501379/1000000000000000000),(244227530857748419/500000000000000000),(161562998446304609/1000000000000000000),(140966927765607693/1000000000000000000)⟩
theorem valid593 : certificate593.Valid := by decide +kernel
theorem sound593 : certificate593.Sound := rat_cut_bin_certificate_sound certificate593 profilesValid593 numericValid593 valid593

def retention594 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(2964888954812029030/6706461380862321011),(3702266616140335519/1000000000000000000),(6/5),(410478776140665219366400175267140250279/370226661614033551900000000000000000000),false,MergedCutProfiles.Batch099.profile3990,(fun _ => MergedCutProfiles.Batch099.profile3990)⟩
theorem profilesValid594 : retention594.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3990
theorem numericValid594 : retention594.NumericValid := by decide +kernel
def certificate594 : RatCutBinCertificate := ⟨⟨retention594,(618237391995703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(271804351274915037/250000000000000000)⟩,(992853392086700737/1000000000000000000),(378095327911293971/1000000000000000000),(127081598924785999/500000000000000000),(189780420737686881/1000000000000000000)⟩
theorem valid594 : certificate594.Valid := by decide +kernel
theorem sound594 : certificate594.Sound := rat_cut_bin_certificate_sound certificate594 profilesValid594 numericValid594 valid594

def retention595 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(3307832758261394876/6706461380862321011),(296488895481202903/25000000000000000),(21/20),(9595189498154006761254960726185023891/9487644655398492896000000000000000000),false,MergedCutProfiles.Batch099.profile3991,(fun _ => MergedCutProfiles.Batch099.profile3991)⟩
theorem profilesValid595 : retention595.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3991
theorem numericValid595 : retention595.NumericValid := by decide +kernel
def certificate595 : RatCutBinCertificate := ⟨⟨retention595,(618237391995703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(496259341016362899/500000000000000000)⟩,(992853392086700737/1000000000000000000),(207085180729357839/500000000000000000),(44149350317974117/200000000000000000),(48126229564964467/250000000000000000)⟩
theorem valid595 : certificate595.Valid := by decide +kernel
theorem sound595 : certificate595.Sound := rat_cut_bin_certificate_sound certificate595 profilesValid595 numericValid595 valid595

def retention596 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(3340911085844008825/6706461380862321011),(826958189565348719/62500000000000000),(21/20),(1327063738887874974786089603311290253559/1323133103304557950400000000000000000000),false,MergedCutProfiles.Batch099.profile3992,(fun _ => MergedCutProfiles.Batch099.profile3992)⟩
theorem profilesValid596 : retention596.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3992
theorem numericValid596 : retention596.NumericValid := by decide +kernel
def certificate596 : RatCutBinCertificate := ⟨⟨retention596,(618237391995703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(984154175345375467/1000000000000000000)⟩,(992853392086700737/1000000000000000000),(208845235629753893/500000000000000000),(54414714884275717/250000000000000000),(47426460892100749/250000000000000000)⟩
theorem valid596 : certificate596.Valid := by decide +kernel
theorem sound596 : certificate596.Sound := rat_cut_bin_certificate_sound certificate596 profilesValid596 numericValid596 valid596

def retention597 : RatCutRetentionCertificate := ⟨(17/400),(43/1000),(1/2),(133636443433760353/10000000000000000),(21/20),(53424796524946512066086370176549147471/53454577373504141200000000000000000000),false,MergedCutProfiles.Batch099.profile3989,(fun _ => MergedCutProfiles.Batch099.profile3989)⟩
theorem profilesValid597 : retention597.ProfilesValid := by
  exact MergedCutProfiles.Batch099.valid3989
theorem numericValid597 : retention597.NumericValid := by decide +kernel
def certificate597 : RatCutBinCertificate := ⟨⟨retention597,(618237391995703707/250000000000000000),(21376650541548341/250000000000000000),(2949939795123234019/250000000000000000),(39675673919527877589/125000000000000000),(980626351494036569/1000000000000000000)⟩,(992853392086700737/1000000000000000000),(419193121483766253/1000000000000000000),(54087439820151359/250000000000000000),(188049180742346383/1000000000000000000)⟩
theorem valid597 : certificate597.Valid := by decide +kernel
theorem sound597 : certificate597.Sound := rat_cut_bin_certificate_sound certificate597 profilesValid597 numericValid597 valid597

def retention598 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(816071342147727342/26140889609024163467),(201997856967259243/250000000000000000),(31/10),(21272065103874836113/10000000000000000000),true,MergedCutProfiles.Batch099.profile3993,![MergedCutProfiles.Batch099.profile3993,MergedCutProfiles.Batch099.profile3994,MergedCutProfiles.Batch099.profile3995,MergedCutProfiles.Batch099.profile3996,MergedCutProfiles.Batch099.profile3997,MergedCutProfiles.Batch099.profile3998,MergedCutProfiles.Batch099.profile3999,MergedCutProfiles.Batch100.profile4000,MergedCutProfiles.Batch100.profile4001,MergedCutProfiles.Batch100.profile4002,MergedCutProfiles.Batch100.profile4003,MergedCutProfiles.Batch100.profile4004,MergedCutProfiles.Batch100.profile4005,MergedCutProfiles.Batch100.profile4006,MergedCutProfiles.Batch100.profile4007,MergedCutProfiles.Batch100.profile4008]⟩
theorem profilesValid598 : retention598.ProfilesValid := by
  change ∀ j : Fin 16, (retention598.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch099.valid3993
  · exact MergedCutProfiles.Batch099.valid3994
  · exact MergedCutProfiles.Batch099.valid3995
  · exact MergedCutProfiles.Batch099.valid3996
  · exact MergedCutProfiles.Batch099.valid3997
  · exact MergedCutProfiles.Batch099.valid3998
  · exact MergedCutProfiles.Batch099.valid3999
  · exact MergedCutProfiles.Batch100.valid4000
  · exact MergedCutProfiles.Batch100.valid4001
  · exact MergedCutProfiles.Batch100.valid4002
  · exact MergedCutProfiles.Batch100.valid4003
  · exact MergedCutProfiles.Batch100.valid4004
  · exact MergedCutProfiles.Batch100.valid4005
  · exact MergedCutProfiles.Batch100.valid4006
  · exact MergedCutProfiles.Batch100.valid4007
  · exact MergedCutProfiles.Batch100.valid4008
theorem numericValid598 : retention598.NumericValid := by decide +kernel
def certificate598 : RatCutBinCertificate := ⟨⟨retention598,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(1039638024564111669/500000000000000000)⟩,(496923799963887517/500000000000000000),(196549477378116429/500000000000000000),(239865291896736611/1000000000000000000),(125983392868923847/1000000000000000000)⟩
theorem valid598 : certificate598.Valid := by decide +kernel
theorem sound598 : certificate598.Sound := rat_cut_bin_certificate_sound certificate598 profilesValid598 numericValid598 valid598

def retention599 : RatCutRetentionCertificate := ⟨(43/1000),(87/2000),(891406537000000000/26140889609024163467),(408035671073863671/500000000000000000),(31/10),(1357638331602920851739/640000000000000000000),true,MergedCutProfiles.Batch100.profile4009,![MergedCutProfiles.Batch100.profile4009,MergedCutProfiles.Batch100.profile4010,MergedCutProfiles.Batch100.profile4011,MergedCutProfiles.Batch100.profile4012,MergedCutProfiles.Batch100.profile4013,MergedCutProfiles.Batch100.profile4014,MergedCutProfiles.Batch100.profile4015,MergedCutProfiles.Batch100.profile4016,MergedCutProfiles.Batch100.profile4017,MergedCutProfiles.Batch100.profile4018,MergedCutProfiles.Batch100.profile4004,MergedCutProfiles.Batch100.profile4019,MergedCutProfiles.Batch100.profile4020,MergedCutProfiles.Batch100.profile4021,MergedCutProfiles.Batch100.profile4022,MergedCutProfiles.Batch100.profile4023]⟩
theorem profilesValid599 : retention599.ProfilesValid := by
  change ∀ j : Fin 16, (retention599.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch100.valid4009
  · exact MergedCutProfiles.Batch100.valid4010
  · exact MergedCutProfiles.Batch100.valid4011
  · exact MergedCutProfiles.Batch100.valid4012
  · exact MergedCutProfiles.Batch100.valid4013
  · exact MergedCutProfiles.Batch100.valid4014
  · exact MergedCutProfiles.Batch100.valid4015
  · exact MergedCutProfiles.Batch100.valid4016
  · exact MergedCutProfiles.Batch100.valid4017
  · exact MergedCutProfiles.Batch100.valid4018
  · exact MergedCutProfiles.Batch100.valid4004
  · exact MergedCutProfiles.Batch100.valid4019
  · exact MergedCutProfiles.Batch100.valid4020
  · exact MergedCutProfiles.Batch100.valid4021
  · exact MergedCutProfiles.Batch100.valid4022
  · exact MergedCutProfiles.Batch100.valid4023
theorem numericValid599 : retention599.NumericValid := by decide +kernel
def certificate599 : RatCutBinCertificate := ⟨⟨retention599,(2096038742167493743/1000000000000000000),(87716241548175929/1000000000000000000),(11892637746559233419/1000000000000000000),(311738188183217569999/1000000000000000000),(2073379485174697629/1000000000000000000)⟩,(496923799963887517/500000000000000000),(78499441331662873/200000000000000000),(9617102844025641/40000000000000000),(15782567601487217/125000000000000000)⟩
theorem valid599 : certificate599.Valid := by decide +kernel
theorem sound599 : certificate599.Sound := rat_cut_bin_certificate_sound certificate599 profilesValid599 numericValid599 valid599

def certificates : List RatCutBinCertificate := [certificate588,certificate589,certificate590,certificate591,certificate592,certificate593,certificate594,certificate595,certificate596,certificate597,certificate598,certificate599]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound588,List.forall_mem_cons.mpr ⟨sound589,List.forall_mem_cons.mpr ⟨sound590,List.forall_mem_cons.mpr ⟨sound591,List.forall_mem_cons.mpr ⟨sound592,List.forall_mem_cons.mpr ⟨sound593,List.forall_mem_cons.mpr ⟨sound594,List.forall_mem_cons.mpr ⟨sound595,List.forall_mem_cons.mpr ⟨sound596,List.forall_mem_cons.mpr ⟨sound597,List.forall_mem_cons.mpr ⟨sound598,List.forall_mem_cons.mpr ⟨sound599,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch049
