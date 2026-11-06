import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch506
import Cycle12.MergedCutProfiles.Batch507
import Cycle12.MergedCutProfiles.Batch508
import Cycle12.MergedCutProfiles.Batch618
import Cycle12.MergedCutProfiles.Batch619
import Cycle12.MergedCutProfiles.Batch702
import Cycle12.MergedCutProfiles.Batch703

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch420

def retention5040 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(8859176331993116791/382857694444840941312),(394702176359188673/125000000000000000),(33/20),(704420388902945724203943287015582204351/315761741087350938400000000000000000000),false,MergedCutProfiles.Batch702.profile28101,(fun _ => MergedCutProfiles.Batch702.profile28101)⟩
theorem profilesValid5040 : retention5040.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28101
theorem numericValid5040 : retention5040.NumericValid := by decide +kernel
def certificate5040 : RatCutBinCertificate := ⟨⟨retention5040,(1935182033133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(137345432762756607/62500000000000000)⟩,(999924479657702943/1000000000000000000),(359755374916006721/500000000000000000),(43637958711929687/1000000000000000000),(23141300263006261/500000000000000000)⟩
theorem valid5040 : certificate5040.Valid := by decide +kernel
theorem sound5040 : certificate5040.Sound := rat_cut_bin_certificate_sound certificate5040 profilesValid5040 numericValid5040 valid5040

def retention5041 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/40),(8859176331993116791/250000000000000000),(21/20),(1967857532555468025479080336575498745611/885917633199311679100000000000000000000),false,MergedCutProfiles.Batch702.profile28102,(fun _ => MergedCutProfiles.Batch702.profile28102)⟩
theorem profilesValid5041 : retention5041.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28102
theorem numericValid5041 : retention5041.NumericValid := by decide +kernel
def certificate5041 : RatCutBinCertificate := ⟨⟨retention5041,(1935182033133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(1100026212136707517/500000000000000000)⟩,(999924479657702943/1000000000000000000),(84733394481570157/125000000000000000),(3660963710243923/62500000000000000),(116180579608810269/1000000000000000000)⟩
theorem valid5041 : certificate5041.Valid := by decide +kernel
theorem sound5041 : certificate5041.Sound := rat_cut_bin_certificate_sound certificate5041 profilesValid5041 numericValid5041 valid5041

def retention5042 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(158485793803075138/367120525546659461781),(77681498776137211/125000000000000000),4,(288755329033670967643537791986230707/124290398041819537600000000000000000),true,MergedCutProfiles.Batch702.profile28103,![MergedCutProfiles.Batch702.profile28103,MergedCutProfiles.Batch702.profile28104,MergedCutProfiles.Batch702.profile28105,MergedCutProfiles.Batch702.profile28106,MergedCutProfiles.Batch702.profile28107,MergedCutProfiles.Batch702.profile28108,MergedCutProfiles.Batch702.profile28109,MergedCutProfiles.Batch702.profile28110,MergedCutProfiles.Batch618.profile24758,MergedCutProfiles.Batch702.profile28111,MergedCutProfiles.Batch618.profile24745,MergedCutProfiles.Batch702.profile28112,MergedCutProfiles.Batch619.profile24766,MergedCutProfiles.Batch702.profile28113,MergedCutProfiles.Batch702.profile28114,MergedCutProfiles.Batch702.profile28115]⟩
theorem profilesValid5042 : retention5042.ProfilesValid := by
  change ∀ j : Fin 16, (retention5042.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch702.valid28103
  · exact MergedCutProfiles.Batch702.valid28104
  · exact MergedCutProfiles.Batch702.valid28105
  · exact MergedCutProfiles.Batch702.valid28106
  · exact MergedCutProfiles.Batch702.valid28107
  · exact MergedCutProfiles.Batch702.valid28108
  · exact MergedCutProfiles.Batch702.valid28109
  · exact MergedCutProfiles.Batch702.valid28110
  · exact MergedCutProfiles.Batch618.valid24758
  · exact MergedCutProfiles.Batch702.valid28111
  · exact MergedCutProfiles.Batch618.valid24745
  · exact MergedCutProfiles.Batch702.valid28112
  · exact MergedCutProfiles.Batch619.valid24766
  · exact MergedCutProfiles.Batch702.valid28113
  · exact MergedCutProfiles.Batch702.valid28114
  · exact MergedCutProfiles.Batch702.valid28115
theorem numericValid5042 : retention5042.NumericValid := by decide +kernel
def certificate5042 : RatCutBinCertificate := ⟨⟨retention5042,(195241372127270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(447939081421677791/200000000000000000)⟩,(199984495138754771/200000000000000000),(167327543761614577/250000000000000000),(7744580625454953/125000000000000000),(14155376499840027/500000000000000000)⟩
theorem valid5042 : certificate5042.Valid := by decide +kernel
theorem sound5042 : certificate5042.Sound := rat_cut_bin_certificate_sound certificate5042 profilesValid5042 numericValid5042 valid5042

def retention5043 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(273899363000000000/367120525546659461781),(79242896901537569/125000000000000000),4,(74804545760005630481/32000000000000000000),true,MergedCutProfiles.Batch702.profile28116,![MergedCutProfiles.Batch702.profile28116,MergedCutProfiles.Batch702.profile28117,MergedCutProfiles.Batch702.profile28118,MergedCutProfiles.Batch702.profile28119,MergedCutProfiles.Batch618.profile24758,MergedCutProfiles.Batch703.profile28120,MergedCutProfiles.Batch703.profile28121,MergedCutProfiles.Batch702.profile28113,MergedCutProfiles.Batch702.profile28114,MergedCutProfiles.Batch618.profile24759,MergedCutProfiles.Batch703.profile28122,MergedCutProfiles.Batch703.profile28123,MergedCutProfiles.Batch618.profile24747,MergedCutProfiles.Batch703.profile28124,MergedCutProfiles.Batch506.profile20252,MergedCutProfiles.Batch703.profile28125]⟩
theorem profilesValid5043 : retention5043.ProfilesValid := by
  change ∀ j : Fin 16, (retention5043.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch702.valid28116
  · exact MergedCutProfiles.Batch702.valid28117
  · exact MergedCutProfiles.Batch702.valid28118
  · exact MergedCutProfiles.Batch702.valid28119
  · exact MergedCutProfiles.Batch618.valid24758
  · exact MergedCutProfiles.Batch703.valid28120
  · exact MergedCutProfiles.Batch703.valid28121
  · exact MergedCutProfiles.Batch702.valid28113
  · exact MergedCutProfiles.Batch702.valid28114
  · exact MergedCutProfiles.Batch618.valid24759
  · exact MergedCutProfiles.Batch703.valid28122
  · exact MergedCutProfiles.Batch703.valid28123
  · exact MergedCutProfiles.Batch618.valid24747
  · exact MergedCutProfiles.Batch703.valid28124
  · exact MergedCutProfiles.Batch506.valid20252
  · exact MergedCutProfiles.Batch703.valid28125
theorem numericValid5043 : retention5043.NumericValid := by decide +kernel
def certificate5043 : RatCutBinCertificate := ⟨⟨retention5043,(195241372127270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(2254106279434297483/1000000000000000000)⟩,(199984495138754771/200000000000000000),(656538237445780291/1000000000000000000),(67207317272535351/1000000000000000000),(30983932909996169/1000000000000000000)⟩
theorem valid5043 : certificate5043.Valid := by decide +kernel
theorem sound5043 : certificate5043.Sound := rat_cut_bin_certificate_sound certificate5043 profilesValid5043 numericValid5043 valid5043

def retention5044 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(755868110723410550/367120525546659461781),(273899363/250000000),(29/10),(19185056364703309811/8000000000000000000),true,MergedCutProfiles.Batch702.profile28107,![MergedCutProfiles.Batch702.profile28107,MergedCutProfiles.Batch703.profile28126,MergedCutProfiles.Batch703.profile28127,MergedCutProfiles.Batch703.profile28122,MergedCutProfiles.Batch703.profile28128,MergedCutProfiles.Batch618.profile24748,MergedCutProfiles.Batch618.profile24749,MergedCutProfiles.Batch703.profile28129,MergedCutProfiles.Batch703.profile28130,MergedCutProfiles.Batch703.profile28131,MergedCutProfiles.Batch506.profile20253,MergedCutProfiles.Batch703.profile28132,MergedCutProfiles.Batch618.profile24753,MergedCutProfiles.Batch619.profile24768,MergedCutProfiles.Batch703.profile28133,MergedCutProfiles.Batch703.profile28134]⟩
theorem profilesValid5044 : retention5044.ProfilesValid := by
  change ∀ j : Fin 16, (retention5044.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch702.valid28107
  · exact MergedCutProfiles.Batch703.valid28126
  · exact MergedCutProfiles.Batch703.valid28127
  · exact MergedCutProfiles.Batch703.valid28122
  · exact MergedCutProfiles.Batch703.valid28128
  · exact MergedCutProfiles.Batch618.valid24748
  · exact MergedCutProfiles.Batch618.valid24749
  · exact MergedCutProfiles.Batch703.valid28129
  · exact MergedCutProfiles.Batch703.valid28130
  · exact MergedCutProfiles.Batch703.valid28131
  · exact MergedCutProfiles.Batch506.valid20253
  · exact MergedCutProfiles.Batch703.valid28132
  · exact MergedCutProfiles.Batch618.valid24753
  · exact MergedCutProfiles.Batch619.valid24768
  · exact MergedCutProfiles.Batch703.valid28133
  · exact MergedCutProfiles.Batch703.valid28134
theorem numericValid5044 : retention5044.NumericValid := by decide +kernel
def certificate5044 : RatCutBinCertificate := ⟨⟨retention5044,(195241372127270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(584392160804415873/250000000000000000)⟩,(199984495138754771/200000000000000000),(461409760427967031/1000000000000000000),(90852001935417687/500000000000000000),(58407461691363049/500000000000000000)⟩
theorem valid5044 : certificate5044.Valid := by decide +kernel
theorem sound5044 : certificate5044.Sound := rat_cut_bin_certificate_sound certificate5044 profilesValid5044 numericValid5044 valid5044

def retention5045 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(16000000000000000000/367120525546659461781),(15117362214468211/5000000000000000),(3/2),(13468804526887978623/6400000000000000000),true,MergedCutProfiles.Batch703.profile28135,![MergedCutProfiles.Batch703.profile28135,MergedCutProfiles.Batch703.profile28136,MergedCutProfiles.Batch703.profile28137,MergedCutProfiles.Batch703.profile28138,MergedCutProfiles.Batch507.profile20308,MergedCutProfiles.Batch703.profile28139,MergedCutProfiles.Batch703.profile28140,MergedCutProfiles.Batch703.profile28141,MergedCutProfiles.Batch703.profile28142,MergedCutProfiles.Batch703.profile28143,MergedCutProfiles.Batch703.profile28144,MergedCutProfiles.Batch703.profile28145,MergedCutProfiles.Batch703.profile28146,MergedCutProfiles.Batch703.profile28147,MergedCutProfiles.Batch703.profile28148,MergedCutProfiles.Batch703.profile28149]⟩
theorem profilesValid5045 : retention5045.ProfilesValid := by
  change ∀ j : Fin 16, (retention5045.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch703.valid28135
  · exact MergedCutProfiles.Batch703.valid28136
  · exact MergedCutProfiles.Batch703.valid28137
  · exact MergedCutProfiles.Batch703.valid28138
  · exact MergedCutProfiles.Batch507.valid20308
  · exact MergedCutProfiles.Batch703.valid28139
  · exact MergedCutProfiles.Batch703.valid28140
  · exact MergedCutProfiles.Batch703.valid28141
  · exact MergedCutProfiles.Batch703.valid28142
  · exact MergedCutProfiles.Batch703.valid28143
  · exact MergedCutProfiles.Batch703.valid28144
  · exact MergedCutProfiles.Batch703.valid28145
  · exact MergedCutProfiles.Batch703.valid28146
  · exact MergedCutProfiles.Batch703.valid28147
  · exact MergedCutProfiles.Batch703.valid28148
  · exact MergedCutProfiles.Batch703.valid28149
theorem numericValid5045 : retention5045.NumericValid := by decide +kernel
def certificate5045 : RatCutBinCertificate := ⟨⟨retention5045,(195241372127270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(2073174830925252247/1000000000000000000)⟩,(199984495138754771/200000000000000000),(175376429650597303/500000000000000000),(56353401593518427/200000000000000000),(14922411873807217/50000000000000000)⟩
theorem valid5045 : certificate5045.Valid := by decide +kernel
theorem sound5045 : certificate5045.Sound := rat_cut_bin_certificate_sound certificate5045 profilesValid5045 numericValid5045 valid5045

def retention5046 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),64,1,(63850233265400851274717381691339297319/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid5046 : retention5046.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid5046 : retention5046.NumericValid := by decide +kernel
def certificate5046 : RatCutBinCertificate := ⟨⟨retention5046,(195241372127270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(195355201630319919/200000000000000000)⟩,(199984495138754771/200000000000000000),(549670853515598249/1000000000000000000),(60693258059932669/500000000000000000),(14596987261550317/125000000000000000)⟩
theorem valid5046 : certificate5046.Valid := by decide +kernel
theorem sound5046 : certificate5046.Sound := rat_cut_bin_certificate_sound certificate5046 profilesValid5046 numericValid5046 valid5046

def retention5047 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(16000000000000000000/367120525546659461781),(40895616397978384099/1000000000000000000),1,(1075578798440256230423066737519486029/511195204974729801237500000000000000),false,MergedCutProfiles.Batch703.profile28150,(fun _ => MergedCutProfiles.Batch703.profile28150)⟩
theorem profilesValid5047 : retention5047.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28150
theorem numericValid5047 : retention5047.NumericValid := by decide +kernel
def certificate5047 : RatCutBinCertificate := ⟨⟨retention5047,(173141072027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(1042763589019248269/500000000000000000)⟩,(999931251144470103/1000000000000000000),(3391374924828533/200000000000000000),(883307440602222529/1000000000000000000),(1752653771999177099/1000000000000000000)⟩
theorem valid5047 : certificate5047.Valid := by decide +kernel
theorem sound5047 : certificate5047.Sound := rat_cut_bin_certificate_sound certificate5047 profilesValid5047 numericValid5047 valid5047

def retention5048 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),64,1,(63850233265400851274717381691339297319/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid5048 : retention5048.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid5048 : retention5048.NumericValid := by decide +kernel
def certificate5048 : RatCutBinCertificate := ⟨⟨retention5048,(173141072027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(979139954668334247/1000000000000000000)⟩,(999931251144470103/1000000000000000000),(36117434197871907/1000000000000000000),(165334728632485287/200000000000000000),(797176817455181161/1000000000000000000)⟩
theorem valid5048 : certificate5048.Valid := by decide +kernel
theorem sound5048 : certificate5048.Sound := rat_cut_bin_certificate_sound certificate5048 profilesValid5048 numericValid5048 valid5048

def retention5049 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(371400351449047387/734241051093318923562),(367723120246581571/500000000000000000),4,(1434499097523816078644108398175308971/588356992394530513600000000000000000),false,MergedCutProfiles.Batch703.profile28151,(fun _ => MergedCutProfiles.Batch703.profile28151)⟩
theorem profilesValid5049 : retention5049.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28151
theorem numericValid5049 : retention5049.NumericValid := by decide +kernel
def certificate5049 : RatCutBinCertificate := ⟨⟨retention5049,(194291503027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(94200588501475721/40000000000000000)⟩,(199984570572496951/200000000000000000),(805046414132410953/1000000000000000000),(10187483625287207/500000000000000000),(9994483875257863/1000000000000000000)⟩
theorem valid5049 : certificate5049.Valid := by decide +kernel
theorem sound5049 : certificate5049.Sound := rat_cut_bin_certificate_sound certificate5049 profilesValid5049 numericValid5049 valid5049

def retention5050 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(290330747217539587/489494034062212615708),(371400351449047387/500000000000000000),4,(1449540370895328414533302656737470811/594240562318475819200000000000000000),false,MergedCutProfiles.Batch703.profile28152,(fun _ => MergedCutProfiles.Batch703.profile28152)⟩
theorem profilesValid5050 : retention5050.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28152
theorem numericValid5050 : retention5050.NumericValid := by decide +kernel
def certificate5050 : RatCutBinCertificate := ⟨⟨retention5050,(194291503027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(1178093216309216431/500000000000000000)⟩,(199984570572496951/200000000000000000),(802886253344388147/1000000000000000000),(20846310413709237/1000000000000000000),(2561714115888201/250000000000000000)⟩
theorem valid5050 : certificate5050.Valid := by decide +kernel
theorem sound5050 : certificate5050.Sound := rat_cut_bin_certificate_sound certificate5050 profilesValid5050 numericValid5050 valid5050

def retention5051 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(249277677402506261/122373508515553153927),(870992241652618761/1000000000000000000),(73/20),(1123258638005460415406541283226460107157/464529195548063339200000000000000000000),false,MergedCutProfiles.Batch703.profile28153,(fun _ => MergedCutProfiles.Batch703.profile28153)⟩
theorem profilesValid5051 : retention5051.ProfilesValid := by
  exact MergedCutProfiles.Batch703.valid28153
theorem numericValid5051 : retention5051.NumericValid := by decide +kernel
def certificate5051 : RatCutBinCertificate := ⟨⟨retention5051,(194291503027270571/100000000000000000),(155212952940275013/1000000000000000000),(2902141146764401583/200000000000000000),(10717789802044865406831/500000000000000000),(23422027140807901/10000000000000000)⟩,(199984570572496951/200000000000000000),(781624375065946743/1000000000000000000),(25798235543970487/1000000000000000000),(6886561718944277/500000000000000000)⟩
theorem valid5051 : certificate5051.Valid := by decide +kernel
theorem sound5051 : certificate5051.Sound := rat_cut_bin_certificate_sound certificate5051 profilesValid5051 numericValid5051 valid5051

def certificates : List RatCutBinCertificate := [certificate5040,certificate5041,certificate5042,certificate5043,certificate5044,certificate5045,certificate5046,certificate5047,certificate5048,certificate5049,certificate5050,certificate5051]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5040,List.forall_mem_cons.mpr ⟨sound5041,List.forall_mem_cons.mpr ⟨sound5042,List.forall_mem_cons.mpr ⟨sound5043,List.forall_mem_cons.mpr ⟨sound5044,List.forall_mem_cons.mpr ⟨sound5045,List.forall_mem_cons.mpr ⟨sound5046,List.forall_mem_cons.mpr ⟨sound5047,List.forall_mem_cons.mpr ⟨sound5048,List.forall_mem_cons.mpr ⟨sound5049,List.forall_mem_cons.mpr ⟨sound5050,List.forall_mem_cons.mpr ⟨sound5051,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch420
