import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch371
import Cycle12.MergedCutProfiles.Batch372
import Cycle12.MergedCutProfiles.Batch485
import Cycle12.MergedCutProfiles.Batch486
import Cycle12.MergedCutProfiles.Batch609
import Cycle12.MergedCutProfiles.Batch694
import Cycle12.MergedCutProfiles.Batch695

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch413

def retention4956 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1/40),(1231092160994941151/25000000000000000),(21/20),(1105862708859271283/500000000000000000),false,MergedCutProfiles.Batch694.profile27773,(fun _ => MergedCutProfiles.Batch694.profile27773)⟩
theorem profilesValid4956 : retention4956.ProfilesValid := by
  exact MergedCutProfiles.Batch694.valid27773
theorem numericValid4956 : retention4956.NumericValid := by decide +kernel
def certificate4956 : RatCutBinCertificate := ⟨⟨retention4956,(938396155085472921/500000000000000000),(13651068898300767/125000000000000000),(12679908924361190897/1000000000000000000),(26698485819870823135647/1000000000000000000),(2194752908228599131/1000000000000000000)⟩,(999937026858685813/1000000000000000000),(2713322713126663/3906250000000000),(52270598201622273/1000000000000000000),(52503117791347897/500000000000000000)⟩
theorem valid4956 : certificate4956.Valid := by decide +kernel
theorem sound4956 : certificate4956.Sound := rat_cut_bin_certificate_sound certificate4956 profilesValid4956 numericValid4956 valid4956

def retention4957 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(640307634242292091/1997789544835731851268),(298613245512299309/500000000000000000),4,(1086538013300173666885947732973869867/477781192819678894400000000000000000),true,MergedCutProfiles.Batch694.profile27774,![MergedCutProfiles.Batch694.profile27774,MergedCutProfiles.Batch694.profile27775,MergedCutProfiles.Batch694.profile27776,MergedCutProfiles.Batch694.profile27777,MergedCutProfiles.Batch609.profile24375,MergedCutProfiles.Batch694.profile27778,MergedCutProfiles.Batch694.profile27779,MergedCutProfiles.Batch694.profile27780,MergedCutProfiles.Batch694.profile27781,MergedCutProfiles.Batch609.profile24376,MergedCutProfiles.Batch694.profile27782,MergedCutProfiles.Batch694.profile27783,MergedCutProfiles.Batch694.profile27784,MergedCutProfiles.Batch694.profile27785,MergedCutProfiles.Batch609.profile24377,MergedCutProfiles.Batch694.profile27786]⟩
theorem profilesValid4957 : retention4957.ProfilesValid := by
  change ∀ j : Fin 16, (retention4957.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch694.valid27774
  · exact MergedCutProfiles.Batch694.valid27775
  · exact MergedCutProfiles.Batch694.valid27776
  · exact MergedCutProfiles.Batch694.valid27777
  · exact MergedCutProfiles.Batch609.valid24375
  · exact MergedCutProfiles.Batch694.valid27778
  · exact MergedCutProfiles.Batch694.valid27779
  · exact MergedCutProfiles.Batch694.valid27780
  · exact MergedCutProfiles.Batch694.valid27781
  · exact MergedCutProfiles.Batch609.valid24376
  · exact MergedCutProfiles.Batch694.valid27782
  · exact MergedCutProfiles.Batch694.valid27783
  · exact MergedCutProfiles.Batch694.valid27784
  · exact MergedCutProfiles.Batch694.valid27785
  · exact MergedCutProfiles.Batch609.valid24377
  · exact MergedCutProfiles.Batch694.valid27786
theorem numericValid4957 : retention4957.NumericValid := by decide +kernel
def certificate4957 : RatCutBinCertificate := ⟨⟨retention4957,(478642176556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(1103081529201972451/500000000000000000)⟩,(249983534894331307/250000000000000000),(87595954169050787/125000000000000000),(10010832880134263/200000000000000000),(2803358399698649/125000000000000000)⟩
theorem valid4957 : certificate4957.Valid := by decide +kernel
theorem sound4957 : certificate4957.Sound := rat_cut_bin_certificate_sound certificate4957 profilesValid4957 numericValid4957 valid4957

def retention4958 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(276178406000000000/499447386208932962817),(640307634242292091/1000000000000000000),4,(374875462458610852779773260571454681/160076908560573022750000000000000000),true,MergedCutProfiles.Batch694.profile27775,![MergedCutProfiles.Batch694.profile27775,MergedCutProfiles.Batch694.profile27787,MergedCutProfiles.Batch609.profile24375,MergedCutProfiles.Batch694.profile27779,MergedCutProfiles.Batch609.profile24385,MergedCutProfiles.Batch694.profile27788,MergedCutProfiles.Batch694.profile27783,MergedCutProfiles.Batch694.profile27785,MergedCutProfiles.Batch694.profile27786,MergedCutProfiles.Batch609.profile24386,MergedCutProfiles.Batch694.profile27789,MergedCutProfiles.Batch694.profile27790,MergedCutProfiles.Batch694.profile27791,MergedCutProfiles.Batch485.profile19427,MergedCutProfiles.Batch609.profile24387,MergedCutProfiles.Batch694.profile27792]⟩
theorem profilesValid4958 : retention4958.ProfilesValid := by
  change ∀ j : Fin 16, (retention4958.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch694.valid27775
  · exact MergedCutProfiles.Batch694.valid27787
  · exact MergedCutProfiles.Batch609.valid24375
  · exact MergedCutProfiles.Batch694.valid27779
  · exact MergedCutProfiles.Batch609.valid24385
  · exact MergedCutProfiles.Batch694.valid27788
  · exact MergedCutProfiles.Batch694.valid27783
  · exact MergedCutProfiles.Batch694.valid27785
  · exact MergedCutProfiles.Batch694.valid27786
  · exact MergedCutProfiles.Batch609.valid24386
  · exact MergedCutProfiles.Batch694.valid27789
  · exact MergedCutProfiles.Batch694.valid27790
  · exact MergedCutProfiles.Batch694.valid27791
  · exact MergedCutProfiles.Batch485.valid19427
  · exact MergedCutProfiles.Batch609.valid24387
  · exact MergedCutProfiles.Batch694.valid27792
theorem numericValid4958 : retention4958.NumericValid := by decide +kernel
def certificate4958 : RatCutBinCertificate := ⟨⟨retention4958,(478642176556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(2273875957011572137/1000000000000000000)⟩,(249983534894331307/250000000000000000),(324809818446977481/500000000000000000),(70155069682259473/1000000000000000000),(16317262278882529/500000000000000000)⟩
theorem valid4958 : certificate4958.Valid := by decide +kernel
theorem sound4958 : certificate4958.Sound := rat_cut_bin_certificate_sound certificate4958 profilesValid4958 numericValid4958 valid4958

def retention4959 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(395889244245717419/499447386208932962817),(138089203/125000000),(57/20),(165999218162983033875732811393407879/69044601500000000000000000000000000),true,MergedCutProfiles.Batch694.profile27793,![MergedCutProfiles.Batch694.profile27793,MergedCutProfiles.Batch609.profile24375,MergedCutProfiles.Batch694.profile27779,MergedCutProfiles.Batch609.profile24376,MergedCutProfiles.Batch609.profile24395,MergedCutProfiles.Batch609.profile24377,MergedCutProfiles.Batch609.profile24386,MergedCutProfiles.Batch609.profile24378,MergedCutProfiles.Batch694.profile27791,MergedCutProfiles.Batch485.profile19427,MergedCutProfiles.Batch694.profile27794,MergedCutProfiles.Batch694.profile27795,MergedCutProfiles.Batch694.profile27796,MergedCutProfiles.Batch609.profile24388,MergedCutProfiles.Batch694.profile27797,MergedCutProfiles.Batch609.profile24379]⟩
theorem profilesValid4959 : retention4959.ProfilesValid := by
  change ∀ j : Fin 16, (retention4959.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch694.valid27793
  · exact MergedCutProfiles.Batch609.valid24375
  · exact MergedCutProfiles.Batch694.valid27779
  · exact MergedCutProfiles.Batch609.valid24376
  · exact MergedCutProfiles.Batch609.valid24395
  · exact MergedCutProfiles.Batch609.valid24377
  · exact MergedCutProfiles.Batch609.valid24386
  · exact MergedCutProfiles.Batch609.valid24378
  · exact MergedCutProfiles.Batch694.valid27791
  · exact MergedCutProfiles.Batch485.valid19427
  · exact MergedCutProfiles.Batch694.valid27794
  · exact MergedCutProfiles.Batch694.valid27795
  · exact MergedCutProfiles.Batch694.valid27796
  · exact MergedCutProfiles.Batch609.valid24388
  · exact MergedCutProfiles.Batch694.valid27797
  · exact MergedCutProfiles.Batch609.valid24379
theorem numericValid4959 : retention4959.NumericValid := by decide +kernel
def certificate4959 : RatCutBinCertificate := ⟨⟨retention4959,(478642176556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(2355803063241019449/1000000000000000000)⟩,(249983534894331307/250000000000000000),(913400780827417/2000000000000000),(92685318703572869/500000000000000000),(60677233441363893/500000000000000000)⟩
theorem valid4959 : certificate4959.Valid := by decide +kernel
theorem sound4959 : certificate4959.Sound := rat_cut_bin_certificate_sound certificate4959 profilesValid4959 numericValid4959 valid4959

def retention4960 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(16000000000000000000/499447386208932962817),(395889244245717419/250000000000000000),(11/5),(692650410531822015919/320000000000000000000),true,MergedCutProfiles.Batch694.profile27798,![MergedCutProfiles.Batch694.profile27798,MergedCutProfiles.Batch694.profile27799,MergedCutProfiles.Batch695.profile27800,MergedCutProfiles.Batch486.profile19448,MergedCutProfiles.Batch695.profile27801,MergedCutProfiles.Batch695.profile27802,MergedCutProfiles.Batch695.profile27803,MergedCutProfiles.Batch695.profile27804,MergedCutProfiles.Batch695.profile27805,MergedCutProfiles.Batch695.profile27806,MergedCutProfiles.Batch371.profile14858,MergedCutProfiles.Batch695.profile27807,MergedCutProfiles.Batch695.profile27808,MergedCutProfiles.Batch695.profile27809,MergedCutProfiles.Batch695.profile27810,MergedCutProfiles.Batch695.profile27811]⟩
theorem profilesValid4960 : retention4960.ProfilesValid := by
  change ∀ j : Fin 16, (retention4960.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch694.valid27798
  · exact MergedCutProfiles.Batch694.valid27799
  · exact MergedCutProfiles.Batch695.valid27800
  · exact MergedCutProfiles.Batch486.valid19448
  · exact MergedCutProfiles.Batch695.valid27801
  · exact MergedCutProfiles.Batch695.valid27802
  · exact MergedCutProfiles.Batch695.valid27803
  · exact MergedCutProfiles.Batch695.valid27804
  · exact MergedCutProfiles.Batch695.valid27805
  · exact MergedCutProfiles.Batch695.valid27806
  · exact MergedCutProfiles.Batch371.valid14858
  · exact MergedCutProfiles.Batch695.valid27807
  · exact MergedCutProfiles.Batch695.valid27808
  · exact MergedCutProfiles.Batch695.valid27809
  · exact MergedCutProfiles.Batch695.valid27810
  · exact MergedCutProfiles.Batch695.valid27811
theorem numericValid4960 : retention4960.NumericValid := by decide +kernel
def certificate4960 : RatCutBinCertificate := ⟨⟨retention4960,(478642176556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(1063574522699775419/500000000000000000)⟩,(249983534894331307/250000000000000000),(427146550214337633/1000000000000000000),(26188750462934641/125000000000000000),(39638221762324207/250000000000000000)⟩
theorem valid4960 : certificate4960.Valid := by decide +kernel
theorem sound4960 : certificate4960.Sound := rat_cut_bin_certificate_sound certificate4960 profilesValid4960 numericValid4960 valid4960

def retention4961 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),64,1,(9976258213095706455955121867646831/10000000000000000000000000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid4961 : retention4961.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid4961 : retention4961.NumericValid := by decide +kernel
def certificate4961 : RatCutBinCertificate := ⟨⟨retention4961,(478642176556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(196126669471837753/200000000000000000)⟩,(249983534894331307/250000000000000000),(54271465379773021/100000000000000000),(125593554343899591/1000000000000000000),(121294512035964971/1000000000000000000)⟩
theorem valid4961 : certificate4961.Valid := by decide +kernel
theorem sound4961 : certificate4961.Sound := rat_cut_bin_certificate_sound certificate4961 profilesValid4961 numericValid4961 valid4961

def retention4962 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(16000000000000000000/499447386208932962817),(7162109324581337561/200000000000000000),1,(76737849232527250756978565118219909381/35810546622906687805000000000000000000),false,MergedCutProfiles.Batch695.profile27812,(fun _ => MergedCutProfiles.Batch695.profile27812)⟩
theorem profilesValid4962 : retention4962.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27812
theorem numericValid4962 : retention4962.NumericValid := by decide +kernel
def certificate4962 : RatCutBinCertificate := ⟨⟨retention4962,(435747942806307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(2127414382615729169/1000000000000000000)⟩,(249985010450221199/250000000000000000),(4686695842517907/250000000000000000),(175563785263503989/200000000000000000),(440663897654862323/250000000000000000)⟩
theorem valid4962 : certificate4962.Valid := by decide +kernel
theorem sound4962 : certificate4962.Sound := rat_cut_bin_certificate_sound certificate4962 profilesValid4962 numericValid4962 valid4962

def retention4963 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),64,1,(9976258213095706455955121867646831/10000000000000000000000000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid4963 : retention4963.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid4963 : retention4963.NumericValid := by decide +kernel
def certificate4963 : RatCutBinCertificate := ⟨⟨retention4963,(435747942806307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(98215615329923889/100000000000000000)⟩,(249985010450221199/250000000000000000),(20303378660969723/500000000000000000),(814048535771871549/1000000000000000000),(78739086139018773/100000000000000000)⟩
theorem valid4963 : certificate4963.Valid := by decide +kernel
theorem sound4963 : certificate4963.Sound := rat_cut_bin_certificate_sound certificate4963 profilesValid4963 numericValid4963 valid4963

def retention4964 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(357158585991921779/998894772417865925634),(70724472473647877/100000000000000000),4,(13335817742898595972657103724813927/5525349412003740390625000000000000),false,MergedCutProfiles.Batch695.profile27813,(fun _ => MergedCutProfiles.Batch695.profile27813)⟩
theorem profilesValid4964 : retention4964.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27813
theorem numericValid4964 : retention4964.NumericValid := by decide +kernel
def certificate4964 : RatCutBinCertificate := ⟨⟨retention4964,(471259808556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(586662092936289097/250000000000000000)⟩,(999935155387811347/1000000000000000000),(845943745657606143/1000000000000000000),(6263910912494747/500000000000000000),(760847231864641/125000000000000000)⟩
theorem valid4964 : certificate4964.Valid := by decide +kernel
theorem sound4964 : certificate4964.Sound := rat_cut_bin_certificate_sound certificate4964 profilesValid4964 numericValid4964 valid4964

def retention4965 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(217900674654621193/499447386208932962817),(357158585991921779/500000000000000000),4,(6903486890474128670123770433857535799/2857268687935374232000000000000000000),false,MergedCutProfiles.Batch695.profile27814,(fun _ => MergedCutProfiles.Batch695.profile27814)⟩
theorem profilesValid4965 : retention4965.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27814
theorem numericValid4965 : retention4965.NumericValid := by decide +kernel
def certificate4965 : RatCutBinCertificate := ⟨⟨retention4965,(471259808556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(1174596173742205389/500000000000000000)⟩,(999935155387811347/1000000000000000000),(843035537167304017/1000000000000000000),(13019376829520981/1000000000000000000),(6342079306245337/1000000000000000000)⟩
theorem valid4965 : certificate4965.Valid := by decide +kernel
theorem sound4965 : certificate4965.Sound := rat_cut_bin_certificate_sound certificate4965 profilesValid4965 numericValid4965 valid4965

def retention4966 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(969314350194012041/499447386208932962817),(217900674654621193/250000000000000000),(73/20),(209810359304812510958275773022181381959/87160269861848477200000000000000000000),false,MergedCutProfiles.Batch695.profile27815,(fun _ => MergedCutProfiles.Batch695.profile27815)⟩
theorem profilesValid4966 : retention4966.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27815
theorem numericValid4966 : retention4966.NumericValid := by decide +kernel
def certificate4966 : RatCutBinCertificate := ⟨⟨retention4966,(471259808556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(1173056430465562131/500000000000000000)⟩,(999935155387811347/1000000000000000000),(404072972773632269/500000000000000000),(9854388223102663/500000000000000000),(5269052378249359/500000000000000000)⟩
theorem valid4966 : certificate4966.Valid := by decide +kernel
theorem sound4966 : certificate4966.Sound := rat_cut_bin_certificate_sound certificate4966 profilesValid4966 numericValid4966 valid4966

def retention4967 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(15550588333307153525/665929848278577283756),(969314350194012041/250000000000000000),(3/2),(34389772163582566559202547197705067007/15509029603104192656000000000000000000),false,MergedCutProfiles.Batch695.profile27816,(fun _ => MergedCutProfiles.Batch695.profile27816)⟩
theorem profilesValid4967 : retention4967.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27816
theorem numericValid4967 : retention4967.NumericValid := by decide +kernel
def certificate4967 : RatCutBinCertificate := ⟨⟨retention4967,(471259808556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(2192307617373561687/1000000000000000000)⟩,(999935155387811347/1000000000000000000),(145844789182952311/200000000000000000),(10126450369547407/250000000000000000),(23654017868215491/500000000000000000)⟩
theorem valid4967 : certificate4967.Valid := by decide +kernel
theorem sound4967 : certificate4967.Sound := rat_cut_bin_certificate_sound certificate4967 profilesValid4967 numericValid4967 valid4967

def certificates : List RatCutBinCertificate := [certificate4956,certificate4957,certificate4958,certificate4959,certificate4960,certificate4961,certificate4962,certificate4963,certificate4964,certificate4965,certificate4966,certificate4967]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4956,List.forall_mem_cons.mpr ⟨sound4957,List.forall_mem_cons.mpr ⟨sound4958,List.forall_mem_cons.mpr ⟨sound4959,List.forall_mem_cons.mpr ⟨sound4960,List.forall_mem_cons.mpr ⟨sound4961,List.forall_mem_cons.mpr ⟨sound4962,List.forall_mem_cons.mpr ⟨sound4963,List.forall_mem_cons.mpr ⟨sound4964,List.forall_mem_cons.mpr ⟨sound4965,List.forall_mem_cons.mpr ⟨sound4966,List.forall_mem_cons.mpr ⟨sound4967,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch413
