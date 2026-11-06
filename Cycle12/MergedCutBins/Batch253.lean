import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch069
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch342
import Cycle12.MergedCutProfiles.Batch343
import Cycle12.MergedCutProfiles.Batch344
import Cycle12.MergedCutProfiles.Batch345
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch468
import Cycle12.MergedCutProfiles.Batch469
import Cycle12.MergedCutProfiles.Batch470

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch253

def retention3036 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(674152497303881211/198679826114424114115),(166869430025713171/250000000000000000),4,(4647014716251899627/2000000000000000000),true,MergedCutProfiles.Batch468.profile18741,![MergedCutProfiles.Batch468.profile18741,MergedCutProfiles.Batch468.profile18742,MergedCutProfiles.Batch468.profile18743,MergedCutProfiles.Batch343.profile13745,MergedCutProfiles.Batch468.profile18744,MergedCutProfiles.Batch468.profile18745,MergedCutProfiles.Batch468.profile18746,MergedCutProfiles.Batch343.profile13746,MergedCutProfiles.Batch468.profile18747,MergedCutProfiles.Batch468.profile18748,MergedCutProfiles.Batch342.profile13717,MergedCutProfiles.Batch343.profile13747,MergedCutProfiles.Batch468.profile18749,MergedCutProfiles.Batch468.profile18750,MergedCutProfiles.Batch468.profile18751,MergedCutProfiles.Batch343.profile13748]⟩
theorem profilesValid3036 : retention3036.ProfilesValid := by
  change ∀ j : Fin 16, (retention3036.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch468.valid18741
  · exact MergedCutProfiles.Batch468.valid18742
  · exact MergedCutProfiles.Batch468.valid18743
  · exact MergedCutProfiles.Batch343.valid13745
  · exact MergedCutProfiles.Batch468.valid18744
  · exact MergedCutProfiles.Batch468.valid18745
  · exact MergedCutProfiles.Batch468.valid18746
  · exact MergedCutProfiles.Batch343.valid13746
  · exact MergedCutProfiles.Batch468.valid18747
  · exact MergedCutProfiles.Batch468.valid18748
  · exact MergedCutProfiles.Batch342.valid13717
  · exact MergedCutProfiles.Batch343.valid13747
  · exact MergedCutProfiles.Batch468.valid18749
  · exact MergedCutProfiles.Batch468.valid18750
  · exact MergedCutProfiles.Batch468.valid18751
  · exact MergedCutProfiles.Batch343.valid13748
theorem numericValid3036 : retention3036.NumericValid := by decide +kernel
def certificate3036 : RatCutBinCertificate := ⟨⟨retention3036,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(2280381618232239959/1000000000000000000)⟩,(499560436118984589/500000000000000000),(513179707955148617/1000000000000000000),(144463099051148719/1000000000000000000),(13559258027725469/200000000000000000)⟩
theorem valid3036 : certificate3036.Valid := by decide +kernel
theorem sound3036 : certificate3036.Sound := rat_cut_bin_certificate_sound certificate3036 profilesValid3036 numericValid3036 valid3036

def retention3037 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(204779200069393515/39735965222884822823),(674152497303881211/1000000000000000000),4,(592045118987968837267/256000000000000000000),true,MergedCutProfiles.Batch468.profile18752,![MergedCutProfiles.Batch468.profile18752,MergedCutProfiles.Batch468.profile18743,MergedCutProfiles.Batch468.profile18753,MergedCutProfiles.Batch468.profile18745,MergedCutProfiles.Batch468.profile18754,MergedCutProfiles.Batch468.profile18755,MergedCutProfiles.Batch468.profile18756,MergedCutProfiles.Batch343.profile13747,MergedCutProfiles.Batch342.profile13718,MergedCutProfiles.Batch468.profile18757,MergedCutProfiles.Batch468.profile18758,MergedCutProfiles.Batch468.profile18759,MergedCutProfiles.Batch469.profile18760,MergedCutProfiles.Batch344.profile13763,MergedCutProfiles.Batch469.profile18761,MergedCutProfiles.Batch343.profile13722]⟩
theorem profilesValid3037 : retention3037.ProfilesValid := by
  change ∀ j : Fin 16, (retention3037.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch468.valid18752
  · exact MergedCutProfiles.Batch468.valid18743
  · exact MergedCutProfiles.Batch468.valid18753
  · exact MergedCutProfiles.Batch468.valid18745
  · exact MergedCutProfiles.Batch468.valid18754
  · exact MergedCutProfiles.Batch468.valid18755
  · exact MergedCutProfiles.Batch468.valid18756
  · exact MergedCutProfiles.Batch343.valid13747
  · exact MergedCutProfiles.Batch342.valid13718
  · exact MergedCutProfiles.Batch468.valid18757
  · exact MergedCutProfiles.Batch468.valid18758
  · exact MergedCutProfiles.Batch468.valid18759
  · exact MergedCutProfiles.Batch469.valid18760
  · exact MergedCutProfiles.Batch344.valid13763
  · exact MergedCutProfiles.Batch469.valid18761
  · exact MergedCutProfiles.Batch343.valid13722
theorem numericValid3037 : retention3037.NumericValid := by decide +kernel
def certificate3037 : RatCutBinCertificate := ⟨⟨retention3037,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(141846906910449031/62500000000000000)⟩,(499560436118984589/500000000000000000),(512550830239444279/1000000000000000000),(72441513243291449/500000000000000000),(67844824356407921/1000000000000000000)⟩
theorem valid3037 : certificate3037.Valid := by decide +kernel
theorem sound3037 : certificate3037.Sound := rat_cut_bin_certificate_sound certificate3037 profilesValid3037 numericValid3037 valid3037

def retention3038 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(229685473200000000/39735965222884822823),(40955840013878703/40000000000000000),(57/20),(117535525207551176823/51200000000000000000),true,MergedCutProfiles.Batch469.profile18762,![MergedCutProfiles.Batch469.profile18762,MergedCutProfiles.Batch343.profile13730,MergedCutProfiles.Batch469.profile18763,MergedCutProfiles.Batch343.profile13731,MergedCutProfiles.Batch344.profile13761,MergedCutProfiles.Batch343.profile13732,MergedCutProfiles.Batch469.profile18764,MergedCutProfiles.Batch342.profile13718,MergedCutProfiles.Batch468.profile18757,MergedCutProfiles.Batch343.profile13733,MergedCutProfiles.Batch344.profile13772,MergedCutProfiles.Batch343.profile13734,MergedCutProfiles.Batch469.profile18765,MergedCutProfiles.Batch343.profile13735,MergedCutProfiles.Batch469.profile18766,MergedCutProfiles.Batch343.profile13736]⟩
theorem profilesValid3038 : retention3038.ProfilesValid := by
  change ∀ j : Fin 16, (retention3038.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch469.valid18762
  · exact MergedCutProfiles.Batch343.valid13730
  · exact MergedCutProfiles.Batch469.valid18763
  · exact MergedCutProfiles.Batch343.valid13731
  · exact MergedCutProfiles.Batch344.valid13761
  · exact MergedCutProfiles.Batch343.valid13732
  · exact MergedCutProfiles.Batch469.valid18764
  · exact MergedCutProfiles.Batch342.valid13718
  · exact MergedCutProfiles.Batch468.valid18757
  · exact MergedCutProfiles.Batch343.valid13733
  · exact MergedCutProfiles.Batch344.valid13772
  · exact MergedCutProfiles.Batch343.valid13734
  · exact MergedCutProfiles.Batch469.valid18765
  · exact MergedCutProfiles.Batch343.valid13735
  · exact MergedCutProfiles.Batch469.valid18766
  · exact MergedCutProfiles.Batch343.valid13736
theorem numericValid3038 : retention3038.NumericValid := by decide +kernel
def certificate3038 : RatCutBinCertificate := ⟨⟨retention3038,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(56622216601323587/25000000000000000)⟩,(499560436118984589/500000000000000000),(12757884182221313/31250000000000000),(226005707608655159/1000000000000000000),(14101961915484503/100000000000000000)⟩
theorem valid3038 : certificate3038.Valid := by decide +kernel
theorem sound3038 : certificate3038.Sound := rat_cut_bin_certificate_sound certificate3038 profilesValid3038 numericValid3038 valid3038

def retention3039 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1339469837922471833/198679826114424114115),(574213683/500000000),(13/5),(36502088327893832501/16000000000000000000),true,MergedCutProfiles.Batch468.profile18742,![MergedCutProfiles.Batch468.profile18742,MergedCutProfiles.Batch343.profile13745,MergedCutProfiles.Batch469.profile18767,MergedCutProfiles.Batch343.profile13746,MergedCutProfiles.Batch468.profile18748,MergedCutProfiles.Batch469.profile18764,MergedCutProfiles.Batch468.profile18750,MergedCutProfiles.Batch469.profile18768,MergedCutProfiles.Batch469.profile18769,MergedCutProfiles.Batch469.profile18760,MergedCutProfiles.Batch343.profile13721,MergedCutProfiles.Batch343.profile13735,MergedCutProfiles.Batch344.profile13764,MergedCutProfiles.Batch469.profile18770,MergedCutProfiles.Batch469.profile18771,MergedCutProfiles.Batch469.profile18772]⟩
theorem profilesValid3039 : retention3039.ProfilesValid := by
  change ∀ j : Fin 16, (retention3039.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch468.valid18742
  · exact MergedCutProfiles.Batch343.valid13745
  · exact MergedCutProfiles.Batch469.valid18767
  · exact MergedCutProfiles.Batch343.valid13746
  · exact MergedCutProfiles.Batch468.valid18748
  · exact MergedCutProfiles.Batch469.valid18764
  · exact MergedCutProfiles.Batch468.valid18750
  · exact MergedCutProfiles.Batch469.valid18768
  · exact MergedCutProfiles.Batch469.valid18769
  · exact MergedCutProfiles.Batch469.valid18760
  · exact MergedCutProfiles.Batch343.valid13721
  · exact MergedCutProfiles.Batch343.valid13735
  · exact MergedCutProfiles.Batch344.valid13764
  · exact MergedCutProfiles.Batch469.valid18770
  · exact MergedCutProfiles.Batch469.valid18771
  · exact MergedCutProfiles.Batch469.valid18772
theorem numericValid3039 : retention3039.NumericValid := by decide +kernel
def certificate3039 : RatCutBinCertificate := ⟨⟨retention3039,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(450669764046176211/200000000000000000)⟩,(499560436118984589/500000000000000000),(194104738612734523/500000000000000000),(24446084198410737/100000000000000000),(164040260289895141/1000000000000000000)⟩
theorem valid3039 : certificate3039.Valid := by decide +kernel
theorem sound3039 : certificate3039.Sound := rat_cut_bin_certificate_sound certificate3039 profilesValid3039 numericValid3039 valid3039

def retention3040 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(8525276281428651177/198679826114424114115),(1339469837922471833/1000000000000000000),(47/20),(2682256796061928807129/1280000000000000000000),true,MergedCutProfiles.Batch344.profile13762,![MergedCutProfiles.Batch344.profile13762,MergedCutProfiles.Batch469.profile18773,MergedCutProfiles.Batch344.profile13774,MergedCutProfiles.Batch469.profile18774,MergedCutProfiles.Batch469.profile18775,MergedCutProfiles.Batch344.profile13777,MergedCutProfiles.Batch469.profile18776,MergedCutProfiles.Batch469.profile18777,MergedCutProfiles.Batch344.profile13781,MergedCutProfiles.Batch469.profile18778,MergedCutProfiles.Batch469.profile18779,MergedCutProfiles.Batch344.profile13785,MergedCutProfiles.Batch469.profile18780,MergedCutProfiles.Batch469.profile18781,MergedCutProfiles.Batch469.profile18782,MergedCutProfiles.Batch469.profile18783]⟩
theorem profilesValid3040 : retention3040.ProfilesValid := by
  change ∀ j : Fin 16, (retention3040.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch344.valid13762
  · exact MergedCutProfiles.Batch469.valid18773
  · exact MergedCutProfiles.Batch344.valid13774
  · exact MergedCutProfiles.Batch469.valid18774
  · exact MergedCutProfiles.Batch469.valid18775
  · exact MergedCutProfiles.Batch344.valid13777
  · exact MergedCutProfiles.Batch469.valid18776
  · exact MergedCutProfiles.Batch469.valid18777
  · exact MergedCutProfiles.Batch344.valid13781
  · exact MergedCutProfiles.Batch469.valid18778
  · exact MergedCutProfiles.Batch469.valid18779
  · exact MergedCutProfiles.Batch344.valid13785
  · exact MergedCutProfiles.Batch469.valid18780
  · exact MergedCutProfiles.Batch469.valid18781
  · exact MergedCutProfiles.Batch469.valid18782
  · exact MergedCutProfiles.Batch469.valid18783
theorem numericValid3040 : retention3040.NumericValid := by decide +kernel
def certificate3040 : RatCutBinCertificate := ⟨⟨retention3040,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(258772098687135463/125000000000000000)⟩,(499560436118984589/500000000000000000),(394306963608664597/1000000000000000000),(119369647288580627/500000000000000000),(32831839653249433/200000000000000000)⟩
theorem valid3040 : certificate3040.Valid := by decide +kernel
theorem sound3040 : certificate3040.Sound := rat_cut_bin_certificate_sound certificate3040 profilesValid3040 numericValid3040 valid3040

def retention3041 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(12800000000000000000/39735965222884822823),(8525276281428651177/1000000000000000000),(21/20),(18300549209579856215743948953872442170471/13640442050285841883200000000000000000000),false,MergedCutProfiles.Batch469.profile18784,(fun _ => MergedCutProfiles.Batch469.profile18784)⟩
theorem profilesValid3041 : retention3041.ProfilesValid := by
  exact MergedCutProfiles.Batch469.valid18784
theorem numericValid3041 : retention3041.NumericValid := by decide +kernel
def certificate3041 : RatCutBinCertificate := ⟨⟨retention3041,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(665159294213930433/500000000000000000)⟩,(499560436118984589/500000000000000000),(195420226893523253/500000000000000000),(241980425085670811/1000000000000000000),(26832022472883189/100000000000000000)⟩
theorem valid3041 : certificate3041.Valid := by decide +kernel
theorem sound3041 : certificate3041.Sound := rat_cut_bin_certificate_sound certificate3041 profilesValid3041 numericValid3041 valid3041

def retention3042 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1/2),64,1,(63844992829629538494070841750131834791/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch344.profile13789,(fun _ => MergedCutProfiles.Batch344.profile13789)⟩
theorem profilesValid3042 : retention3042.ProfilesValid := by
  exact MergedCutProfiles.Batch344.valid13789
theorem numericValid3042 : retention3042.NumericValid := by decide +kernel
def certificate3042 : RatCutBinCertificate := ⟨⟨retention3042,(1955754116652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(6167479279980639/6250000000000000)⟩,(499560436118984589/500000000000000000),(478377068317597261/1000000000000000000),(10555538539332241/62500000000000000),(40995631392317929/250000000000000000)⟩
theorem valid3042 : certificate3042.Valid := by decide +kernel
theorem sound3042 : certificate3042.Sound := rat_cut_bin_certificate_sound certificate3042 profilesValid3042 numericValid3042 valid3042

def retention3043 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(12800000000000000000/39735965222884822823),(2423166607914452469/250000000000000000),1,(10230668953660475290704999671128988443/7754133145326247900800000000000000000),false,MergedCutProfiles.Batch469.profile18784,(fun _ => MergedCutProfiles.Batch469.profile18784)⟩
theorem profilesValid3043 : retention3043.ProfilesValid := by
  exact MergedCutProfiles.Batch469.valid18784
theorem numericValid3043 : retention3043.NumericValid := by decide +kernel
def certificate3043 : RatCutBinCertificate := ⟨⟨retention3043,(2102963952652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(1307789809863909229/1000000000000000000)⟩,(249763674143939587/250000000000000000),(99532109441162277/1000000000000000000),(667415304455241857/1000000000000000000),(768309259287702937/1000000000000000000)⟩
theorem valid3043 : certificate3043.Valid := by decide +kernel
theorem sound3043 : certificate3043.Sound := rat_cut_bin_certificate_sound certificate3043 profilesValid3043 numericValid3043 valid3043

def retention3044 : RatCutRetentionCertificate := ⟨(7/200),(9/250),(1/2),64,1,(63844992829629538494070841750131834791/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch344.profile13789,(fun _ => MergedCutProfiles.Batch344.profile13789)⟩
theorem profilesValid3044 : retention3044.ProfilesValid := by
  exact MergedCutProfiles.Batch344.valid13789
theorem numericValid3044 : retention3044.NumericValid := by decide +kernel
def certificate3044 : RatCutBinCertificate := ⟨⟨retention3044,(2102963952652129019/1000000000000000000),(3628243259175483/62500000000000000),(5265365929944836817/500000000000000000),(2103217083560914222659/1000000000000000000),(492992586496501491/500000000000000000)⟩,(249763674143939587/250000000000000000),(4125539930987353/31250000000000000),(59912213188283473/100000000000000000),(581208443443735001/1000000000000000000)⟩
theorem valid3044 : certificate3044.Valid := by decide +kernel
theorem sound3044 : certificate3044.Sound := rat_cut_bin_certificate_sound certificate3044 profilesValid3044 numericValid3044 valid3044

def retention3045 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(344065346086855703/93549116114128117578),(337285899506769633/500000000000000000),4,(18623032012097297421/8000000000000000000),true,MergedCutProfiles.Batch469.profile18785,![MergedCutProfiles.Batch469.profile18785,MergedCutProfiles.Batch469.profile18786,MergedCutProfiles.Batch469.profile18787,MergedCutProfiles.Batch469.profile18788,MergedCutProfiles.Batch469.profile18789,MergedCutProfiles.Batch469.profile18790,MergedCutProfiles.Batch069.profile2772,MergedCutProfiles.Batch345.profile13831,MergedCutProfiles.Batch469.profile18791,MergedCutProfiles.Batch345.profile13806,MergedCutProfiles.Batch344.profile13796,MergedCutProfiles.Batch345.profile13832,MergedCutProfiles.Batch469.profile18792,MergedCutProfiles.Batch069.profile2773,MergedCutProfiles.Batch469.profile18793,MergedCutProfiles.Batch469.profile18794]⟩
theorem profilesValid3045 : retention3045.ProfilesValid := by
  change ∀ j : Fin 16, (retention3045.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch469.valid18785
  · exact MergedCutProfiles.Batch469.valid18786
  · exact MergedCutProfiles.Batch469.valid18787
  · exact MergedCutProfiles.Batch469.valid18788
  · exact MergedCutProfiles.Batch469.valid18789
  · exact MergedCutProfiles.Batch469.valid18790
  · exact MergedCutProfiles.Batch069.valid2772
  · exact MergedCutProfiles.Batch345.valid13831
  · exact MergedCutProfiles.Batch469.valid18791
  · exact MergedCutProfiles.Batch345.valid13806
  · exact MergedCutProfiles.Batch344.valid13796
  · exact MergedCutProfiles.Batch345.valid13832
  · exact MergedCutProfiles.Batch469.valid18792
  · exact MergedCutProfiles.Batch069.valid2773
  · exact MergedCutProfiles.Batch469.valid18793
  · exact MergedCutProfiles.Batch469.valid18794
theorem numericValid3045 : retention3045.NumericValid := by decide +kernel
def certificate3045 : RatCutBinCertificate := ⟨⟨retention3045,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(1141313816450425151/500000000000000000)⟩,(999080091205210327/1000000000000000000),(253080602823361503/500000000000000000),(149193552235852413/1000000000000000000),(274217984595213/3906250000000000)⟩
theorem valid3045 : certificate3045.Valid := by decide +kernel
theorem sound3045 : certificate3045.Sound := rat_cut_bin_certificate_sound certificate3045 profilesValid3045 numericValid3045 valid3045

def retention3046 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(289793702750000000/46774558057064058789),(344065346086855703/500000000000000000),(79/20),(1476513950622205360439/640000000000000000000),true,MergedCutProfiles.Batch469.profile18795,![MergedCutProfiles.Batch469.profile18795,MergedCutProfiles.Batch345.profile13804,MergedCutProfiles.Batch469.profile18789,MergedCutProfiles.Batch345.profile13805,MergedCutProfiles.Batch469.profile18796,MergedCutProfiles.Batch345.profile13806,MergedCutProfiles.Batch345.profile13819,MergedCutProfiles.Batch345.profile13807,MergedCutProfiles.Batch469.profile18793,MergedCutProfiles.Batch068.profile2743,MergedCutProfiles.Batch469.profile18797,MergedCutProfiles.Batch345.profile13809,MergedCutProfiles.Batch469.profile18798,MergedCutProfiles.Batch345.profile13810,MergedCutProfiles.Batch069.profile2760,MergedCutProfiles.Batch070.profile2802]⟩
theorem profilesValid3046 : retention3046.ProfilesValid := by
  change ∀ j : Fin 16, (retention3046.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch469.valid18795
  · exact MergedCutProfiles.Batch345.valid13804
  · exact MergedCutProfiles.Batch469.valid18789
  · exact MergedCutProfiles.Batch345.valid13805
  · exact MergedCutProfiles.Batch469.valid18796
  · exact MergedCutProfiles.Batch345.valid13806
  · exact MergedCutProfiles.Batch345.valid13819
  · exact MergedCutProfiles.Batch345.valid13807
  · exact MergedCutProfiles.Batch469.valid18793
  · exact MergedCutProfiles.Batch068.valid2743
  · exact MergedCutProfiles.Batch469.valid18797
  · exact MergedCutProfiles.Batch345.valid13809
  · exact MergedCutProfiles.Batch469.valid18798
  · exact MergedCutProfiles.Batch345.valid13810
  · exact MergedCutProfiles.Batch069.valid2760
  · exact MergedCutProfiles.Batch070.valid2802
theorem numericValid3046 : retention3046.NumericValid := by decide +kernel
def certificate3046 : RatCutBinCertificate := ⟨⟨retention3046,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(141397957815320843/62500000000000000)⟩,(999080091205210327/1000000000000000000),(126169372558959871/250000000000000000),(30041197735958527/200000000000000000),(70980893539343339/1000000000000000000)⟩
theorem valid3046 : certificate3046.Valid := by decide +kernel
theorem sound3046 : certificate3046.Sound := rat_cut_bin_certificate_sound certificate3046 profilesValid3046 numericValid3046 valid3046

def retention3047 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1788639477413566585/187098232228256235156),(1159174811/1000000000),(51/20),(36082770409111716367/16000000000000000000),true,MergedCutProfiles.Batch469.profile18799,![MergedCutProfiles.Batch469.profile18799,MergedCutProfiles.Batch346.profile13844,MergedCutProfiles.Batch345.profile13818,MergedCutProfiles.Batch470.profile18800,MergedCutProfiles.Batch469.profile18792,MergedCutProfiles.Batch345.profile13820,MergedCutProfiles.Batch470.profile18801,MergedCutProfiles.Batch346.profile13846,MergedCutProfiles.Batch345.profile13810,MergedCutProfiles.Batch069.profile2789,MergedCutProfiles.Batch470.profile18802,MergedCutProfiles.Batch345.profile13824,MergedCutProfiles.Batch470.profile18803,MergedCutProfiles.Batch346.profile13847,MergedCutProfiles.Batch345.profile13826,MergedCutProfiles.Batch470.profile18804]⟩
theorem profilesValid3047 : retention3047.ProfilesValid := by
  change ∀ j : Fin 16, (retention3047.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch469.valid18799
  · exact MergedCutProfiles.Batch346.valid13844
  · exact MergedCutProfiles.Batch345.valid13818
  · exact MergedCutProfiles.Batch470.valid18800
  · exact MergedCutProfiles.Batch469.valid18792
  · exact MergedCutProfiles.Batch345.valid13820
  · exact MergedCutProfiles.Batch470.valid18801
  · exact MergedCutProfiles.Batch346.valid13846
  · exact MergedCutProfiles.Batch345.valid13810
  · exact MergedCutProfiles.Batch069.valid2789
  · exact MergedCutProfiles.Batch470.valid18802
  · exact MergedCutProfiles.Batch345.valid13824
  · exact MergedCutProfiles.Batch470.valid18803
  · exact MergedCutProfiles.Batch346.valid13847
  · exact MergedCutProfiles.Batch345.valid13826
  · exact MergedCutProfiles.Batch470.valid18804
theorem numericValid3047 : retention3047.NumericValid := by decide +kernel
def certificate3047 : RatCutBinCertificate := ⟨⟨retention3047,(490761386733647183/250000000000000000),(61591158108543061/1000000000000000000),(1335955411678237373/125000000000000000),(2010190772826632488059/1000000000000000000),(2226325431627468933/1000000000000000000)⟩,(999080091205210327/1000000000000000000),(389241557746816071/1000000000000000000),(48697141127163959/200000000000000000),(1280737404384213/7812500000000000)⟩
theorem valid3047 : certificate3047.Valid := by decide +kernel
theorem sound3047 : certificate3047.Sound := rat_cut_bin_certificate_sound certificate3047 profilesValid3047 numericValid3047 valid3047

def certificates : List RatCutBinCertificate := [certificate3036,certificate3037,certificate3038,certificate3039,certificate3040,certificate3041,certificate3042,certificate3043,certificate3044,certificate3045,certificate3046,certificate3047]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3036,List.forall_mem_cons.mpr ⟨sound3037,List.forall_mem_cons.mpr ⟨sound3038,List.forall_mem_cons.mpr ⟨sound3039,List.forall_mem_cons.mpr ⟨sound3040,List.forall_mem_cons.mpr ⟨sound3041,List.forall_mem_cons.mpr ⟨sound3042,List.forall_mem_cons.mpr ⟨sound3043,List.forall_mem_cons.mpr ⟨sound3044,List.forall_mem_cons.mpr ⟨sound3045,List.forall_mem_cons.mpr ⟨sound3046,List.forall_mem_cons.mpr ⟨sound3047,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch253
