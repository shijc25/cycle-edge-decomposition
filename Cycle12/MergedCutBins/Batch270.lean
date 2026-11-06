import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch496
import Cycle12.MergedCutProfiles.Batch497
import Cycle12.MergedCutProfiles.Batch498

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch270

def retention3240 : RatCutRetentionCertificate := ⟨(51/1000),(103/2000),(44156178103669869754/89139318625963389647),(10929747055363829147/250000000000000000),1,(43938116725622689248024345854454543583/43718988221455316588000000000000000000),false,MergedCutProfiles.Batch496.profile19873,(fun _ => MergedCutProfiles.Batch496.profile19873)⟩
theorem profilesValid3240 : retention3240.ProfilesValid := by
  exact MergedCutProfiles.Batch496.valid19873
theorem numericValid3240 : retention3240.NumericValid := by decide +kernel
def certificate3240 : RatCutBinCertificate := ⟨⟨retention3240,(1049271155515494869/500000000000000000),(64019242937268319/500000000000000000),(2709606499497404023/200000000000000000),(30278839599139293129/25000000000000000),(985179447863569249/1000000000000000000)⟩,(19969679419299913/20000000000000000),(112104449546805823/250000000000000000),(191937428068700633/1000000000000000000),(184641423945450509/1000000000000000000)⟩
theorem valid3240 : certificate3240.Valid := by decide +kernel
theorem sound3240 : certificate3240.Sound := rat_cut_bin_certificate_sound certificate3240 profilesValid3240 numericValid3240 valid3240

def retention3241 : RatCutRetentionCertificate := ⟨(51/1000),(103/2000),(1/2),(22078089051834934877/500000000000000000),1,(87948409996388878994505422120843517/88312356207339739508000000000000000),false,MergedCutProfiles.Batch496.profile19874,(fun _ => MergedCutProfiles.Batch496.profile19874)⟩
theorem profilesValid3241 : retention3241.ProfilesValid := by
  exact MergedCutProfiles.Batch496.valid19874
theorem numericValid3241 : retention3241.NumericValid := by decide +kernel
def certificate3241 : RatCutBinCertificate := ⟨⟨retention3241,(1049271155515494869/500000000000000000),(64019242937268319/500000000000000000),(2709606499497404023/200000000000000000),(30278839599139293129/25000000000000000),(488023059752071753/500000000000000000)⟩,(19969679419299913/20000000000000000),(226263576340104199/500000000000000000),(188660411912521433/1000000000000000000),(179882112754596273/1000000000000000000)⟩
theorem valid3241 : certificate3241.Valid := by decide +kernel
theorem sound3241 : certificate3241.Sound := rat_cut_bin_certificate_sound certificate3241 profilesValid3241 numericValid3241 valid3241

def retention3242 : RatCutRetentionCertificate := ⟨(51/1000),(103/2000),(41076349383353236397/89139318625963389647),(9900004414754382953/1000000000000000000),1,(1664779069547805016269173389844447563/1584000706360701272480000000000000000),false,MergedCutProfiles.Batch496.profile19875,(fun _ => MergedCutProfiles.Batch496.profile19875)⟩
theorem profilesValid3242 : retention3242.ProfilesValid := by
  exact MergedCutProfiles.Batch496.valid19875
theorem numericValid3242 : retention3242.NumericValid := by decide +kernel
def certificate3242 : RatCutBinCertificate := ⟨⟨retention3242,(1103807762015494869/500000000000000000),(64019242937268319/500000000000000000),(2709606499497404023/200000000000000000),(30278839599139293129/25000000000000000),(1030132668338480733/1000000000000000000)⟩,(998405156299236303/1000000000000000000),(12109386268184397/100000000000000000),(621237126866353201/1000000000000000000),(578668843035514753/1000000000000000000)⟩
theorem valid3242 : certificate3242.Valid := by decide +kernel
theorem sound3242 : certificate3242.Sound := rat_cut_bin_certificate_sound certificate3242 profilesValid3242 numericValid3242 valid3242

def retention3243 : RatCutRetentionCertificate := ⟨(51/1000),(103/2000),(44479800372485905047/89139318625963389647),(41076349383353236397/1000000000000000000),1,(40971520240973942490445323349848324709/41076349383353236397000000000000000000),false,MergedCutProfiles.Batch496.profile19876,(fun _ => MergedCutProfiles.Batch496.profile19876)⟩
theorem profilesValid3243 : retention3243.ProfilesValid := by
  exact MergedCutProfiles.Batch496.valid19876
theorem numericValid3243 : retention3243.NumericValid := by decide +kernel
def certificate3243 : RatCutBinCertificate := ⟨⟨retention3243,(1103807762015494869/500000000000000000),(64019242937268319/500000000000000000),(2709606499497404023/200000000000000000),(30278839599139293129/25000000000000000),(48829218140208361/50000000000000000)⟩,(998405156299236303/1000000000000000000),(63866855048587313/500000000000000000),(607697012192334121/1000000000000000000),(289374058148823019/500000000000000000)⟩
theorem valid3243 : certificate3243.Valid := by decide +kernel
theorem sound3243 : certificate3243.Sound := rat_cut_bin_certificate_sound certificate3243 profilesValid3243 numericValid3243 valid3243

def retention3244 : RatCutRetentionCertificate := ⟨(51/1000),(103/2000),(1/2),(44479800372485905047/1000000000000000000),1,(5537291444169164589782502041077859461/5559975046560738130875000000000000000),false,MergedCutProfiles.Batch496.profile19874,(fun _ => MergedCutProfiles.Batch496.profile19874)⟩
theorem profilesValid3244 : retention3244.ProfilesValid := by
  exact MergedCutProfiles.Batch496.valid19874
theorem numericValid3244 : retention3244.NumericValid := by decide +kernel
def certificate3244 : RatCutBinCertificate := ⟨⟨retention3244,(1103807762015494869/500000000000000000),(64019242937268319/500000000000000000),(2709606499497404023/200000000000000000),(30278839599139293129/25000000000000000),(487528309981313397/500000000000000000)⟩,(998405156299236303/1000000000000000000),(25586769287027209/200000000000000000),(607293612350449437/1000000000000000000),(57850748984149353/100000000000000000)⟩
theorem valid3244 : certificate3244.Valid := by decide +kernel
theorem sound3244 : certificate3244.Sound := rat_cut_bin_certificate_sound certificate3244 profilesValid3244 numericValid3244 valid3244

def retention3245 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(805040271138036194/87180495143465975733),(797069575384194251/1000000000000000000),(17/5),(182854475491376805583/80000000000000000000),true,MergedCutProfiles.Batch496.profile19877,![MergedCutProfiles.Batch496.profile19877,MergedCutProfiles.Batch496.profile19878,MergedCutProfiles.Batch496.profile19879,MergedCutProfiles.Batch497.profile19880,MergedCutProfiles.Batch497.profile19881,MergedCutProfiles.Batch497.profile19882,MergedCutProfiles.Batch497.profile19883,MergedCutProfiles.Batch497.profile19884,MergedCutProfiles.Batch497.profile19885,MergedCutProfiles.Batch497.profile19886,MergedCutProfiles.Batch497.profile19887,MergedCutProfiles.Batch497.profile19888,MergedCutProfiles.Batch497.profile19889,MergedCutProfiles.Batch497.profile19890,MergedCutProfiles.Batch497.profile19891,MergedCutProfiles.Batch497.profile19892]⟩
theorem profilesValid3245 : retention3245.ProfilesValid := by
  change ∀ j : Fin 16, (retention3245.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch496.valid19877
  · exact MergedCutProfiles.Batch496.valid19878
  · exact MergedCutProfiles.Batch496.valid19879
  · exact MergedCutProfiles.Batch497.valid19880
  · exact MergedCutProfiles.Batch497.valid19881
  · exact MergedCutProfiles.Batch497.valid19882
  · exact MergedCutProfiles.Batch497.valid19883
  · exact MergedCutProfiles.Batch497.valid19884
  · exact MergedCutProfiles.Batch497.valid19885
  · exact MergedCutProfiles.Batch497.valid19886
  · exact MergedCutProfiles.Batch497.valid19887
  · exact MergedCutProfiles.Batch497.valid19888
  · exact MergedCutProfiles.Batch497.valid19889
  · exact MergedCutProfiles.Batch497.valid19890
  · exact MergedCutProfiles.Batch497.valid19891
  · exact MergedCutProfiles.Batch497.valid19892
theorem numericValid3245 : retention3245.NumericValid := by decide +kernel
def certificate3245 : RatCutBinCertificate := ⟨⟨retention3245,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(2771444155754327/1250000000000000)⟩,(124808007605054243/125000000000000000),(403930460659556767/1000000000000000000),(22990031740314173/100000000000000000),(120621853033077409/1000000000000000000)⟩
theorem valid3245 : certificate3245.Valid := by decide +kernel
theorem sound3245 : certificate3245.Sound := rat_cut_bin_certificate_sound certificate3245 profilesValid3245 numericValid3245 valid3245

def retention3246 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(1012066857155932207/87180495143465975733),(402520135569018097/500000000000000000),(67/20),(1451024999864212907393/640000000000000000000),true,MergedCutProfiles.Batch497.profile19893,![MergedCutProfiles.Batch497.profile19893,MergedCutProfiles.Batch497.profile19894,MergedCutProfiles.Batch497.profile19895,MergedCutProfiles.Batch497.profile19881,MergedCutProfiles.Batch497.profile19896,MergedCutProfiles.Batch497.profile19897,MergedCutProfiles.Batch497.profile19898,MergedCutProfiles.Batch497.profile19899,MergedCutProfiles.Batch497.profile19900,MergedCutProfiles.Batch497.profile19901,MergedCutProfiles.Batch497.profile19902,MergedCutProfiles.Batch497.profile19903,MergedCutProfiles.Batch497.profile19904,MergedCutProfiles.Batch497.profile19905,MergedCutProfiles.Batch497.profile19906,MergedCutProfiles.Batch497.profile19907]⟩
theorem profilesValid3246 : retention3246.ProfilesValid := by
  change ∀ j : Fin 16, (retention3246.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch497.valid19893
  · exact MergedCutProfiles.Batch497.valid19894
  · exact MergedCutProfiles.Batch497.valid19895
  · exact MergedCutProfiles.Batch497.valid19881
  · exact MergedCutProfiles.Batch497.valid19896
  · exact MergedCutProfiles.Batch497.valid19897
  · exact MergedCutProfiles.Batch497.valid19898
  · exact MergedCutProfiles.Batch497.valid19899
  · exact MergedCutProfiles.Batch497.valid19900
  · exact MergedCutProfiles.Batch497.valid19901
  · exact MergedCutProfiles.Batch497.valid19902
  · exact MergedCutProfiles.Batch497.valid19903
  · exact MergedCutProfiles.Batch497.valid19904
  · exact MergedCutProfiles.Batch497.valid19905
  · exact MergedCutProfiles.Batch497.valid19906
  · exact MergedCutProfiles.Batch497.valid19907
theorem numericValid3246 : retention3246.NumericValid := by decide +kernel
def certificate3246 : RatCutBinCertificate := ⟨⟨retention3246,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(2199708659629408503/1000000000000000000)⟩,(124808007605054243/125000000000000000),(405044197655532689/1000000000000000000),(228892274689248799/1000000000000000000),(1508111453640251/12500000000000000)⟩
theorem valid3246 : certificate3246.Valid := by decide +kernel
theorem sound3246 : certificate3246.Sound := rat_cut_bin_certificate_sound certificate3246 profilesValid3246 numericValid3246 valid3246

def retention3247 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(366000007000000000/29060165047821991911),(1012066857155932207/1000000000000000000),(11/4),(4489325806643307133/2000000000000000000),true,MergedCutProfiles.Batch497.profile19908,![MergedCutProfiles.Batch497.profile19908,MergedCutProfiles.Batch497.profile19909,MergedCutProfiles.Batch497.profile19910,MergedCutProfiles.Batch497.profile19911,MergedCutProfiles.Batch497.profile19912,MergedCutProfiles.Batch497.profile19913,MergedCutProfiles.Batch497.profile19914,MergedCutProfiles.Batch497.profile19915,MergedCutProfiles.Batch497.profile19916,MergedCutProfiles.Batch497.profile19917,MergedCutProfiles.Batch497.profile19891,MergedCutProfiles.Batch497.profile19918,MergedCutProfiles.Batch497.profile19919,MergedCutProfiles.Batch498.profile19920,MergedCutProfiles.Batch498.profile19921,MergedCutProfiles.Batch498.profile19922]⟩
theorem profilesValid3247 : retention3247.ProfilesValid := by
  change ∀ j : Fin 16, (retention3247.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch497.valid19908
  · exact MergedCutProfiles.Batch497.valid19909
  · exact MergedCutProfiles.Batch497.valid19910
  · exact MergedCutProfiles.Batch497.valid19911
  · exact MergedCutProfiles.Batch497.valid19912
  · exact MergedCutProfiles.Batch497.valid19913
  · exact MergedCutProfiles.Batch497.valid19914
  · exact MergedCutProfiles.Batch497.valid19915
  · exact MergedCutProfiles.Batch497.valid19916
  · exact MergedCutProfiles.Batch497.valid19917
  · exact MergedCutProfiles.Batch497.valid19891
  · exact MergedCutProfiles.Batch497.valid19918
  · exact MergedCutProfiles.Batch497.valid19919
  · exact MergedCutProfiles.Batch498.valid19920
  · exact MergedCutProfiles.Batch498.valid19921
  · exact MergedCutProfiles.Batch498.valid19922
theorem numericValid3247 : retention3247.NumericValid := by decide +kernel
def certificate3247 : RatCutBinCertificate := ⟨⟨retention3247,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(2189237829166885617/1000000000000000000)⟩,(124808007605054243/125000000000000000),(364024777269259477/1000000000000000000),(53622431018901283/200000000000000000),(165669125495464887/1000000000000000000)⟩
theorem valid3247 : certificate3247.Valid := by decide +kernel
theorem sound3247 : certificate3247.Sound := rat_cut_bin_certificate_sound certificate3247 profilesValid3247 numericValid3247 valid3247

def retention3248 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(1310885987900436787/87180495143465975733),(1098000021/1000000000),(13/5),(35725935387465879179/16000000000000000000),true,MergedCutProfiles.Batch498.profile19923,![MergedCutProfiles.Batch498.profile19923,MergedCutProfiles.Batch498.profile19924,MergedCutProfiles.Batch498.profile19925,MergedCutProfiles.Batch498.profile19926,MergedCutProfiles.Batch497.profile19913,MergedCutProfiles.Batch498.profile19927,MergedCutProfiles.Batch498.profile19928,MergedCutProfiles.Batch497.profile19889,MergedCutProfiles.Batch498.profile19929,MergedCutProfiles.Batch497.profile19904,MergedCutProfiles.Batch498.profile19930,MergedCutProfiles.Batch498.profile19931,MergedCutProfiles.Batch498.profile19932,MergedCutProfiles.Batch498.profile19933,MergedCutProfiles.Batch498.profile19934,MergedCutProfiles.Batch498.profile19935]⟩
theorem profilesValid3248 : retention3248.ProfilesValid := by
  change ∀ j : Fin 16, (retention3248.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch498.valid19923
  · exact MergedCutProfiles.Batch498.valid19924
  · exact MergedCutProfiles.Batch498.valid19925
  · exact MergedCutProfiles.Batch498.valid19926
  · exact MergedCutProfiles.Batch497.valid19913
  · exact MergedCutProfiles.Batch498.valid19927
  · exact MergedCutProfiles.Batch498.valid19928
  · exact MergedCutProfiles.Batch497.valid19889
  · exact MergedCutProfiles.Batch498.valid19929
  · exact MergedCutProfiles.Batch497.valid19904
  · exact MergedCutProfiles.Batch498.valid19930
  · exact MergedCutProfiles.Batch498.valid19931
  · exact MergedCutProfiles.Batch498.valid19932
  · exact MergedCutProfiles.Batch498.valid19933
  · exact MergedCutProfiles.Batch498.valid19934
  · exact MergedCutProfiles.Batch498.valid19935
theorem numericValid3248 : retention3248.NumericValid := by decide +kernel
def certificate3248 : RatCutBinCertificate := ⟨⟨retention3248,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(545117281293521201/250000000000000000)⟩,(124808007605054243/125000000000000000),(176181477403475869/500000000000000000),(140042048905147777/500000000000000000),(181230146242222657/1000000000000000000)⟩
theorem valid3248 : certificate3248.Valid := by decide +kernel
theorem sound3248 : certificate3248.Sound := rat_cut_bin_certificate_sound certificate3248 profilesValid3248 numericValid3248 valid3248

def retention3249 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(5831375242661275940/87180495143465975733),(1310885987900436787/1000000000000000000),(9/4),(515489096099815013487/256000000000000000000),true,MergedCutProfiles.Batch498.profile19936,![MergedCutProfiles.Batch498.profile19936,MergedCutProfiles.Batch498.profile19937,MergedCutProfiles.Batch498.profile19922,MergedCutProfiles.Batch498.profile19938,MergedCutProfiles.Batch498.profile19939,MergedCutProfiles.Batch498.profile19940,MergedCutProfiles.Batch498.profile19941,MergedCutProfiles.Batch498.profile19942,MergedCutProfiles.Batch498.profile19943,MergedCutProfiles.Batch498.profile19944,MergedCutProfiles.Batch498.profile19945,MergedCutProfiles.Batch498.profile19946,MergedCutProfiles.Batch498.profile19947,MergedCutProfiles.Batch498.profile19948,MergedCutProfiles.Batch498.profile19949,MergedCutProfiles.Batch498.profile19950]⟩
theorem profilesValid3249 : retention3249.ProfilesValid := by
  change ∀ j : Fin 16, (retention3249.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch498.valid19936
  · exact MergedCutProfiles.Batch498.valid19937
  · exact MergedCutProfiles.Batch498.valid19922
  · exact MergedCutProfiles.Batch498.valid19938
  · exact MergedCutProfiles.Batch498.valid19939
  · exact MergedCutProfiles.Batch498.valid19940
  · exact MergedCutProfiles.Batch498.valid19941
  · exact MergedCutProfiles.Batch498.valid19942
  · exact MergedCutProfiles.Batch498.valid19943
  · exact MergedCutProfiles.Batch498.valid19944
  · exact MergedCutProfiles.Batch498.valid19945
  · exact MergedCutProfiles.Batch498.valid19946
  · exact MergedCutProfiles.Batch498.valid19947
  · exact MergedCutProfiles.Batch498.valid19948
  · exact MergedCutProfiles.Batch498.valid19949
  · exact MergedCutProfiles.Batch498.valid19950
theorem numericValid3249 : retention3249.NumericValid := by decide +kernel
def certificate3249 : RatCutBinCertificate := ⟨⟨retention3249,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(1968281594352924213/1000000000000000000)⟩,(124808007605054243/125000000000000000),(90634467233527497/250000000000000000),(26961759601960797/100000000000000000),(90791439965777243/500000000000000000)⟩
theorem valid3249 : certificate3249.Valid := by decide +kernel
theorem sound3249 : certificate3249.Sound := rat_cut_bin_certificate_sound certificate3249 profilesValid3249 numericValid3249 valid3249

def retention3250 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(36023208430092171593/87180495143465975733),(291568762133063797/50000000000000000),(11/10),(1694814470065063045848764947634506189/1457843810665318985000000000000000000),false,MergedCutProfiles.Batch498.profile19951,(fun _ => MergedCutProfiles.Batch498.profile19951)⟩
theorem profilesValid3250 : retention3250.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19951
theorem numericValid3250 : retention3250.NumericValid := by decide +kernel
def certificate3250 : RatCutBinCertificate := ⟨⟨retention3250,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(1140379194023830421/1000000000000000000)⟩,(124808007605054243/125000000000000000),(17352571354798283/40000000000000000),(203890125435169979/1000000000000000000),(11353930235421/62500000000000)⟩
theorem valid3250 : certificate3250.Valid := by decide +kernel
theorem sound3250 : certificate3250.Sound := rat_cut_bin_certificate_sound certificate3250 profilesValid3250 numericValid3250 valid3250

def retention3251 : RatCutRetentionCertificate := ⟨(103/2000),(13/250),(43089069829789336481/87180495143465975733),(36023208430092171593/1000000000000000000),1,(144951886381028230286139067935802114971/144092833720368686372000000000000000000),false,MergedCutProfiles.Batch498.profile19952,(fun _ => MergedCutProfiles.Batch498.profile19952)⟩
theorem profilesValid3251 : retention3251.ProfilesValid := by
  exact MergedCutProfiles.Batch498.valid19952
theorem numericValid3251 : retention3251.NumericValid := by decide +kernel
def certificate3251 : RatCutBinCertificate := ⟨⟨retention3251,(52594324540364433/25000000000000000),(65444215677591123/500000000000000000),(3415730931803916221/250000000000000000),(597297544153012880923/500000000000000000),(985807959718097201/1000000000000000000)⟩,(124808007605054243/125000000000000000),(447875302383525449/1000000000000000000),(96186424485201293/500000000000000000),(184302938122789057/1000000000000000000)⟩
theorem valid3251 : certificate3251.Valid := by decide +kernel
theorem sound3251 : certificate3251.Sound := rat_cut_bin_certificate_sound certificate3251 profilesValid3251 numericValid3251 valid3251

def certificates : List RatCutBinCertificate := [certificate3240,certificate3241,certificate3242,certificate3243,certificate3244,certificate3245,certificate3246,certificate3247,certificate3248,certificate3249,certificate3250,certificate3251]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3240,List.forall_mem_cons.mpr ⟨sound3241,List.forall_mem_cons.mpr ⟨sound3242,List.forall_mem_cons.mpr ⟨sound3243,List.forall_mem_cons.mpr ⟨sound3244,List.forall_mem_cons.mpr ⟨sound3245,List.forall_mem_cons.mpr ⟨sound3246,List.forall_mem_cons.mpr ⟨sound3247,List.forall_mem_cons.mpr ⟨sound3248,List.forall_mem_cons.mpr ⟨sound3249,List.forall_mem_cons.mpr ⟨sound3250,List.forall_mem_cons.mpr ⟨sound3251,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch270
