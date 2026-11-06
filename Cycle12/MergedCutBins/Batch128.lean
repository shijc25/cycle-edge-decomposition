import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch247
import Cycle12.MergedCutProfiles.Batch248
import Cycle12.MergedCutProfiles.Batch249

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch128

def retention1536 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(1360112531024015483/11224248051368933810),(904479060065044863/1000000000000000000),(51/20),(2358544906848669692127/1280000000000000000000),true,MergedCutProfiles.Batch247.profile9905,![MergedCutProfiles.Batch247.profile9905,MergedCutProfiles.Batch247.profile9906,MergedCutProfiles.Batch247.profile9907,MergedCutProfiles.Batch247.profile9908,MergedCutProfiles.Batch247.profile9909,MergedCutProfiles.Batch247.profile9910,MergedCutProfiles.Batch247.profile9911,MergedCutProfiles.Batch247.profile9912,MergedCutProfiles.Batch247.profile9913,MergedCutProfiles.Batch247.profile9914,MergedCutProfiles.Batch247.profile9915,MergedCutProfiles.Batch247.profile9916,MergedCutProfiles.Batch247.profile9917,MergedCutProfiles.Batch247.profile9918,MergedCutProfiles.Batch247.profile9919,MergedCutProfiles.Batch248.profile9920]⟩
theorem profilesValid1536 : retention1536.ProfilesValid := by
  change ∀ j : Fin 16, (retention1536.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch247.valid9905
  · exact MergedCutProfiles.Batch247.valid9906
  · exact MergedCutProfiles.Batch247.valid9907
  · exact MergedCutProfiles.Batch247.valid9908
  · exact MergedCutProfiles.Batch247.valid9909
  · exact MergedCutProfiles.Batch247.valid9910
  · exact MergedCutProfiles.Batch247.valid9911
  · exact MergedCutProfiles.Batch247.valid9912
  · exact MergedCutProfiles.Batch247.valid9913
  · exact MergedCutProfiles.Batch247.valid9914
  · exact MergedCutProfiles.Batch247.valid9915
  · exact MergedCutProfiles.Batch247.valid9916
  · exact MergedCutProfiles.Batch247.valid9917
  · exact MergedCutProfiles.Batch247.valid9918
  · exact MergedCutProfiles.Batch247.valid9919
  · exact MergedCutProfiles.Batch248.valid9920
theorem numericValid1536 : retention1536.NumericValid := by decide +kernel
def certificate1536 : RatCutBinCertificate := ⟨⟨retention1536,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(1769642477672642363/1000000000000000000)⟩,(989962010643109923/1000000000000000000),(85862977817788923/250000000000000000),(72372808040100173/250000000000000000),(152553162233702143/1000000000000000000)⟩
theorem valid1536 : certificate1536.Valid := by decide +kernel
theorem sound1536 : certificate1536.Sound := rat_cut_bin_certificate_sound certificate1536 profilesValid1536 numericValid1536 valid1536

def retention1537 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(602996428923506161/2244849610273786762),(1360112531024015483/1000000000000000000),(7/4),(375346811270227216559/256000000000000000000),true,MergedCutProfiles.Batch248.profile9921,![MergedCutProfiles.Batch248.profile9921,MergedCutProfiles.Batch248.profile9922,MergedCutProfiles.Batch248.profile9923,MergedCutProfiles.Batch248.profile9924,MergedCutProfiles.Batch248.profile9925,MergedCutProfiles.Batch248.profile9926,MergedCutProfiles.Batch248.profile9927,MergedCutProfiles.Batch248.profile9928,MergedCutProfiles.Batch248.profile9929,MergedCutProfiles.Batch248.profile9930,MergedCutProfiles.Batch248.profile9931,MergedCutProfiles.Batch248.profile9932,MergedCutProfiles.Batch248.profile9933,MergedCutProfiles.Batch248.profile9934,MergedCutProfiles.Batch248.profile9935,MergedCutProfiles.Batch248.profile9936]⟩
theorem profilesValid1537 : retention1537.ProfilesValid := by
  change ∀ j : Fin 16, (retention1537.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch248.valid9921
  · exact MergedCutProfiles.Batch248.valid9922
  · exact MergedCutProfiles.Batch248.valid9923
  · exact MergedCutProfiles.Batch248.valid9924
  · exact MergedCutProfiles.Batch248.valid9925
  · exact MergedCutProfiles.Batch248.valid9926
  · exact MergedCutProfiles.Batch248.valid9927
  · exact MergedCutProfiles.Batch248.valid9928
  · exact MergedCutProfiles.Batch248.valid9929
  · exact MergedCutProfiles.Batch248.valid9930
  · exact MergedCutProfiles.Batch248.valid9931
  · exact MergedCutProfiles.Batch248.valid9932
  · exact MergedCutProfiles.Batch248.valid9933
  · exact MergedCutProfiles.Batch248.valid9934
  · exact MergedCutProfiles.Batch248.valid9935
  · exact MergedCutProfiles.Batch248.valid9936
theorem numericValid1537 : retention1537.NumericValid := by decide +kernel
def certificate1537 : RatCutBinCertificate := ⟨⟨retention1537,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(354030314735198297/250000000000000000)⟩,(989962010643109923/1000000000000000000),(376187993261353511/1000000000000000000),(64005739687385303/250000000000000000),(30549932185583939/200000000000000000)⟩
theorem valid1537 : certificate1537.Valid := by decide +kernel
theorem sound1537 : certificate1537.Sound := rat_cut_bin_certificate_sound certificate1537 profilesValid1537 numericValid1537 valid1537

def retention1538 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(4909441165672380129/11224248051368933810),(602996428923506161/200000000000000000),(11/10),(278467407400874596813/256000000000000000000),true,MergedCutProfiles.Batch248.profile9937,![MergedCutProfiles.Batch248.profile9937,MergedCutProfiles.Batch248.profile9938,MergedCutProfiles.Batch248.profile9939,MergedCutProfiles.Batch248.profile9940,MergedCutProfiles.Batch248.profile9941,MergedCutProfiles.Batch248.profile9942,MergedCutProfiles.Batch248.profile9943,MergedCutProfiles.Batch248.profile9944,MergedCutProfiles.Batch248.profile9945,MergedCutProfiles.Batch248.profile9946,MergedCutProfiles.Batch248.profile9947,MergedCutProfiles.Batch248.profile9948,MergedCutProfiles.Batch248.profile9949,MergedCutProfiles.Batch248.profile9950,MergedCutProfiles.Batch248.profile9951,MergedCutProfiles.Batch248.profile9952]⟩
theorem profilesValid1538 : retention1538.ProfilesValid := by
  change ∀ j : Fin 16, (retention1538.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch248.valid9937
  · exact MergedCutProfiles.Batch248.valid9938
  · exact MergedCutProfiles.Batch248.valid9939
  · exact MergedCutProfiles.Batch248.valid9940
  · exact MergedCutProfiles.Batch248.valid9941
  · exact MergedCutProfiles.Batch248.valid9942
  · exact MergedCutProfiles.Batch248.valid9943
  · exact MergedCutProfiles.Batch248.valid9944
  · exact MergedCutProfiles.Batch248.valid9945
  · exact MergedCutProfiles.Batch248.valid9946
  · exact MergedCutProfiles.Batch248.valid9947
  · exact MergedCutProfiles.Batch248.valid9948
  · exact MergedCutProfiles.Batch248.valid9949
  · exact MergedCutProfiles.Batch248.valid9950
  · exact MergedCutProfiles.Batch248.valid9951
  · exact MergedCutProfiles.Batch248.valid9952
theorem numericValid1538 : retention1538.NumericValid := by decide +kernel
def certificate1538 : RatCutBinCertificate := ⟨⟨retention1538,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(1056290248236333143/1000000000000000000)⟩,(989962010643109923/1000000000000000000),(213456575691149583/500000000000000000),(13106787424962461/62500000000000000),(154358800685831741/1000000000000000000)⟩
theorem valid1538 : certificate1538.Valid := by decide +kernel
theorem sound1538 : certificate1538.Sound := rat_cut_bin_certificate_sound certificate1538 profilesValid1538 numericValid1538 valid1538

def retention1539 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(5477308108356348807/11224248051368933810),(4909441165672380129/1000000000000000000),(11/10),(24514824761019695839266850314226662639/24244153904554963600000000000000000000),false,MergedCutProfiles.Batch248.profile9953,(fun _ => MergedCutProfiles.Batch248.profile9953)⟩
theorem profilesValid1539 : retention1539.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9953
theorem numericValid1539 : retention1539.NumericValid := by decide +kernel
def certificate1539 : RatCutBinCertificate := ⟨⟨retention1539,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(489847643362719819/500000000000000000)⟩,(989962010643109923/1000000000000000000),(433815044792691807/1000000000000000000),(12743093123198323/62500000000000000),(154158707489563273/1000000000000000000)⟩
theorem valid1539 : certificate1539.Valid := by decide +kernel
theorem sound1539 : certificate1539.Sound := rat_cut_bin_certificate_sound certificate1539 profilesValid1539 numericValid1539 valid1539

def retention1540 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(5587402001334311419/11224248051368933810),(5477308108356348807/1000000000000000000),(11/10),(2183145972308298811657973331293458079231/2190923243342539522800000000000000000000),false,MergedCutProfiles.Batch248.profile9954,(fun _ => MergedCutProfiles.Batch248.profile9954)⟩
theorem profilesValid1540 : retention1540.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9954
theorem numericValid1540 : retention1540.NumericValid := by decide +kernel
def certificate1540 : RatCutBinCertificate := ⟨⟨retention1540,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(192996359413140957/200000000000000000)⟩,(989962010643109923/1000000000000000000),(21799732076900683/50000000000000000),(202074725959329617/1000000000000000000),(153043682514444681/1000000000000000000)⟩
theorem valid1540 : certificate1540.Valid := by decide +kernel
theorem sound1540 : certificate1540.Sound := rat_cut_bin_certificate_sound certificate1540 profilesValid1540 numericValid1540 valid1540

def retention1541 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(1/2),(5587402001334311419/1000000000000000000),(11/10),(2218974908445745512682091686607022970159/2234960800533724567600000000000000000000),false,MergedCutProfiles.Batch248.profile9955,(fun _ => MergedCutProfiles.Batch248.profile9955)⟩
theorem profilesValid1541 : retention1541.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9955
theorem numericValid1541 : retention1541.NumericValid := by decide +kernel
def certificate1541 : RatCutBinCertificate := ⟨⟨retention1541,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(192275805534529989/200000000000000000)⟩,(989962010643109923/1000000000000000000),(218435105107519699/500000000000000000),(6292149528652337/31250000000000000),(152379424178294443/1000000000000000000)⟩
theorem valid1541 : certificate1541.Valid := by decide +kernel
theorem sound1541 : certificate1541.Sound := rat_cut_bin_certificate_sound certificate1541 profilesValid1541 numericValid1541 valid1541

def retention1542 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(1/2),64,1,(255412391307616758291831027173117719119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch248.profile9955,(fun _ => MergedCutProfiles.Batch248.profile9955)⟩
theorem profilesValid1542 : retention1542.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9955
theorem numericValid1542 : retention1542.NumericValid := by decide +kernel
def certificate1542 : RatCutBinCertificate := ⟨⟨retention1542,(146659583869042209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(193820330517918301/200000000000000000)⟩,(989962010643109923/1000000000000000000),(399229522293478343/1000000000000000000),(58547263865082307/250000000000000000),(354082286344889/1600000000000000)⟩
theorem valid1542 : certificate1542.Valid := by decide +kernel
theorem sound1542 : certificate1542.Sound := rat_cut_bin_certificate_sound certificate1542 profilesValid1542 numericValid1542 valid1542

def retention1543 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(526143710083651372/1122424805136893381),(840586810601234109/250000000000000000),(6/5),(5532566862763660730700859862011859861/5253667566257713181250000000000000000),false,MergedCutProfiles.Batch248.profile9956,(fun _ => MergedCutProfiles.Batch248.profile9956)⟩
theorem profilesValid1543 : retention1543.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9956
theorem numericValid1543 : retention1543.NumericValid := by decide +kernel
def certificate1543 : RatCutBinCertificate := ⟨⟨retention1543,(166743234556542209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(1014052861319386961/1000000000000000000)⟩,(988583432354787483/1000000000000000000),(2427228711905071/6250000000000000),(122160837466850713/500000000000000000),(84268170037074323/500000000000000000)⟩
theorem valid1543 : certificate1543.Valid := by decide +kernel
theorem sound1543 : certificate1543.Sound := rat_cut_bin_certificate_sound certificate1543 profilesValid1543 numericValid1543 valid1543

def retention1544 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(552982327094818304/1122424805136893381),(131535927520912843/25000000000000000),(11/10),(5287276106354571346623993743606884831/5261437100836513720000000000000000000),false,MergedCutProfiles.Batch248.profile9957,(fun _ => MergedCutProfiles.Batch248.profile9957)⟩
theorem profilesValid1544 : retention1544.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9957
theorem numericValid1544 : retention1544.NumericValid := by decide +kernel
def certificate1544 : RatCutBinCertificate := ⟨⟨retention1544,(166743234556542209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(484566506091540773/500000000000000000)⟩,(988583432354787483/1000000000000000000),(81271427205707169/200000000000000000),(113853932827741229/500000000000000000),(85978743843301527/500000000000000000)⟩
theorem valid1544 : certificate1544.Valid := by decide +kernel
theorem sound1544 : certificate1544.Sound := rat_cut_bin_certificate_sound certificate1544 profilesValid1544 numericValid1544 valid1544

def retention1545 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(5585121503657664871/11224248051368933810),(1080043607607067/195312500000000),(11/10),(1378513391247153047971541106797489359/1382455817737045760000000000000000000),false,MergedCutProfiles.Batch248.profile9958,(fun _ => MergedCutProfiles.Batch248.profile9958)⟩
theorem profilesValid1545 : retention1545.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9958
theorem numericValid1545 : retention1545.NumericValid := by decide +kernel
def certificate1545 : RatCutBinCertificate := ⟨⟨retention1545,(166743234556542209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(240342641279103839/250000000000000000)⟩,(988583432354787483/1000000000000000000),(40963820773287039/100000000000000000),(112383251150727403/500000000000000000),(4241052345919537/25000000000000000)⟩
theorem valid1545 : certificate1545.Valid := by decide +kernel
theorem sound1545 : certificate1545.Sound := rat_cut_bin_certificate_sound certificate1545 profilesValid1545 numericValid1545 valid1545

def retention1546 : RatCutRetentionCertificate := ⟨(501/8000),(251/4000),(1/2),(5585121503657664871/1000000000000000000),(21/20),(8741977259709719065853261185383504560919/8936194405852263793600000000000000000000),false,MergedCutProfiles.Batch248.profile9955,(fun _ => MergedCutProfiles.Batch248.profile9955)⟩
theorem profilesValid1546 : retention1546.ProfilesValid := by
  exact MergedCutProfiles.Batch248.valid9955
theorem numericValid1546 : retention1546.NumericValid := by decide +kernel
def certificate1546 : RatCutBinCertificate := ⟨⟨retention1546,(166743234556542209/62500000000000000),(202964570941253559/1000000000000000000),(16651234186491603043/1000000000000000000),(37408637886965884507/200000000000000000),(236028646896649693/250000000000000000)⟩,(988583432354787483/1000000000000000000),(208562668366408761/500000000000000000),(218152598889493537/1000000000000000000),(83986720024724389/500000000000000000)⟩
theorem valid1546 : certificate1546.Valid := by decide +kernel
theorem sound1546 : certificate1546.Sound := rat_cut_bin_certificate_sound certificate1546 profilesValid1546 numericValid1546 valid1546

def retention1547 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1277970172024908044/11117990995896675357),(446602619053824163/500000000000000000),(51/20),(297130728813257960761/160000000000000000000),true,MergedCutProfiles.Batch248.profile9959,![MergedCutProfiles.Batch248.profile9959,MergedCutProfiles.Batch249.profile9960,MergedCutProfiles.Batch249.profile9961,MergedCutProfiles.Batch249.profile9962,MergedCutProfiles.Batch249.profile9963,MergedCutProfiles.Batch249.profile9964,MergedCutProfiles.Batch249.profile9965,MergedCutProfiles.Batch249.profile9966,MergedCutProfiles.Batch249.profile9967,MergedCutProfiles.Batch249.profile9968,MergedCutProfiles.Batch249.profile9969,MergedCutProfiles.Batch249.profile9970,MergedCutProfiles.Batch249.profile9971,MergedCutProfiles.Batch249.profile9972,MergedCutProfiles.Batch249.profile9973,MergedCutProfiles.Batch249.profile9974]⟩
theorem profilesValid1547 : retention1547.ProfilesValid := by
  change ∀ j : Fin 16, (retention1547.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch248.valid9959
  · exact MergedCutProfiles.Batch249.valid9960
  · exact MergedCutProfiles.Batch249.valid9961
  · exact MergedCutProfiles.Batch249.valid9962
  · exact MergedCutProfiles.Batch249.valid9963
  · exact MergedCutProfiles.Batch249.valid9964
  · exact MergedCutProfiles.Batch249.valid9965
  · exact MergedCutProfiles.Batch249.valid9966
  · exact MergedCutProfiles.Batch249.valid9967
  · exact MergedCutProfiles.Batch249.valid9968
  · exact MergedCutProfiles.Batch249.valid9969
  · exact MergedCutProfiles.Batch249.valid9970
  · exact MergedCutProfiles.Batch249.valid9971
  · exact MergedCutProfiles.Batch249.valid9972
  · exact MergedCutProfiles.Batch249.valid9973
  · exact MergedCutProfiles.Batch249.valid9974
theorem numericValid1547 : retention1547.NumericValid := by decide +kernel
def certificate1547 : RatCutBinCertificate := ⟨⟨retention1547,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(14267613610099663/8000000000000000)⟩,(989893539807969717/1000000000000000000),(2753183755115043/8000000000000000),(18046761847340621/62500000000000000),(152608649830195279/1000000000000000000)⟩
theorem valid1547 : certificate1547.Valid := by decide +kernel
theorem sound1547 : certificate1547.Sound := rat_cut_bin_certificate_sound certificate1547 profilesValid1547 numericValid1547 valid1547

def certificates : List RatCutBinCertificate := [certificate1536,certificate1537,certificate1538,certificate1539,certificate1540,certificate1541,certificate1542,certificate1543,certificate1544,certificate1545,certificate1546,certificate1547]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1536,List.forall_mem_cons.mpr ⟨sound1537,List.forall_mem_cons.mpr ⟨sound1538,List.forall_mem_cons.mpr ⟨sound1539,List.forall_mem_cons.mpr ⟨sound1540,List.forall_mem_cons.mpr ⟨sound1541,List.forall_mem_cons.mpr ⟨sound1542,List.forall_mem_cons.mpr ⟨sound1543,List.forall_mem_cons.mpr ⟨sound1544,List.forall_mem_cons.mpr ⟨sound1545,List.forall_mem_cons.mpr ⟨sound1546,List.forall_mem_cons.mpr ⟨sound1547,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch128
