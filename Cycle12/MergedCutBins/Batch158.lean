import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch302
import Cycle12.MergedCutProfiles.Batch303

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch158

def retention1896 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(1/2),(4784923963924330563/1000000000000000000),(11/10),(1889760750828049114831257340148492257391/1913969585569732225200000000000000000000),false,MergedCutProfiles.Batch302.profile12089,(fun _ => MergedCutProfiles.Batch302.profile12089)⟩
theorem profilesValid1896 : retention1896.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12089
theorem numericValid1896 : retention1896.NumericValid := by decide +kernel
def certificate1896 : RatCutBinCertificate := ⟨⟨retention1896,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(238093514721141011/250000000000000000)⟩,(989315767820691727/1000000000000000000),(415443786855600303/1000000000000000000),(219626244589704773/1000000000000000000),(161357180937385891/1000000000000000000)⟩
theorem valid1896 : certificate1896.Valid := by decide +kernel
theorem sound1896 : certificate1896.Sound := rat_cut_bin_certificate_sound certificate1896 profilesValid1896 numericValid1896 valid1896

def retention1897 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(1/2),64,1,(63854862172039494045293658505381868631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch302.profile12089,(fun _ => MergedCutProfiles.Batch302.profile12089)⟩
theorem profilesValid1897 : retention1897.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12089
theorem numericValid1897 : retention1897.NumericValid := by decide +kernel
def certificate1897 : RatCutBinCertificate := ⟨⟨retention1897,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(965942104183187387/1000000000000000000)⟩,(989315767820691727/1000000000000000000),(9296232281686067/25000000000000000),(16268094282359227/62500000000000000),(30626608004563881/125000000000000000)⟩
theorem valid1897 : certificate1897.Valid := by decide +kernel
theorem sound1897 : certificate1897.Sound := rat_cut_bin_certificate_sound certificate1897 profilesValid1897 numericValid1897 valid1897

def retention1898 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(4445001347524845429/9627882220611476356),(1420299980490139253/500000000000000000),(5/4),(48491840899429250978654447464367364631/45449599375684456096000000000000000000),false,MergedCutProfiles.Batch302.profile12090,(fun _ => MergedCutProfiles.Batch302.profile12090)⟩
theorem profilesValid1898 : retention1898.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12090
theorem numericValid1898 : retention1898.NumericValid := by decide +kernel
def certificate1898 : RatCutBinCertificate := ⟨⟨retention1898,(272732560436646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(1022110639469787453/1000000000000000000)⟩,(9879469828883821/10000000000000000),(370938523867644657/1000000000000000000),(52238306641770357/200000000000000000),(21402763910247091/125000000000000000)⟩
theorem valid1898 : certificate1898.Valid := by decide +kernel
theorem sound1898 : certificate1898.Sound := rat_cut_bin_certificate_sound certificate1898 profilesValid1898 numericValid1898 valid1898

def retention1899 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(4765643084844684081/9627882220611476356),(4445001347524845429/1000000000000000000),(11/10),(252378007541997599417535737045870735057/254000077001419738800000000000000000000),false,MergedCutProfiles.Batch302.profile12091,(fun _ => MergedCutProfiles.Batch302.profile12091)⟩
theorem profilesValid1899 : retention1899.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12091
theorem numericValid1899 : retention1899.NumericValid := by decide +kernel
def certificate1899 : RatCutBinCertificate := ⟨⟨retention1899,(272732560436646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(119271400819673377/125000000000000000)⟩,(9879469828883821/10000000000000000),(198675148248426289/500000000000000000),(235918945324864351/1000000000000000000),(85749448260966343/500000000000000000)⟩
theorem valid1899 : certificate1899.Valid := by decide +kernel
theorem sound1899 : certificate1899.Sound := rat_cut_bin_certificate_sound certificate1899 profilesValid1899 numericValid1899 valid1899

def retention1900 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(2406649757846565461/4813941110305738178),(4765643084844684081/1000000000000000000),(11/10),(1882074015655510394763812389052651801399/1906257233937873632400000000000000000000),false,MergedCutProfiles.Batch302.profile12092,(fun _ => MergedCutProfiles.Batch302.profile12092)⟩
theorem profilesValid1900 : retention1900.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12092
theorem numericValid1900 : retention1900.NumericValid := by decide +kernel
def certificate1900 : RatCutBinCertificate := ⟨⟨retention1900,(272732560436646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(473935907349392579/500000000000000000)⟩,(9879469828883821/10000000000000000),(12499719303910457/31250000000000000),(116745296596000179/500000000000000000),(34102366216076867/200000000000000000)⟩
theorem valid1900 : certificate1900.Valid := by decide +kernel
theorem sound1900 : certificate1900.Sound := rat_cut_bin_certificate_sound certificate1900 profilesValid1900 numericValid1900 valid1900

def retention1901 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(1/2),(2406649757846565461/500000000000000000),(11/10),(475356452107390153221056223288114556639/481329951569313092200000000000000000000),false,MergedCutProfiles.Batch302.profile12089,(fun _ => MergedCutProfiles.Batch302.profile12089)⟩
theorem profilesValid1901 : retention1901.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12089
theorem numericValid1901 : retention1901.NumericValid := by decide +kernel
def certificate1901 : RatCutBinCertificate := ⟨⟨retention1901,(272732560436646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(948147741953649543/1000000000000000000)⟩,(9879469828883821/10000000000000000),(199937306739307547/500000000000000000),(233597268128546221/1000000000000000000),(17087299463931111/100000000000000000)⟩
theorem valid1901 : certificate1901.Valid := by decide +kernel
theorem sound1901 : certificate1901.Sound := rat_cut_bin_certificate_sound certificate1901 profilesValid1901 numericValid1901 valid1901

def retention1902 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(674805647185989101/4792150356305589724),(36621414749100103/40000000000000000),(12/5),(114198057731705426223/64000000000000000000),true,MergedCutProfiles.Batch302.profile12093,![MergedCutProfiles.Batch302.profile12093,MergedCutProfiles.Batch302.profile12094,MergedCutProfiles.Batch302.profile12095,MergedCutProfiles.Batch302.profile12096,MergedCutProfiles.Batch302.profile12097,MergedCutProfiles.Batch302.profile12098,MergedCutProfiles.Batch302.profile12099,MergedCutProfiles.Batch302.profile12100,MergedCutProfiles.Batch302.profile12101,MergedCutProfiles.Batch302.profile12102,MergedCutProfiles.Batch302.profile12103,MergedCutProfiles.Batch302.profile12104,MergedCutProfiles.Batch302.profile12105,MergedCutProfiles.Batch302.profile12106,MergedCutProfiles.Batch302.profile12107,MergedCutProfiles.Batch302.profile12108]⟩
theorem profilesValid1902 : retention1902.ProfilesValid := by
  change ∀ j : Fin 16, (retention1902.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch302.valid12093
  · exact MergedCutProfiles.Batch302.valid12094
  · exact MergedCutProfiles.Batch302.valid12095
  · exact MergedCutProfiles.Batch302.valid12096
  · exact MergedCutProfiles.Batch302.valid12097
  · exact MergedCutProfiles.Batch302.valid12098
  · exact MergedCutProfiles.Batch302.valid12099
  · exact MergedCutProfiles.Batch302.valid12100
  · exact MergedCutProfiles.Batch302.valid12101
  · exact MergedCutProfiles.Batch302.valid12102
  · exact MergedCutProfiles.Batch302.valid12103
  · exact MergedCutProfiles.Batch302.valid12104
  · exact MergedCutProfiles.Batch302.valid12105
  · exact MergedCutProfiles.Batch302.valid12106
  · exact MergedCutProfiles.Batch302.valid12107
  · exact MergedCutProfiles.Batch302.valid12108
theorem numericValid1902 : retention1902.NumericValid := by decide +kernel
def certificate1902 : RatCutBinCertificate := ⟨⟨retention1902,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(1707773731468665891/1000000000000000000)⟩,(989299106743340583/1000000000000000000),(164494581511235603/500000000000000000),(76313274562453127/250000000000000000),(80959152585918157/500000000000000000)⟩
theorem valid1902 : certificate1902.Valid := by decide +kernel
theorem sound1902 : certificate1902.Sound := rat_cut_bin_certificate_sound certificate1902 profilesValid1902 numericValid1902 valid1902

def retention1903 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(1327492651268681891/4792150356305589724),(674805647185989101/500000000000000000),(7/4),(185520835465463409833/128000000000000000000),true,MergedCutProfiles.Batch302.profile12109,![MergedCutProfiles.Batch302.profile12109,MergedCutProfiles.Batch302.profile12110,MergedCutProfiles.Batch302.profile12111,MergedCutProfiles.Batch302.profile12112,MergedCutProfiles.Batch302.profile12113,MergedCutProfiles.Batch302.profile12114,MergedCutProfiles.Batch302.profile12115,MergedCutProfiles.Batch302.profile12116,MergedCutProfiles.Batch302.profile12117,MergedCutProfiles.Batch302.profile12118,MergedCutProfiles.Batch302.profile12119,MergedCutProfiles.Batch303.profile12120,MergedCutProfiles.Batch303.profile12121,MergedCutProfiles.Batch303.profile12122,MergedCutProfiles.Batch303.profile12123,MergedCutProfiles.Batch303.profile12124]⟩
theorem profilesValid1903 : retention1903.ProfilesValid := by
  change ∀ j : Fin 16, (retention1903.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch302.valid12109
  · exact MergedCutProfiles.Batch302.valid12110
  · exact MergedCutProfiles.Batch302.valid12111
  · exact MergedCutProfiles.Batch302.valid12112
  · exact MergedCutProfiles.Batch302.valid12113
  · exact MergedCutProfiles.Batch302.valid12114
  · exact MergedCutProfiles.Batch302.valid12115
  · exact MergedCutProfiles.Batch302.valid12116
  · exact MergedCutProfiles.Batch302.valid12117
  · exact MergedCutProfiles.Batch302.valid12118
  · exact MergedCutProfiles.Batch302.valid12119
  · exact MergedCutProfiles.Batch303.valid12120
  · exact MergedCutProfiles.Batch303.valid12121
  · exact MergedCutProfiles.Batch303.valid12122
  · exact MergedCutProfiles.Batch303.valid12123
  · exact MergedCutProfiles.Batch303.valid12124
theorem numericValid1903 : retention1903.NumericValid := by decide +kernel
def certificate1903 : RatCutBinCertificate := ⟨⟨retention1903,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(1393550993435707437/1000000000000000000)⟩,(989299106743340583/1000000000000000000),(35545021056285187/100000000000000000),(276877744079969653/1000000000000000000),(162752078288266451/1000000000000000000)⟩
theorem valid1903 : certificate1903.Valid := by decide +kernel
theorem sound1903 : certificate1903.Sound := rat_cut_bin_certificate_sound certificate1903 profilesValid1903 numericValid1903 valid1903

def retention1904 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(4154549535149830049/9584300712611179448),(1327492651268681891/500000000000000000),(23/20),(703961394137565185947/640000000000000000000),true,MergedCutProfiles.Batch303.profile12125,![MergedCutProfiles.Batch303.profile12125,MergedCutProfiles.Batch303.profile12126,MergedCutProfiles.Batch303.profile12127,MergedCutProfiles.Batch303.profile12128,MergedCutProfiles.Batch303.profile12129,MergedCutProfiles.Batch303.profile12130,MergedCutProfiles.Batch303.profile12131,MergedCutProfiles.Batch303.profile12132,MergedCutProfiles.Batch303.profile12133,MergedCutProfiles.Batch303.profile12134,MergedCutProfiles.Batch303.profile12135,MergedCutProfiles.Batch303.profile12136,MergedCutProfiles.Batch303.profile12137,MergedCutProfiles.Batch303.profile12138,MergedCutProfiles.Batch303.profile12139,MergedCutProfiles.Batch303.profile12140]⟩
theorem profilesValid1904 : retention1904.ProfilesValid := by
  change ∀ j : Fin 16, (retention1904.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch303.valid12125
  · exact MergedCutProfiles.Batch303.valid12126
  · exact MergedCutProfiles.Batch303.valid12127
  · exact MergedCutProfiles.Batch303.valid12128
  · exact MergedCutProfiles.Batch303.valid12129
  · exact MergedCutProfiles.Batch303.valid12130
  · exact MergedCutProfiles.Batch303.valid12131
  · exact MergedCutProfiles.Batch303.valid12132
  · exact MergedCutProfiles.Batch303.valid12133
  · exact MergedCutProfiles.Batch303.valid12134
  · exact MergedCutProfiles.Batch303.valid12135
  · exact MergedCutProfiles.Batch303.valid12136
  · exact MergedCutProfiles.Batch303.valid12137
  · exact MergedCutProfiles.Batch303.valid12138
  · exact MergedCutProfiles.Batch303.valid12139
  · exact MergedCutProfiles.Batch303.valid12140
theorem numericValid1904 : retention1904.NumericValid := by decide +kernel
def certificate1904 : RatCutBinCertificate := ⟨⟨retention1904,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(265813967427037581/250000000000000000)⟩,(989299106743340583/1000000000000000000),(401009628320381913/1000000000000000000),(2906982045537581/12500000000000000),(10186156346577969/62500000000000000)⟩
theorem valid1904 : certificate1904.Valid := by decide +kernel
theorem sound1904 : certificate1904.Sound := rat_cut_bin_certificate_sound certificate1904 profilesValid1904 numericValid1904 valid1904

def retention1905 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(579387426377471293/1198037589076397431),(4154549535149830049/1000000000000000000),1,(252196230958102915889/256000000000000000000),true,MergedCutProfiles.Batch303.profile12141,![MergedCutProfiles.Batch303.profile12141,MergedCutProfiles.Batch303.profile12142,MergedCutProfiles.Batch303.profile12143,MergedCutProfiles.Batch302.profile12115,MergedCutProfiles.Batch303.profile12144,MergedCutProfiles.Batch303.profile12145,MergedCutProfiles.Batch303.profile12146,MergedCutProfiles.Batch303.profile12147,MergedCutProfiles.Batch303.profile12148,MergedCutProfiles.Batch303.profile12149,MergedCutProfiles.Batch303.profile12150,MergedCutProfiles.Batch303.profile12151,MergedCutProfiles.Batch303.profile12152,MergedCutProfiles.Batch303.profile12153,MergedCutProfiles.Batch303.profile12154,MergedCutProfiles.Batch303.profile12155]⟩
theorem profilesValid1905 : retention1905.ProfilesValid := by
  change ∀ j : Fin 16, (retention1905.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch303.valid12141
  · exact MergedCutProfiles.Batch303.valid12142
  · exact MergedCutProfiles.Batch303.valid12143
  · exact MergedCutProfiles.Batch302.valid12115
  · exact MergedCutProfiles.Batch303.valid12144
  · exact MergedCutProfiles.Batch303.valid12145
  · exact MergedCutProfiles.Batch303.valid12146
  · exact MergedCutProfiles.Batch303.valid12147
  · exact MergedCutProfiles.Batch303.valid12148
  · exact MergedCutProfiles.Batch303.valid12149
  · exact MergedCutProfiles.Batch303.valid12150
  · exact MergedCutProfiles.Batch303.valid12151
  · exact MergedCutProfiles.Batch303.valid12152
  · exact MergedCutProfiles.Batch303.valid12153
  · exact MergedCutProfiles.Batch303.valid12154
  · exact MergedCutProfiles.Batch303.valid12155
theorem numericValid1905 : retention1905.NumericValid := by decide +kernel
def certificate1905 : RatCutBinCertificate := ⟨⟨retention1905,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(119155795570540287/125000000000000000)⟩,(989299106743340583/1000000000000000000),(105072719482262613/250000000000000000),(215396805167458391/1000000000000000000),(82493556948272869/500000000000000000)⟩
theorem valid1905 : certificate1905.Valid := by decide +kernel
theorem sound1905 : certificate1905.Sound := rat_cut_bin_certificate_sound certificate1905 profilesValid1905 numericValid1905 valid1905

def retention1906 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(4728264909181267729/9584300712611179448),(579387426377471293/125000000000000000),(11/10),(115716878268179447735239861090318885199/115877485275494258600000000000000000000),false,MergedCutProfiles.Batch303.profile12156,(fun _ => MergedCutProfiles.Batch303.profile12156)⟩
theorem profilesValid1906 : retention1906.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12156
theorem numericValid1906 : retention1906.NumericValid := by decide +kernel
def certificate1906 : RatCutBinCertificate := ⟨⟨retention1906,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(963531460620556551/1000000000000000000)⟩,(989299106743340583/1000000000000000000),(102725456251712133/250000000000000000),(111820366552927443/500000000000000000),(165186621371327421/1000000000000000000)⟩
theorem valid1906 : certificate1906.Valid := by decide +kernel
theorem sound1906 : certificate1906.Sound := rat_cut_bin_certificate_sound certificate1906 profilesValid1906 numericValid1906 valid1906

def retention1907 : RatCutRetentionCertificate := ⟨(107/1600),(67/1000),(280914562251357671/563782394859481144),(4728264909181267729/1000000000000000000),(11/10),(1872662055509659452765525603642589450639/1891305963672507091600000000000000000000),false,MergedCutProfiles.Batch303.profile12157,(fun _ => MergedCutProfiles.Batch303.profile12157)⟩
theorem profilesValid1907 : retention1907.ProfilesValid := by
  exact MergedCutProfiles.Batch303.valid12157
theorem numericValid1907 : retention1907.NumericValid := by decide +kernel
def certificate1907 : RatCutBinCertificate := ⟨⟨retention1907,(1210339299435513181/500000000000000000),(11895173549139047/50000000000000000),(18061616308736539321/1000000000000000000),(4331171436219614029/25000000000000000),(238764990903747059/250000000000000000)⟩,(989299106743340583/1000000000000000000),(206851997691628113/500000000000000000),(221158092991529027/1000000000000000000),(162594876174521129/1000000000000000000)⟩
theorem valid1907 : certificate1907.Valid := by decide +kernel
theorem sound1907 : certificate1907.Sound := rat_cut_bin_certificate_sound certificate1907 profilesValid1907 numericValid1907 valid1907

def certificates : List RatCutBinCertificate := [certificate1896,certificate1897,certificate1898,certificate1899,certificate1900,certificate1901,certificate1902,certificate1903,certificate1904,certificate1905,certificate1906,certificate1907]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1896,List.forall_mem_cons.mpr ⟨sound1897,List.forall_mem_cons.mpr ⟨sound1898,List.forall_mem_cons.mpr ⟨sound1899,List.forall_mem_cons.mpr ⟨sound1900,List.forall_mem_cons.mpr ⟨sound1901,List.forall_mem_cons.mpr ⟨sound1902,List.forall_mem_cons.mpr ⟨sound1903,List.forall_mem_cons.mpr ⟨sound1904,List.forall_mem_cons.mpr ⟨sound1905,List.forall_mem_cons.mpr ⟨sound1906,List.forall_mem_cons.mpr ⟨sound1907,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch158
