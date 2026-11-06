import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch300
import Cycle12.MergedCutProfiles.Batch301
import Cycle12.MergedCutProfiles.Batch302

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch157

def retention1884 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(2328273089619688651/4835861345882636105),(12659446068943599/3125000000000000),1,(197716072308075123/200000000000000000),true,MergedCutProfiles.Batch300.profile12004,![MergedCutProfiles.Batch300.profile12004,MergedCutProfiles.Batch300.profile12005,MergedCutProfiles.Batch300.profile12006,MergedCutProfiles.Batch300.profile12007,MergedCutProfiles.Batch300.profile12008,MergedCutProfiles.Batch300.profile12009,MergedCutProfiles.Batch300.profile12010,MergedCutProfiles.Batch300.profile12011,MergedCutProfiles.Batch300.profile12012,MergedCutProfiles.Batch300.profile12013,MergedCutProfiles.Batch300.profile12014,MergedCutProfiles.Batch300.profile12015,MergedCutProfiles.Batch300.profile12016,MergedCutProfiles.Batch300.profile12017,MergedCutProfiles.Batch300.profile12018,MergedCutProfiles.Batch300.profile12019]⟩
theorem profilesValid1884 : retention1884.ProfilesValid := by
  change ∀ j : Fin 16, (retention1884.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch300.valid12004
  · exact MergedCutProfiles.Batch300.valid12005
  · exact MergedCutProfiles.Batch300.valid12006
  · exact MergedCutProfiles.Batch300.valid12007
  · exact MergedCutProfiles.Batch300.valid12008
  · exact MergedCutProfiles.Batch300.valid12009
  · exact MergedCutProfiles.Batch300.valid12010
  · exact MergedCutProfiles.Batch300.valid12011
  · exact MergedCutProfiles.Batch300.valid12012
  · exact MergedCutProfiles.Batch300.valid12013
  · exact MergedCutProfiles.Batch300.valid12014
  · exact MergedCutProfiles.Batch300.valid12015
  · exact MergedCutProfiles.Batch300.valid12016
  · exact MergedCutProfiles.Batch300.valid12017
  · exact MergedCutProfiles.Batch300.valid12018
  · exact MergedCutProfiles.Batch300.valid12019
theorem numericValid1884 : retention1884.NumericValid := by decide +kernel
def certificate1884 : RatCutBinCertificate := ⟨⟨retention1884,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(956851518690150593/1000000000000000000)⟩,(494662241135546001/500000000000000000),(421971483893773947/1000000000000000000),(213943434545529913/1000000000000000000),(32719195622848519/200000000000000000)⟩
theorem valid1884 : certificate1884.Valid := by decide +kernel
theorem sound1884 : certificate1884.Sound := rat_cut_bin_certificate_sound certificate1884 profilesValid1884 numericValid1884 valid1884

def retention1885 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(959528837003301935/1934344538353054442),(2328273089619688651/500000000000000000),(11/10),(57839421722619588043553553655051064813/58206827240492216275000000000000000000),false,MergedCutProfiles.Batch300.profile12020,(fun _ => MergedCutProfiles.Batch300.profile12020)⟩
theorem profilesValid1885 : retention1885.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12020
theorem numericValid1885 : retention1885.NumericValid := by decide +kernel
def certificate1885 : RatCutBinCertificate := ⟨⟨retention1885,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(59924290262540481/62500000000000000)⟩,(494662241135546001/500000000000000000),(207281975556963121/500000000000000000),(220400008510139607/1000000000000000000),(40555908897195327/250000000000000000)⟩
theorem valid1885 : certificate1885.Valid := by decide +kernel
theorem sound1885 : certificate1885.Sound := rat_cut_bin_certificate_sound certificate1885 profilesValid1885 numericValid1885 valid1885

def retention1886 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(1/2),(191905767400660387/40000000000000000),(11/10),(75799543043094508030815245443711043479/76762306960264154800000000000000000000),false,MergedCutProfiles.Batch300.profile12021,(fun _ => MergedCutProfiles.Batch300.profile12021)⟩
theorem profilesValid1886 : retention1886.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12021
theorem numericValid1886 : retention1886.NumericValid := by decide +kernel
def certificate1886 : RatCutBinCertificate := ⟨⟨retention1886,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(5953492754081189/6250000000000000)⟩,(494662241135546001/500000000000000000),(415977065650608993/1000000000000000000),(13697385256226013/62500000000000000),(161102873406627477/1000000000000000000)⟩
theorem valid1886 : certificate1886.Valid := by decide +kernel
theorem sound1886 : certificate1886.Sound := rat_cut_bin_certificate_sound certificate1886 profilesValid1886 numericValid1886 valid1886

def retention1887 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(1/2),64,1,(63854806264426706035670628814159569639/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch300.profile12021,(fun _ => MergedCutProfiles.Batch300.profile12021)⟩
theorem profilesValid1887 : retention1887.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12021
theorem numericValid1887 : retention1887.NumericValid := by decide +kernel
def certificate1887 : RatCutBinCertificate := ⟨⟨retention1887,(2418384026863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(483006221278984017/500000000000000000)⟩,(494662241135546001/500000000000000000),(92776258441195711/250000000000000000),(13051322748092681/50000000000000000),(245726429708149409/1000000000000000000)⟩
theorem valid1887 : certificate1887.Valid := by decide +kernel
theorem sound1887 : certificate1887.Sound := rat_cut_bin_certificate_sound certificate1887 profilesValid1887 numericValid1887 valid1887

def retention1888 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(2233061653569862348/4835861345882636105),(2854098053099252309/1000000000000000000),(5/4),(194907111696148716706240402824184050511/182662275398352147776000000000000000000),false,MergedCutProfiles.Batch300.profile12022,(fun _ => MergedCutProfiles.Batch300.profile12022)⟩
theorem profilesValid1888 : retention1888.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12022
theorem numericValid1888 : retention1888.NumericValid := by decide +kernel
def certificate1888 : RatCutBinCertificate := ⟨⟨retention1888,(2725866276863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(31947801737471757/31250000000000000)⟩,(246990537973094209/250000000000000000),(372159299313415111/1000000000000000000),(64995746249165139/250000000000000000),(42653785352658293/250000000000000000)⟩
theorem valid1888 : certificate1888.Valid := by decide +kernel
theorem sound1888 : certificate1888.Sound := rat_cut_bin_certificate_sound certificate1888 profilesValid1888 numericValid1888 valid1888

def retention1889 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(2394144342226786354/4835861345882636105),(558265413392465587/125000000000000000),(11/10),(443775813585806373625801066689504376271/446612330713972469600000000000000000000),false,MergedCutProfiles.Batch300.profile12023,(fun _ => MergedCutProfiles.Batch300.profile12023)⟩
theorem profilesValid1889 : retention1889.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12023
theorem numericValid1889 : retention1889.NumericValid := by decide +kernel
def certificate1889 : RatCutBinCertificate := ⟨⟨retention1889,(2725866276863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(238577965472252467/250000000000000000)⟩,(246990537973094209/250000000000000000),(199342323767183091/500000000000000000),(234689718830148799/1000000000000000000),(170752488462661937/1000000000000000000)⟩
theorem valid1889 : certificate1889.Valid := by decide +kernel
theorem sound1889 : certificate1889.Sound := rat_cut_bin_certificate_sound certificate1889 profilesValid1889 numericValid1889 valid1889

def retention1890 : RatCutRetentionCertificate := ⟨(533/8000),(267/4000),(1/2),(1197072171113393177/250000000000000000),(11/10),(29549100964103832391300332639067512229/29926804277834829425000000000000000000),false,MergedCutProfiles.Batch300.profile12021,(fun _ => MergedCutProfiles.Batch300.profile12021)⟩
theorem profilesValid1890 : retention1890.ProfilesValid := by
  exact MergedCutProfiles.Batch300.valid12021
theorem numericValid1890 : retention1890.NumericValid := by decide +kernel
def certificate1890 : RatCutBinCertificate := ⟨⟨retention1890,(2725866276863338841/1000000000000000000),(58933568729026887/250000000000000000),(4493440654925608833/250000000000000000),(173976484208467857237/1000000000000000000),(948042872087501143/1000000000000000000)⟩,(246990537973094209/250000000000000000),(100330243361602057/250000000000000000),(58068549737041067/250000000000000000),(169767198586426103/1000000000000000000)⟩
theorem valid1890 : certificate1890.Valid := by decide +kernel
theorem sound1890 : certificate1890.Sound := rat_cut_bin_certificate_sound certificate1890 profilesValid1890 numericValid1890 valid1890

def retention1891 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(1365783759679747669/9627882220611476356),(917332949193513101/1000000000000000000),(12/5),(2281216882348061376417/1280000000000000000000),true,MergedCutProfiles.Batch300.profile12024,![MergedCutProfiles.Batch300.profile12024,MergedCutProfiles.Batch300.profile12025,MergedCutProfiles.Batch300.profile12026,MergedCutProfiles.Batch300.profile12027,MergedCutProfiles.Batch300.profile12028,MergedCutProfiles.Batch300.profile12029,MergedCutProfiles.Batch300.profile12030,MergedCutProfiles.Batch300.profile12031,MergedCutProfiles.Batch300.profile12032,MergedCutProfiles.Batch300.profile12033,MergedCutProfiles.Batch300.profile12034,MergedCutProfiles.Batch300.profile12035,MergedCutProfiles.Batch300.profile12036,MergedCutProfiles.Batch300.profile12037,MergedCutProfiles.Batch300.profile12038,MergedCutProfiles.Batch300.profile12039]⟩
theorem profilesValid1891 : retention1891.ProfilesValid := by
  change ∀ j : Fin 16, (retention1891.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch300.valid12024
  · exact MergedCutProfiles.Batch300.valid12025
  · exact MergedCutProfiles.Batch300.valid12026
  · exact MergedCutProfiles.Batch300.valid12027
  · exact MergedCutProfiles.Batch300.valid12028
  · exact MergedCutProfiles.Batch300.valid12029
  · exact MergedCutProfiles.Batch300.valid12030
  · exact MergedCutProfiles.Batch300.valid12031
  · exact MergedCutProfiles.Batch300.valid12032
  · exact MergedCutProfiles.Batch300.valid12033
  · exact MergedCutProfiles.Batch300.valid12034
  · exact MergedCutProfiles.Batch300.valid12035
  · exact MergedCutProfiles.Batch300.valid12036
  · exact MergedCutProfiles.Batch300.valid12037
  · exact MergedCutProfiles.Batch300.valid12038
  · exact MergedCutProfiles.Batch300.valid12039
theorem numericValid1891 : retention1891.NumericValid := by decide +kernel
def certificate1891 : RatCutBinCertificate := ⟨⟨retention1891,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(852929381623551263/500000000000000000)⟩,(989315767820691727/1000000000000000000),(164684949893565967/500000000000000000),(304830151332980923/1000000000000000000),(16163876827148061/100000000000000000)⟩
theorem valid1891 : certificate1891.Valid := by decide +kernel
theorem sound1891 : certificate1891.Sound := rat_cut_bin_certificate_sound certificate1891 profilesValid1891 numericValid1891 valid1891

def retention1892 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(2740804818074641739/9627882220611476356),(1365783759679747669/1000000000000000000),(17/10),(1829554045037908199809/1280000000000000000000),true,MergedCutProfiles.Batch301.profile12040,![MergedCutProfiles.Batch301.profile12040,MergedCutProfiles.Batch301.profile12041,MergedCutProfiles.Batch301.profile12042,MergedCutProfiles.Batch301.profile12043,MergedCutProfiles.Batch301.profile12044,MergedCutProfiles.Batch301.profile12045,MergedCutProfiles.Batch301.profile12046,MergedCutProfiles.Batch301.profile12047,MergedCutProfiles.Batch301.profile12048,MergedCutProfiles.Batch301.profile12049,MergedCutProfiles.Batch301.profile12050,MergedCutProfiles.Batch301.profile12051,MergedCutProfiles.Batch301.profile12052,MergedCutProfiles.Batch301.profile12053,MergedCutProfiles.Batch301.profile12054,MergedCutProfiles.Batch301.profile12055]⟩
theorem profilesValid1892 : retention1892.ProfilesValid := by
  change ∀ j : Fin 16, (retention1892.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch301.valid12040
  · exact MergedCutProfiles.Batch301.valid12041
  · exact MergedCutProfiles.Batch301.valid12042
  · exact MergedCutProfiles.Batch301.valid12043
  · exact MergedCutProfiles.Batch301.valid12044
  · exact MergedCutProfiles.Batch301.valid12045
  · exact MergedCutProfiles.Batch301.valid12046
  · exact MergedCutProfiles.Batch301.valid12047
  · exact MergedCutProfiles.Batch301.valid12048
  · exact MergedCutProfiles.Batch301.valid12049
  · exact MergedCutProfiles.Batch301.valid12050
  · exact MergedCutProfiles.Batch301.valid12051
  · exact MergedCutProfiles.Batch301.valid12052
  · exact MergedCutProfiles.Batch301.valid12053
  · exact MergedCutProfiles.Batch301.valid12054
  · exact MergedCutProfiles.Batch301.valid12055
theorem numericValid1892 : retention1892.NumericValid := by decide +kernel
def certificate1892 : RatCutBinCertificate := ⟨⟨retention1892,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(687632650304558317/500000000000000000)⟩,(989315767820691727/1000000000000000000),(89863308738290623/250000000000000000),(54552026097656011/200000000000000000),(80760975044041991/500000000000000000)⟩
theorem valid1892 : certificate1892.Valid := by decide +kernel
theorem sound1892 : certificate1892.Sound := rat_cut_bin_certificate_sound certificate1892 profilesValid1892 numericValid1892 valid1892

def retention1893 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(2102166863731344255/4813941110305738178),(2740804818074641739/1000000000000000000),(11/10),(1390482459227994149807/1280000000000000000000),true,MergedCutProfiles.Batch301.profile12056,![MergedCutProfiles.Batch301.profile12056,MergedCutProfiles.Batch301.profile12057,MergedCutProfiles.Batch301.profile12058,MergedCutProfiles.Batch301.profile12059,MergedCutProfiles.Batch301.profile12060,MergedCutProfiles.Batch301.profile12061,MergedCutProfiles.Batch301.profile12062,MergedCutProfiles.Batch301.profile12063,MergedCutProfiles.Batch301.profile12064,MergedCutProfiles.Batch301.profile12065,MergedCutProfiles.Batch301.profile12066,MergedCutProfiles.Batch301.profile12067,MergedCutProfiles.Batch301.profile12068,MergedCutProfiles.Batch301.profile12069,MergedCutProfiles.Batch301.profile12070,MergedCutProfiles.Batch301.profile12071]⟩
theorem profilesValid1893 : retention1893.ProfilesValid := by
  change ∀ j : Fin 16, (retention1893.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch301.valid12056
  · exact MergedCutProfiles.Batch301.valid12057
  · exact MergedCutProfiles.Batch301.valid12058
  · exact MergedCutProfiles.Batch301.valid12059
  · exact MergedCutProfiles.Batch301.valid12060
  · exact MergedCutProfiles.Batch301.valid12061
  · exact MergedCutProfiles.Batch301.valid12062
  · exact MergedCutProfiles.Batch301.valid12063
  · exact MergedCutProfiles.Batch301.valid12064
  · exact MergedCutProfiles.Batch301.valid12065
  · exact MergedCutProfiles.Batch301.valid12066
  · exact MergedCutProfiles.Batch301.valid12067
  · exact MergedCutProfiles.Batch301.valid12068
  · exact MergedCutProfiles.Batch301.valid12069
  · exact MergedCutProfiles.Batch301.valid12070
  · exact MergedCutProfiles.Batch301.valid12071
theorem numericValid1893 : retention1893.NumericValid := by decide +kernel
def certificate1893 : RatCutBinCertificate := ⟨⟨retention1893,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(1051330216309278213/1000000000000000000)⟩,(989315767820691727/1000000000000000000),(80860965189697471/200000000000000000),(114780568766294659/500000000000000000),(41128677441590149/250000000000000000)⟩
theorem valid1893 : certificate1893.Valid := by decide +kernel
theorem sound1893 : certificate1893.Sound := rat_cut_bin_certificate_sound certificate1893 profilesValid1893 numericValid1893 valid1893

def retention1894 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(4690642058547525303/9627882220611476356),(420433372746268851/100000000000000000),1,(25060201979274947667/25600000000000000000),true,MergedCutProfiles.Batch301.profile12072,![MergedCutProfiles.Batch301.profile12072,MergedCutProfiles.Batch301.profile12073,MergedCutProfiles.Batch301.profile12074,MergedCutProfiles.Batch301.profile12075,MergedCutProfiles.Batch301.profile12076,MergedCutProfiles.Batch301.profile12077,MergedCutProfiles.Batch301.profile12078,MergedCutProfiles.Batch301.profile12079,MergedCutProfiles.Batch302.profile12080,MergedCutProfiles.Batch302.profile12081,MergedCutProfiles.Batch302.profile12082,MergedCutProfiles.Batch302.profile12083,MergedCutProfiles.Batch302.profile12084,MergedCutProfiles.Batch302.profile12085,MergedCutProfiles.Batch302.profile12086,MergedCutProfiles.Batch302.profile12087]⟩
theorem profilesValid1894 : retention1894.ProfilesValid := by
  change ∀ j : Fin 16, (retention1894.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch301.valid12072
  · exact MergedCutProfiles.Batch301.valid12073
  · exact MergedCutProfiles.Batch301.valid12074
  · exact MergedCutProfiles.Batch301.valid12075
  · exact MergedCutProfiles.Batch301.valid12076
  · exact MergedCutProfiles.Batch301.valid12077
  · exact MergedCutProfiles.Batch301.valid12078
  · exact MergedCutProfiles.Batch301.valid12079
  · exact MergedCutProfiles.Batch302.valid12080
  · exact MergedCutProfiles.Batch302.valid12081
  · exact MergedCutProfiles.Batch302.valid12082
  · exact MergedCutProfiles.Batch302.valid12083
  · exact MergedCutProfiles.Batch302.valid12084
  · exact MergedCutProfiles.Batch302.valid12085
  · exact MergedCutProfiles.Batch302.valid12086
  · exact MergedCutProfiles.Batch302.valid12087
theorem numericValid1894 : retention1894.NumericValid := by decide +kernel
def certificate1894 : RatCutBinCertificate := ⟨⟨retention1894,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(947114386214018283/1000000000000000000)⟩,(989315767820691727/1000000000000000000),(16939941372975989/40000000000000000),(212628660323913769/1000000000000000000),(81187955025685943/500000000000000000)⟩
theorem valid1894 : certificate1894.Valid := by decide +kernel
theorem sound1894 : certificate1894.Sound := rat_cut_bin_certificate_sound certificate1894 profilesValid1894 numericValid1894 valid1894

def retention1895 : RatCutRetentionCertificate := ⟨(267/4000),(107/1600),(4784923963924330563/9627882220611476356),(4690642058547525303/1000000000000000000),(11/10),(1861676774906620331928507893186042759471/1876256823419010121200000000000000000000),false,MergedCutProfiles.Batch302.profile12088,(fun _ => MergedCutProfiles.Batch302.profile12088)⟩
theorem profilesValid1895 : retention1895.ProfilesValid := by
  exact MergedCutProfiles.Batch302.valid12088
theorem numericValid1895 : retention1895.NumericValid := by decide +kernel
def certificate1895 : RatCutBinCertificate := ⟨⟨retention1895,(241861703736646759/100000000000000000),(47363405557021917/200000000000000000),(18017609099584127983/1000000000000000000),(173610483423788505349/1000000000000000000),(957251554684722123/1000000000000000000)⟩,(989315767820691727/1000000000000000000),(82830940353851063/200000000000000000),(220760555133958353/1000000000000000000),(162436971532411583/1000000000000000000)⟩
theorem valid1895 : certificate1895.Valid := by decide +kernel
theorem sound1895 : certificate1895.Sound := rat_cut_bin_certificate_sound certificate1895 profilesValid1895 numericValid1895 valid1895

def certificates : List RatCutBinCertificate := [certificate1884,certificate1885,certificate1886,certificate1887,certificate1888,certificate1889,certificate1890,certificate1891,certificate1892,certificate1893,certificate1894,certificate1895]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1884,List.forall_mem_cons.mpr ⟨sound1885,List.forall_mem_cons.mpr ⟨sound1886,List.forall_mem_cons.mpr ⟨sound1887,List.forall_mem_cons.mpr ⟨sound1888,List.forall_mem_cons.mpr ⟨sound1889,List.forall_mem_cons.mpr ⟨sound1890,List.forall_mem_cons.mpr ⟨sound1891,List.forall_mem_cons.mpr ⟨sound1892,List.forall_mem_cons.mpr ⟨sound1893,List.forall_mem_cons.mpr ⟨sound1894,List.forall_mem_cons.mpr ⟨sound1895,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch157
