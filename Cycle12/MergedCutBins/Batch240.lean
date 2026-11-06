import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch019
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch317
import Cycle12.MergedCutProfiles.Batch318
import Cycle12.MergedCutProfiles.Batch452
import Cycle12.MergedCutProfiles.Batch453

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch240

def retention2880 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(593299070541796199/370136445912164459406),(1251597399/1000000000),(5/2),(465499635102142771/200000000000000000),true,MergedCutProfiles.Batch452.profile18091,![MergedCutProfiles.Batch452.profile18091,MergedCutProfiles.Batch452.profile18108,MergedCutProfiles.Batch452.profile18095,MergedCutProfiles.Batch452.profile18109,MergedCutProfiles.Batch452.profile18102,MergedCutProfiles.Batch316.profile12670,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch316.profile12671,MergedCutProfiles.Batch017.profile707,MergedCutProfiles.Batch452.profile18106,MergedCutProfiles.Batch017.profile708,MergedCutProfiles.Batch018.profile736,MergedCutProfiles.Batch452.profile18110,MergedCutProfiles.Batch316.profile12678,MergedCutProfiles.Batch452.profile18111,MergedCutProfiles.Batch316.profile12679]⟩
theorem profilesValid2880 : retention2880.ProfilesValid := by
  change ∀ j : Fin 16, (retention2880.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch452.valid18091
  · exact MergedCutProfiles.Batch452.valid18108
  · exact MergedCutProfiles.Batch452.valid18095
  · exact MergedCutProfiles.Batch452.valid18109
  · exact MergedCutProfiles.Batch452.valid18102
  · exact MergedCutProfiles.Batch316.valid12670
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch316.valid12671
  · exact MergedCutProfiles.Batch017.valid707
  · exact MergedCutProfiles.Batch452.valid18106
  · exact MergedCutProfiles.Batch017.valid708
  · exact MergedCutProfiles.Batch018.valid736
  · exact MergedCutProfiles.Batch452.valid18110
  · exact MergedCutProfiles.Batch316.valid12678
  · exact MergedCutProfiles.Batch452.valid18111
  · exact MergedCutProfiles.Batch316.valid12679
theorem numericValid2880 : retention2880.NumericValid := by decide +kernel
def certificate2880 : RatCutBinCertificate := ⟨⟨retention2880,(92034014439784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(1160701690868087711/500000000000000000)⟩,(6248724591683959/6250000000000000),(364853450200191457/1000000000000000000),(267275787940612331/1000000000000000000),(191341750854267319/1000000000000000000)⟩
theorem valid2880 : certificate2880.Valid := by decide +kernel
theorem sound2880 : certificate2880.Sound := rat_cut_bin_certificate_sound certificate2880 profilesValid2880 numericValid2880 valid2880

def retention2881 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(32000000000000000000/555204668868246689109),(1779897211625388597/1000000000000000000),2,(601044298245016915600332667968478419/296649535270898099500000000000000000),false,MergedCutProfiles.Batch452.profile18112,(fun _ => MergedCutProfiles.Batch452.profile18112)⟩
theorem profilesValid2881 : retention2881.ProfilesValid := by
  exact MergedCutProfiles.Batch452.valid18112
theorem numericValid2881 : retention2881.NumericValid := by decide +kernel
def certificate2881 : RatCutBinCertificate := ⟨⟨retention2881,(92034014439784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(2021233182014778453/1000000000000000000)⟩,(6248724591683959/6250000000000000),(17919696991831211/50000000000000000),(34230674537051443/125000000000000000),(215507379883046931/1000000000000000000)⟩
theorem valid2881 : certificate2881.Valid := by decide +kernel
theorem sound2881 : certificate2881.Sound := rat_cut_bin_certificate_sound certificate2881 profilesValid2881 numericValid2881 valid2881

def retention2882 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid2882 : retention2882.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid2882 : retention2882.NumericValid := by decide +kernel
def certificate2882 : RatCutBinCertificate := ⟨⟨retention2882,(92034014439784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(995101421342581079/1000000000000000000)⟩,(6248724591683959/6250000000000000),(444258668294857311/1000000000000000000),(9764624010365877/50000000000000000),(2391513514551917/12500000000000000)⟩
theorem valid2882 : certificate2882.Valid := by decide +kernel
theorem sound2882 : certificate2882.Sound := rat_cut_bin_certificate_sound certificate2882 profilesValid2882 numericValid2882 valid2882

def retention2883 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(32000000000000000000/555204668868246689109),(1656375908311522161/200000000000000000),1,(7031232043247364385717326446779500819/3680835351803382580000000000000000000),false,MergedCutProfiles.Batch452.profile18112,(fun _ => MergedCutProfiles.Batch452.profile18112)⟩
theorem profilesValid2883 : retention2883.ProfilesValid := by
  exact MergedCutProfiles.Batch452.valid18112
theorem numericValid2883 : retention2883.NumericValid := by decide +kernel
def certificate2883 : RatCutBinCertificate := ⟨⟨retention2883,(99640613989784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(190758785352520329/100000000000000000)⟩,(199955813732190013/200000000000000000),(74386481802614983/1000000000000000000),(72598666931447009/100000000000000000),(1125355762373553237/1000000000000000000)⟩
theorem valid2883 : certificate2883.Valid := by decide +kernel
theorem sound2883 : certificate2883.Sound := rat_cut_bin_certificate_sound certificate2883 profilesValid2883 numericValid2883 valid2883

def retention2884 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(1/2),64,1,(255370070520985369056173916463207973031/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch019.profile763,(fun _ => MergedCutProfiles.Batch019.profile763)⟩
theorem profilesValid2884 : retention2884.ProfilesValid := by
  exact MergedCutProfiles.Batch019.valid763
theorem numericValid2884 : retention2884.NumericValid := by decide +kernel
def certificate2884 : RatCutBinCertificate := ⟨⟨retention2884,(99640613989784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(248724981961046453/250000000000000000)⟩,(199955813732190013/200000000000000000),(5705046112953989/40000000000000000),(578406367583394331/1000000000000000000),(35407597602793907/62500000000000000)⟩
theorem valid2884 : certificate2884.Valid := by decide +kernel
theorem sound2884 : certificate2884.Sound := rat_cut_bin_certificate_sound certificate2884 profilesValid2884 numericValid2884 valid2884

def retention2885 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(85575882754874592/139860846685285251617),(293613949261896943/500000000000000000),4,(1048275249740777659567752646032567507/469782318819035108800000000000000000),true,MergedCutProfiles.Batch452.profile18113,![MergedCutProfiles.Batch452.profile18113,MergedCutProfiles.Batch452.profile18114,MergedCutProfiles.Batch452.profile18115,MergedCutProfiles.Batch452.profile18116,MergedCutProfiles.Batch317.profile12705,MergedCutProfiles.Batch452.profile18117,MergedCutProfiles.Batch452.profile18118,MergedCutProfiles.Batch317.profile12706,MergedCutProfiles.Batch318.profile12721,MergedCutProfiles.Batch020.profile804,MergedCutProfiles.Batch452.profile18119,MergedCutProfiles.Batch453.profile18120,MergedCutProfiles.Batch317.profile12707,MergedCutProfiles.Batch453.profile18121,MergedCutProfiles.Batch020.profile817,MergedCutProfiles.Batch019.profile766]⟩
theorem profilesValid2885 : retention2885.ProfilesValid := by
  change ∀ j : Fin 16, (retention2885.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch452.valid18113
  · exact MergedCutProfiles.Batch452.valid18114
  · exact MergedCutProfiles.Batch452.valid18115
  · exact MergedCutProfiles.Batch452.valid18116
  · exact MergedCutProfiles.Batch317.valid12705
  · exact MergedCutProfiles.Batch452.valid18117
  · exact MergedCutProfiles.Batch452.valid18118
  · exact MergedCutProfiles.Batch317.valid12706
  · exact MergedCutProfiles.Batch318.valid12721
  · exact MergedCutProfiles.Batch020.valid804
  · exact MergedCutProfiles.Batch452.valid18119
  · exact MergedCutProfiles.Batch453.valid18120
  · exact MergedCutProfiles.Batch317.valid12707
  · exact MergedCutProfiles.Batch453.valid18121
  · exact MergedCutProfiles.Batch020.valid817
  · exact MergedCutProfiles.Batch019.valid766
theorem numericValid2885 : retention2885.NumericValid := by decide +kernel
def certificate2885 : RatCutBinCertificate := ⟨⟨retention2885,(1846308694409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(2220465798262922329/1000000000000000000)⟩,(199954219407923867/200000000000000000),(295617920101445129/500000000000000000),(98045904399492613/1000000000000000000),(11002744714035441/250000000000000000)⟩
theorem valid2885 : certificate2885.Valid := by decide +kernel
theorem sound2885 : certificate2885.Sound := rat_cut_bin_certificate_sound certificate2885 profilesValid2885 numericValid2885 valid2885

def retention2886 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1262467532000000000/979025926796996761319),(18719724352628817/31250000000000000),4,(1076210709360436416163625705147720179/479224943427297715200000000000000000),true,MergedCutProfiles.Batch453.profile18122,![MergedCutProfiles.Batch453.profile18122,MergedCutProfiles.Batch453.profile18123,MergedCutProfiles.Batch452.profile18117,MergedCutProfiles.Batch453.profile18124,MergedCutProfiles.Batch019.profile765,MergedCutProfiles.Batch317.profile12707,MergedCutProfiles.Batch453.profile18125,MergedCutProfiles.Batch453.profile18126,MergedCutProfiles.Batch453.profile18127,MergedCutProfiles.Batch019.profile767,MergedCutProfiles.Batch453.profile18128,MergedCutProfiles.Batch453.profile18129,MergedCutProfiles.Batch019.profile782,MergedCutProfiles.Batch453.profile18130,MergedCutProfiles.Batch019.profile769,MergedCutProfiles.Batch317.profile12711]⟩
theorem profilesValid2886 : retention2886.ProfilesValid := by
  change ∀ j : Fin 16, (retention2886.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch453.valid18122
  · exact MergedCutProfiles.Batch453.valid18123
  · exact MergedCutProfiles.Batch452.valid18117
  · exact MergedCutProfiles.Batch453.valid18124
  · exact MergedCutProfiles.Batch019.valid765
  · exact MergedCutProfiles.Batch317.valid12707
  · exact MergedCutProfiles.Batch453.valid18125
  · exact MergedCutProfiles.Batch453.valid18126
  · exact MergedCutProfiles.Batch453.valid18127
  · exact MergedCutProfiles.Batch019.valid767
  · exact MergedCutProfiles.Batch453.valid18128
  · exact MergedCutProfiles.Batch453.valid18129
  · exact MergedCutProfiles.Batch019.valid782
  · exact MergedCutProfiles.Batch453.valid18130
  · exact MergedCutProfiles.Batch019.valid769
  · exact MergedCutProfiles.Batch317.valid12711
theorem numericValid2886 : retention2886.NumericValid := by decide +kernel
def certificate2886 : RatCutBinCertificate := ⟨⟨retention2886,(1846308694409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(558697819473675351/250000000000000000)⟩,(199954219407923867/200000000000000000),(579712877931460453/1000000000000000000),(104214710173846363/1000000000000000000),(47202603419625189/1000000000000000000)⟩
theorem valid2886 : certificate2886.Valid := by decide +kernel
theorem sound2886 : certificate2886.Sound := rat_cut_bin_certificate_sound certificate2886 profilesValid2886 numericValid2886 valid2886

def retention2887 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(3032727255683688847/979025926796996761319),(315616883/250000000),(49/20),(920147368692023399/400000000000000000),true,MergedCutProfiles.Batch317.profile12705,![MergedCutProfiles.Batch317.profile12705,MergedCutProfiles.Batch020.profile804,MergedCutProfiles.Batch020.profile817,MergedCutProfiles.Batch019.profile794,MergedCutProfiles.Batch453.profile18129,MergedCutProfiles.Batch019.profile795,MergedCutProfiles.Batch318.profile12723,MergedCutProfiles.Batch020.profile806,MergedCutProfiles.Batch020.profile818,MergedCutProfiles.Batch020.profile807,MergedCutProfiles.Batch019.profile784,MergedCutProfiles.Batch020.profile808,MergedCutProfiles.Batch453.profile18131,MergedCutProfiles.Batch020.profile809,MergedCutProfiles.Batch020.profile819,MergedCutProfiles.Batch019.profile799]⟩
theorem profilesValid2887 : retention2887.ProfilesValid := by
  change ∀ j : Fin 16, (retention2887.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch317.valid12705
  · exact MergedCutProfiles.Batch020.valid804
  · exact MergedCutProfiles.Batch020.valid817
  · exact MergedCutProfiles.Batch019.valid794
  · exact MergedCutProfiles.Batch453.valid18129
  · exact MergedCutProfiles.Batch019.valid795
  · exact MergedCutProfiles.Batch318.valid12723
  · exact MergedCutProfiles.Batch020.valid806
  · exact MergedCutProfiles.Batch020.valid818
  · exact MergedCutProfiles.Batch020.valid807
  · exact MergedCutProfiles.Batch019.valid784
  · exact MergedCutProfiles.Batch020.valid808
  · exact MergedCutProfiles.Batch453.valid18131
  · exact MergedCutProfiles.Batch020.valid809
  · exact MergedCutProfiles.Batch020.valid819
  · exact MergedCutProfiles.Batch019.valid799
theorem numericValid2887 : retention2887.NumericValid := by decide +kernel
def certificate2887 : RatCutBinCertificate := ⟨⟨retention2887,(1846308694409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(2293667334289901139/1000000000000000000)⟩,(199954219407923867/200000000000000000),(18392241733659687/50000000000000000),(264272240775446487/1000000000000000000),(94937190881814331/500000000000000000)⟩
theorem valid2887 : certificate2887.Valid := by decide +kernel
theorem sound2887 : certificate2887.Sound := rat_cut_bin_certificate_sound certificate2887 profilesValid2887 numericValid2887 valid2887

def retention2888 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/979025926796996761319),(3032727255683688847/1000000000000000000),(29/20),(2533586531609304100727/1280000000000000000000),true,MergedCutProfiles.Batch020.profile820,![MergedCutProfiles.Batch020.profile820,MergedCutProfiles.Batch453.profile18132,MergedCutProfiles.Batch453.profile18133,MergedCutProfiles.Batch453.profile18134,MergedCutProfiles.Batch453.profile18135,MergedCutProfiles.Batch453.profile18136,MergedCutProfiles.Batch453.profile18137,MergedCutProfiles.Batch453.profile18138,MergedCutProfiles.Batch453.profile18139,MergedCutProfiles.Batch453.profile18140,MergedCutProfiles.Batch453.profile18141,MergedCutProfiles.Batch453.profile18142,MergedCutProfiles.Batch453.profile18143,MergedCutProfiles.Batch453.profile18144,MergedCutProfiles.Batch453.profile18145,MergedCutProfiles.Batch453.profile18146]⟩
theorem profilesValid2888 : retention2888.ProfilesValid := by
  change ∀ j : Fin 16, (retention2888.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid820
  · exact MergedCutProfiles.Batch453.valid18132
  · exact MergedCutProfiles.Batch453.valid18133
  · exact MergedCutProfiles.Batch453.valid18134
  · exact MergedCutProfiles.Batch453.valid18135
  · exact MergedCutProfiles.Batch453.valid18136
  · exact MergedCutProfiles.Batch453.valid18137
  · exact MergedCutProfiles.Batch453.valid18138
  · exact MergedCutProfiles.Batch453.valid18139
  · exact MergedCutProfiles.Batch453.valid18140
  · exact MergedCutProfiles.Batch453.valid18141
  · exact MergedCutProfiles.Batch453.valid18142
  · exact MergedCutProfiles.Batch453.valid18143
  · exact MergedCutProfiles.Batch453.valid18144
  · exact MergedCutProfiles.Batch453.valid18145
  · exact MergedCutProfiles.Batch453.valid18146
theorem numericValid2888 : retention2888.NumericValid := by decide +kernel
def certificate2888 : RatCutBinCertificate := ⟨⟨retention2888,(1846308694409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(1975398528683113767/1000000000000000000)⟩,(199954219407923867/200000000000000000),(38320050219662451/125000000000000000),(330961535012335997/1000000000000000000),(344151239475820031/1000000000000000000)⟩
theorem valid2888 : certificate2888.Valid := by decide +kernel
theorem sound2888 : certificate2888.Sound := rat_cut_bin_certificate_sound certificate2888 profilesValid2888 numericValid2888 valid2888

def retention2889 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid2889 : retention2889.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid2889 : retention2889.NumericValid := by decide +kernel
def certificate2889 : RatCutBinCertificate := ⟨⟨retention2889,(1846308694409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(497402600065151873/500000000000000000)⟩,(199954219407923867/200000000000000000),(223058618777530961/500000000000000000),(96894217574135127/500000000000000000),(47446804516302017/250000000000000000)⟩
theorem valid2889 : certificate2889.Valid := by decide +kernel
theorem sound2889 : certificate2889.Sound := rat_cut_bin_certificate_sound certificate2889 profilesValid2889 numericValid2889 valid2889

def retention2890 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/979025926796996761319),(2099091381246000543/250000000000000000),1,(63408424061327984333094450169523505311/33585462099936008688000000000000000000),false,MergedCutProfiles.Batch453.profile18147,(fun _ => MergedCutProfiles.Batch453.profile18147)⟩
theorem profilesValid2890 : retention2890.ProfilesValid := by
  exact MergedCutProfiles.Batch453.valid18147
theorem numericValid2890 : retention2890.NumericValid := by decide +kernel
def certificate2890 : RatCutBinCertificate := ⟨⟨retention2890,(1998894817409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(1885011178355503967/1000000000000000000)⟩,(999752179559465113/1000000000000000000),(37189581815234147/500000000000000000),(36300226191357727/50000000000000000),(1117327077013795143/1000000000000000000)⟩
theorem valid2890 : certificate2890.Valid := by decide +kernel
theorem sound2890 : certificate2890.Sound := rat_cut_bin_certificate_sound certificate2890 profilesValid2890 numericValid2890 valid2890

def retention2891 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid2891 : retention2891.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid2891 : retention2891.NumericValid := by decide +kernel
def certificate2891 : RatCutBinCertificate := ⟨⟨retention2891,(1998894817409359161/1000000000000000000),(12019078477736559/1000000000000000000),(2028320150818310677/250000000000000000),(1596069211513529826833/200000000000000000),(497289578913796149/500000000000000000)⟩,(999752179559465113/1000000000000000000),(17621216191882807/125000000000000000),(581593026718359821/1000000000000000000),(113889291274879863/200000000000000000)⟩
theorem valid2891 : certificate2891.Valid := by decide +kernel
theorem sound2891 : certificate2891.Sound := rat_cut_bin_certificate_sound certificate2891 profilesValid2891 numericValid2891 valid2891

def certificates : List RatCutBinCertificate := [certificate2880,certificate2881,certificate2882,certificate2883,certificate2884,certificate2885,certificate2886,certificate2887,certificate2888,certificate2889,certificate2890,certificate2891]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2880,List.forall_mem_cons.mpr ⟨sound2881,List.forall_mem_cons.mpr ⟨sound2882,List.forall_mem_cons.mpr ⟨sound2883,List.forall_mem_cons.mpr ⟨sound2884,List.forall_mem_cons.mpr ⟨sound2885,List.forall_mem_cons.mpr ⟨sound2886,List.forall_mem_cons.mpr ⟨sound2887,List.forall_mem_cons.mpr ⟨sound2888,List.forall_mem_cons.mpr ⟨sound2889,List.forall_mem_cons.mpr ⟨sound2890,List.forall_mem_cons.mpr ⟨sound2891,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch240
