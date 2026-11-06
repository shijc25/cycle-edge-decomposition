import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay110
import Cycle12.CutFailureCertificates.Decay111
import Cycle12.CutFailureCertificates.Decay112
import Cycle12.CutFailureCertificates.Decay113

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget044

def certificate880 : RatFailureBudget := ⟨(13947560834922328059369/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay110.certificate2208),(916,CutFailureCertificates.Decay110.certificate2209),(1,CutFailureCertificates.Decay110.certificate2210)]⟩
theorem numericValid880 : certificate880.NumericValid := by decide +kernel
theorem sound880 : certificate880.Sound := rat_failure_budget_sound certificate880 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2208,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2209,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2210,List.forall_mem_nil _⟩⟩⟩) numericValid880

def certificate881 : RatFailureBudget := ⟨(12590448292418869216701/1000000000000000000),(20846070743167/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay110.certificate2211),(2,CutFailureCertificates.Decay110.certificate2212),(2,CutFailureCertificates.Decay110.certificate2213)]⟩
theorem numericValid881 : certificate881.NumericValid := by decide +kernel
theorem sound881 : certificate881.Sound := rat_failure_budget_sound certificate881 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2211,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2212,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2213,List.forall_mem_nil _⟩⟩⟩) numericValid881

def certificate882 : RatFailureBudget := ⟨(12590448292418869216701/1000000000000000000),(78884878026589/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay110.certificate2214),(2,CutFailureCertificates.Decay110.certificate2215)]⟩
theorem numericValid882 : certificate882.NumericValid := by decide +kernel
theorem sound882 : certificate882.Sound := rat_failure_budget_sound certificate882 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2214,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2215,List.forall_mem_nil _⟩⟩) numericValid882

def certificate883 : RatFailureBudget := ⟨(12590448292418869216701/1000000000000000000),(4473355659738909/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay110.certificate2216),(920,CutFailureCertificates.Decay110.certificate2217),(1,CutFailureCertificates.Decay110.certificate2218)]⟩
theorem numericValid883 : certificate883.NumericValid := by decide +kernel
theorem sound883 : certificate883.Sound := rat_failure_budget_sound certificate883 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2216,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2217,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2218,List.forall_mem_nil _⟩⟩⟩) numericValid883

def certificate884 : RatFailureBudget := ⟨(11416785527815779703113/1000000000000000000),(1576859604463/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay110.certificate2219),(2,CutFailureCertificates.Decay111.certificate2220),(2,CutFailureCertificates.Decay111.certificate2221)]⟩
theorem numericValid884 : certificate884.NumericValid := by decide +kernel
theorem sound884 : certificate884.Sound := rat_failure_budget_sound certificate884 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2219,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2220,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2221,List.forall_mem_nil _⟩⟩⟩) numericValid884

def certificate885 : RatFailureBudget := ⟨(11416785527815779703113/1000000000000000000),(43387471982557/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay111.certificate2222),(2,CutFailureCertificates.Decay111.certificate2223)]⟩
theorem numericValid885 : certificate885.NumericValid := by decide +kernel
theorem sound885 : certificate885.Sound := rat_failure_budget_sound certificate885 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2222,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2223,List.forall_mem_nil _⟩⟩) numericValid885

def certificate886 : RatFailureBudget := ⟨(11416785527815779703113/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay111.certificate2224),(920,CutFailureCertificates.Decay111.certificate2225),(1,CutFailureCertificates.Decay111.certificate2226)]⟩
theorem numericValid886 : certificate886.NumericValid := by decide +kernel
theorem sound886 : certificate886.Sound := rat_failure_budget_sound certificate886 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2224,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2225,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2226,List.forall_mem_nil _⟩⟩⟩) numericValid886

def certificate887 : RatFailureBudget := ⟨(10395149607104828422059/1000000000000000000),(12794079029111/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay111.certificate2227),(2,CutFailureCertificates.Decay111.certificate2228),(2,CutFailureCertificates.Decay111.certificate2229)]⟩
theorem numericValid887 : certificate887.NumericValid := by decide +kernel
theorem sound887 : certificate887.Sound := rat_failure_budget_sound certificate887 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2227,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2228,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2229,List.forall_mem_nil _⟩⟩⟩) numericValid887

def certificate888 : RatFailureBudget := ⟨(10395149607104828422059/1000000000000000000),(95450029861847/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay111.certificate2230),(2,CutFailureCertificates.Decay111.certificate2231)]⟩
theorem numericValid888 : certificate888.NumericValid := by decide +kernel
theorem sound888 : certificate888.Sound := rat_failure_budget_sound certificate888 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2230,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2231,List.forall_mem_nil _⟩⟩) numericValid888

def certificate889 : RatFailureBudget := ⟨(10395149607104828422059/1000000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay111.certificate2232),(918,CutFailureCertificates.Decay111.certificate2233),(1,CutFailureCertificates.Decay111.certificate2234)]⟩
theorem numericValid889 : certificate889.NumericValid := by decide +kernel
theorem sound889 : certificate889.Sound := rat_failure_budget_sound certificate889 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2232,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2233,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2234,List.forall_mem_nil _⟩⟩⟩) numericValid889

def certificate890 : RatFailureBudget := ⟨(9500551814030085163711/1000000000000000000),(71131327452917/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay111.certificate2235),(2,CutFailureCertificates.Decay111.certificate2236),(2,CutFailureCertificates.Decay111.certificate2237)]⟩
theorem numericValid890 : certificate890.NumericValid := by decide +kernel
theorem sound890 : certificate890.Sound := rat_failure_budget_sound certificate890 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2235,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2236,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2237,List.forall_mem_nil _⟩⟩⟩) numericValid890

def certificate891 : RatFailureBudget := ⟨(9500551814030085163711/1000000000000000000),(10355230317643/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay111.certificate2238),(2,CutFailureCertificates.Decay111.certificate2239)]⟩
theorem numericValid891 : certificate891.NumericValid := by decide +kernel
theorem sound891 : certificate891.Sound := rat_failure_budget_sound certificate891 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2238,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay111.sound2239,List.forall_mem_nil _⟩⟩) numericValid891

def certificate892 : RatFailureBudget := ⟨(9500551814030085163711/1000000000000000000),(1124546536924517/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay112.certificate2240),(918,CutFailureCertificates.Decay112.certificate2241),(1,CutFailureCertificates.Decay112.certificate2242)]⟩
theorem numericValid892 : certificate892.NumericValid := by decide +kernel
theorem sound892 : certificate892.Sound := rat_failure_budget_sound certificate892 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2240,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2241,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2242,List.forall_mem_nil _⟩⟩⟩) numericValid892

def certificate893 : RatFailureBudget := ⟨(4356460485383070622671/500000000000000000),(44953611465869/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay112.certificate2243),(2,CutFailureCertificates.Decay112.certificate2244),(2,CutFailureCertificates.Decay112.certificate2245)]⟩
theorem numericValid893 : certificate893.NumericValid := by decide +kernel
theorem sound893 : certificate893.Sound := rat_failure_budget_sound certificate893 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2243,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2244,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2245,List.forall_mem_nil _⟩⟩⟩) numericValid893

def certificate894 : RatFailureBudget := ⟨(4356460485383070622671/500000000000000000),(56292584785023/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay112.certificate2246),(2,CutFailureCertificates.Decay112.certificate2247)]⟩
theorem numericValid894 : certificate894.NumericValid := by decide +kernel
theorem sound894 : certificate894.Sound := rat_failure_budget_sound certificate894 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2246,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2247,List.forall_mem_nil _⟩⟩) numericValid894

def certificate895 : RatFailureBudget := ⟨(4356460485383070622671/500000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay112.certificate2248),(916,CutFailureCertificates.Decay112.certificate2249),(1,CutFailureCertificates.Decay112.certificate2250)]⟩
theorem numericValid895 : certificate895.NumericValid := by decide +kernel
theorem sound895 : certificate895.Sound := rat_failure_budget_sound certificate895 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2248,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2249,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2250,List.forall_mem_nil _⟩⟩⟩) numericValid895

def certificate896 : RatFailureBudget := ⟨(1603197552115051441481/200000000000000000),(28635836456073/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay112.certificate2251),(2,CutFailureCertificates.Decay112.certificate2252),(2,CutFailureCertificates.Decay112.certificate2253)]⟩
theorem numericValid896 : certificate896.NumericValid := by decide +kernel
theorem sound896 : certificate896.Sound := rat_failure_budget_sound certificate896 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2251,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2252,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2253,List.forall_mem_nil _⟩⟩⟩) numericValid896

def certificate897 : RatFailureBudget := ⟨(1603197552115051441481/200000000000000000),(12176265727817/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay112.certificate2254),(2,CutFailureCertificates.Decay112.certificate2255)]⟩
theorem numericValid897 : certificate897.NumericValid := by decide +kernel
theorem sound897 : certificate897.Sound := rat_failure_budget_sound certificate897 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2254,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2255,List.forall_mem_nil _⟩⟩) numericValid897

def certificate898 : RatFailureBudget := ⟨(1603197552115051441481/200000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay112.certificate2256),(924,CutFailureCertificates.Decay112.certificate2257),(1,CutFailureCertificates.Decay112.certificate2258)]⟩
theorem numericValid898 : certificate898.NumericValid := by decide +kernel
theorem sound898 : certificate898.Sound := rat_failure_budget_sound certificate898 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2256,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2257,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2258,List.forall_mem_nil _⟩⟩⟩) numericValid898

def certificate899 : RatFailureBudget := ⟨(369822667834612896403/50000000000000000),(1371070793529/20000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay112.certificate2259),(2,CutFailureCertificates.Decay113.certificate2260),(2,CutFailureCertificates.Decay113.certificate2261)]⟩
theorem numericValid899 : certificate899.NumericValid := by decide +kernel
theorem sound899 : certificate899.Sound := rat_failure_budget_sound certificate899 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay112.sound2259,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2260,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2261,List.forall_mem_nil _⟩⟩⟩) numericValid899

end Cycle12.CutFailureCertificates.Budget044
