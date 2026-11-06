import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay113
import Cycle12.CutFailureCertificates.Decay114
import Cycle12.CutFailureCertificates.Decay115

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget045

def certificate900 : RatFailureBudget := ⟨(369822667834612896403/50000000000000000),(135074393382847/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay113.certificate2262),(2,CutFailureCertificates.Decay113.certificate2263)]⟩
theorem numericValid900 : certificate900.NumericValid := by decide +kernel
theorem sound900 : certificate900.Sound := rat_failure_budget_sound certificate900 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2262,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2263,List.forall_mem_nil _⟩⟩) numericValid900

def certificate901 : RatFailureBudget := ⟨(369822667834612896403/50000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay113.certificate2264),(922,CutFailureCertificates.Decay113.certificate2265),(1,CutFailureCertificates.Decay113.certificate2266)]⟩
theorem numericValid901 : certificate901.NumericValid := by decide +kernel
theorem sound901 : certificate901.Sound := rat_failure_budget_sound certificate901 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2264,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2265,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2266,List.forall_mem_nil _⟩⟩⟩) numericValid901

def certificate902 : RatFailureBudget := ⟨(6843362511200915649309/1000000000000000000),(3675950311439/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay113.certificate2267),(2,CutFailureCertificates.Decay113.certificate2268),(2,CutFailureCertificates.Decay113.certificate2269)]⟩
theorem numericValid902 : certificate902.NumericValid := by decide +kernel
theorem sound902 : certificate902.Sound := rat_failure_budget_sound certificate902 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2267,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2268,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2269,List.forall_mem_nil _⟩⟩⟩) numericValid902

def certificate903 : RatFailureBudget := ⟨(6843362511200915649309/1000000000000000000),(70802493049409/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay113.certificate2270),(2,CutFailureCertificates.Decay113.certificate2271)]⟩
theorem numericValid903 : certificate903.NumericValid := by decide +kernel
theorem sound903 : certificate903.Sound := rat_failure_budget_sound certificate903 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2270,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2271,List.forall_mem_nil _⟩⟩) numericValid903

def certificate904 : RatFailureBudget := ⟨(6843362511200915649309/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay113.certificate2272),(922,CutFailureCertificates.Decay113.certificate2273),(1,CutFailureCertificates.Decay113.certificate2274)]⟩
theorem numericValid904 : certificate904.NumericValid := by decide +kernel
theorem sound904 : certificate904.Sound := rat_failure_budget_sound certificate904 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2272,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2273,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2274,List.forall_mem_nil _⟩⟩⟩) numericValid904

def certificate905 : RatFailureBudget := ⟨(6347625620013930963373/1000000000000000000),(3895735891051/50000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay113.certificate2275),(2,CutFailureCertificates.Decay113.certificate2276),(2,CutFailureCertificates.Decay113.certificate2277)]⟩
theorem numericValid905 : certificate905.NumericValid := by decide +kernel
theorem sound905 : certificate905.Sound := rat_failure_budget_sound certificate905 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2275,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2276,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2277,List.forall_mem_nil _⟩⟩⟩) numericValid905

def certificate906 : RatFailureBudget := ⟨(6347625620013930963373/1000000000000000000),(75991223950877/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay113.certificate2278),(2,CutFailureCertificates.Decay113.certificate2279)]⟩
theorem numericValid906 : certificate906.NumericValid := by decide +kernel
theorem sound906 : certificate906.Sound := rat_failure_budget_sound certificate906 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2278,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay113.sound2279,List.forall_mem_nil _⟩⟩) numericValid906

def certificate907 : RatFailureBudget := ⟨(6347625620013930963373/1000000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay114.certificate2280),(920,CutFailureCertificates.Decay114.certificate2281),(1,CutFailureCertificates.Decay114.certificate2282)]⟩
theorem numericValid907 : certificate907.NumericValid := by decide +kernel
theorem sound907 : certificate907.Sound := rat_failure_budget_sound certificate907 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2280,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2281,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2282,List.forall_mem_nil _⟩⟩⟩) numericValid907

def certificate908 : RatFailureBudget := ⟨(368853166020647134363/62500000000000000),(3388153299181/40000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay114.certificate2283),(2,CutFailureCertificates.Decay114.certificate2284),(2,CutFailureCertificates.Decay114.certificate2285)]⟩
theorem numericValid908 : certificate908.NumericValid := by decide +kernel
theorem sound908 : certificate908.Sound := rat_failure_budget_sound certificate908 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2283,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2284,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2285,List.forall_mem_nil _⟩⟩⟩) numericValid908

def certificate909 : RatFailureBudget := ⟨(368853166020647134363/62500000000000000),(26366845222801/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay114.certificate2286),(2,CutFailureCertificates.Decay114.certificate2287)]⟩
theorem numericValid909 : certificate909.NumericValid := by decide +kernel
theorem sound909 : certificate909.Sound := rat_failure_budget_sound certificate909 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2286,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2287,List.forall_mem_nil _⟩⟩) numericValid909

def certificate910 : RatFailureBudget := ⟨(368853166020647134363/62500000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay114.certificate2288),(918,CutFailureCertificates.Decay114.certificate2289),(1,CutFailureCertificates.Decay114.certificate2290)]⟩
theorem numericValid910 : certificate910.NumericValid := by decide +kernel
theorem sound910 : certificate910.Sound := rat_failure_budget_sound certificate910 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2288,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2289,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2290,List.forall_mem_nil _⟩⟩⟩) numericValid910

def certificate911 : RatFailureBudget := ⟨(2749528521369003032971/500000000000000000),(35216132542557/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay114.certificate2291),(2,CutFailureCertificates.Decay114.certificate2292),(2,CutFailureCertificates.Decay114.certificate2293)]⟩
theorem numericValid911 : certificate911.NumericValid := by decide +kernel
theorem sound911 : certificate911.Sound := rat_failure_budget_sound certificate911 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2291,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2292,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2293,List.forall_mem_nil _⟩⟩⟩) numericValid911

def certificate912 : RatFailureBudget := ⟨(2749528521369003032971/500000000000000000),(9622504682487/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay114.certificate2294),(2,CutFailureCertificates.Decay114.certificate2295)]⟩
theorem numericValid912 : certificate912.NumericValid := by decide +kernel
theorem sound912 : certificate912.Sound := rat_failure_budget_sound certificate912 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2294,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2295,List.forall_mem_nil _⟩⟩) numericValid912

def certificate913 : RatFailureBudget := ⟨(2749528521369003032971/500000000000000000),(4479061456810613/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay114.certificate2296),(920,CutFailureCertificates.Decay114.certificate2297),(1,CutFailureCertificates.Decay114.certificate2298)]⟩
theorem numericValid913 : certificate913.NumericValid := by decide +kernel
theorem sound913 : certificate913.Sound := rat_failure_budget_sound certificate913 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2296,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2297,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2298,List.forall_mem_nil _⟩⟩⟩) numericValid913

def certificate914 : RatFailureBudget := ⟨(5134451270410500746393/1000000000000000000),(91312797837891/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay114.certificate2299),(2,CutFailureCertificates.Decay115.certificate2300),(2,CutFailureCertificates.Decay115.certificate2301)]⟩
theorem numericValid914 : certificate914.NumericValid := by decide +kernel
theorem sound914 : certificate914.Sound := rat_failure_budget_sound certificate914 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay114.sound2299,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2300,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2301,List.forall_mem_nil _⟩⟩⟩) numericValid914

def certificate915 : RatFailureBudget := ⟨(5134451270410500746393/1000000000000000000),(18338106310463/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay115.certificate2302),(2,CutFailureCertificates.Decay115.certificate2303)]⟩
theorem numericValid915 : certificate915.NumericValid := by decide +kernel
theorem sound915 : certificate915.Sound := rat_failure_budget_sound certificate915 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2302,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2303,List.forall_mem_nil _⟩⟩) numericValid915

def certificate916 : RatFailureBudget := ⟨(5134451270410500746393/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay115.certificate2304),(920,CutFailureCertificates.Decay115.certificate2305),(1,CutFailureCertificates.Decay115.certificate2306)]⟩
theorem numericValid916 : certificate916.NumericValid := by decide +kernel
theorem sound916 : certificate916.Sound := rat_failure_budget_sound certificate916 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2304,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2305,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2306,List.forall_mem_nil _⟩⟩⟩) numericValid916

def certificate917 : RatFailureBudget := ⟨(960649900360527327901/200000000000000000),(24085900667389/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay115.certificate2307),(2,CutFailureCertificates.Decay115.certificate2308),(2,CutFailureCertificates.Decay115.certificate2309)]⟩
theorem numericValid917 : certificate917.NumericValid := by decide +kernel
theorem sound917 : certificate917.Sound := rat_failure_budget_sound certificate917 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2307,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2308,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2309,List.forall_mem_nil _⟩⟩⟩) numericValid917

def certificate918 : RatFailureBudget := ⟨(960649900360527327901/200000000000000000),(97668840971177/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay115.certificate2310),(2,CutFailureCertificates.Decay115.certificate2311)]⟩
theorem numericValid918 : certificate918.NumericValid := by decide +kernel
theorem sound918 : certificate918.Sound := rat_failure_budget_sound certificate918 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2310,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2311,List.forall_mem_nil _⟩⟩) numericValid918

def certificate919 : RatFailureBudget := ⟨(960649900360527327901/200000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay115.certificate2312),(918,CutFailureCertificates.Decay115.certificate2313),(1,CutFailureCertificates.Decay115.certificate2314)]⟩
theorem numericValid919 : certificate919.NumericValid := by decide +kernel
theorem sound919 : certificate919.Sound := rat_failure_budget_sound certificate919 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2312,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2313,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2314,List.forall_mem_nil _⟩⟩⟩) numericValid919

end Cycle12.CutFailureCertificates.Budget045
