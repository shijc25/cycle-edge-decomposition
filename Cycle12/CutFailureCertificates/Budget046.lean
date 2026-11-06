import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay115
import Cycle12.CutFailureCertificates.Decay116
import Cycle12.CutFailureCertificates.Decay117
import Cycle12.CutFailureCertificates.Decay118

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget046

def certificate920 : RatFailureBudget := ⟨(4501536247443668921467/1000000000000000000),(12681591094399/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay115.certificate2315),(2,CutFailureCertificates.Decay115.certificate2316),(2,CutFailureCertificates.Decay115.certificate2317)]⟩
theorem numericValid920 : certificate920.NumericValid := by decide +kernel
theorem sound920 : certificate920.Sound := rat_failure_budget_sound certificate920 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2315,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2316,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2317,List.forall_mem_nil _⟩⟩⟩) numericValid920

def certificate921 : RatFailureBudget := ⟨(4501536247443668921467/1000000000000000000),(51865006253091/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay115.certificate2318),(2,CutFailureCertificates.Decay115.certificate2319)]⟩
theorem numericValid921 : certificate921.NumericValid := by decide +kernel
theorem sound921 : certificate921.Sound := rat_failure_budget_sound certificate921 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2318,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay115.sound2319,List.forall_mem_nil _⟩⟩) numericValid921

def certificate922 : RatFailureBudget := ⟨(4501536247443668921467/1000000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay116.certificate2320),(918,CutFailureCertificates.Decay116.certificate2321),(1,CutFailureCertificates.Decay116.certificate2322)]⟩
theorem numericValid922 : certificate922.NumericValid := by decide +kernel
theorem sound922 : certificate922.Sound := rat_failure_budget_sound certificate922 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2320,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2321,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2322,List.forall_mem_nil _⟩⟩⟩) numericValid922

def certificate923 : RatFailureBudget := ⟨(1056487743880087529817/250000000000000000),(106680392684819/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay116.certificate2323),(2,CutFailureCertificates.Decay116.certificate2324),(2,CutFailureCertificates.Decay116.certificate2325)]⟩
theorem numericValid923 : certificate923.NumericValid := by decide +kernel
theorem sound923 : certificate923.Sound := rat_failure_budget_sound certificate923 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2323,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2324,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2325,List.forall_mem_nil _⟩⟩⟩) numericValid923

def certificate924 : RatFailureBudget := ⟨(1056487743880087529817/250000000000000000),(429626199721/1953125000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay116.certificate2326),(2,CutFailureCertificates.Decay116.certificate2327)]⟩
theorem numericValid924 : certificate924.NumericValid := by decide +kernel
theorem sound924 : certificate924.Sound := rat_failure_budget_sound certificate924 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2326,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2327,List.forall_mem_nil _⟩⟩) numericValid924

def certificate925 : RatFailureBudget := ⟨(1056487743880087529817/250000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay116.certificate2328),(916,CutFailureCertificates.Decay116.certificate2329),(1,CutFailureCertificates.Decay116.certificate2330)]⟩
theorem numericValid925 : certificate925.NumericValid := by decide +kernel
theorem sound925 : certificate925.Sound := rat_failure_budget_sound certificate925 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2328,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2329,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2330,List.forall_mem_nil _⟩⟩⟩) numericValid925

def certificate926 : RatFailureBudget := ⟨(819407000984203374491/200000000000000000),(10850964500599/100000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay116.certificate2331),(2,CutFailureCertificates.Decay116.certificate2332),(2,CutFailureCertificates.Decay116.certificate2333)]⟩
theorem numericValid926 : certificate926.NumericValid := by decide +kernel
theorem sound926 : certificate926.Sound := rat_failure_budget_sound certificate926 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2331,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2332,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2333,List.forall_mem_nil _⟩⟩⟩) numericValid926

def certificate927 : RatFailureBudget := ⟨(819407000984203374491/200000000000000000),(112986104781673/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay116.certificate2334),(2,CutFailureCertificates.Decay116.certificate2335)]⟩
theorem numericValid927 : certificate927.NumericValid := by decide +kernel
theorem sound927 : certificate927.Sound := rat_failure_budget_sound certificate927 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2334,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2335,List.forall_mem_nil _⟩⟩) numericValid927

def certificate928 : RatFailureBudget := ⟨(819407000984203374491/200000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay116.certificate2336),(916,CutFailureCertificates.Decay116.certificate2337),(1,CutFailureCertificates.Decay116.certificate2338)]⟩
theorem numericValid928 : certificate928.NumericValid := by decide +kernel
theorem sound928 : certificate928.Sound := rat_failure_budget_sound certificate928 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2336,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2337,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2338,List.forall_mem_nil _⟩⟩⟩) numericValid928

def certificate929 : RatFailureBudget := ⟨(3973596522288482282311/1000000000000000000),(55563559439731/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay116.certificate2339),(2,CutFailureCertificates.Decay117.certificate2340),(2,CutFailureCertificates.Decay117.certificate2341)]⟩
theorem numericValid929 : certificate929.NumericValid := by decide +kernel
theorem sound929 : certificate929.Sound := rat_failure_budget_sound certificate929 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay116.sound2339,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2340,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2341,List.forall_mem_nil _⟩⟩⟩) numericValid929

def certificate930 : RatFailureBudget := ⟨(3973596522288482282311/1000000000000000000),(46491201274331/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay117.certificate2342),(2,CutFailureCertificates.Decay117.certificate2343)]⟩
theorem numericValid930 : certificate930.NumericValid := by decide +kernel
theorem sound930 : certificate930.Sound := rat_failure_budget_sound certificate930 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2342,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2343,List.forall_mem_nil _⟩⟩) numericValid930

def certificate931 : RatFailureBudget := ⟨(3973596522288482282311/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay117.certificate2344),(914,CutFailureCertificates.Decay117.certificate2345),(1,CutFailureCertificates.Decay117.certificate2346)]⟩
theorem numericValid931 : certificate931.NumericValid := by decide +kernel
theorem sound931 : certificate931.Sound := rat_failure_budget_sound certificate931 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2344,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2345,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2346,List.forall_mem_nil _⟩⟩⟩) numericValid931

def certificate932 : RatFailureBudget := ⟨(3741964644565124703121/1000000000000000000),(117255197997839/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay117.certificate2347),(2,CutFailureCertificates.Decay117.certificate2348),(2,CutFailureCertificates.Decay117.certificate2349)]⟩
theorem numericValid932 : certificate932.NumericValid := by decide +kernel
theorem sound932 : certificate932.Sound := rat_failure_budget_sound certificate932 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2347,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2348,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2349,List.forall_mem_nil _⟩⟩⟩) numericValid932

def certificate933 : RatFailureBudget := ⟨(3741964644565124703121/1000000000000000000),(61470702495217/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay117.certificate2350),(2,CutFailureCertificates.Decay117.certificate2351)]⟩
theorem numericValid933 : certificate933.NumericValid := by decide +kernel
theorem sound933 : certificate933.Sound := rat_failure_budget_sound certificate933 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2350,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2351,List.forall_mem_nil _⟩⟩) numericValid933

def certificate934 : RatFailureBudget := ⟨(3741964644565124703121/1000000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay117.certificate2352),(916,CutFailureCertificates.Decay117.certificate2353),(1,CutFailureCertificates.Decay117.certificate2354)]⟩
theorem numericValid934 : certificate934.NumericValid := by decide +kernel
theorem sound934 : certificate934.Sound := rat_failure_budget_sound certificate934 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2352,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2353,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2354,List.forall_mem_nil _⟩⟩⟩) numericValid934

def certificate935 : RatFailureBudget := ⟨(28384585768098355063/7812500000000000),(119068842598949/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay117.certificate2355),(2,CutFailureCertificates.Decay117.certificate2356),(2,CutFailureCertificates.Decay117.certificate2357)]⟩
theorem numericValid935 : certificate935.NumericValid := by decide +kernel
theorem sound935 : certificate935.Sound := rat_failure_budget_sound certificate935 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2355,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2356,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2357,List.forall_mem_nil _⟩⟩⟩) numericValid935

def certificate936 : RatFailureBudget := ⟨(28384585768098355063/7812500000000000),(251541292107797/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay117.certificate2358),(2,CutFailureCertificates.Decay117.certificate2359)]⟩
theorem numericValid936 : certificate936.NumericValid := by decide +kernel
theorem sound936 : certificate936.Sound := rat_failure_budget_sound certificate936 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2358,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay117.sound2359,List.forall_mem_nil _⟩⟩) numericValid936

def certificate937 : RatFailureBudget := ⟨(28384585768098355063/7812500000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay118.certificate2360),(916,CutFailureCertificates.Decay118.certificate2361),(1,CutFailureCertificates.Decay118.certificate2362)]⟩
theorem numericValid937 : certificate937.NumericValid := by decide +kernel
theorem sound937 : certificate937.Sound := rat_failure_budget_sound certificate937 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2360,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2361,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2362,List.forall_mem_nil _⟩⟩⟩) numericValid937

def certificate938 : RatFailureBudget := ⟨(705775029171982801787/200000000000000000),(15219160670537/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay118.certificate2363),(2,CutFailureCertificates.Decay118.certificate2364),(2,CutFailureCertificates.Decay118.certificate2365)]⟩
theorem numericValid938 : certificate938.NumericValid := by decide +kernel
theorem sound938 : certificate938.Sound := rat_failure_budget_sound certificate938 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2363,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2364,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2365,List.forall_mem_nil _⟩⟩⟩) numericValid938

def certificate939 : RatFailureBudget := ⟨(705775029171982801787/200000000000000000),(259980275841269/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay118.certificate2366),(2,CutFailureCertificates.Decay118.certificate2367)]⟩
theorem numericValid939 : certificate939.NumericValid := by decide +kernel
theorem sound939 : certificate939.Sound := rat_failure_budget_sound certificate939 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2366,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay118.sound2367,List.forall_mem_nil _⟩⟩) numericValid939

end Cycle12.CutFailureCertificates.Budget046
