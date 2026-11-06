import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay107
import Cycle12.CutFailureCertificates.Decay108
import Cycle12.CutFailureCertificates.Decay109
import Cycle12.CutFailureCertificates.Decay110

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget043

def certificate860 : RatFailureBudget := ⟨(14638423109307511934043/500000000000000000),(1545843803911/125000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay107.certificate2155),(2,CutFailureCertificates.Decay107.certificate2156),(2,CutFailureCertificates.Decay107.certificate2157)]⟩
theorem numericValid860 : certificate860.NumericValid := by decide +kernel
theorem sound860 : certificate860.Sound := rat_failure_budget_sound certificate860 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2155,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2156,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2157,List.forall_mem_nil _⟩⟩⟩) numericValid860

def certificate861 : RatFailureBudget := ⟨(14638423109307511934043/500000000000000000),(33147474641927/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay107.certificate2158),(2,CutFailureCertificates.Decay107.certificate2159)]⟩
theorem numericValid861 : certificate861.NumericValid := by decide +kernel
theorem sound861 : certificate861.Sound := rat_failure_budget_sound certificate861 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2158,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay107.sound2159,List.forall_mem_nil _⟩⟩) numericValid861

def certificate862 : RatFailureBudget := ⟨(14638423109307511934043/500000000000000000),(4472588439023811/1000000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay108.certificate2160),(922,CutFailureCertificates.Decay108.certificate2161),(1,CutFailureCertificates.Decay108.certificate2162)]⟩
theorem numericValid862 : certificate862.NumericValid := by decide +kernel
theorem sound862 : certificate862.Sound := rat_failure_budget_sound certificate862 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2160,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2161,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2162,List.forall_mem_nil _⟩⟩⟩) numericValid862

def certificate863 : RatFailureBudget := ⟨(25385747812366614322327/1000000000000000000),(26427371218303/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay108.certificate2163),(2,CutFailureCertificates.Decay108.certificate2164),(2,CutFailureCertificates.Decay108.certificate2165)]⟩
theorem numericValid863 : certificate863.NumericValid := by decide +kernel
theorem sound863 : certificate863.Sound := rat_failure_budget_sound certificate863 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2163,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2164,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2165,List.forall_mem_nil _⟩⟩⟩) numericValid863

def certificate864 : RatFailureBudget := ⟨(25385747812366614322327/1000000000000000000),(132320169300023/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay108.certificate2166),(2,CutFailureCertificates.Decay108.certificate2167)]⟩
theorem numericValid864 : certificate864.NumericValid := by decide +kernel
theorem sound864 : certificate864.Sound := rat_failure_budget_sound certificate864 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2166,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2167,List.forall_mem_nil _⟩⟩) numericValid864

def certificate865 : RatFailureBudget := ⟨(25385747812366614322327/1000000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay108.certificate2168),(920,CutFailureCertificates.Decay108.certificate2169),(1,CutFailureCertificates.Decay108.certificate2170)]⟩
theorem numericValid865 : certificate865.NumericValid := by decide +kernel
theorem sound865 : certificate865.Sound := rat_failure_budget_sound certificate865 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2168,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2169,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2170,List.forall_mem_nil _⟩⟩⟩) numericValid865

def certificate866 : RatFailureBudget := ⟨(5552046688682466891091/250000000000000000),(12992374411273/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay108.certificate2171),(2,CutFailureCertificates.Decay108.certificate2172),(2,CutFailureCertificates.Decay108.certificate2173)]⟩
theorem numericValid866 : certificate866.NumericValid := by decide +kernel
theorem sound866 : certificate866.Sound := rat_failure_budget_sound certificate866 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2171,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2172,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2173,List.forall_mem_nil _⟩⟩⟩) numericValid866

def certificate867 : RatFailureBudget := ⟨(5552046688682466891091/250000000000000000),(45707610940211/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay108.certificate2174),(2,CutFailureCertificates.Decay108.certificate2175)]⟩
theorem numericValid867 : certificate867.NumericValid := by decide +kernel
theorem sound867 : certificate867.Sound := rat_failure_budget_sound certificate867 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2174,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2175,List.forall_mem_nil _⟩⟩) numericValid867

def certificate868 : RatFailureBudget := ⟨(5552046688682466891091/250000000000000000),(894518082263017/200000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay108.certificate2176),(920,CutFailureCertificates.Decay108.certificate2177),(1,CutFailureCertificates.Decay108.certificate2178)]⟩
theorem numericValid868 : certificate868.NumericValid := by decide +kernel
theorem sound868 : certificate868.Sound := rat_failure_budget_sound certificate868 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2176,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2177,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2178,List.forall_mem_nil _⟩⟩⟩) numericValid868

def certificate869 : RatFailureBudget := ⟨(19580518535939935226393/1000000000000000000),(5843235513389/200000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay108.certificate2179),(2,CutFailureCertificates.Decay109.certificate2180),(2,CutFailureCertificates.Decay109.certificate2181)]⟩
theorem numericValid869 : certificate869.NumericValid := by decide +kernel
theorem sound869 : certificate869.Sound := rat_failure_budget_sound certificate869 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay108.sound2179,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2180,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2181,List.forall_mem_nil _⟩⟩⟩) numericValid869

def certificate870 : RatFailureBudget := ⟨(19580518535939935226393/1000000000000000000),(51657684898817/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay109.certificate2182),(2,CutFailureCertificates.Decay109.certificate2183)]⟩
theorem numericValid870 : certificate870.NumericValid := by decide +kernel
theorem sound870 : certificate870.Sound := rat_failure_budget_sound certificate870 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2182,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2183,List.forall_mem_nil _⟩⟩) numericValid870

def certificate871 : RatFailureBudget := ⟨(19580518535939935226393/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay109.certificate2184),(920,CutFailureCertificates.Decay109.certificate2185),(1,CutFailureCertificates.Decay109.certificate2186)]⟩
theorem numericValid871 : certificate871.NumericValid := by decide +kernel
theorem sound871 : certificate871.Sound := rat_failure_budget_sound certificate871 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2184,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2185,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2186,List.forall_mem_nil _⟩⟩⟩) numericValid871

def certificate872 : RatFailureBudget := ⟨(17383381910873022483903/1000000000000000000),(4920449571903/250000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay109.certificate2187),(2,CutFailureCertificates.Decay109.certificate2188),(2,CutFailureCertificates.Decay109.certificate2189)]⟩
theorem numericValid872 : certificate872.NumericValid := by decide +kernel
theorem sound872 : certificate872.Sound := rat_failure_budget_sound certificate872 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2187,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2188,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2189,List.forall_mem_nil _⟩⟩⟩) numericValid872

def certificate873 : RatFailureBudget := ⟨(17383381910873022483903/1000000000000000000),(4168420619211/1000000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay109.certificate2190),(2,CutFailureCertificates.Decay109.certificate2191)]⟩
theorem numericValid873 : certificate873.NumericValid := by decide +kernel
theorem sound873 : certificate873.Sound := rat_failure_budget_sound certificate873 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2190,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2191,List.forall_mem_nil _⟩⟩) numericValid873

def certificate874 : RatFailureBudget := ⟨(17383381910873022483903/1000000000000000000),(447258843902381/100000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay109.certificate2192),(918,CutFailureCertificates.Decay109.certificate2193),(1,CutFailureCertificates.Decay109.certificate2194)]⟩
theorem numericValid874 : certificate874.NumericValid := by decide +kernel
theorem sound874 : certificate874.Sound := rat_failure_budget_sound certificate874 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2192,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2193,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2194,List.forall_mem_nil _⟩⟩⟩) numericValid874

def certificate875 : RatFailureBudget := ⟨(7764035718697559137017/500000000000000000),(17965086929471/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay109.certificate2195),(2,CutFailureCertificates.Decay109.certificate2196),(2,CutFailureCertificates.Decay109.certificate2197)]⟩
theorem numericValid875 : certificate875.NumericValid := by decide +kernel
theorem sound875 : certificate875.Sound := rat_failure_budget_sound certificate875 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2195,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2196,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2197,List.forall_mem_nil _⟩⟩⟩) numericValid875

def certificate876 : RatFailureBudget := ⟨(7764035718697559137017/500000000000000000),(32327234062201/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay109.certificate2198),(2,CutFailureCertificates.Decay109.certificate2199)]⟩
theorem numericValid876 : certificate876.NumericValid := by decide +kernel
theorem sound876 : certificate876.Sound := rat_failure_budget_sound certificate876 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2198,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay109.sound2199,List.forall_mem_nil _⟩⟩) numericValid876

def certificate877 : RatFailureBudget := ⟨(7764035718697559137017/500000000000000000),(1118147109755953/250000000000000000),(1/500000000000000000),[(2,CutFailureCertificates.Decay110.certificate2200),(918,CutFailureCertificates.Decay110.certificate2201),(1,CutFailureCertificates.Decay110.certificate2202)]⟩
theorem numericValid877 : certificate877.NumericValid := by decide +kernel
theorem sound877 : certificate877.Sound := rat_failure_budget_sound certificate877 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2200,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2201,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2202,List.forall_mem_nil _⟩⟩⟩) numericValid877

def certificate878 : RatFailureBudget := ⟨(13947560834922328059369/1000000000000000000),(1476762143627/31250000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay110.certificate2203),(2,CutFailureCertificates.Decay110.certificate2204),(2,CutFailureCertificates.Decay110.certificate2205)]⟩
theorem numericValid878 : certificate878.NumericValid := by decide +kernel
theorem sound878 : certificate878.Sound := rat_failure_budget_sound certificate878 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2203,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2204,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2205,List.forall_mem_nil _⟩⟩⟩) numericValid878

def certificate879 : RatFailureBudget := ⟨(13947560834922328059369/1000000000000000000),(35854830013581/500000000000000000),(1/1000000000000000000),[(2,CutFailureCertificates.Decay110.certificate2206),(2,CutFailureCertificates.Decay110.certificate2207)]⟩
theorem numericValid879 : certificate879.NumericValid := by decide +kernel
theorem sound879 : certificate879.Sound := rat_failure_budget_sound certificate879 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2206,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay110.sound2207,List.forall_mem_nil _⟩⟩) numericValid879

end Cycle12.CutFailureCertificates.Budget043
