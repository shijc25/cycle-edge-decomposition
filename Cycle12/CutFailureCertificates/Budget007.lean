import Cycle12.RationalFailureBudget
import Cycle12.CutFailureCertificates.Decay017
import Cycle12.CutFailureCertificates.Decay018
import Cycle12.CutFailureCertificates.Decay019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutFailureCertificates.Budget007

def certificate140 : RatFailureBudget := ⟨(10468701106791427219/500000000000000000),(10063275870719433/500000000000000000),(223571553019110547/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate350),(2,CutFailureCertificates.Decay017.certificate351),(2,CutFailureCertificates.Decay017.certificate352)]⟩
theorem numericValid140 : certificate140.NumericValid := by decide +kernel
theorem sound140 : certificate140.Sound := rat_failure_budget_sound certificate140 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound350,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound351,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound352,List.forall_mem_nil _⟩⟩⟩) numericValid140

def certificate141 : RatFailureBudget := ⟨(10468701106791427219/500000000000000000),(8888823291350397/500000000000000000),(77038736091831/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate353),(2,CutFailureCertificates.Decay017.certificate354)]⟩
theorem numericValid141 : certificate141.NumericValid := by decide +kernel
theorem sound141 : certificate141.Sound := rat_failure_budget_sound certificate141 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound353,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound354,List.forall_mem_nil _⟩⟩) numericValid141

def certificate142 : RatFailureBudget := ⟨(4138340901353819989/200000000000000000),(20050049664025817/1000000000000000000),(214017898034825441/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate355),(2,CutFailureCertificates.Decay017.certificate356),(2,CutFailureCertificates.Decay017.certificate357)]⟩
theorem numericValid142 : certificate142.NumericValid := by decide +kernel
theorem sound142 : certificate142.Sound := rat_failure_budget_sound certificate142 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound355,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound356,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound357,List.forall_mem_nil _⟩⟩⟩) numericValid142

def certificate143 : RatFailureBudget := ⟨(4138340901353819989/200000000000000000),(1796332227833843/100000000000000000),(65533293079691/1000000000000000000),[(2,CutFailureCertificates.Decay017.certificate358),(2,CutFailureCertificates.Decay017.certificate359)]⟩
theorem numericValid143 : certificate143.NumericValid := by decide +kernel
theorem sound143 : certificate143.Sound := rat_failure_budget_sound certificate143 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound358,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay017.sound359,List.forall_mem_nil _⟩⟩) numericValid143

def certificate144 : RatFailureBudget := ⟨(20449941781027281327/1000000000000000000),(3982775620357481/200000000000000000),(99919977834362903/500000000000000000),[(2,CutFailureCertificates.Decay018.certificate360),(2,CutFailureCertificates.Decay018.certificate361),(2,CutFailureCertificates.Decay018.certificate362)]⟩
theorem numericValid144 : certificate144.NumericValid := by decide +kernel
theorem sound144 : certificate144.Sound := rat_failure_budget_sound certificate144 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound360,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound361,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound362,List.forall_mem_nil _⟩⟩⟩) numericValid144

def certificate145 : RatFailureBudget := ⟨(20449941781027281327/1000000000000000000),(18117614217914161/1000000000000000000),(668847202828469/1000000000000000000),[(2,CutFailureCertificates.Decay018.certificate363),(2,CutFailureCertificates.Decay018.certificate364)]⟩
theorem numericValid145 : certificate145.NumericValid := by decide +kernel
theorem sound145 : certificate145.Sound := rat_failure_budget_sound certificate145 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound363,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound364,List.forall_mem_nil _⟩⟩) numericValid145

def certificate146 : RatFailureBudget := ⟨(20212032053131816613/1000000000000000000),(20425738723373657/1000000000000000000),(184690648063167437/1000000000000000000),[(2,CutFailureCertificates.Decay018.certificate365),(2,CutFailureCertificates.Decay018.certificate366),(2,CutFailureCertificates.Decay018.certificate367)]⟩
theorem numericValid146 : certificate146.NumericValid := by decide +kernel
theorem sound146 : certificate146.Sound := rat_failure_budget_sound certificate146 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound365,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound366,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound367,List.forall_mem_nil _⟩⟩⟩) numericValid146

def certificate147 : RatFailureBudget := ⟨(20212032053131816613/1000000000000000000),(732152288714979/40000000000000000),(2790796534809/5000000000000000),[(2,CutFailureCertificates.Decay018.certificate368),(2,CutFailureCertificates.Decay018.certificate369)]⟩
theorem numericValid147 : certificate147.NumericValid := by decide +kernel
theorem sound147 : certificate147.Sound := rat_failure_budget_sound certificate147 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound368,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound369,List.forall_mem_nil _⟩⟩) numericValid147

def certificate148 : RatFailureBudget := ⟨(1248618465522332407/62500000000000000),(5129546907215903/250000000000000000),(183404128588824097/1000000000000000000),[(2,CutFailureCertificates.Decay018.certificate370),(2,CutFailureCertificates.Decay018.certificate371),(2,CutFailureCertificates.Decay018.certificate372)]⟩
theorem numericValid148 : certificate148.NumericValid := by decide +kernel
theorem sound148 : certificate148.Sound := rat_failure_budget_sound certificate148 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound370,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound371,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound372,List.forall_mem_nil _⟩⟩⟩) numericValid148

def certificate149 : RatFailureBudget := ⟨(1248618465522332407/62500000000000000),(184548598738167/10000000000000000),(121644879833323/250000000000000000),[(2,CutFailureCertificates.Decay018.certificate373),(2,CutFailureCertificates.Decay018.certificate374)]⟩
theorem numericValid149 : certificate149.NumericValid := by decide +kernel
theorem sound149 : certificate149.Sound := rat_failure_budget_sound certificate149 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound373,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound374,List.forall_mem_nil _⟩⟩) numericValid149

def certificate150 : RatFailureBudget := ⟨(1974745413596958271/100000000000000000),(10374564181944717/500000000000000000),(89276567900235313/500000000000000000),[(2,CutFailureCertificates.Decay018.certificate375),(2,CutFailureCertificates.Decay018.certificate376),(2,CutFailureCertificates.Decay018.certificate377)]⟩
theorem numericValid150 : certificate150.NumericValid := by decide +kernel
theorem sound150 : certificate150.Sound := rat_failure_budget_sound certificate150 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound375,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound376,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound377,List.forall_mem_nil _⟩⟩⟩) numericValid150

def certificate151 : RatFailureBudget := ⟨(1974745413596958271/100000000000000000),(1864303341249787/100000000000000000),(40792428228269/100000000000000000),[(2,CutFailureCertificates.Decay018.certificate378),(2,CutFailureCertificates.Decay018.certificate379)]⟩
theorem numericValid151 : certificate151.NumericValid := by decide +kernel
theorem sound151 : certificate151.Sound := rat_failure_budget_sound certificate151 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound378,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay018.sound379,List.forall_mem_nil _⟩⟩) numericValid151

def certificate152 : RatFailureBudget := ⟨(4880158066750713963/250000000000000000),(5207208264857873/250000000000000000),(81449923005559299/500000000000000000),[(2,CutFailureCertificates.Decay019.certificate380),(2,CutFailureCertificates.Decay019.certificate381),(2,CutFailureCertificates.Decay019.certificate382)]⟩
theorem numericValid152 : certificate152.NumericValid := by decide +kernel
theorem sound152 : certificate152.Sound := rat_failure_budget_sound certificate152 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound380,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound381,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound382,List.forall_mem_nil _⟩⟩⟩) numericValid152

def certificate153 : RatFailureBudget := ⟨(4880158066750713963/250000000000000000),(9397822403960629/500000000000000000),(342574232301599/1000000000000000000),[(2,CutFailureCertificates.Decay019.certificate383),(2,CutFailureCertificates.Decay019.certificate384)]⟩
theorem numericValid153 : certificate153.NumericValid := by decide +kernel
theorem sound153 : certificate153.Sound := rat_failure_budget_sound certificate153 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound383,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound384,List.forall_mem_nil _⟩⟩) numericValid153

def certificate154 : RatFailureBudget := ⟨(120608474463946003/6250000000000000),(10841327163949979/500000000000000000),(158904502546774237/1000000000000000000),[(2,CutFailureCertificates.Decay019.certificate385),(2,CutFailureCertificates.Decay019.certificate386),(2,CutFailureCertificates.Decay019.certificate387)]⟩
theorem numericValid154 : certificate154.NumericValid := by decide +kernel
theorem sound154 : certificate154.Sound := rat_failure_budget_sound certificate154 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound385,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound386,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound387,List.forall_mem_nil _⟩⟩⟩) numericValid154

def certificate155 : RatFailureBudget := ⟨(120608474463946003/6250000000000000),(3797154904345189/200000000000000000),(302924164848669/1000000000000000000),[(2,CutFailureCertificates.Decay019.certificate388),(2,CutFailureCertificates.Decay019.certificate389)]⟩
theorem numericValid155 : certificate155.NumericValid := by decide +kernel
theorem sound155 : certificate155.Sound := rat_failure_budget_sound certificate155 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound388,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound389,List.forall_mem_nil _⟩⟩) numericValid155

def certificate156 : RatFailureBudget := ⟨(19077553014247196799/1000000000000000000),(10569345984730369/500000000000000000),(148663785010667713/1000000000000000000),[(2,CutFailureCertificates.Decay019.certificate390),(2,CutFailureCertificates.Decay019.certificate391),(2,CutFailureCertificates.Decay019.certificate392)]⟩
theorem numericValid156 : certificate156.NumericValid := by decide +kernel
theorem sound156 : certificate156.Sound := rat_failure_budget_sound certificate156 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound390,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound391,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound392,List.forall_mem_nil _⟩⟩⟩) numericValid156

def certificate157 : RatFailureBudget := ⟨(19077553014247196799/1000000000000000000),(3827789131151949/200000000000000000),(63823348845831/250000000000000000),[(2,CutFailureCertificates.Decay019.certificate393),(2,CutFailureCertificates.Decay019.certificate394)]⟩
theorem numericValid157 : certificate157.NumericValid := by decide +kernel
theorem sound157 : certificate157.Sound := rat_failure_budget_sound certificate157 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound393,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound394,List.forall_mem_nil _⟩⟩) numericValid157

def certificate158 : RatFailureBudget := ⟨(18861153311560677731/1000000000000000000),(10622878262812281/500000000000000000),(619033417668128553/1000000000000000000),[(2,CutFailureCertificates.Decay019.certificate395),(2,CutFailureCertificates.Decay019.certificate396),(2,CutFailureCertificates.Decay019.certificate397)]⟩
theorem numericValid158 : certificate158.NumericValid := by decide +kernel
theorem sound158 : certificate158.Sound := rat_failure_budget_sound certificate158 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound395,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound396,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound397,List.forall_mem_nil _⟩⟩⟩) numericValid158

def certificate159 : RatFailureBudget := ⟨(18861153311560677731/1000000000000000000),(4823179329440131/250000000000000000),(8076020475841/31250000000000000),[(2,CutFailureCertificates.Decay019.certificate398),(2,CutFailureCertificates.Decay019.certificate399)]⟩
theorem numericValid159 : certificate159.NumericValid := by decide +kernel
theorem sound159 : certificate159.Sound := rat_failure_budget_sound certificate159 (List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound398,List.forall_mem_cons.mpr ⟨CutFailureCertificates.Decay019.sound399,List.forall_mem_nil _⟩⟩) numericValid159

end Cycle12.CutFailureCertificates.Budget007
