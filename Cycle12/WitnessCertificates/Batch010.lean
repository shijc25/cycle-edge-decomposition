import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch010

def certificate200 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope200,(97803/50000),(138520313/1000000000),(215533313156228691711/1000000000000000000),(2178439071/1000000000),(43/20),(377874031/1000000000),0,1,(5028274467672051/200000000000000000)⟩
theorem valid200 : certificate200.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid200,?_⟩
  decide +kernel
theorem sound200 : certificate200.Sound :=
  rat_witness_certificate_sound certificate200 valid200 MajorityCertificates.Inputs010.envelope_sound200

def certificate201 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope201,(97803/50000),(138520313/1000000000),(215533313156228691711/1000000000000000000),(1265750801/500000000),(43/20),(679098509/500000000),0,(566524912094415293/500000000000000000),(366721214646767/15625000000000000)⟩
theorem valid201 : certificate201.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid201,?_⟩
  decide +kernel
theorem sound201 : certificate201.Sound :=
  rat_witness_certificate_sound certificate201 valid201 MajorityCertificates.Inputs010.envelope_sound201

def certificate202 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope202,(196449/100000),(16851853/125000000),(53717100140915108179/250000000000000000),(2190662991/1000000000),(43/20),(14610681/40000000),0,1,(25218634264699189/1000000000000000000)⟩
theorem valid202 : certificate202.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid202,?_⟩
  decide +kernel
theorem sound202 : certificate202.Sound :=
  rat_witness_certificate_sound certificate202 valid202 MajorityCertificates.Inputs010.envelope_sound202

def certificate203 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope203,(196449/100000),(16851853/125000000),(53717100140915108179/250000000000000000),(633151481/250000000),(43/20),(1356709683/1000000000),0,(113304003014566229/100000000000000000),(23615991734710809/1000000000000000000)⟩
theorem valid203 : certificate203.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid203,?_⟩
  decide +kernel
theorem sound203 : certificate203.Sound :=
  rat_witness_certificate_sound certificate203 valid203 MajorityCertificates.Inputs010.envelope_sound203

def certificate204 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope204,(196373/100000),(134492559/1000000000),(106796751771871583253/500000000000000000),(219146261/100000000),(43/20),(364428023/1000000000),0,1,(5092293921271877/200000000000000000)⟩
theorem valid204 : certificate204.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid204,?_⟩
  decide +kernel
theorem sound204 : certificate204.Sound :=
  rat_witness_certificate_sound certificate204 valid204 MajorityCertificates.Inputs010.envelope_sound204

def certificate205 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope205,(196373/100000),(134492559/1000000000),(106796751771871583253/500000000000000000),(316749959/125000000),(43/20),(1357586161/1000000000),0,(283272858850765137/250000000000000000),(23821198007354921/1000000000000000000)⟩
theorem valid205 : certificate205.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid205,?_⟩
  decide +kernel
theorem sound205 : certificate205.Sound :=
  rat_witness_certificate_sound certificate205 valid205 MajorityCertificates.Inputs010.envelope_sound205

def certificate206 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope206,(98149/50000),(134170293/1000000000),(106168057433297533833/500000000000000000),(2196225939/1000000000),(43/20),(363235387/1000000000),0,1,(25590551318821967/1000000000000000000)⟩
theorem valid206 : certificate206.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid206,?_⟩
  decide +kernel
theorem sound206 : certificate206.Sound :=
  rat_witness_certificate_sound certificate206 valid206 MajorityCertificates.Inputs010.envelope_sound206

def certificate207 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope207,(98149/50000),(134170293/1000000000),(106168057433297533833/500000000000000000),(2536176841/1000000000),(43/20),(1358055933/1000000000),0,(226628549435977961/200000000000000000),(2998251684220911/125000000000000000)⟩
theorem valid207 : certificate207.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid207,?_⟩
  decide +kernel
theorem sound207 : certificate207.Sound :=
  rat_witness_certificate_sound certificate207 valid207 MajorityCertificates.Inputs010.envelope_sound207

def certificate208 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope208,(6132/3125),(133767461/1000000000),(211095948276747537531/1000000000000000000),(2200167577/1000000000),(43/20),(361883841/1000000000),0,1,(5146805500410207/200000000000000000)⟩
theorem valid208 : certificate208.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid208,?_⟩
  decide +kernel
theorem sound208 : certificate208.Sound :=
  rat_witness_certificate_sound certificate208 valid208 MajorityCertificates.Inputs010.envelope_sound208

def certificate209 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope209,(6132/3125),(133767461/1000000000),(211095948276747537531/1000000000000000000),(1269354761/500000000),(43/20),(1358422817/1000000000),0,(1133193962032667881/1000000000000000000),(24141456833076291/1000000000000000000)⟩
theorem valid209 : certificate209.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid209,?_⟩
  decide +kernel
theorem sound209 : certificate209.Sound :=
  rat_witness_certificate_sound certificate209 valid209 MajorityCertificates.Inputs010.envelope_sound209

def certificate210 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope210,(196151/100000),(26689039/200000000),(52468180930640026063/250000000000000000),(1101223253/500000000),(43/20),(360913181/1000000000),0,1,(12967204058596549/500000000000000000)⟩
theorem valid210 : certificate210.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid210,?_⟩
  decide +kernel
theorem sound210 : certificate210.Sound :=
  rat_witness_certificate_sound certificate210 valid210 MajorityCertificates.Inputs010.envelope_sound210

def certificate211 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope211,(196151/100000),(26689039/200000000),(52468180930640026063/250000000000000000),(253984051/100000000),(43/20),(271884527/200000000),0,(566622538260341929/500000000000000000),(12180050293336571/500000000000000000)⟩
theorem valid211 : certificate211.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid211,?_⟩
  decide +kernel
theorem sound211 : certificate211.Sound :=
  rat_witness_certificate_sound certificate211 valid211 MajorityCertificates.Inputs010.envelope_sound211

def certificate212 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope212,(196153/100000),(13312293/100000000),(41915401615407667629/200000000000000000),(4312172/1953125),(43/20),(359582909/1000000000),0,1,(6503243057320883/250000000000000000)⟩
theorem valid212 : certificate212.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid212,?_⟩
  decide +kernel
theorem sound212 : certificate212.Sound :=
  rat_witness_certificate_sound certificate212 valid212 MajorityCertificates.Inputs010.envelope_sound212

def certificate213 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope213,(196153/100000),(13312293/100000000),(41915401615407667629/200000000000000000),(635541657/250000000),(43/20),(271767489/200000000),0,(226651338420690949/200000000000000000),(12192356822380207/500000000000000000)⟩
theorem valid213 : certificate213.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid213,?_⟩
  decide +kernel
theorem sound213 : certificate213.Sound :=
  rat_witness_certificate_sound certificate213 valid213 MajorityCertificates.Inputs010.envelope_sound213

def certificate214 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope214,(196117/100000),(132961797/1000000000),(104487659163103801799/500000000000000000),(441533159/200000000),(43/20),(359181889/1000000000),0,1,(2604106471810297/100000000000000000)⟩
theorem valid214 : certificate214.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid214,?_⟩
  decide +kernel
theorem sound214 : certificate214.Sound :=
  rat_witness_certificate_sound certificate214 valid214 MajorityCertificates.Inputs010.envelope_sound214

def certificate215 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope215,(196117/100000),(132961797/1000000000),(104487659163103801799/500000000000000000),(254336667/100000000),(43/20),(33975251/25000000),0,(566641064886584147/500000000000000000),(24461580055877939/1000000000000000000)⟩
theorem valid215 : certificate215.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid215,?_⟩
  decide +kernel
theorem sound215 : certificate215.Sound :=
  rat_witness_certificate_sound certificate215 valid215 MajorityCertificates.Inputs010.envelope_sound215

def certificate216 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope216,(196007/100000),(66360049/500000000),(41495202117139022471/200000000000000000),(2203887557/1000000000),(11/5),(359022819/1000000000),0,1,(2646066731925093/100000000000000000)⟩
theorem valid216 : certificate216.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid216,?_⟩
  decide +kernel
theorem sound216 : certificate216.Sound :=
  rat_witness_certificate_sound certificate216 valid216 MajorityCertificates.Inputs010.envelope_sound216

def certificate217 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope217,(196007/100000),(66360049/500000000),(41495202117139022471/200000000000000000),(636123933/250000000),(11/5),(54483937/40000000),0,(28333675837146063/25000000000000000),(12369596294491491/500000000000000000)⟩
theorem valid217 : certificate217.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid217,?_⟩
  decide +kernel
theorem sound217 : certificate217.Sound :=
  rat_witness_certificate_sound certificate217 valid217 MajorityCertificates.Inputs010.envelope_sound217

def certificate218 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs010.envelope218,(6123/3125),(66158633/500000000),(51575497878328939587/250000000000000000),(2211492691/1000000000),(11/5),(89337213/250000000),0,1,(26468476551133621/1000000000000000000)⟩
theorem valid218 : certificate218.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid218,?_⟩
  decide +kernel
theorem sound218 : certificate218.Sound :=
  rat_witness_certificate_sound certificate218 valid218 MajorityCertificates.Inputs010.envelope_sound218

def certificate219 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs010.envelope219,(6123/3125),(66158633/500000000),(51575497878328939587/250000000000000000),(1273539863/500000000),(11/5),(272488747/200000000),0,(70837366853343609/62500000000000000),(1244630110326721/50000000000000000)⟩
theorem valid219 : certificate219.Valid := by
  refine ⟨MajorityCertificates.Inputs010.inputs_valid219,?_⟩
  decide +kernel
theorem sound219 : certificate219.Sound :=
  rat_witness_certificate_sound certificate219 valid219 MajorityCertificates.Inputs010.envelope_sound219

def certificates : List RatWitnessCertificate := [certificate200,certificate201,certificate202,certificate203,certificate204,certificate205,certificate206,certificate207,certificate208,certificate209,certificate210,certificate211,certificate212,certificate213,certificate214,certificate215,certificate216,certificate217,certificate218,certificate219]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound200,List.forall_mem_cons.mpr ⟨sound201,List.forall_mem_cons.mpr ⟨sound202,List.forall_mem_cons.mpr ⟨sound203,List.forall_mem_cons.mpr ⟨sound204,List.forall_mem_cons.mpr ⟨sound205,List.forall_mem_cons.mpr ⟨sound206,List.forall_mem_cons.mpr ⟨sound207,List.forall_mem_cons.mpr ⟨sound208,List.forall_mem_cons.mpr ⟨sound209,List.forall_mem_cons.mpr ⟨sound210,List.forall_mem_cons.mpr ⟨sound211,List.forall_mem_cons.mpr ⟨sound212,List.forall_mem_cons.mpr ⟨sound213,List.forall_mem_cons.mpr ⟨sound214,List.forall_mem_cons.mpr ⟨sound215,List.forall_mem_cons.mpr ⟨sound216,List.forall_mem_cons.mpr ⟨sound217,List.forall_mem_cons.mpr ⟨sound218,List.forall_mem_cons.mpr ⟨sound219,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch010
