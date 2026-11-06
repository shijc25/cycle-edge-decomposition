import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch004

def certificate80 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope80,(6399/3125),(150122441/1000000000),(201006317128626647647/500000000000000000),(504559869/250000000),(9/5),(206190691/500000000),0,1,(2629018621975111/200000000000000000)⟩
theorem valid80 : certificate80.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid80,?_⟩
  decide +kernel
theorem sound80 : certificate80.Sound :=
  rat_witness_certificate_sound certificate80 valid80 MajorityCertificates.Inputs004.envelope_sound80

def certificate81 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope81,(6399/3125),(150122441/1000000000),(201006317128626647647/500000000000000000),(601040497/250000000),(9/5),(5073417/3906250),0,(22582230787210047/20000000000000000),(10833550643570369/1000000000000000000)⟩
theorem valid81 : certificate81.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid81,?_⟩
  decide +kernel
theorem sound81 : certificate81.Sound :=
  rat_witness_certificate_sound certificate81 valid81 MajorityCertificates.Inputs004.envelope_sound81

def certificate82 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope82,(204587/100000),(74940371/500000000),(395155788030754533383/1000000000000000000),(506294701/250000000),(9/5),(102762443/250000000),0,1,(12775448736124257/1000000000000000000)⟩
theorem valid82 : certificate82.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid82,?_⟩
  decide +kernel
theorem sound82 : certificate82.Sound :=
  rat_witness_certificate_sound certificate82 valid82 MajorityCertificates.Inputs004.envelope_sound82

def certificate83 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope83,(204587/100000),(74940371/500000000),(395155788030754533383/1000000000000000000),(240971381/100000000),(9/5),(1298279309/1000000000),0,(564593400810714611/500000000000000000),(11049719882304171/1000000000000000000)⟩
theorem valid83 : certificate83.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid83,?_⟩
  decide +kernel
theorem sound83 : certificate83.Sound :=
  rat_witness_certificate_sound certificate83 valid83 MajorityCertificates.Inputs004.envelope_sound83

def certificate84 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope84,(204299/100000),(9362511/62500000),(193348572747214585511/500000000000000000),(405668639/200000000),(9/5),(411010793/1000000000),0,1,(6667288727164741/500000000000000000)⟩
theorem valid84 : certificate84.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid84,?_⟩
  decide +kernel
theorem sound84 : certificate84.Sound :=
  rat_witness_certificate_sound certificate84 valid84 MajorityCertificates.Inputs004.envelope_sound84

def certificate85 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope85,(204299/100000),(9362511/62500000),(193348572747214585511/500000000000000000),(301612827/125000000),(9/5),(1299431283/1000000000),0,(56464235214355567/50000000000000000),(11328473703785713/1000000000000000000)⟩
theorem valid85 : certificate85.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid85,?_⟩
  decide +kernel
theorem sound85 : certificate85.Sound :=
  rat_witness_certificate_sound certificate85 valid85 MajorityCertificates.Inputs004.envelope_sound85

def certificate86 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope86,(40803/20000),(149639043/1000000000),(75711793260584595709/200000000000000000),(2021127257/1000000000),(9/5),(411748573/1000000000),0,1,(13621866736788031/1000000000000000000)⟩
theorem valid86 : certificate86.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid86,?_⟩
  decide +kernel
theorem sound86 : certificate86.Sound :=
  rat_witness_certificate_sound certificate86 valid86 MajorityCertificates.Inputs004.envelope_sound86

def certificate87 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope87,(40803/20000),(149639043/1000000000),(75711793260584595709/200000000000000000),(48317409/20000000),(9/5),(650372249/500000000),0,(1129383206154022961/1000000000000000000),(1452244448909963/125000000000000000)⟩
theorem valid87 : certificate87.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid87,?_⟩
  decide +kernel
theorem sound87 : certificate87.Sound :=
  rat_witness_certificate_sound certificate87 valid87 MajorityCertificates.Inputs004.envelope_sound87

def certificate88 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope88,(25467/12500),(14947791/100000000),(185362666901472325183/500000000000000000),(2022797807/1000000000),(9/5),(411532973/1000000000),0,1,(13894742652031287/1000000000000000000)⟩
theorem valid88 : certificate88.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid88,?_⟩
  decide +kernel
theorem sound88 : certificate88.Sound :=
  rat_witness_certificate_sound certificate88 valid88 MajorityCertificates.Inputs004.envelope_sound88

def certificate89 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope89,(25467/12500),(14947791/100000000),(185362666901472325183/500000000000000000),(120955163/50000000),(9/5),(325481137/250000000),0,(1129482260874694419/1000000000000000000),(11903381040463489/1000000000000000000)⟩
theorem valid89 : certificate89.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid89,?_⟩
  decide +kernel
theorem sound89 : certificate89.Sound :=
  rat_witness_certificate_sound certificate89 valid89 MajorityCertificates.Inputs004.envelope_sound89

def certificate90 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope90,(10173/5000),(149316777/1000000000),(14527252830750459517/40000000000000000),(2028299077/1000000000),(9/5),(82184363/200000000),0,1,(7109919609915963/500000000000000000)⟩
theorem valid90 : certificate90.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid90,?_⟩
  decide +kernel
theorem sound90 : certificate90.Sound :=
  rat_witness_certificate_sound certificate90 valid90 MajorityCertificates.Inputs004.envelope_sound90

def certificate91 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope91,(10173/5000),(149316777/1000000000),(14527252830750459517/40000000000000000),(605578807/250000000),(9/5),(651557011/500000000),0,(282395471898330041/250000000000000000),(3047899281067909/250000000000000000)⟩
theorem valid91 : certificate91.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid91,?_⟩
  decide +kernel
theorem sound91 : certificate91.Sound :=
  rat_witness_certificate_sound certificate91 valid91 MajorityCertificates.Inputs004.envelope_sound91

def certificate92 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope92,(203189/100000),(74537539/500000000),(71182583261338560763/200000000000000000),(507830937/250000000),(37/20),(410467407/1000000000),0,1,(14968935979477859/1000000000000000000)⟩
theorem valid92 : certificate92.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid92,?_⟩
  decide +kernel
theorem sound92 : certificate92.Sound :=
  rat_witness_certificate_sound certificate92 valid92 MajorityCertificates.Inputs004.envelope_sound92

def certificate93 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope93,(203189/100000),(74537539/500000000),(71182583261338560763/200000000000000000),(2425575183/1000000000),(37/20),(261052383/200000000),0,(225936403397072307/200000000000000000),(2500793808381299/200000000000000000)⟩
theorem valid93 : certificate93.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid93,?_⟩
  decide +kernel
theorem sound93 : certificate93.Sound :=
  rat_witness_certificate_sound certificate93 valid93 MajorityCertificates.Inputs004.envelope_sound93

def certificate94 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope94,(202921/100000),(29782789/200000000),(21806684937427826307/62500000000000000),(1017763507/500000000),(37/20),(102462493/250000000),0,1,(7425470907306759/500000000000000000)⟩
theorem valid94 : certificate94.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid94,?_⟩
  decide +kernel
theorem sound94 : certificate94.Sound :=
  rat_witness_certificate_sound certificate94 valid94 MajorityCertificates.Inputs004.envelope_sound94

def certificate95 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope95,(202921/100000),(29782789/200000000),(21806684937427826307/62500000000000000),(75899869/31250000),(37/20),(261291689/200000000),0,(56489133495753931/50000000000000000),(12797195991526991/1000000000000000000)⟩
theorem valid95 : certificate95.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid95,?_⟩
  decide +kernel
theorem sound95 : certificate95.Sound :=
  rat_witness_certificate_sound certificate95 valid95 MajorityCertificates.Inputs004.envelope_sound95

def certificate96 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope96,(202657/100000),(74336123/500000000),(342151075683948305859/1000000000000000000),(203857971/100000000),(37/20),(51163223/125000000),0,1,(3835898736562463/250000000000000000)⟩
theorem valid96 : certificate96.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid96,?_⟩
  decide +kernel
theorem sound96 : certificate96.Sound :=
  rat_witness_certificate_sound certificate96 valid96 MajorityCertificates.Inputs004.envelope_sound96

def certificate97 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope97,(202657/100000),(74336123/500000000),(342151075683948305859/1000000000000000000),(2432108351/1000000000),(37/20),(1307670277/1000000000),0,(225976759754452329/200000000000000000),(6546955931491901/500000000000000000)⟩
theorem valid97 : certificate97.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid97,?_⟩
  decide +kernel
theorem sound97 : certificate97.Sound :=
  rat_witness_certificate_sound certificate97 valid97 MajorityCertificates.Inputs004.envelope_sound97

def certificate98 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs004.envelope98,(202397/100000),(148430547/1000000000),(335633625337807551309/1000000000000000000),(1020615649/500000000),(37/20),(204417679/500000000),0,1,(15950810463922627/1000000000000000000)⟩
theorem valid98 : certificate98.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid98,?_⟩
  decide +kernel
theorem sound98 : certificate98.Sound :=
  rat_witness_certificate_sound certificate98 valid98 MajorityCertificates.Inputs004.envelope_sound98

def certificate99 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs004.envelope99,(202397/100000),(148430547/1000000000),(335633625337807551309/1000000000000000000),(2434976473/1000000000),(37/20),(1309085269/1000000000),0,(1129985378363555507/1000000000000000000),(13404455762886387/1000000000000000000)⟩
theorem valid99 : certificate99.Valid := by
  refine ⟨MajorityCertificates.Inputs004.inputs_valid99,?_⟩
  decide +kernel
theorem sound99 : certificate99.Sound :=
  rat_witness_certificate_sound certificate99 valid99 MajorityCertificates.Inputs004.envelope_sound99

def certificates : List RatWitnessCertificate := [certificate80,certificate81,certificate82,certificate83,certificate84,certificate85,certificate86,certificate87,certificate88,certificate89,certificate90,certificate91,certificate92,certificate93,certificate94,certificate95,certificate96,certificate97,certificate98,certificate99]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound80,List.forall_mem_cons.mpr ⟨sound81,List.forall_mem_cons.mpr ⟨sound82,List.forall_mem_cons.mpr ⟨sound83,List.forall_mem_cons.mpr ⟨sound84,List.forall_mem_cons.mpr ⟨sound85,List.forall_mem_cons.mpr ⟨sound86,List.forall_mem_cons.mpr ⟨sound87,List.forall_mem_cons.mpr ⟨sound88,List.forall_mem_cons.mpr ⟨sound89,List.forall_mem_cons.mpr ⟨sound90,List.forall_mem_cons.mpr ⟨sound91,List.forall_mem_cons.mpr ⟨sound92,List.forall_mem_cons.mpr ⟨sound93,List.forall_mem_cons.mpr ⟨sound94,List.forall_mem_cons.mpr ⟨sound95,List.forall_mem_cons.mpr ⟨sound96,List.forall_mem_cons.mpr ⟨sound97,List.forall_mem_cons.mpr ⟨sound98,List.forall_mem_cons.mpr ⟨sound99,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch004
