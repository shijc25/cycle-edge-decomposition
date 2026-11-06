import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch048

def certificate960 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope960,(47/20),(3631/20000),(35594456451166953387459/1000000000000000000),(219226907/125000000),32,(7575197/5000000),0,(562520174634184237/500000000000000000),(71720681717887/250000000000000000)⟩
theorem valid960 : certificate960.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid960,?_⟩
  decide +kernel
theorem sound960 : certificate960.Sound :=
  rat_witness_certificate_sound certificate960 valid960 MajorityCertificates.Inputs048.envelope_sound960

def certificate961 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope961,(47/20),(31/100),(35594456451166953387459/1000000000000000000),(1831684543/1000000000),32,(1007000243/1000000000),(374239673430705167/1000000000000000000),1,(4472828072356481/1000000000000000000)⟩
theorem valid961 : certificate961.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid961,?_⟩
  decide +kernel
theorem sound961 : certificate961.Sound :=
  rat_witness_certificate_sound certificate961 valid961 MajorityCertificates.Inputs048.envelope_sound961

def certificate962 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope962,(47/20),(91/500),(35328760435458533561193/1000000000000000000),(943673171/500000000),32,(120094613/250000000),0,1,(133529817133571/1000000000000000000)⟩
theorem valid962 : certificate962.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid962,?_⟩
  decide +kernel
theorem sound962 : certificate962.Sound :=
  rat_witness_certificate_sound certificate962 valid962 MajorityCertificates.Inputs048.envelope_sound962

def certificate963 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope963,(47/20),(91/500),(35328760435458533561193/1000000000000000000),(14016953/8000000),32,(758257347/500000000),0,(1125040652730505799/1000000000000000000),(276765221427569/1000000000000000000)⟩
theorem valid963 : certificate963.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid963,?_⟩
  decide +kernel
theorem sound963 : certificate963.Sound :=
  rat_witness_certificate_sound certificate963 valid963 MajorityCertificates.Inputs048.envelope_sound963

def certificate964 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope964,(47/20),(31/100),(35328760435458533561193/1000000000000000000),(1835874411/1000000000),32,(1007/1000),(74765546216776447/200000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid964 : certificate964.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid964,?_⟩
  decide +kernel
theorem sound964 : certificate964.Sound :=
  rat_witness_certificate_sound certificate964 valid964 MajorityCertificates.Inputs048.envelope_sound964

def certificate965 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope965,(47/20),(7289/40000),(17490523395247794866119/500000000000000000),(1888012387/1000000000),32,(24048083/50000000),0,1,(33707269966807/250000000000000000)⟩
theorem valid965 : certificate965.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid965,?_⟩
  decide +kernel
theorem sound965 : certificate965.Sound :=
  rat_witness_certificate_sound certificate965 valid965 MajorityCertificates.Inputs048.envelope_sound965

def certificate966 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope966,(47/20),(7289/40000),(17490523395247794866119/500000000000000000),(1752555053/1000000000),32,(1515780211/1000000000),0,(140630132104060959/125000000000000000),(294653097469227/1000000000000000000)⟩
theorem valid966 : certificate966.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid966,?_⟩
  decide +kernel
theorem sound966 : certificate966.Sound :=
  rat_witness_certificate_sound certificate966 valid966 MajorityCertificates.Inputs048.envelope_sound966

def certificate967 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope967,(47/20),(31/100),(17490523395247794866119/500000000000000000),(367569087/200000000),32,(1007/1000),(186817698299259089/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid967 : certificate967.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid967,?_⟩
  decide +kernel
theorem sound967 : certificate967.Sound :=
  rat_witness_certificate_sound certificate967 valid967 MajorityCertificates.Inputs048.envelope_sound967

def certificate968 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope968,(47/20),(3649/20000),(34639596741050693742707/1000000000000000000),(944530561/500000000),32,(60188191/125000000),0,1,(2129492229331/15625000000000000)⟩
theorem valid968 : certificate968.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid968,?_⟩
  decide +kernel
theorem sound968 : certificate968.Sound :=
  rat_witness_certificate_sound certificate968 valid968 MajorityCertificates.Inputs048.envelope_sound968

def certificate969 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope969,(47/20),(3649/20000),(34639596741050693742707/1000000000000000000),(1752589239/1000000000),32,(47359597/31250000),0,(1125041461550228277/1000000000000000000),(298150754798389/1000000000000000000)⟩
theorem valid969 : certificate969.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid969,?_⟩
  decide +kernel
theorem sound969 : certificate969.Sound :=
  rat_witness_certificate_sound certificate969 valid969 MajorityCertificates.Inputs048.envelope_sound969

def certificate970 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope970,(47/20),(31/100),(34639596741050693742707/1000000000000000000),(57514443/31250000),32,(1007/1000),(93345336940389403/250000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid970 : certificate970.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid970,?_⟩
  decide +kernel
theorem sound970 : certificate970.Sound :=
  rat_witness_certificate_sound certificate970 valid970 MajorityCertificates.Inputs048.envelope_sound970

def certificate971 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope971,(47/20),(7307/40000),(17257197573927185931247/500000000000000000),(945049931/500000000),32,(482050459/1000000000),0,1,(136739177966079/1000000000000000000)⟩
theorem valid971 : certificate971.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid971,?_⟩
  decide +kernel
theorem sound971 : certificate971.Sound :=
  rat_witness_certificate_sound certificate971 valid971 MajorityCertificates.Inputs048.envelope_sound971

def certificate972 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope972,(47/20),(7307/40000),(17257197573927185931247/500000000000000000),(219066803/125000000),32,(1515300917/1000000000),0,(562520805978539581/500000000000000000),(299940999249373/1000000000000000000)⟩
theorem valid972 : certificate972.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid972,?_⟩
  decide +kernel
theorem sound972 : certificate972.Sound :=
  rat_witness_certificate_sound certificate972 valid972 MajorityCertificates.Inputs048.envelope_sound972

def certificate973 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope973,(47/20),(31/100),(17257197573927185931247/500000000000000000),(1842108969/1000000000),32,(1007/1000),(186611107348776169/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid973 : certificate973.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid973,?_⟩
  decide +kernel
theorem sound973 : certificate973.Sound :=
  rat_witness_certificate_sound certificate973 valid973 MajorityCertificates.Inputs048.envelope_sound973

def certificate974 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope974,(47/20),(14623/80000),(17173662233480934388993/500000000000000000),(94526833/50000000),32,(96466363/200000000),0,1,(68704406545009/500000000000000000)⟩
theorem valid974 : certificate974.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid974,?_⟩
  decide +kernel
theorem sound974 : certificate974.Sound :=
  rat_witness_certificate_sound certificate974 valid974 MajorityCertificates.Inputs048.envelope_sound974

def certificate975 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope975,(47/20),(14623/80000),(17173662233480934388993/500000000000000000),(1752397383/1000000000),32,(303069579/200000000),0,(281260453592476057/250000000000000000),(479982913267/1600000000000000)⟩
theorem valid975 : certificate975.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid975,?_⟩
  decide +kernel
theorem sound975 : certificate975.Sound :=
  rat_witness_certificate_sound certificate975 valid975 MajorityCertificates.Inputs048.envelope_sound975

def certificate976 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope976,(47/20),(31/100),(17173662233480934388993/500000000000000000),(921562301/500000000),32,(40280001/40000000),(93281100727309531/250000000000000000),1,(4472613092664197/1000000000000000000)⟩
theorem valid976 : certificate976.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid976,?_⟩
  decide +kernel
theorem sound976 : certificate976.Sound :=
  rat_witness_certificate_sound certificate976 valid976 MajorityCertificates.Inputs048.envelope_sound976

def certificate977 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs048.envelope977,(47/20),(1899/10000),(32772344532278908303541/1000000000000000000),(467004737/250000000),32,(126384051/250000000),0,1,(146523993265823/1000000000000000000)⟩
theorem valid977 : certificate977.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid977,?_⟩
  decide +kernel
theorem sound977 : certificate977.Sound :=
  rat_witness_certificate_sound certificate977 valid977 MajorityCertificates.Inputs048.envelope_sound977

def certificate978 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs048.envelope978,(47/20),(1899/10000),(32772344532278908303541/1000000000000000000),(1744278153/1000000000),32,(758172013/500000000),0,(281260955988549963/250000000000000000),(317054836742443/1000000000000000000)⟩
theorem valid978 : certificate978.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid978,?_⟩
  decide +kernel
theorem sound978 : certificate978.Sound :=
  rat_witness_certificate_sound certificate978 valid978 MajorityCertificates.Inputs048.envelope_sound978

def certificate979 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs048.envelope979,(47/20),(31/100),(32772344532278908303541/1000000000000000000),(368362587/200000000),32,(1007/1000),(373251301198753753/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid979 : certificate979.Valid := by
  refine ⟨MajorityCertificates.Inputs048.inputs_valid979,?_⟩
  decide +kernel
theorem sound979 : certificate979.Sound :=
  rat_witness_certificate_sound certificate979 valid979 MajorityCertificates.Inputs048.envelope_sound979

def certificates : List RatWitnessCertificate := [certificate960,certificate961,certificate962,certificate963,certificate964,certificate965,certificate966,certificate967,certificate968,certificate969,certificate970,certificate971,certificate972,certificate973,certificate974,certificate975,certificate976,certificate977,certificate978,certificate979]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound960,List.forall_mem_cons.mpr ⟨sound961,List.forall_mem_cons.mpr ⟨sound962,List.forall_mem_cons.mpr ⟨sound963,List.forall_mem_cons.mpr ⟨sound964,List.forall_mem_cons.mpr ⟨sound965,List.forall_mem_cons.mpr ⟨sound966,List.forall_mem_cons.mpr ⟨sound967,List.forall_mem_cons.mpr ⟨sound968,List.forall_mem_cons.mpr ⟨sound969,List.forall_mem_cons.mpr ⟨sound970,List.forall_mem_cons.mpr ⟨sound971,List.forall_mem_cons.mpr ⟨sound972,List.forall_mem_cons.mpr ⟨sound973,List.forall_mem_cons.mpr ⟨sound974,List.forall_mem_cons.mpr ⟨sound975,List.forall_mem_cons.mpr ⟨sound976,List.forall_mem_cons.mpr ⟨sound977,List.forall_mem_cons.mpr ⟨sound978,List.forall_mem_cons.mpr ⟨sound979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch048
