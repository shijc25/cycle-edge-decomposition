import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch002

def certificate40 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope40,(215609/100000),(4671167/31250000),(124176955782508323627/125000000000000000),(386254463/200000000),(8/5),(404736323/1000000000),0,1,(75224544716211/15625000000000000)⟩
theorem valid40 : certificate40.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid40,?_⟩
  decide +kernel
theorem sound40 : certificate40.Sound :=
  rat_witness_certificate_sound certificate40 valid40 MajorityCertificates.Inputs002.envelope_sound40

def certificate41 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope41,(215609/100000),(4671167/31250000),(124176955782508323627/125000000000000000),(230278659/100000000),(8/5),(1266194791/1000000000),0,(1126577426828602319/1000000000000000000),(789827860602431/200000000000000000)⟩
theorem valid41 : certificate41.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid41,?_⟩
  decide +kernel
theorem sound41 : certificate41.Sound :=
  rat_witness_certificate_sound certificate41 valid41 MajorityCertificates.Inputs002.envelope_sound41

def certificate42 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope42,(214751/100000),(48039/320000),(916665799546033481853/1000000000000000000),(483960599/250000000),(8/5),(203574181/500000000),0,1,(2615087909717737/500000000000000000)⟩
theorem valid42 : certificate42.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid42,?_⟩
  decide +kernel
theorem sound42 : certificate42.Sound :=
  rat_witness_certificate_sound certificate42 valid42 MajorityCertificates.Inputs002.envelope_sound42

def certificate43 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope43,(214751/100000),(48039/320000),(916665799546033481853/1000000000000000000),(2309098139/1000000000),(8/5),(1267983619/1000000000),0,(112671649515310639/100000000000000000),(4310252836006449/1000000000000000000)⟩
theorem valid43 : certificate43.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid43,?_⟩
  decide +kernel
theorem sound43 : certificate43.Sound :=
  rat_witness_certificate_sound certificate43 valid43 MajorityCertificates.Inputs002.envelope_sound43

def certificate44 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope44,(213913/100000),(48039/320000),(53069362478983016179/62500000000000000),(1938821831/1000000000),(33/20),(50986529/125000000),0,1,(5643432850945303/1000000000000000000)⟩
theorem valid44 : certificate44.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid44,?_⟩
  decide +kernel
theorem sound44 : certificate44.Sound :=
  rat_witness_certificate_sound certificate44 valid44 MajorityCertificates.Inputs002.envelope_sound44

def certificate45 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope45,(213913/100000),(48039/320000),(53069362478983016179/62500000000000000),(579383029/250000000),(33/20),(158704221/125000000),0,(56343025273315887/50000000000000000),(4679072421606269/1000000000000000000)⟩
theorem valid45 : certificate45.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid45,?_⟩
  decide +kernel
theorem sound45 : certificate45.Sound :=
  rat_witness_certificate_sound certificate45 valid45 MajorityCertificates.Inputs002.envelope_sound45

def certificate46 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope46,(26637/12500),(75383203/500000000),(789324760767518664023/1000000000000000000),(970181703/500000000),(33/20),(102658141/250000000),0,1,(3034260705243897/500000000000000000)⟩
theorem valid46 : certificate46.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid46,?_⟩
  decide +kernel
theorem sound46 : certificate46.Sound :=
  rat_witness_certificate_sound certificate46 valid46 MajorityCertificates.Inputs002.envelope_sound46

def certificate47 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope47,(26637/12500),(75383203/500000000),(789324760767518664023/1000000000000000000),(2323815483/1000000000),(33/20),(254290301/200000000),0,(11270093036136779/10000000000000000),(1266840691516533/250000000000000000)⟩
theorem valid47 : certificate47.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid47,?_⟩
  decide +kernel
theorem sound47 : certificate47.Sound :=
  rat_witness_certificate_sound certificate47 valid47 MajorityCertificates.Inputs002.envelope_sound47

def certificate48 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope48,(2123/1000),(75705469/500000000),(73615407029209521159/100000000000000000),(243140839/125000000),(33/20),(412948397/1000000000),0,1,(315639804933787/50000000000000000)⟩
theorem valid48 : certificate48.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid48,?_⟩
  decide +kernel
theorem sound48 : certificate48.Sound :=
  rat_witness_certificate_sound certificate48 valid48 MajorityCertificates.Inputs002.envelope_sound48

def certificate49 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope49,(2123/1000),(75705469/500000000),(73615407029209521159/100000000000000000),(116482901/50000000),(33/20),(1273458409/1000000000),0,(225432547558868677/200000000000000000),(2736693390147867/500000000000000000)⟩
theorem valid49 : certificate49.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid49,?_⟩
  decide +kernel
theorem sound49 : certificate49.Sound :=
  rat_witness_certificate_sound certificate49 valid49 MajorityCertificates.Inputs002.envelope_sound49

def certificate50 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope50,(52881/25000),(75705469/500000000),(172162408772343592041/250000000000000000),(97892039/50000000),(33/20),(51585113/125000000),0,1,(1422456203235449/200000000000000000)⟩
theorem valid50 : certificate50.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid50,?_⟩
  decide +kernel
theorem sound50 : certificate50.Sound :=
  rat_witness_certificate_sound certificate50 valid50 MajorityCertificates.Inputs002.envelope_sound50

def certificate51 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope51,(52881/25000),(75705469/500000000),(172162408772343592041/250000000000000000),(2336560977/1000000000),(33/20),(159431451/125000000),0,(1127320662269275223/1000000000000000000),(5892665873330429/1000000000000000000)⟩
theorem valid51 : certificate51.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid51,?_⟩
  decide +kernel
theorem sound51 : certificate51.Sound :=
  rat_witness_certificate_sound certificate51 valid51 MajorityCertificates.Inputs002.envelope_sound51

def certificate52 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope52,(105383/50000),(75705469/500000000),(646028248295473760117/1000000000000000000),(981204841/500000000),(33/20),(413192341/1000000000),0,1,(375900511454869/50000000000000000)⟩
theorem valid52 : certificate52.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid52,?_⟩
  decide +kernel
theorem sound52 : certificate52.Sound :=
  rat_witness_certificate_sound certificate52 valid52 MajorityCertificates.Inputs002.envelope_sound52

def certificate53 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope53,(105383/50000),(75705469/500000000),(646028248295473760117/1000000000000000000),(292921007/125000000),(33/20),(127748599/100000000),0,(140935367684109187/125000000000000000),(1581551426212033/250000000000000000)⟩
theorem valid53 : certificate53.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid53,?_⟩
  decide +kernel
theorem sound53 : certificate53.Sound :=
  rat_witness_certificate_sound certificate53 valid53 MajorityCertificates.Inputs002.envelope_sound53

def certificate54 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope54,(52507/25000),(152055469/1000000000),(121527652363862859971/200000000000000000),(1966628111/1000000000),(17/10),(20781333/50000000),0,1,(8042065482993687/1000000000000000000)⟩
theorem valid54 : certificate54.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid54,?_⟩
  decide +kernel
theorem sound54 : certificate54.Sound :=
  rat_witness_certificate_sound certificate54 valid54 MajorityCertificates.Inputs002.envelope_sound54

def certificate55 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope55,(52507/25000),(152055469/1000000000),(121527652363862859971/200000000000000000),(2350064271/1000000000),(17/10),(639789281/500000000),0,(140956173914914047/125000000000000000),(3383068772662723/500000000000000000)⟩
theorem valid55 : certificate55.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid55,?_⟩
  decide +kernel
theorem sound55 : certificate55.Sound :=
  rat_witness_certificate_sound certificate55 valid55 MajorityCertificates.Inputs002.envelope_sound55

def certificate56 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope56,(209309/100000),(152055469/1000000000),(22917354861350491377/40000000000000000),(246827363/125000000),(17/10),(415826953/1000000000),0,1,(8755955685373489/1000000000000000000)⟩
theorem valid56 : certificate56.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid56,?_⟩
  decide +kernel
theorem sound56 : certificate56.Sound :=
  rat_witness_certificate_sound certificate56 valid56 MajorityCertificates.Inputs002.envelope_sound56

def certificate57 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope57,(209309/100000),(152055469/1000000000),(22917354861350491377/40000000000000000),(1178270581/500000000),(17/10),(640884797/500000000),0,(112781985701951651/100000000000000000),(7228805146497797/1000000000000000000)⟩
theorem valid57 : certificate57.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid57,?_⟩
  decide +kernel
theorem sound57 : certificate57.Sound :=
  rat_witness_certificate_sound certificate57 valid57 MajorityCertificates.Inputs002.envelope_sound57

def certificate58 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs002.envelope58,(104067/50000),(152055469/1000000000),(33840943074420866071/62500000000000000),(396008651/200000000),(17/10),(416728443/1000000000),0,1,(9064221611448977/1000000000000000000)⟩
theorem valid58 : certificate58.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid58,?_⟩
  decide +kernel
theorem sound58 : certificate58.Sound :=
  rat_witness_certificate_sound certificate58 valid58 MajorityCertificates.Inputs002.envelope_sound58

def certificate59 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs002.envelope59,(104067/50000),(152055469/1000000000),(33840943074420866071/62500000000000000),(2367073387/1000000000),(17/10),(256863959/200000000),0,(564000507909771691/500000000000000000),(3847019746748329/500000000000000000)⟩
theorem valid59 : certificate59.Valid := by
  refine ⟨MajorityCertificates.Inputs002.inputs_valid59,?_⟩
  decide +kernel
theorem sound59 : certificate59.Sound :=
  rat_witness_certificate_sound certificate59 valid59 MajorityCertificates.Inputs002.envelope_sound59

def certificates : List RatWitnessCertificate := [certificate40,certificate41,certificate42,certificate43,certificate44,certificate45,certificate46,certificate47,certificate48,certificate49,certificate50,certificate51,certificate52,certificate53,certificate54,certificate55,certificate56,certificate57,certificate58,certificate59]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound40,List.forall_mem_cons.mpr ⟨sound41,List.forall_mem_cons.mpr ⟨sound42,List.forall_mem_cons.mpr ⟨sound43,List.forall_mem_cons.mpr ⟨sound44,List.forall_mem_cons.mpr ⟨sound45,List.forall_mem_cons.mpr ⟨sound46,List.forall_mem_cons.mpr ⟨sound47,List.forall_mem_cons.mpr ⟨sound48,List.forall_mem_cons.mpr ⟨sound49,List.forall_mem_cons.mpr ⟨sound50,List.forall_mem_cons.mpr ⟨sound51,List.forall_mem_cons.mpr ⟨sound52,List.forall_mem_cons.mpr ⟨sound53,List.forall_mem_cons.mpr ⟨sound54,List.forall_mem_cons.mpr ⟨sound55,List.forall_mem_cons.mpr ⟨sound56,List.forall_mem_cons.mpr ⟨sound57,List.forall_mem_cons.mpr ⟨sound58,List.forall_mem_cons.mpr ⟨sound59,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch002
