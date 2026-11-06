import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch017

def certificate340 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope340,(58677/25000),(44739/320000),(17405413990888538335399/1000000000000000000),(453317379/250000000),(21/10),(370767551/1000000000),0,1,(263947624182981/1000000000000000000)⟩
theorem valid340 : certificate340.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid340,?_⟩
  decide +kernel
theorem sound340 : certificate340.Sound :=
  rat_witness_certificate_sound certificate340 valid340 MajorityCertificates.Inputs017.envelope_sound340

def certificate341 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope341,(58677/25000),(44739/320000),(17405413990888538335399/1000000000000000000),(2076832317/1000000000),(21/10),(644922109/500000000),0,(35158831881791657/31250000000000000),(61187322877371/250000000000000000)⟩
theorem valid341 : certificate341.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid341,?_⟩
  decide +kernel
theorem sound341 : certificate341.Sound :=
  rat_witness_certificate_sound certificate341 valid341 MajorityCertificates.Inputs017.envelope_sound341

def certificate342 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope342,(58441/25000),(70226953/500000000),(1342765598892166014881/100000000000000000),(455131079/250000000),(21/10),(372572041/1000000000),0,1,(68529944380277/200000000000000000)⟩
theorem valid342 : certificate342.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid342,?_⟩
  decide +kernel
theorem sound342 : certificate342.Sound :=
  rat_witness_certificate_sound certificate342 valid342 MajorityCertificates.Inputs017.envelope_sound342

def certificate343 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope343,(58441/25000),(70226953/500000000),(1342765598892166014881/100000000000000000),(1042277859/500000000),(21/10),(1289358073/1000000000),0,(1125107529648365291/1000000000000000000),(31853284876239/100000000000000000)⟩
theorem valid343 : certificate343.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid343,?_⟩
  decide +kernel
theorem sound343 : certificate343.Sound :=
  rat_witness_certificate_sound certificate343 valid343 MajorityCertificates.Inputs017.envelope_sound343

def certificate344 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope344,(232849/100000),(141742969/1000000000),(10691004789939291771169/1000000000000000000),(1825629261/1000000000),(21/10),(376358773/1000000000),0,1,(17216851186599/40000000000000000)⟩
theorem valid344 : certificate344.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid344,?_⟩
  decide +kernel
theorem sound344 : certificate344.Sound :=
  rat_witness_certificate_sound certificate344 valid344 MajorityCertificates.Inputs017.envelope_sound344

def certificate345 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope345,(232849/100000),(141742969/1000000000),(10691004789939291771169/1000000000000000000),(1045550621/500000000),(21/10),(322217683/250000000),0,(225027117620588157/200000000000000000),(50209655366393/125000000000000000)⟩
theorem valid345 : certificate345.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid345,?_⟩
  decide +kernel
theorem sound345 : certificate345.Sound :=
  rat_witness_certificate_sound certificate345 valid345 MajorityCertificates.Inputs017.envelope_sound345

def certificate346 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope346,(5799/2500),(11391/80000),(8726715693851369783053/1000000000000000000),(1832457697/1000000000),(43/20),(75639363/200000000),0,1,(527653903631431/1000000000000000000)⟩
theorem valid346 : certificate346.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid346,?_⟩
  decide +kernel
theorem sound346 : certificate346.Sound :=
  rat_witness_certificate_sound certificate346 valid346 MajorityCertificates.Inputs017.envelope_sound346

def certificate347 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope347,(5799/2500),(11391/80000),(8726715693851369783053/1000000000000000000),(84181893/40000000),(43/20),(1285172579/1000000000),0,(281291686930813261/250000000000000000),(48985206477709/100000000000000000)⟩
theorem valid347 : certificate347.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid347,?_⟩
  decide +kernel
theorem sound347 : certificate347.Sound :=
  rat_witness_certificate_sound certificate347 valid347 MajorityCertificates.Inputs017.envelope_sound347

def certificate348 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope348,(28887/12500),(143032031/1000000000),(908546141764463021387/125000000000000000),(1839235633/1000000000),(43/20),(190016651/500000000),0,1,(317031609759859/500000000000000000)⟩
theorem valid348 : certificate348.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid348,?_⟩
  decide +kernel
theorem sound348 : certificate348.Sound :=
  rat_witness_certificate_sound certificate348 valid348 MajorityCertificates.Inputs017.envelope_sound348

def certificate349 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope349,(28887/12500),(143032031/1000000000),(908546141764463021387/125000000000000000),(2111346913/1000000000),(43/20),(642553073/500000000),0,(140650119715686447/125000000000000000),(294647973872701/500000000000000000)⟩
theorem valid349 : certificate349.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid349,?_⟩
  decide +kernel
theorem sound349 : certificate349.Sound :=
  rat_witness_certificate_sound certificate349 valid349 MajorityCertificates.Inputs017.envelope_sound349

def certificate350 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope350,(14391/6250),(72160547/500000000),(3077697513182770252021/500000000000000000),(461022467/250000000),(43/20),(383842179/1000000000),0,1,(749101259634027/1000000000000000000)⟩
theorem valid350 : certificate350.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid350,?_⟩
  decide +kernel
theorem sound350 : certificate350.Sound :=
  rat_witness_certificate_sound certificate350 valid350 MajorityCertificates.Inputs017.envelope_sound350

def certificate351 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope351,(14391/6250),(72160547/500000000),(3077697513182770252021/500000000000000000),(1058831577/500000000),(43/20),(1284685149/1000000000),0,(225047633049988579/200000000000000000),(697926283997461/1000000000000000000)⟩
theorem valid351 : certificate351.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid351,?_⟩
  decide +kernel
theorem sound351 : certificate351.Sound :=
  rat_witness_certificate_sound certificate351 valid351 MajorityCertificates.Inputs017.envelope_sound351

def certificate352 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope352,(229437/100000),(46389/320000),(660788836219184268857/125000000000000000),(1850934377/1000000000),(43/20),(38566347/100000000),0,1,(174801136037507/200000000000000000)⟩
theorem valid352 : certificate352.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid352,?_⟩
  decide +kernel
theorem sound352 : certificate352.Sound :=
  rat_witness_certificate_sound certificate352 valid352 MajorityCertificates.Inputs017.envelope_sound352

def certificate353 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope353,(229437/100000),(46389/320000),(660788836219184268857/125000000000000000),(2124947541/1000000000),(43/20),(1284308297/1000000000),0,(1125278317935381341/1000000000000000000),(816683519209887/1000000000000000000)⟩
theorem valid353 : certificate353.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid353,?_⟩
  decide +kernel
theorem sound353 : certificate353.Sound :=
  rat_witness_certificate_sound certificate353 valid353 MajorityCertificates.Inputs017.envelope_sound353

def certificate354 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope354,(1429/625),(36402539/250000000),(4594407606916828314031/1000000000000000000),(1857407379/1000000000),(11/5),(387520307/1000000000),0,1,(503234152124859/500000000000000000)⟩
theorem valid354 : certificate354.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid354,?_⟩
  decide +kernel
theorem sound354 : certificate354.Sound :=
  rat_witness_certificate_sound certificate354 valid354 MajorityCertificates.Inputs017.envelope_sound354

def certificate355 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope355,(1429/625),(36402539/250000000),(4594407606916828314031/1000000000000000000),(2137385773/1000000000),(11/5),(320305333/250000000),0,(1125321357558709547/1000000000000000000),(233380972513611/250000000000000000)⟩
theorem valid355 : certificate355.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid355,?_⟩
  decide +kernel
theorem sound355 : certificate355.Sound :=
  rat_witness_certificate_sound certificate355 valid355 MajorityCertificates.Inputs017.envelope_sound355

def certificate356 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope356,(113931/50000),(4570459/31250000),(4034362102860816049913/1000000000000000000),(372761183/200000000),(11/5),(48672771/125000000),0,1,(1147358094030663/1000000000000000000)⟩
theorem valid356 : certificate356.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid356,?_⟩
  decide +kernel
theorem sound356 : certificate356.Sound :=
  rat_witness_certificate_sound certificate356 valid356 MajorityCertificates.Inputs017.envelope_sound356

def certificate357 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope357,(113931/50000),(4570459/31250000),(4034362102860816049913/1000000000000000000),(134031713/62500000),(11/5),(64045903/50000000),0,(112536722922997251/100000000000000000),(133401300721507/125000000000000000)⟩
theorem valid357 : certificate357.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid357,?_⟩
  decide +kernel
theorem sound357 : certificate357.Sound :=
  rat_witness_certificate_sound certificate357 valid357 MajorityCertificates.Inputs017.envelope_sound357

def certificate358 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs017.envelope358,(7097/3125),(146899219/1000000000),(714899821114160991899/200000000000000000),(935275157/500000000),(11/5),(195600981/500000000),0,1,(162302859744549/125000000000000000)⟩
theorem valid358 : certificate358.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid358,?_⟩
  decide +kernel
theorem sound358 : certificate358.Sound :=
  rat_witness_certificate_sound certificate358 valid358 MajorityCertificates.Inputs017.envelope_sound358

def certificate359 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs017.envelope359,(7097/3125),(146899219/1000000000),(714899821114160991899/200000000000000000),(1075699207/500000000),(11/5),(1280714127/1000000000),0,(562707935504704483/500000000000000000),(1207765410772213/1000000000000000000)⟩
theorem valid359 : certificate359.Valid := by
  refine ⟨MajorityCertificates.Inputs017.inputs_valid359,?_⟩
  decide +kernel
theorem sound359 : certificate359.Sound :=
  rat_witness_certificate_sound certificate359 valid359 MajorityCertificates.Inputs017.envelope_sound359

def certificates : List RatWitnessCertificate := [certificate340,certificate341,certificate342,certificate343,certificate344,certificate345,certificate346,certificate347,certificate348,certificate349,certificate350,certificate351,certificate352,certificate353,certificate354,certificate355,certificate356,certificate357,certificate358,certificate359]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound340,List.forall_mem_cons.mpr ⟨sound341,List.forall_mem_cons.mpr ⟨sound342,List.forall_mem_cons.mpr ⟨sound343,List.forall_mem_cons.mpr ⟨sound344,List.forall_mem_cons.mpr ⟨sound345,List.forall_mem_cons.mpr ⟨sound346,List.forall_mem_cons.mpr ⟨sound347,List.forall_mem_cons.mpr ⟨sound348,List.forall_mem_cons.mpr ⟨sound349,List.forall_mem_cons.mpr ⟨sound350,List.forall_mem_cons.mpr ⟨sound351,List.forall_mem_cons.mpr ⟨sound352,List.forall_mem_cons.mpr ⟨sound353,List.forall_mem_cons.mpr ⟨sound354,List.forall_mem_cons.mpr ⟨sound355,List.forall_mem_cons.mpr ⟨sound356,List.forall_mem_cons.mpr ⟨sound357,List.forall_mem_cons.mpr ⟨sound358,List.forall_mem_cons.mpr ⟨sound359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch017
