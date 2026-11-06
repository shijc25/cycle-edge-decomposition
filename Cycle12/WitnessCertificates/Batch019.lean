import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch019

def certificate380 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope380,(10993/5000),(1527/10000),(1377319449894569306277/1000000000000000000),(482983617/250000000),(47/20),(2554909/6250000),0,1,(3426929342808047/1000000000000000000)⟩
theorem valid380 : certificate380.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid380,?_⟩
  decide +kernel
theorem sound380 : certificate380.Sound :=
  rat_witness_certificate_sound certificate380 valid380 MajorityCertificates.Inputs019.envelope_sound380

def certificate381 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope381,(10993/5000),(1527/10000),(1377319449894569306277/1000000000000000000),(1119416749/500000000),(47/20),(636897551/500000000),0,(1126115392250588387/1000000000000000000),(31882751505031/10000000000000000)⟩
theorem valid381 : certificate381.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid381,?_⟩
  decide +kernel
theorem sound381 : certificate381.Sound :=
  rat_witness_certificate_sound certificate381 valid381 MajorityCertificates.Inputs019.envelope_sound381

def certificate382 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope382,(21929/10000),(1527/10000),(161509788327666181233/125000000000000000),(974337537/500000000),(47/20),(101929533/250000000),0,1,(3700322588892879/1000000000000000000)⟩
theorem valid382 : certificate382.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid382,?_⟩
  decide +kernel
theorem sound382 : certificate382.Sound :=
  rat_witness_certificate_sound certificate382 valid382 MajorityCertificates.Inputs019.envelope_sound382

def certificate383 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope383,(21929/10000),(1527/10000),(161509788327666181233/125000000000000000),(2244654253/1000000000),(47/20),(1274543547/1000000000),0,(1126192130732466169/1000000000000000000),(1709514791790849/500000000000000000)⟩
theorem valid383 : certificate383.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid383,?_⟩
  decide +kernel
theorem sound383 : certificate383.Sound :=
  rat_witness_certificate_sound certificate383 valid383 MajorityCertificates.Inputs019.envelope_sound383

def certificate384 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope384,(109367/50000),(1527/10000),(1215300036292237339909/1000000000000000000),(977615869/500000000),(12/5),(407697939/1000000000),0,1,(982791801739351/250000000000000000)⟩
theorem valid384 : certificate384.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid384,?_⟩
  decide +kernel
theorem sound384 : certificate384.Sound :=
  rat_witness_certificate_sound certificate384 valid384 MajorityCertificates.Inputs019.envelope_sound384

def certificate385 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope385,(109367/50000),(1527/10000),(1215300036292237339909/1000000000000000000),(450984799/200000000),(12/5),(19896983/15625000),0,(140783841994533657/125000000000000000),(725204858549667/200000000000000000)⟩
theorem valid385 : certificate385.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid385,?_⟩
  decide +kernel
theorem sound385 : certificate385.Sound :=
  rat_witness_certificate_sound certificate385 valid385 MajorityCertificates.Inputs019.envelope_sound385

def certificate386 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope386,(218191/100000),(153344531/1000000000),(143236628970677986199/125000000000000000),(391511681/200000000),(12/5),(102483239/250000000),0,1,(26109451123069/6250000000000000)⟩
theorem valid386 : certificate386.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid386,?_⟩
  decide +kernel
theorem sound386 : certificate386.Sound :=
  rat_witness_certificate_sound certificate386 valid386 MajorityCertificates.Inputs019.envelope_sound386

def certificate387 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope387,(218191/100000),(153344531/1000000000),(143236628970677986199/125000000000000000),(1129522459/500000000),(12/5),(79653911/62500000),0,(563175566852090227/500000000000000000),(1936448257834409/500000000000000000)⟩
theorem valid387 : certificate387.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid387,?_⟩
  decide +kernel
theorem sound387 : certificate387.Sound :=
  rat_witness_certificate_sound certificate387 valid387 MajorityCertificates.Inputs019.envelope_sound387

def certificate388 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope388,(217661/100000),(153344531/1000000000),(1082937317681299850407/1000000000000000000),(491668779/250000000),(12/5),(40964719/100000000),0,1,(444565042415777/100000000000000000)⟩
theorem valid388 : certificate388.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid388,?_⟩
  decide +kernel
theorem sound388 : certificate388.Sound :=
  rat_witness_certificate_sound certificate388 valid388 MajorityCertificates.Inputs019.envelope_sound388

def certificate389 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope389,(217661/100000),(153344531/1000000000),(1082937317681299850407/1000000000000000000),(2264020507/1000000000),(12/5),(318894347/250000000),0,(1126433243316262493/1000000000000000000),(4127902780019731/1000000000000000000)⟩
theorem valid389 : certificate389.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid389,?_⟩
  decide +kernel
theorem sound389 : certificate389.Sound :=
  rat_witness_certificate_sound certificate389 valid389 MajorityCertificates.Inputs019.envelope_sound389

def certificate390 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope390,(217143/100000),(153344531/1000000000),(1025653079030248895453/1000000000000000000),(1973382987/1000000000),(49/20),(204799333/500000000),0,1,(117628769522511/25000000000000000)⟩
theorem valid390 : certificate390.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid390,?_⟩
  decide +kernel
theorem sound390 : certificate390.Sound :=
  rat_witness_certificate_sound certificate390 valid390 MajorityCertificates.Inputs019.envelope_sound390

def certificate391 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope391,(217143/100000),(153344531/1000000000),(1025653079030248895453/1000000000000000000),(2273671607/1000000000),(49/20),(159346831/125000000),0,(1126516989792360141/1000000000000000000),(217580133765473/50000000000000000)⟩
theorem valid391 : certificate391.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid391,?_⟩
  decide +kernel
theorem sound391 : certificate391.Sound :=
  rat_witness_certificate_sound certificate391 valid391 MajorityCertificates.Inputs019.envelope_sound391

def certificate392 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope392,(108319/50000),(153344531/1000000000),(486687866250905701561/500000000000000000),(1979242021/1000000000),(49/20),(409623929/1000000000),0,1,(990810123650341/200000000000000000)⟩
theorem valid392 : certificate392.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid392,?_⟩
  decide +kernel
theorem sound392 : certificate392.Sound :=
  rat_witness_certificate_sound certificate392 valid392 MajorityCertificates.Inputs019.envelope_sound392

def certificate393 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope393,(108319/50000),(153344531/1000000000),(486687866250905701561/500000000000000000),(569608421/250000000),(49/20),(1275972643/1000000000),0,(563301141833628549/500000000000000000),(4619526817112969/1000000000000000000)⟩
theorem valid393 : certificate393.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid393,?_⟩
  decide +kernel
theorem sound393 : certificate393.Sound :=
  rat_witness_certificate_sound certificate393 valid393 MajorityCertificates.Inputs019.envelope_sound393

def certificate394 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope394,(108073/50000),(1527/10000),(925536029579625736477/1000000000000000000),(396175273/200000000),(49/20),(102056383/250000000),0,1,(2598592157493257/500000000000000000)⟩
theorem valid394 : certificate394.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid394,?_⟩
  decide +kernel
theorem sound394 : certificate394.Sound :=
  rat_witness_certificate_sound certificate394 valid394 MajorityCertificates.Inputs019.envelope_sound394

def certificate395 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope395,(108073/50000),(1527/10000),(925536029579625736477/1000000000000000000),(2284003719/1000000000),(49/20),(15965619/12500000),0,(1126689040408736231/1000000000000000000),(2448016377023213/500000000000000000)⟩
theorem valid395 : certificate395.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid395,?_⟩
  decide +kernel
theorem sound395 : certificate395.Sound :=
  rat_witness_certificate_sound certificate395 valid395 MajorityCertificates.Inputs019.envelope_sound395

def certificate396 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope396,(43133/20000),(1527/10000),(440822031069632704001/500000000000000000),(199386599/100000000),(5/2),(3260361/8000000),0,1,(2750445640206703/500000000000000000)⟩
theorem valid396 : certificate396.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid396,?_⟩
  decide +kernel
theorem sound396 : certificate396.Sound :=
  rat_witness_certificate_sound certificate396 valid396 MajorityCertificates.Inputs019.envelope_sound396

def certificate397 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope397,(43133/20000),(1527/10000),(440822031069632704001/500000000000000000),(1146629649/500000000),(5/2),(159583097/125000000),0,(225355438151862373/200000000000000000),(2567027225698353/500000000000000000)⟩
theorem valid397 : certificate397.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid397,?_⟩
  decide +kernel
theorem sound397 : certificate397.Sound :=
  rat_witness_certificate_sound certificate397 valid397 MajorityCertificates.Inputs019.envelope_sound397

def certificate398 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs019.envelope398,(215197/100000),(1527/10000),(168255263760065364129/200000000000000000),(2000396911/1000000000),(5/2),(407494737/1000000000),0,1,(5796505973055277/1000000000000000000)⟩
theorem valid398 : certificate398.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid398,?_⟩
  decide +kernel
theorem sound398 : certificate398.Sound :=
  rat_witness_certificate_sound certificate398 valid398 MajorityCertificates.Inputs019.envelope_sound398

def certificate399 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs019.envelope399,(215197/100000),(1527/10000),(168255263760065364129/200000000000000000),(1148811157/500000000),(5/2),(1278008189/1000000000),0,(1126866633012459513/1000000000000000000),(5422766727703843/1000000000000000000)⟩
theorem valid399 : certificate399.Valid := by
  refine ⟨MajorityCertificates.Inputs019.inputs_valid399,?_⟩
  decide +kernel
theorem sound399 : certificate399.Sound :=
  rat_witness_certificate_sound certificate399 valid399 MajorityCertificates.Inputs019.envelope_sound399

def certificates : List RatWitnessCertificate := [certificate380,certificate381,certificate382,certificate383,certificate384,certificate385,certificate386,certificate387,certificate388,certificate389,certificate390,certificate391,certificate392,certificate393,certificate394,certificate395,certificate396,certificate397,certificate398,certificate399]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound380,List.forall_mem_cons.mpr ⟨sound381,List.forall_mem_cons.mpr ⟨sound382,List.forall_mem_cons.mpr ⟨sound383,List.forall_mem_cons.mpr ⟨sound384,List.forall_mem_cons.mpr ⟨sound385,List.forall_mem_cons.mpr ⟨sound386,List.forall_mem_cons.mpr ⟨sound387,List.forall_mem_cons.mpr ⟨sound388,List.forall_mem_cons.mpr ⟨sound389,List.forall_mem_cons.mpr ⟨sound390,List.forall_mem_cons.mpr ⟨sound391,List.forall_mem_cons.mpr ⟨sound392,List.forall_mem_cons.mpr ⟨sound393,List.forall_mem_cons.mpr ⟨sound394,List.forall_mem_cons.mpr ⟨sound395,List.forall_mem_cons.mpr ⟨sound396,List.forall_mem_cons.mpr ⟨sound397,List.forall_mem_cons.mpr ⟨sound398,List.forall_mem_cons.mpr ⟨sound399,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch019
