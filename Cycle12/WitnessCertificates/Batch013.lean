import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch013

def certificate260 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope260,(48711/25000),(31226289/250000000),(93977194418985317703/500000000000000000),(450991659/200000000),(23/10),(167590383/500000000),0,1,(30291525989796289/1000000000000000000)⟩
theorem valid260 : certificate260.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid260,?_⟩
  decide +kernel
theorem sound260 : certificate260.Sound :=
  rat_witness_certificate_sound certificate260 valid260 MajorityCertificates.Inputs013.envelope_sound260

def certificate261 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope261,(48711/25000),(31226289/250000000),(93977194418985317703/500000000000000000),(2578012953/1000000000),(23/10),(86250521/62500000),0,(28356872240676873/25000000000000000),(7130119695795749/250000000000000000)⟩
theorem valid261 : certificate261.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid261,?_⟩
  decide +kernel
theorem sound261 : certificate261.Sound :=
  rat_witness_certificate_sound certificate261 valid261 MajorityCertificates.Inputs013.envelope_sound261

def certificate262 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope262,(6088/3125),(124663457/1000000000),(46874322267087648777/250000000000000000),(565230627/250000000),(23/10),(334104741/1000000000),0,1,(7576178563321169/250000000000000000)⟩
theorem valid262 : certificate262.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid262,?_⟩
  decide +kernel
theorem sound262 : certificate262.Sound :=
  rat_witness_certificate_sound certificate262 valid262 MajorityCertificates.Inputs013.envelope_sound262

def certificate263 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope263,(6088/3125),(124663457/1000000000),(46874322267087648777/250000000000000000),(515738633/200000000),(23/10),(690260661/500000000),0,(226859798193976727/200000000000000000),(3578580873886007/125000000000000000)⟩
theorem valid263 : certificate263.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid263,?_⟩
  decide +kernel
theorem sound263 : certificate263.Sound :=
  rat_witness_certificate_sound certificate263 valid263 MajorityCertificates.Inputs013.envelope_sound263

def certificate264 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope264,(48697/25000),(62210879/500000000),(37408637886965884507/200000000000000000),(1128730257/500000000),(23/10),(166888207/500000000),0,1,(30616142402348993/1000000000000000000)⟩
theorem valid264 : certificate264.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid264,?_⟩
  decide +kernel
theorem sound264 : certificate264.Sound :=
  rat_witness_certificate_sound certificate264 valid264 MajorityCertificates.Inputs013.envelope_sound264

def certificate265 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope265,(48697/25000),(62210879/500000000),(37408637886965884507/200000000000000000),(103151957/40000000),(23/10),(55255713/40000000),0,(45372922431926827/40000000000000000),(28803845436301819/1000000000000000000)⟩
theorem valid265 : certificate265.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid265,?_⟩
  decide +kernel
theorem sound265 : certificate265.Sound :=
  rat_witness_certificate_sound certificate265 valid265 MajorityCertificates.Inputs013.envelope_sound265

def certificate266 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope266,(48673/25000),(31024873/250000000),(92925823817745143157/500000000000000000),(565082913/250000000),(23/10),(166407563/500000000),0,1,(30838376212078659/1000000000000000000)⟩
theorem valid266 : certificate266.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid266,?_⟩
  decide +kernel
theorem sound266 : certificate266.Sound :=
  rat_witness_certificate_sound certificate266 valid266 MajorityCertificates.Inputs013.envelope_sound266

def certificate267 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope267,(48673/25000),(31024873/250000000),(92925823817745143157/500000000000000000),(322511119/125000000),(23/10),(172839631/125000000),0,(283596969344080619/250000000000000000),(14519725097961717/500000000000000000)⟩
theorem valid267 : certificate267.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid267,?_⟩
  decide +kernel
theorem sound267 : certificate267.Sound :=
  rat_witness_certificate_sound certificate267 valid267 MajorityCertificates.Inputs013.envelope_sound267

def certificate268 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope268,(194707/100000),(123777227/1000000000),(185698677009292092909/1000000000000000000),(2260436363/1000000000),(23/10),(331923881/1000000000),0,1,(15494723650197061/500000000000000000)⟩
theorem valid268 : certificate268.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid268,?_⟩
  decide +kernel
theorem sound268 : certificate268.Sound :=
  rat_witness_certificate_sound certificate268 valid268 MajorityCertificates.Inputs013.envelope_sound268

def certificate269 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope269,(194707/100000),(123777227/1000000000),(185698677009292092909/1000000000000000000),(2581631463/1000000000),(23/10),(1382362463/1000000000),0,(1134394932361709257/1000000000000000000),(1815263702251351/62500000000000000)⟩
theorem valid269 : certificate269.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid269,?_⟩
  decide +kernel
theorem sound269 : certificate269.Sound :=
  rat_witness_certificate_sound certificate269 valid269 MajorityCertificates.Inputs013.envelope_sound269

def certificate270 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope270,(4867/2500),(123535527/1000000000),(92628182321493895023/500000000000000000),(14143143/6250000),(47/20),(331110693/1000000000),0,1,(31049070486031229/1000000000000000000)⟩
theorem valid270 : certificate270.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid270,?_⟩
  decide +kernel
theorem sound270 : certificate270.Sound :=
  rat_witness_certificate_sound certificate270 valid270 MajorityCertificates.Inputs013.envelope_sound270

def certificate271 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope271,(4867/2500),(123535527/1000000000),(92628182321493895023/500000000000000000),(323045947/125000000),(47/20),(43248149/31250000),0,(1134418823905059117/1000000000000000000),(14557486479873161/500000000000000000)⟩
theorem valid271 : certificate271.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid271,?_⟩
  decide +kernel
theorem sound271 : certificate271.Sound :=
  rat_witness_certificate_sound certificate271 valid271 MajorityCertificates.Inputs013.envelope_sound271

def certificate272 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope272,(97293/50000),(61606631/500000000),(184089318713182580423/1000000000000000000),(2272566433/1000000000),(47/20),(13183979/40000000),0,1,(30963835839472083/1000000000000000000)⟩
theorem valid272 : certificate272.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid272,?_⟩
  decide +kernel
theorem sound272 : certificate272.Sound :=
  rat_witness_certificate_sound certificate272 valid272 MajorityCertificates.Inputs013.envelope_sound272

def certificate273 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope273,(97293/50000),(61606631/500000000),(184089318713182580423/1000000000000000000),(10339861/4000000),(47/20),(692805437/500000000),0,(70905220941872457/62500000000000000),(29371294271169597/1000000000000000000)⟩
theorem valid273 : certificate273.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid273,?_⟩
  decide +kernel
theorem sound273 : certificate273.Sound :=
  rat_witness_certificate_sound certificate273 valid273 MajorityCertificates.Inputs013.envelope_sound273

def certificate274 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope274,(97301/50000),(12281043/100000000),(36789342620044720287/200000000000000000),(1133610287/500000000),(47/20),(164464191/500000000),0,1,(980683411100743/31250000000000000)⟩
theorem valid274 : certificate274.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid274,?_⟩
  decide +kernel
theorem sound274 : certificate274.Sound :=
  rat_witness_certificate_sound certificate274 valid274 MajorityCertificates.Inputs013.envelope_sound274

def certificate275 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope275,(97301/50000),(12281043/100000000),(36789342620044720287/200000000000000000),(1293355147/500000000),(47/20),(173161511/125000000),0,(1134490149968348919/1000000000000000000),(5881430111439521/200000000000000000)⟩
theorem valid275 : certificate275.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid275,?_⟩
  decide +kernel
theorem sound275 : certificate275.Sound :=
  rat_witness_certificate_sound certificate275 valid275 MajorityCertificates.Inputs013.envelope_sound275

def certificate276 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope276,(12161/6250),(12256873/100000000),(1433717631298357343/7812500000000000),(284573781/125000000),(47/20),(163773447/500000000),0,1,(485346966500233/15625000000000000)⟩
theorem valid276 : certificate276.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid276,?_⟩
  decide +kernel
theorem sound276 : certificate276.Sound :=
  rat_witness_certificate_sound certificate276 valid276 MajorityCertificates.Inputs013.envelope_sound276

def certificate277 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope277,(12161/6250),(12256873/100000000),(1433717631298357343/7812500000000000),(2590705419/1000000000),(47/20),(692091899/500000000),0,(567256928330877581/500000000000000000),(2940269084373931/100000000000000000)⟩
theorem valid277 : certificate277.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid277,?_⟩
  decide +kernel
theorem sound277 : certificate277.Sound :=
  rat_witness_certificate_sound certificate277 valid277 MajorityCertificates.Inputs013.envelope_sound277

def certificate278 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs013.envelope278,(3891/2000),(122327031/1000000000),(5721494197070798261/31250000000000000),(2277534453/1000000000),(47/20),(326865823/1000000000),0,1,(31210276662705533/1000000000000000000)⟩
theorem valid278 : certificate278.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid278,?_⟩
  decide +kernel
theorem sound278 : certificate278.Sound :=
  rat_witness_certificate_sound certificate278 valid278 MajorityCertificates.Inputs013.envelope_sound278

def certificate279 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs013.envelope279,(3891/2000),(122327031/1000000000),(5721494197070798261/31250000000000000),(2591769931/1000000000),(47/20),(21632577/15625000),0,(567268764253508453/500000000000000000),(29482887897810429/1000000000000000000)⟩
theorem valid279 : certificate279.Valid := by
  refine ⟨MajorityCertificates.Inputs013.inputs_valid279,?_⟩
  decide +kernel
theorem sound279 : certificate279.Sound :=
  rat_witness_certificate_sound certificate279 valid279 MajorityCertificates.Inputs013.envelope_sound279

def certificates : List RatWitnessCertificate := [certificate260,certificate261,certificate262,certificate263,certificate264,certificate265,certificate266,certificate267,certificate268,certificate269,certificate270,certificate271,certificate272,certificate273,certificate274,certificate275,certificate276,certificate277,certificate278,certificate279]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound260,List.forall_mem_cons.mpr ⟨sound261,List.forall_mem_cons.mpr ⟨sound262,List.forall_mem_cons.mpr ⟨sound263,List.forall_mem_cons.mpr ⟨sound264,List.forall_mem_cons.mpr ⟨sound265,List.forall_mem_cons.mpr ⟨sound266,List.forall_mem_cons.mpr ⟨sound267,List.forall_mem_cons.mpr ⟨sound268,List.forall_mem_cons.mpr ⟨sound269,List.forall_mem_cons.mpr ⟨sound270,List.forall_mem_cons.mpr ⟨sound271,List.forall_mem_cons.mpr ⟨sound272,List.forall_mem_cons.mpr ⟨sound273,List.forall_mem_cons.mpr ⟨sound274,List.forall_mem_cons.mpr ⟨sound275,List.forall_mem_cons.mpr ⟨sound276,List.forall_mem_cons.mpr ⟨sound277,List.forall_mem_cons.mpr ⟨sound278,List.forall_mem_cons.mpr ⟨sound279,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch013
