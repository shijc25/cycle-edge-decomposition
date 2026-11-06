import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs016

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch016

def certificate320 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope320,(38811/20000),(29312837/250000000),(2183945909433927173/12500000000000000),(144526043/62500000),(49/20),(155690561/500000000),0,1,(6669582467472849/200000000000000000)⟩
theorem valid320 : certificate320.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid320,?_⟩
  decide +kernel
theorem sound320 : certificate320.Sound :=
  rat_witness_certificate_sound certificate320 valid320 MajorityCertificates.Inputs016.envelope_sound320

def certificate321 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope321,(38811/20000),(29312837/250000000),(2183945909433927173/12500000000000000),(130999181/50000000),(49/20),(348154151/250000000),0,(567511694266806303/500000000000000000),(15623004630048303/500000000000000000)⟩
theorem valid321 : certificate321.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid321,?_⟩
  decide +kernel
theorem sound321 : certificate321.Sound :=
  rat_witness_certificate_sound certificate321 valid321 MajorityCertificates.Inputs016.envelope_sound321

def certificate322 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope322,(97017/50000),(7313103/62500000),(43586218850587268037/250000000000000000),(1157492381/500000000),(49/20),(310580617/1000000000),0,1,(33407149535615837/1000000000000000000)⟩
theorem valid322 : certificate322.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid322,?_⟩
  decide +kernel
theorem sound322 : certificate322.Sound :=
  rat_witness_certificate_sound certificate322 valid322 MajorityCertificates.Inputs016.envelope_sound322

def certificate323 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope323,(97017/50000),(7313103/62500000),(43586218850587268037/250000000000000000),(1310614731/500000000),(49/20),(696419601/500000000),0,(1135045948872272847/1000000000000000000),(31328614918046771/1000000000000000000)⟩
theorem valid323 : certificate323.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid323,?_⟩
  decide +kernel
theorem sound323 : certificate323.Sound :=
  rat_witness_certificate_sound certificate323 valid323 MajorityCertificates.Inputs016.envelope_sound323

def certificate324 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope324,(194013/100000),(116767949/1000000000),(173976484208467857237/1000000000000000000),(231498983/100000000),(49/20),(38746403/125000000),0,1,(6717575555026817/200000000000000000)⟩
theorem valid324 : certificate324.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid324,?_⟩
  decide +kernel
theorem sound324 : certificate324.Sound :=
  rat_witness_certificate_sound certificate324 valid324 MajorityCertificates.Inputs016.envelope_sound324

def certificate325 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope325,(194013/100000),(116767949/1000000000),(173976484208467857237/1000000000000000000),(32780901/12500000),(49/20),(6965319/5000000),0,(227013693219451937/200000000000000000),(785281847294857/25000000000000000)⟩
theorem valid325 : certificate325.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid325,?_⟩
  decide +kernel
theorem sound325 : certificate325.Sound :=
  rat_witness_certificate_sound certificate325 valid325 MajorityCertificates.Inputs016.envelope_sound325

def certificate326 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope326,(24249/12500),(93221/800000),(173610483423788505349/1000000000000000000),(578688009/250000000),(49/20),(77345031/250000000),0,1,(6756149031340643/200000000000000000)⟩
theorem valid326 : certificate326.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid326,?_⟩
  decide +kernel
theorem sound326 : certificate326.Sound :=
  rat_witness_certificate_sound certificate326 valid326 MajorityCertificates.Inputs016.envelope_sound326

def certificate327 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope327,(24249/12500),(93221/800000),(173610483423788505349/1000000000000000000),(2623460603/1000000000),(49/20),(1393426727/1000000000),0,(1135090939911232073/1000000000000000000),(15756023773931779/500000000000000000)⟩
theorem valid327 : certificate327.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid327,?_⟩
  decide +kernel
theorem sound327 : certificate327.Sound :=
  rat_witness_certificate_sound certificate327 valid327 MajorityCertificates.Inputs016.envelope_sound327

def certificate328 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope328,(193971/100000),(116284551/1000000000),(4331171436219614029/25000000000000000),(463268261/200000000),(49/20),(61731063/200000000),0,1,(1355778226088041/40000000000000000)⟩
theorem valid328 : certificate328.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid328,?_⟩
  decide +kernel
theorem sound328 : certificate328.Sound :=
  rat_witness_certificate_sound certificate328 valid328 MajorityCertificates.Inputs016.envelope_sound328

def certificate329 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope329,(193971/100000),(116284551/1000000000),(4331171436219614029/25000000000000000),(524939209/200000000),(49/20),(1393655897/1000000000),0,(1135113370017362483/1000000000000000000),(7898754021968899/250000000000000000)⟩
theorem valid329 : certificate329.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid329,?_⟩
  decide +kernel
theorem sound329 : certificate329.Sound :=
  rat_witness_certificate_sound certificate329 valid329 MajorityCertificates.Inputs016.envelope_sound329

def certificate330 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope330,(192763/100000),(38139/320000),(34193528398953411263/200000000000000000),(231269203/100000000),(49/20),(318156591/1000000000),0,1,(34470580413748877/1000000000000000000)⟩
theorem valid330 : certificate330.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid330,?_⟩
  decide +kernel
theorem sound330 : certificate330.Sound :=
  rat_witness_certificate_sound certificate330 valid330 MajorityCertificates.Inputs016.envelope_sound330

def certificate331 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope331,(192763/100000),(38139/320000),(34193528398953411263/200000000000000000),(82125167/31250000),(49/20),(699342737/500000000),0,(227062766950112471/200000000000000000),(8019979966146033/250000000000000000)⟩
theorem valid331 : certificate331.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid331,?_⟩
  decide +kernel
theorem sound331 : certificate331.Sound :=
  rat_witness_certificate_sound certificate331 valid331 MajorityCertificates.Inputs016.envelope_sound331

def certificate332 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope332,(96339/50000),(117895313/1000000000),(84787762377982862633/500000000000000000),(1159954523/500000000),(49/20),(62856971/200000000),0,1,(34969325268687839/1000000000000000000)⟩
theorem valid332 : certificate332.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid332,?_⟩
  decide +kernel
theorem sound332 : certificate332.Sound :=
  rat_witness_certificate_sound certificate332 valid332 MajorityCertificates.Inputs016.envelope_sound332

def certificate333 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope333,(96339/50000),(117895313/1000000000),(84787762377982862633/500000000000000000),(2633599301/1000000000),(49/20),(1399667191/1000000000),0,(283850933487206163/250000000000000000),(8106078504879763/250000000000000000)⟩
theorem valid333 : certificate333.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid333,?_⟩
  decide +kernel
theorem sound333 : certificate333.Sound :=
  rat_witness_certificate_sound certificate333 valid333 MajorityCertificates.Inputs016.envelope_sound333

def certificate334 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope334,(47549/20000),(21957/160000),(2605974078352198744117/50000000000000000),(1800223269/1000000000),(41/20),(362553739/1000000000),0,1,(79584512371023/1000000000000000000)⟩
theorem valid334 : certificate334.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid334,?_⟩
  decide +kernel
theorem sound334 : certificate334.Sound :=
  rat_witness_certificate_sound certificate334 valid334 MajorityCertificates.Inputs016.envelope_sound334

def certificate335 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope335,(47549/20000),(21957/160000),(2605974078352198744117/50000000000000000),(32011023/15625000),(41/20),(258889409/200000000),0,(70314202356421979/62500000000000000),(81665809385729/1000000000000000000)⟩
theorem valid335 : certificate335.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid335,?_⟩
  decide +kernel
theorem sound335 : certificate335.Sound :=
  rat_witness_certificate_sound certificate335 valid335 MajorityCertificates.Inputs016.envelope_sound335

def certificate336 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope336,(118347/50000),(137875781/1000000000),(3360552228563666647927/100000000000000000),(1800320503/1000000000),(21/10),(91302811/250000000),0,1,(67218927550033/500000000000000000)⟩
theorem valid336 : certificate336.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid336,?_⟩
  decide +kernel
theorem sound336 : certificate336.Sound :=
  rat_witness_certificate_sound certificate336 valid336 MajorityCertificates.Inputs016.envelope_sound336

def certificate337 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope337,(118347/50000),(137875781/1000000000),(3360552228563666647927/100000000000000000),(1031330511/500000000),(21/10),(1290545041/1000000000),0,(1125042431522844009/1000000000000000000),(31553589229627/250000000000000000)⟩
theorem valid337 : certificate337.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid337,?_⟩
  decide +kernel
theorem sound337 : certificate337.Sound :=
  rat_witness_certificate_sound certificate337 valid337 MajorityCertificates.Inputs016.envelope_sound337

def certificate338 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs016.envelope338,(235683/100000),(34791211/250000000),(23512646959416672557299/1000000000000000000),(180515861/100000000),(21/10),(369049747/1000000000),0,1,(48781211855081/250000000000000000)⟩
theorem valid338 : certificate338.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid338,?_⟩
  decide +kernel
theorem sound338 : certificate338.Sound :=
  rat_witness_certificate_sound certificate338 valid338 MajorityCertificates.Inputs016.envelope_sound338

def certificate339 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs016.envelope339,(235683/100000),(34791211/250000000),(23512646959416672557299/1000000000000000000),(2068967039/1000000000),(21/10),(1290357163/1000000000),0,(1125060906309261113/1000000000000000000),(36087822717983/200000000000000000)⟩
theorem valid339 : certificate339.Valid := by
  refine ⟨MajorityCertificates.Inputs016.inputs_valid339,?_⟩
  decide +kernel
theorem sound339 : certificate339.Sound :=
  rat_witness_certificate_sound certificate339 valid339 MajorityCertificates.Inputs016.envelope_sound339

def certificates : List RatWitnessCertificate := [certificate320,certificate321,certificate322,certificate323,certificate324,certificate325,certificate326,certificate327,certificate328,certificate329,certificate330,certificate331,certificate332,certificate333,certificate334,certificate335,certificate336,certificate337,certificate338,certificate339]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound320,List.forall_mem_cons.mpr ⟨sound321,List.forall_mem_cons.mpr ⟨sound322,List.forall_mem_cons.mpr ⟨sound323,List.forall_mem_cons.mpr ⟨sound324,List.forall_mem_cons.mpr ⟨sound325,List.forall_mem_cons.mpr ⟨sound326,List.forall_mem_cons.mpr ⟨sound327,List.forall_mem_cons.mpr ⟨sound328,List.forall_mem_cons.mpr ⟨sound329,List.forall_mem_cons.mpr ⟨sound330,List.forall_mem_cons.mpr ⟨sound331,List.forall_mem_cons.mpr ⟨sound332,List.forall_mem_cons.mpr ⟨sound333,List.forall_mem_cons.mpr ⟨sound334,List.forall_mem_cons.mpr ⟨sound335,List.forall_mem_cons.mpr ⟨sound336,List.forall_mem_cons.mpr ⟨sound337,List.forall_mem_cons.mpr ⟨sound338,List.forall_mem_cons.mpr ⟨sound339,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch016
