import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch024

def certificate480 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope480,(41213/20000),(54758203/500000000),(171047067277992696389/500000000000000000),(2311849937/1000000000),(69/20),(11105409/40000000),0,1,(8101151577567/488281250000000)⟩
theorem valid480 : certificate480.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid480,?_⟩
  decide +kernel
theorem sound480 : certificate480.Sound :=
  rat_witness_certificate_sound certificate480 valid480 MajorityCertificates.Inputs024.envelope_sound480

def certificate481 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope481,(41213/20000),(54758203/500000000),(171047067277992696389/500000000000000000),(637898511/250000000),(69/20),(1310387579/1000000000),0,(70612722639297673/62500000000000000),(15775090388640293/1000000000000000000)⟩
theorem valid481 : certificate481.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid481,?_⟩
  decide +kernel
theorem sound481 : certificate481.Sound :=
  rat_witness_certificate_sound certificate481 valid481 MajorityCertificates.Inputs024.envelope_sound481

def certificate482 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope482,(102999/50000),(6764209/62500000),(13572511252097274473/40000000000000000),(2321583659/1000000000),(7/2),(273832171/1000000000),0,1,(1673145273748633/100000000000000000)⟩
theorem valid482 : certificate482.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid482,?_⟩
  decide +kernel
theorem sound482 : certificate482.Sound :=
  rat_witness_certificate_sound certificate482 valid482 MajorityCertificates.Inputs024.envelope_sound482

def certificate483 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope483,(102999/50000),(6764209/62500000),(13572511252097274473/40000000000000000),(1279189353/500000000),(7/2),(1311115477/1000000000),0,(564922324673526737/500000000000000000),(15919991077256263/1000000000000000000)⟩
theorem valid483 : certificate483.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid483,?_⟩
  decide +kernel
theorem sound483 : certificate483.Sound :=
  rat_witness_certificate_sound certificate483 valid483 MajorityCertificates.Inputs024.envelope_sound483

def certificate484 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope484,(1497/625),(137875781/1000000000),(130298704196336693278041/1000000000000000000),(223222643/125000000),(33/10),(4554439/12500000),0,1,(2196581116551/62500000000000000)⟩
theorem valid484 : certificate484.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid484,?_⟩
  decide +kernel
theorem sound484 : certificate484.Sound :=
  rat_witness_certificate_sound certificate484 valid484 MajorityCertificates.Inputs024.envelope_sound484

def certificate485 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope485,(1497/625),(137875781/1000000000),(130298704196336693278041/1000000000000000000),(1932937597/1000000000),(33/10),(1363340663/1000000000),0,(1125010814218605247/1000000000000000000),(10039673111939/250000000000000000)⟩
theorem valid485 : certificate485.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid485,?_⟩
  decide +kernel
theorem sound485 : certificate485.Sound :=
  rat_witness_certificate_sound certificate485 valid485 MajorityCertificates.Inputs024.envelope_sound485

def certificate486 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope486,(59711/25000),(138520313/1000000000),(84013806151498242387647/1000000000000000000),(1778415211/1000000000),(33/10),(367544897/1000000000),0,1,(86307575911093/1000000000000000000)⟩
theorem valid486 : certificate486.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid486,?_⟩
  decide +kernel
theorem sound486 : certificate486.Sound :=
  rat_witness_certificate_sound certificate486 valid486 MajorityCertificates.Inputs024.envelope_sound486

def certificate487 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope487,(59711/25000),(138520313/1000000000),(84013806151498242387647/1000000000000000000),(1940859779/1000000000),(33/10),(680110341/500000000),0,(140627102441129881/125000000000000000),(10290569353659/125000000000000000)⟩
theorem valid487 : certificate487.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid487,?_⟩
  decide +kernel
theorem sound487 : certificate487.Sound :=
  rat_witness_certificate_sound certificate487 valid487 MajorityCertificates.Inputs024.envelope_sound487

def certificate488 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope488,(14887/6250),(44739/320000),(7347702253895599093683/125000000000000000),(179337483/100000000),(33/10),(46232341/125000000),0,1,(476886284343/5000000000000000)⟩
theorem valid488 : certificate488.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid488,?_⟩
  decide +kernel
theorem sound488 : certificate488.Sound :=
  rat_witness_certificate_sound certificate488 valid488 MajorityCertificates.Inputs024.envelope_sound488

def certificate489 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope489,(14887/6250),(44739/320000),(7347702253895599093683/125000000000000000),(485777043/250000000),(33/10),(5442107/4000000),0,(1125024105287044361/1000000000000000000),(48927442923493/500000000000000000)⟩
theorem valid489 : certificate489.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid489,?_⟩
  decide +kernel
theorem sound489 : certificate489.Sound :=
  rat_witness_certificate_sound certificate489 valid489 MajorityCertificates.Inputs024.envelope_sound489

def certificate490 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope490,(237561/100000),(70549219/500000000),(5439191980260362501551/125000000000000000),(449837317/250000000),(67/20),(373214071/1000000000),0,1,(105470953369893/1000000000000000000)⟩
theorem valid490 : certificate490.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid490,?_⟩
  decide +kernel
theorem sound490 : certificate490.Sound :=
  rat_witness_certificate_sound certificate490 valid490 MajorityCertificates.Inputs024.envelope_sound490

def certificate491 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope491,(237561/100000),(70549219/500000000),(5439191980260362501551/125000000000000000),(1950169237/1000000000),(67/20),(67855557/50000000),0,(1125032650065792561/1000000000000000000),(23208630031949/200000000000000000)⟩
theorem valid491 : certificate491.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid491,?_⟩
  decide +kernel
theorem sound491 : certificate491.Sound :=
  rat_witness_certificate_sound certificate491 valid491 MajorityCertificates.Inputs024.envelope_sound491

def certificate492 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope492,(29661/12500),(141742969/1000000000),(38194222826487881556691/1000000000000000000),(1804179609/1000000000),(67/20),(187326927/500000000),0,1,(119974155436543/1000000000000000000)⟩
theorem valid492 : certificate492.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid492,?_⟩
  decide +kernel
theorem sound492 : certificate492.Sound :=
  rat_witness_certificate_sound certificate492 valid492 MajorityCertificates.Inputs024.envelope_sound492

def certificate493 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope493,(29661/12500),(141742969/1000000000),(38194222826487881556691/1000000000000000000),(1954069017/1000000000),(67/20),(1354954181/1000000000),0,(281259310039290631/250000000000000000),(140216702201301/1000000000000000000)⟩
theorem valid493 : certificate493.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid493,?_⟩
  decide +kernel
theorem sound493 : certificate493.Sound :=
  rat_witness_certificate_sound certificate493 valid493 MajorityCertificates.Inputs024.envelope_sound493

def certificate494 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope494,(47397/20000),(11391/80000),(16848798986218848632169/500000000000000000),(1806226653/1000000000),(67/20),(376440341/1000000000),0,1,(135974691782569/1000000000000000000)⟩
theorem valid494 : certificate494.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid494,?_⟩
  decide +kernel
theorem sound494 : certificate494.Sound :=
  rat_witness_certificate_sound certificate494 valid494 MajorityCertificates.Inputs024.envelope_sound494

def certificate495 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope495,(47397/20000),(11391/80000),(16848798986218848632169/500000000000000000),(1953485341/1000000000),(67/20),(1356339853/1000000000),0,(562521131808591403/500000000000000000),(15629349254077/100000000000000000)⟩
theorem valid495 : certificate495.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid495,?_⟩
  decide +kernel
theorem sound495 : certificate495.Sound :=
  rat_witness_certificate_sound certificate495 valid495 MajorityCertificates.Inputs024.envelope_sound495

def certificate496 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope496,(47271/20000),(143032031/1000000000),(167046958857763097523/6250000000000000),(1809290373/1000000000),(67/20),(378417449/1000000000),0,1,(171874052847573/1000000000000000000)⟩
theorem valid496 : certificate496.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid496,?_⟩
  decide +kernel
theorem sound496 : certificate496.Sound :=
  rat_witness_certificate_sound certificate496 valid496 MajorityCertificates.Inputs024.envelope_sound496

def certificate497 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope497,(47271/20000),(143032031/1000000000),(167046958857763097523/6250000000000000),(1956633869/1000000000),(67/20),(678422761/500000000),0,(562526713849361933/500000000000000000),(201201942201773/1000000000000000000)⟩
theorem valid497 : certificate497.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid497,?_⟩
  decide +kernel
theorem sound497 : certificate497.Sound :=
  rat_witness_certificate_sound certificate497 valid497 MajorityCertificates.Inputs024.envelope_sound497

def certificate498 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs024.envelope498,(117889/50000),(72160547/500000000),(10908395511668070660349/500000000000000000),(453308963/250000000),(17/5),(191002903/500000000),0,1,(210788635479573/1000000000000000000)⟩
theorem valid498 : certificate498.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid498,?_⟩
  decide +kernel
theorem sound498 : certificate498.Sound :=
  rat_witness_certificate_sound certificate498 valid498 MajorityCertificates.Inputs024.envelope_sound498

def certificate499 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs024.envelope499,(117889/50000),(72160547/500000000),(10908395511668070660349/500000000000000000),(1963669987/1000000000),(17/5),(21147299/15625000),0,(1125065614424868437/1000000000000000000),(246614885723987/1000000000000000000)⟩
theorem valid499 : certificate499.Valid := by
  refine ⟨MajorityCertificates.Inputs024.inputs_valid499,?_⟩
  decide +kernel
theorem sound499 : certificate499.Sound :=
  rat_witness_certificate_sound certificate499 valid499 MajorityCertificates.Inputs024.envelope_sound499

def certificates : List RatWitnessCertificate := [certificate480,certificate481,certificate482,certificate483,certificate484,certificate485,certificate486,certificate487,certificate488,certificate489,certificate490,certificate491,certificate492,certificate493,certificate494,certificate495,certificate496,certificate497,certificate498,certificate499]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound480,List.forall_mem_cons.mpr ⟨sound481,List.forall_mem_cons.mpr ⟨sound482,List.forall_mem_cons.mpr ⟨sound483,List.forall_mem_cons.mpr ⟨sound484,List.forall_mem_cons.mpr ⟨sound485,List.forall_mem_cons.mpr ⟨sound486,List.forall_mem_cons.mpr ⟨sound487,List.forall_mem_cons.mpr ⟨sound488,List.forall_mem_cons.mpr ⟨sound489,List.forall_mem_cons.mpr ⟨sound490,List.forall_mem_cons.mpr ⟨sound491,List.forall_mem_cons.mpr ⟨sound492,List.forall_mem_cons.mpr ⟨sound493,List.forall_mem_cons.mpr ⟨sound494,List.forall_mem_cons.mpr ⟨sound495,List.forall_mem_cons.mpr ⟨sound496,List.forall_mem_cons.mpr ⟨sound497,List.forall_mem_cons.mpr ⟨sound498,List.forall_mem_cons.mpr ⟨sound499,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch024
