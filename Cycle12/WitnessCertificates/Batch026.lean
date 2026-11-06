import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs026

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch026

def certificate520 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope520,(1442/625),(77316797/500000000),(236403677302909347931/40000000000000000),(929043331/500000000),(18/5),(41033399/100000000),0,1,(783732980653209/1000000000000000000)⟩
theorem valid520 : certificate520.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid520,?_⟩
  decide +kernel
theorem sound520 : certificate520.Sound :=
  rat_witness_certificate_sound certificate520 valid520 MajorityCertificates.Inputs026.envelope_sound520

def certificate521 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope521,(1442/625),(77316797/500000000),(236403677302909347931/40000000000000000),(1006351699/500000000),(18/5),(1338087467/1000000000),0,(1125247553242320443/1000000000000000000),(188011526034287/200000000000000000)⟩
theorem valid521 : certificate521.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid521,?_⟩
  decide +kernel
theorem sound521 : certificate521.Sound :=
  rat_witness_certificate_sound certificate521 valid521 MajorityCertificates.Inputs026.envelope_sound521

def certificate522 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope522,(9211/4000),(49689/320000),(5405667221822570221929/1000000000000000000),(1863448287/1000000000),(18/5),(82400437/200000000),0,1,(34303760552179/40000000000000000)⟩
theorem valid522 : certificate522.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid522,?_⟩
  decide +kernel
theorem sound522 : certificate522.Sound :=
  rat_witness_certificate_sound certificate522 valid522 MajorityCertificates.Inputs026.envelope_sound522

def certificate523 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope523,(9211/4000),(49689/320000),(5405667221822570221929/1000000000000000000),(504099391/250000000),(18/5),(1337759117/1000000000),0,(281317795224352101/250000000000000000),(206881907472191/200000000000000000)⟩
theorem valid523 : certificate523.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid523,?_⟩
  decide +kernel
theorem sound523 : certificate523.Sound :=
  rat_witness_certificate_sound certificate523 valid523 MajorityCertificates.Inputs026.envelope_sound523

def certificate524 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope524,(2873/1250),(4872583/31250000),(4967120072758941344351/1000000000000000000),(116797591/62500000),(18/5),(12927333/31250000),0,1,(934093668684447/1000000000000000000)⟩
theorem valid524 : certificate524.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid524,?_⟩
  decide +kernel
theorem sound524 : certificate524.Sound :=
  rat_witness_certificate_sound certificate524 valid524 MajorityCertificates.Inputs026.envelope_sound524

def certificate525 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope525,(2873/1250),(4872583/31250000),(4967120072758941344351/1000000000000000000),(1262521/625000),(18/5),(66872649/50000000),0,(1125295687030625319/1000000000000000000),(1132934613376329/1000000000000000000)⟩
theorem valid525 : certificate525.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid525,?_⟩
  decide +kernel
theorem sound525 : certificate525.Sound :=
  rat_witness_certificate_sound certificate525 valid525 MajorityCertificates.Inputs026.envelope_sound525

def certificate526 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope526,(45883/20000),(39141797/250000000),(572921868759744189203/125000000000000000),(374276917/200000000),(73/20),(415637481/1000000000),0,1,(31505159667067/31250000000000000)⟩
theorem valid526 : certificate526.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid526,?_⟩
  decide +kernel
theorem sound526 : certificate526.Sound :=
  rat_witness_certificate_sound certificate526 valid526 MajorityCertificates.Inputs026.envelope_sound526

def certificate527 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope527,(45883/20000),(39141797/250000000),(572921868759744189203/125000000000000000),(50681461/25000000),(73/20),(1334784361/1000000000),0,(225064208564022953/200000000000000000),(306737926916159/250000000000000000)⟩
theorem valid527 : certificate527.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid527,?_⟩
  decide +kernel
theorem sound527 : certificate527.Sound :=
  rat_witness_certificate_sound certificate527 valid527 MajorityCertificates.Inputs026.envelope_sound527

def certificate528 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope528,(228999/100000),(25257/160000),(265349954764930120907/62500000000000000),(1877828633/1000000000),(73/20),(209497409/500000000),0,1,(548254706428033/500000000000000000)⟩
theorem valid528 : certificate528.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid528,?_⟩
  decide +kernel
theorem sound528 : certificate528.Sound :=
  rat_witness_certificate_sound certificate528 valid528 MajorityCertificates.Inputs026.envelope_sound528

def certificate529 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope529,(228999/100000),(25257/160000),(265349954764930120907/62500000000000000),(7929359/3906250),(73/20),(1334489539/1000000000),0,(281336805139400129/250000000000000000),(1332759751987063/1000000000000000000)⟩
theorem valid529 : certificate529.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid529,?_⟩
  decide +kernel
theorem sound529 : certificate529.Sound :=
  rat_witness_certificate_sound certificate529 valid529 MajorityCertificates.Inputs026.envelope_sound529

def certificate530 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope530,(228591/100000),(158500781/1000000000),(1973339312607329729513/500000000000000000),(23538419/12500000),(37/10),(420675951/1000000000),0,1,(590357814544379/500000000000000000)⟩
theorem valid530 : certificate530.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid530,?_⟩
  decide +kernel
theorem sound530 : certificate530.Sound :=
  rat_witness_certificate_sound certificate530 valid530 MajorityCertificates.Inputs026.envelope_sound530

def certificate531 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope531,(228591/100000),(158500781/1000000000),(1973339312607329729513/500000000000000000),(407405603/200000000),(37/10),(1331942711/1000000000),0,(1125374192623199309/1000000000000000000),(17912699451749/12500000000000000)⟩
theorem valid531 : certificate531.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid531,?_⟩
  decide +kernel
theorem sound531 : certificate531.Sound :=
  rat_witness_certificate_sound certificate531 valid531 MajorityCertificates.Inputs026.envelope_sound531

def certificate532 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope532,(228193/100000),(159145313/1000000000),(3680829937447970025631/1000000000000000000),(472083861/250000000),(37/10),(422353719/1000000000),0,1,(633589209981383/500000000000000000)⟩
theorem valid532 : certificate532.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid532,?_⟩
  decide +kernel
theorem sound532 : certificate532.Sound :=
  rat_witness_certificate_sound certificate532 valid532 MajorityCertificates.Inputs026.envelope_sound532

def certificate533 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope533,(228193/100000),(159145313/1000000000),(3680829937447970025631/1000000000000000000),(1020225129/500000000),(37/10),(665873321/500000000),0,(1125401926245943707/1000000000000000000),(386053575112201/250000000000000000)⟩
theorem valid533 : certificate533.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid533,?_⟩
  decide +kernel
theorem sound533 : certificate533.Sound :=
  rat_witness_certificate_sound certificate533 valid533 MajorityCertificates.Inputs026.envelope_sound533

def certificate534 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope534,(56951/25000),(39947461/250000000),(3443312750537497668733/1000000000000000000),(1893541717/1000000000),(15/4),(424036873/1000000000),0,1,(339003811692693/250000000000000000)⟩
theorem valid534 : certificate534.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid534,?_⟩
  decide +kernel
theorem sound534 : certificate534.Sound :=
  rat_witness_certificate_sound certificate534 valid534 MajorityCertificates.Inputs026.envelope_sound534

def certificate535 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope535,(56951/25000),(39947461/250000000),(3443312750537497668733/1000000000000000000),(409494661/200000000),(15/4),(1329288937/1000000000),0,(17584849890098291/15625000000000000),(1651779698807101/1000000000000000000)⟩
theorem valid535 : certificate535.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid535,?_⟩
  decide +kernel
theorem sound535 : certificate535.Sound :=
  rat_witness_certificate_sound certificate535 valid535 MajorityCertificates.Inputs026.envelope_sound535

def certificate536 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope536,(227423/100000),(51339/320000),(1615105516787295487701/500000000000000000),(1899144969/1000000000),(15/4),(425678977/1000000000),0,1,(1449428536980661/1000000000000000000)⟩
theorem valid536 : certificate536.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid536,?_⟩
  decide +kernel
theorem sound536 : certificate536.Sound :=
  rat_witness_certificate_sound certificate536 valid536 MajorityCertificates.Inputs026.envelope_sound536

def certificate537 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope537,(227423/100000),(51339/320000),(1615105516787295487701/500000000000000000),(410057893/200000000),(15/4),(1329462773/1000000000),0,(1125459564482601817/1000000000000000000),(1766533162546739/1000000000000000000)⟩
theorem valid537 : certificate537.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid537,?_⟩
  decide +kernel
theorem sound537 : certificate537.Sound :=
  rat_witness_certificate_sound certificate537 valid537 MajorityCertificates.Inputs026.envelope_sound537

def certificate538 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs026.envelope538,(4541/2000),(51339/320000),(3038266549588119464343/1000000000000000000),(1906218281/1000000000),(19/5),(17013739/40000000),0,1,(771431198337369/500000000000000000)⟩
theorem valid538 : certificate538.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid538,?_⟩
  decide +kernel
theorem sound538 : certificate538.Sound :=
  rat_witness_certificate_sound certificate538 valid538 MajorityCertificates.Inputs026.envelope_sound538

def certificate539 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs026.envelope539,(4541/2000),(51339/320000),(3038266549588119464343/1000000000000000000),(2058575147/1000000000),(19/5),(663414083/500000000),0,(112548941053848199/100000000000000000),(1883121635670639/1000000000000000000)⟩
theorem valid539 : certificate539.Valid := by
  refine ⟨MajorityCertificates.Inputs026.inputs_valid539,?_⟩
  decide +kernel
theorem sound539 : certificate539.Sound :=
  rat_witness_certificate_sound certificate539 valid539 MajorityCertificates.Inputs026.envelope_sound539

def certificates : List RatWitnessCertificate := [certificate520,certificate521,certificate522,certificate523,certificate524,certificate525,certificate526,certificate527,certificate528,certificate529,certificate530,certificate531,certificate532,certificate533,certificate534,certificate535,certificate536,certificate537,certificate538,certificate539]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound520,List.forall_mem_cons.mpr ⟨sound521,List.forall_mem_cons.mpr ⟨sound522,List.forall_mem_cons.mpr ⟨sound523,List.forall_mem_cons.mpr ⟨sound524,List.forall_mem_cons.mpr ⟨sound525,List.forall_mem_cons.mpr ⟨sound526,List.forall_mem_cons.mpr ⟨sound527,List.forall_mem_cons.mpr ⟨sound528,List.forall_mem_cons.mpr ⟨sound529,List.forall_mem_cons.mpr ⟨sound530,List.forall_mem_cons.mpr ⟨sound531,List.forall_mem_cons.mpr ⟨sound532,List.forall_mem_cons.mpr ⟨sound533,List.forall_mem_cons.mpr ⟨sound534,List.forall_mem_cons.mpr ⟨sound535,List.forall_mem_cons.mpr ⟨sound536,List.forall_mem_cons.mpr ⟨sound537,List.forall_mem_cons.mpr ⟨sound538,List.forall_mem_cons.mpr ⟨sound539,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch026
