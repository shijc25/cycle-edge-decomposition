import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch031

def certificate620 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope620,(219127/100000),(67004297/500000000),(964357342583473521597/1000000000000000000),(1100404377/500000000),(101/20),(337371673/1000000000),0,1,(1044751746481913/200000000000000000)⟩
theorem valid620 : certificate620.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid620,?_⟩
  decide +kernel
theorem sound620 : certificate620.Sound :=
  rat_witness_certificate_sound certificate620 valid620 MajorityCertificates.Inputs031.envelope_sound620

def certificate621 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope621,(219127/100000),(67004297/500000000),(964357342583473521597/1000000000000000000),(2267736533/1000000000),(101/20),(1304163553/1000000000),0,(1126598893941632351/1000000000000000000),(6655148741295103/1000000000000000000)⟩
theorem valid621 : certificate621.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid621,?_⟩
  decide +kernel
theorem sound621 : certificate621.Sound :=
  rat_witness_certificate_sound certificate621 valid621 MajorityCertificates.Inputs031.envelope_sound621

def certificate622 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope622,(109529/50000),(132719531/1000000000),(477293369344536448549/500000000000000000),(551951411/250000000),(51/10),(333592077/1000000000),0,1,(1326801599828629/250000000000000000)⟩
theorem valid622 : certificate622.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid622,?_⟩
  decide +kernel
theorem sound622 : certificate622.Sound :=
  rat_witness_certificate_sound certificate622 valid622 MajorityCertificates.Inputs031.envelope_sound622

def certificate623 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope623,(109529/50000),(132719531/1000000000),(477293369344536448549/500000000000000000),(2273329607/1000000000),(51/10),(325922873/250000000),0,(225323157386919833/200000000000000000),(336367052483551/50000000000000000)⟩
theorem valid623 : certificate623.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid623,?_⟩
  decide +kernel
theorem sound623 : certificate623.Sound :=
  rat_witness_certificate_sound certificate623 valid623 MajorityCertificates.Inputs031.envelope_sound623

def certificate624 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope624,(21899/10000),(131430469/1000000000),(945071694641299341683/1000000000000000000),(553617607/250000000),(103/20),(206151/625000),0,1,(5376421350593989/1000000000000000000)⟩
theorem valid624 : certificate624.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid624,?_⟩
  decide +kernel
theorem sound624 : certificate624.Sound :=
  rat_witness_certificate_sound certificate624 valid624 MajorityCertificates.Inputs031.envelope_sound624

def certificate625 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope625,(21899/10000),(131430469/1000000000),(945071694641299341683/1000000000000000000),(2279031753/1000000000),(103/20),(32579709/25000000),0,(563316290246868481/500000000000000000),(6797621304198009/1000000000000000000)⟩
theorem valid625 : certificate625.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid625,?_⟩
  decide +kernel
theorem sound625 : certificate625.Sound :=
  rat_witness_certificate_sound certificate625 valid625 MajorityCertificates.Inputs031.envelope_sound625

def certificate626 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope626,(54751/25000),(65392969/500000000),(11791708434151031007/12500000000000000),(2219984541/1000000000),(103/20),(65562583/200000000),0,1,(5369262860107523/1000000000000000000)⟩
theorem valid626 : certificate626.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid626,?_⟩
  decide +kernel
theorem sound626 : certificate626.Sound :=
  rat_witness_certificate_sound certificate626 valid626 MajorityCertificates.Inputs031.envelope_sound626

def certificate627 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope627,(54751/25000),(65392969/500000000),(11791708434151031007/12500000000000000),(228075953/100000000),(103/20),(162877697/125000000),0,(17603679404952223/15625000000000000),(6841975502091379/1000000000000000000)⟩
theorem valid627 : certificate627.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid627,?_⟩
  decide +kernel
theorem sound627 : certificate627.Sound :=
  rat_witness_certificate_sound certificate627 valid627 MajorityCertificates.Inputs031.envelope_sound627

def certificate628 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope628,(218971/100000),(65070703/500000000),(938727443778951818319/1000000000000000000),(2223089589/1000000000),(26/5),(325959263/1000000000),0,1,(5403563111921433/1000000000000000000)⟩
theorem valid628 : certificate628.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid628,?_⟩
  decide +kernel
theorem sound628 : certificate628.Sound :=
  rat_witness_certificate_sound certificate628 valid628 MajorityCertificates.Inputs031.envelope_sound628

def certificate629 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope629,(218971/100000),(65070703/500000000),(938727443778951818319/1000000000000000000),(2284890789/1000000000),(26/5),(130229891/100000000),0,(1126643769362177637/1000000000000000000),(6861570040585511/1000000000000000000)⟩
theorem valid629 : certificate629.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid629,?_⟩
  decide +kernel
theorem sound629 : certificate629.Sound :=
  rat_witness_certificate_sound certificate629 valid629 MajorityCertificates.Inputs031.envelope_sound629

def certificate630 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope630,(109469/50000),(41439/320000),(23354465164861497557/25000000000000000),(1113494229/500000000),(26/5),(8101761/25000000),0,1,(2726890136294657/500000000000000000)⟩
theorem valid630 : certificate630.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid630,?_⟩
  decide +kernel
theorem sound630 : certificate630.Sound :=
  rat_witness_certificate_sound certificate630 valid630 MajorityCertificates.Inputs031.envelope_sound630

def certificate631 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope631,(109469/50000),(41439/320000),(23354465164861497557/25000000000000000),(1143231009/500000000),(26/5),(1302546929/1000000000),0,(225330406366655057/200000000000000000),(6912461306653271/1000000000000000000)⟩
theorem valid631 : certificate631.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid631,?_⟩
  decide +kernel
theorem sound631 : certificate631.Sound :=
  rat_witness_certificate_sound certificate631 valid631 MajorityCertificates.Inputs031.envelope_sound631

def certificate632 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope632,(109453/50000),(16106543/125000000),(929689298073764836353/1000000000000000000),(2230453093/1000000000),(26/5),(322204683/1000000000),0,1,(5490111323521921/1000000000000000000)⟩
theorem valid632 : certificate632.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid632,?_⟩
  decide +kernel
theorem sound632 : certificate632.Sound :=
  rat_witness_certificate_sound certificate632 valid632 MajorityCertificates.Inputs031.envelope_sound632

def certificate633 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope633,(109453/50000),(16106543/125000000),(929689298073764836353/1000000000000000000),(71491441/31250000),(26/5),(130295043/100000000),0,(1126660261304792761/1000000000000000000),(55755373872471/8000000000000000)⟩
theorem valid633 : certificate633.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid633,?_⟩
  decide +kernel
theorem sound633 : certificate633.Sound :=
  rat_witness_certificate_sound certificate633 valid633 MajorityCertificates.Inputs031.envelope_sound633

def certificate634 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope634,(109437/50000),(128207813/1000000000),(462629335143013743249/500000000000000000),(2233535287/1000000000),(21/4),(80090531/250000000),0,1,(5525091473577199/1000000000000000000)⟩
theorem valid634 : certificate634.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid634,?_⟩
  decide +kernel
theorem sound634 : certificate634.Sound :=
  rat_witness_certificate_sound certificate634 valid634 MajorityCertificates.Inputs031.envelope_sound634

def certificate635 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope635,(109437/50000),(128207813/1000000000),(462629335143013743249/500000000000000000),(2292021503/1000000000),(21/4),(65108237/50000000),0,(281667116215325243/250000000000000000),(3492868003309109/500000000000000000)⟩
theorem valid635 : certificate635.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid635,?_⟩
  decide +kernel
theorem sound635 : certificate635.Sound :=
  rat_witness_certificate_sound certificate635 valid635 MajorityCertificates.Inputs031.envelope_sound635

def certificate636 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope636,(218843/100000),(127563281/1000000000),(920885892078861988323/1000000000000000000),(2236822499/1000000000),(21/4),(318508113/1000000000),0,1,(5543877701066383/1000000000000000000)⟩
theorem valid636 : certificate636.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid636,?_⟩
  decide +kernel
theorem sound636 : certificate636.Sound :=
  rat_witness_certificate_sound certificate636 valid636 MajorityCertificates.Inputs031.envelope_sound636

def certificate637 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope637,(218843/100000),(127563281/1000000000),(920885892078861988323/1000000000000000000),(2293597021/1000000000),(21/4),(1302415501/1000000000),0,(70417289650188923/62500000000000000),(7036846794986257/1000000000000000000)⟩
theorem valid637 : certificate637.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid637,?_⟩
  decide +kernel
theorem sound637 : certificate637.Sound :=
  rat_witness_certificate_sound certificate637 valid637 MajorityCertificates.Inputs031.envelope_sound637

def certificate638 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs031.envelope638,(218733/100000),(126274219/1000000000),(909423140879630589347/1000000000000000000),(224882809/100000000),(21/4),(157322321/500000000),0,1,(1486964436485471/250000000000000000)⟩
theorem valid638 : certificate638.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid638,?_⟩
  decide +kernel
theorem sound638 : certificate638.Sound :=
  rat_witness_certificate_sound certificate638 valid638 MajorityCertificates.Inputs031.envelope_sound638

def certificate639 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs031.envelope639,(218733/100000),(126274219/1000000000),(909423140879630589347/1000000000000000000),(2296303979/1000000000),(21/4),(1303493847/1000000000),0,(70418665438987321/62500000000000000),(3576220153859997/500000000000000000)⟩
theorem valid639 : certificate639.Valid := by
  refine ⟨MajorityCertificates.Inputs031.inputs_valid639,?_⟩
  decide +kernel
theorem sound639 : certificate639.Sound :=
  rat_witness_certificate_sound certificate639 valid639 MajorityCertificates.Inputs031.envelope_sound639

def certificates : List RatWitnessCertificate := [certificate620,certificate621,certificate622,certificate623,certificate624,certificate625,certificate626,certificate627,certificate628,certificate629,certificate630,certificate631,certificate632,certificate633,certificate634,certificate635,certificate636,certificate637,certificate638,certificate639]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound620,List.forall_mem_cons.mpr ⟨sound621,List.forall_mem_cons.mpr ⟨sound622,List.forall_mem_cons.mpr ⟨sound623,List.forall_mem_cons.mpr ⟨sound624,List.forall_mem_cons.mpr ⟨sound625,List.forall_mem_cons.mpr ⟨sound626,List.forall_mem_cons.mpr ⟨sound627,List.forall_mem_cons.mpr ⟨sound628,List.forall_mem_cons.mpr ⟨sound629,List.forall_mem_cons.mpr ⟨sound630,List.forall_mem_cons.mpr ⟨sound631,List.forall_mem_cons.mpr ⟨sound632,List.forall_mem_cons.mpr ⟨sound633,List.forall_mem_cons.mpr ⟨sound634,List.forall_mem_cons.mpr ⟨sound635,List.forall_mem_cons.mpr ⟨sound636,List.forall_mem_cons.mpr ⟨sound637,List.forall_mem_cons.mpr ⟨sound638,List.forall_mem_cons.mpr ⟨sound639,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch031
