import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch023

def certificate460 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope460,(51717/25000),(60236719/500000000),(374284969214866128027/1000000000000000000),(2256841413/1000000000),(13/4),(308770717/1000000000),0,1,(7323036226997731/500000000000000000)⟩
theorem valid460 : certificate460.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid460,?_⟩
  decide +kernel
theorem sound460 : certificate460.Sound :=
  rat_witness_certificate_sound certificate460 valid460 MajorityCertificates.Inputs023.envelope_sound460

def certificate461 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope461,(51717/25000),(60236719/500000000),(374284969214866128027/1000000000000000000),(156572699/62500000),(13/4),(651218423/500000000),0,(1129372084063609587/1000000000000000000),(13935602627917063/1000000000000000000)⟩
theorem valid461 : certificate461.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid461,?_⟩
  decide +kernel
theorem sound461 : certificate461.Sound :=
  rat_witness_certificate_sound certificate461 valid461 MajorityCertificates.Inputs023.envelope_sound461

def certificate462 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope462,(206777/100000),(38139/320000),(74134781647593655627/200000000000000000),(283098957/125000000),(33/10),(304933849/1000000000),0,1,(7348641899360223/500000000000000000)⟩
theorem valid462 : certificate462.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid462,?_⟩
  decide +kernel
theorem sound462 : certificate462.Sound :=
  rat_witness_certificate_sound certificate462 valid462 MajorityCertificates.Inputs023.envelope_sound462

def certificate463 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope463,(206777/100000),(38139/320000),(74134781647593655627/200000000000000000),(251213661/100000000),(33/10),(1302916119/1000000000),0,(1129416755152675929/1000000000000000000),(7040323030625189/500000000000000000)⟩
theorem valid463 : certificate463.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid463,?_⟩
  decide +kernel
theorem sound463 : certificate463.Sound :=
  rat_witness_certificate_sound certificate463 valid463 MajorityCertificates.Inputs023.envelope_sound463

def certificate464 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope464,(206689/100000),(29634961/250000000),(183578255566301162661/500000000000000000),(2245986699/1000000000),(33/10),(12188793/40000000),0,1,(16309140789832939/1000000000000000000)⟩
theorem valid464 : certificate464.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid464,?_⟩
  decide +kernel
theorem sound464 : certificate464.Sound :=
  rat_witness_certificate_sound certificate464 valid464 MajorityCertificates.Inputs023.envelope_sound464

def certificate465 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope465,(206689/100000),(29634961/250000000),(183578255566301162661/500000000000000000),(2515347667/1000000000),(33/10),(651746167/500000000),0,(564730551452680333/500000000000000000),(713277109053861/50000000000000000)⟩
theorem valid465 : certificate465.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid465,?_⟩
  decide +kernel
theorem sound465 : certificate465.Sound :=
  rat_witness_certificate_sound certificate465 valid465 MajorityCertificates.Inputs023.envelope_sound465

def certificate466 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope466,(206603/100000),(117250781/1000000000),(181865074432318742627/500000000000000000),(2273981843/1000000000),(33/10),(149774507/500000000),0,1,(485185681711607/31250000000000000)⟩
theorem valid466 : certificate466.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid466,?_⟩
  decide +kernel
theorem sound466 : certificate466.Sound :=
  rat_witness_certificate_sound certificate466 valid466 MajorityCertificates.Inputs023.envelope_sound466

def certificate467 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope467,(206603/100000),(117250781/1000000000),(181865074432318742627/500000000000000000),(314895753/125000000),(33/10),(652231221/500000000),0,(1129505137911091923/1000000000000000000),(7241962923704079/500000000000000000)⟩
theorem valid467 : certificate467.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid467,?_⟩
  decide +kernel
theorem sound467 : certificate467.Sound :=
  rat_witness_certificate_sound certificate467 valid467 MajorityCertificates.Inputs023.envelope_sound467

def certificate468 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope468,(206519/100000),(115961719/1000000000),(11262259210868497377/31250000000000000),(2281757399/1000000000),(67/20),(73928383/250000000),0,1,(48073322153863/3125000000000000)⟩
theorem valid468 : certificate468.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid468,?_⟩
  decide +kernel
theorem sound468 : certificate468.Sound :=
  rat_witness_certificate_sound certificate468 valid468 MajorityCertificates.Inputs023.envelope_sound468

def certificate469 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope469,(206519/100000),(115961719/1000000000),(11262259210868497377/31250000000000000),(2526616497/1000000000),(67/20),(652393843/500000000),0,(70596803101615017/62500000000000000),(1826704287079117/125000000000000000)⟩
theorem valid469 : certificate469.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid469,?_⟩
  decide +kernel
theorem sound469 : certificate469.Sound :=
  rat_witness_certificate_sound certificate469 valid469 MajorityCertificates.Inputs023.envelope_sound469

def certificate470 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope470,(206437/100000),(28829297/250000000),(357140519850849198987/1000000000000000000),(1129691813/500000000),(67/20),(29562473/100000000),0,1,(16848060607207701/1000000000000000000)⟩
theorem valid470 : certificate470.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid470,?_⟩
  decide +kernel
theorem sound470 : certificate470.Sound :=
  rat_witness_certificate_sound certificate470 valid470 MajorityCertificates.Inputs023.envelope_sound470

def certificate471 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope471,(206437/100000),(28829297/250000000),(357140519850849198987/1000000000000000000),(2529108941/1000000000),(67/20),(326420399/250000000),0,(564796113786932399/500000000000000000),(14827134495426159/1000000000000000000)⟩
theorem valid471 : certificate471.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid471,?_⟩
  decide +kernel
theorem sound471 : certificate471.Sound :=
  rat_witness_certificate_sound certificate471 valid471 MajorityCertificates.Inputs023.envelope_sound471

def certificate472 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope472,(103179/50000),(36489/320000),(88493122161958402527/250000000000000000),(2293743927/1000000000),(17/5),(1160683/4000000),0,1,(4002389389264167/250000000000000000)⟩
theorem valid472 : certificate472.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid472,?_⟩
  decide +kernel
theorem sound472 : certificate472.Sound :=
  rat_witness_certificate_sound certificate472 valid472 MajorityCertificates.Inputs023.envelope_sound472

def certificate473 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope473,(103179/50000),(36489/320000),(88493122161958402527/250000000000000000),(634138377/250000000),(17/5),(653022793/500000000),0,(1129635238816694997/1000000000000000000),(14957017401448101/1000000000000000000)⟩
theorem valid473 : certificate473.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid473,?_⟩
  decide +kernel
theorem sound473 : certificate473.Sound :=
  rat_witness_certificate_sound certificate473 valid473 MajorityCertificates.Inputs023.envelope_sound473

def certificate474 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope474,(103141/50000),(112739063/1000000000),(175442977448303472037/500000000000000000),(2302942819/1000000000),(17/5),(286319771/1000000000),0,1,(15986739051325607/1000000000000000000)⟩
theorem valid474 : certificate474.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid474,?_⟩
  decide +kernel
theorem sound474 : certificate474.Sound :=
  rat_witness_certificate_sound certificate474 valid474 MajorityCertificates.Inputs023.envelope_sound474

def certificate475 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope475,(103141/50000),(112739063/1000000000),(175442977448303472037/500000000000000000),(508086029/200000000),(17/5),(1307027979/1000000000),0,(1129677872375076529/1000000000000000000),(15180224815020867/1000000000000000000)⟩
theorem valid475 : certificate475.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid475,?_⟩
  decide +kernel
theorem sound475 : certificate475.Sound :=
  rat_witness_certificate_sound certificate475 valid475 MajorityCertificates.Inputs023.envelope_sound475

def certificate476 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope476,(206207/100000),(2229/20000),(347878757732324395133/1000000000000000000),(231032139/100000000),(17/5),(70655633/250000000),0,1,(8087075389915401/500000000000000000)⟩
theorem valid476 : certificate476.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid476,?_⟩
  decide +kernel
theorem sound476 : certificate476.Sound :=
  rat_witness_certificate_sound certificate476 valid476 MajorityCertificates.Inputs023.envelope_sound476

def certificate477 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope477,(206207/100000),(2229/20000),(347878757732324395133/1000000000000000000),(2545241237/1000000000),(17/5),(130761741/100000000),0,(1129720163288942207/1000000000000000000),(1537045683664699/100000000000000000)⟩
theorem valid477 : certificate477.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid477,?_⟩
  decide +kernel
theorem sound477 : certificate477.Sound :=
  rat_witness_certificate_sound certificate477 valid477 MajorityCertificates.Inputs023.envelope_sound477

def certificate478 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs023.envelope478,(41227/20000),(110805469/1000000000),(86237204490772403387/250000000000000000),(36156139/15625000),(69/20),(35106873/125000000),0,1,(4132038717277449/250000000000000000)⟩
theorem valid478 : certificate478.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid478,?_⟩
  decide +kernel
theorem sound478 : certificate478.Sound :=
  rat_witness_certificate_sound certificate478 valid478 MajorityCertificates.Inputs023.envelope_sound478

def certificate479 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs023.envelope479,(41227/20000),(110805469/1000000000),(86237204490772403387/250000000000000000),(25506391/10000000),(69/20),(327054867/250000000),0,(1129762055681570323/1000000000000000000),(969894227704459/62500000000000000)⟩
theorem valid479 : certificate479.Valid := by
  refine ⟨MajorityCertificates.Inputs023.inputs_valid479,?_⟩
  decide +kernel
theorem sound479 : certificate479.Sound :=
  rat_witness_certificate_sound certificate479 valid479 MajorityCertificates.Inputs023.envelope_sound479

def certificates : List RatWitnessCertificate := [certificate460,certificate461,certificate462,certificate463,certificate464,certificate465,certificate466,certificate467,certificate468,certificate469,certificate470,certificate471,certificate472,certificate473,certificate474,certificate475,certificate476,certificate477,certificate478,certificate479]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound460,List.forall_mem_cons.mpr ⟨sound461,List.forall_mem_cons.mpr ⟨sound462,List.forall_mem_cons.mpr ⟨sound463,List.forall_mem_cons.mpr ⟨sound464,List.forall_mem_cons.mpr ⟨sound465,List.forall_mem_cons.mpr ⟨sound466,List.forall_mem_cons.mpr ⟨sound467,List.forall_mem_cons.mpr ⟨sound468,List.forall_mem_cons.mpr ⟨sound469,List.forall_mem_cons.mpr ⟨sound470,List.forall_mem_cons.mpr ⟨sound471,List.forall_mem_cons.mpr ⟨sound472,List.forall_mem_cons.mpr ⟨sound473,List.forall_mem_cons.mpr ⟨sound474,List.forall_mem_cons.mpr ⟨sound475,List.forall_mem_cons.mpr ⟨sound476,List.forall_mem_cons.mpr ⟨sound477,List.forall_mem_cons.mpr ⟨sound478,List.forall_mem_cons.mpr ⟨sound479,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch023
