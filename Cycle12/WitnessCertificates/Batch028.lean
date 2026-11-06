import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch028

def certificate560 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope560,(8939/4000),(162367969/1000000000),(354187289948331892891/200000000000000000),(989644359/500000000),(41/10),(213790781/500000000),0,1,(2703891699845947/1000000000000000000)⟩
theorem valid560 : certificate560.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid560,?_⟩
  decide +kernel
theorem sound560 : certificate560.Sound :=
  rat_witness_certificate_sound certificate560 valid560 MajorityCertificates.Inputs028.envelope_sound560

def certificate561 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope561,(8939/4000),(162367969/1000000000),(354187289948331892891/200000000000000000),(2119782419/1000000000),(41/10),(1314828477/1000000000),0,(225170658516425149/200000000000000000),(832490067788311/250000000000000000)⟩
theorem valid561 : certificate561.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid561,?_⟩
  decide +kernel
theorem sound561 : certificate561.Sound :=
  rat_witness_certificate_sound certificate561 valid561 MajorityCertificates.Inputs028.envelope_sound561

def certificate562 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope562,(44639/20000),(80861719/500000000),(1702396676814811822403/1000000000000000000),(994131043/500000000),(83/20),(13288599/31250000),0,1,(2817524148763533/1000000000000000000)⟩
theorem valid562 : certificate562.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid562,?_⟩
  decide +kernel
theorem sound562 : certificate562.Sound :=
  rat_witness_certificate_sound certificate562 valid562 MajorityCertificates.Inputs028.envelope_sound562

def certificate563 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope563,(44639/20000),(80861719/500000000),(1702396676814811822403/1000000000000000000),(1063844703/500000000),(83/20),(1313148323/1000000000),0,(1125888782136372959/1000000000000000000),(346479720352069/100000000000000000)⟩
theorem valid563 : certificate563.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid563,?_⟩
  decide +kernel
theorem sound563 : certificate563.Sound :=
  rat_witness_certificate_sound certificate563 valid563 MajorityCertificates.Inputs028.envelope_sound563

def certificate564 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope564,(222923/100000),(80539453/500000000),(1638610208469183050743/1000000000000000000),(998571023/500000000),(21/5),(211451993/500000000),0,1,(293251815046197/100000000000000000)⟩
theorem valid564 : certificate564.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid564,?_⟩
  decide +kernel
theorem sound564 : certificate564.Sound :=
  rat_witness_certificate_sound certificate564 valid564 MajorityCertificates.Inputs028.envelope_sound564

def certificate565 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope565,(222923/100000),(80539453/500000000),(1638610208469183050743/1000000000000000000),(2135309341/1000000000),(21/5),(327910241/250000000),0,(1125924529411343307/1000000000000000000),(1797029892535081/500000000000000000)⟩
theorem valid565 : certificate565.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid565,?_⟩
  decide +kernel
theorem sound565 : certificate565.Sound :=
  rat_witness_certificate_sound certificate565 valid565 MajorityCertificates.Inputs028.envelope_sound565

def certificate566 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope566,(222657/100000),(80539453/500000000),(1542141089801017007/976562500000000),(2003758153/1000000000),(21/5),(52825883/125000000),0,1,(3038987611053887/1000000000000000000)⟩
theorem valid566 : certificate566.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid566,?_⟩
  decide +kernel
theorem sound566 : certificate566.Sound :=
  rat_witness_certificate_sound certificate566 valid566 MajorityCertificates.Inputs028.envelope_sound566

def certificate567 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope567,(222657/100000),(80539453/500000000),(1542141089801017007/976562500000000),(2139150657/1000000000),(21/5),(655805917/500000000),0,(225192101890351767/200000000000000000),(1879997332910947/500000000000000000)⟩
theorem valid567 : certificate567.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid567,?_⟩
  decide +kernel
theorem sound567 : certificate567.Sound :=
  rat_witness_certificate_sound certificate567 valid567 MajorityCertificates.Inputs028.envelope_sound567

def certificate568 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope568,(111199/50000),(51339/320000),(1523646054422456694899/1000000000000000000),(2005450421/1000000000),(17/4),(420910537/1000000000),0,1,(313259524050137/100000000000000000)⟩
theorem valid568 : certificate568.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid568,?_⟩
  decide +kernel
theorem sound568 : certificate568.Sound :=
  rat_witness_certificate_sound certificate568 valid568 MajorityCertificates.Inputs028.envelope_sound568

def certificate569 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope569,(111199/50000),(51339/320000),(1523646054422456694899/1000000000000000000),(2146133117/1000000000),(17/4),(655246571/500000000),0,(1125996685055047987/1000000000000000000),(1951470005311251/500000000000000000)⟩
theorem valid569 : certificate569.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid569,?_⟩
  decide +kernel
theorem sound569 : certificate569.Sound :=
  rat_witness_certificate_sound certificate569 valid569 MajorityCertificates.Inputs028.envelope_sound569

def certificate570 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope570,(111073/50000),(39947461/250000000),(1471754506257890891311/1000000000000000000),(31580449/15625000),(43/10),(418005099/1000000000),0,1,(410225862094709/125000000000000000)⟩
theorem valid570 : certificate570.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid570,?_⟩
  decide +kernel
theorem sound570 : certificate570.Sound :=
  rat_witness_certificate_sound certificate570 valid570 MajorityCertificates.Inputs028.envelope_sound570

def certificate571 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope571,(111073/50000),(39947461/250000000),(1471754506257890891311/1000000000000000000),(2152732031/1000000000),(43/10),(261920527/200000000),0,(1126033022889689859/1000000000000000000),(506269200242281/125000000000000000)⟩
theorem valid571 : certificate571.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid571,?_⟩
  decide +kernel
theorem sound571 : certificate571.Sound :=
  rat_witness_certificate_sound certificate571 valid571 MajorityCertificates.Inputs028.envelope_sound571

def certificate572 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope572,(110951/50000),(159145313/1000000000),(355794286259728427773/250000000000000000),(1014594379/500000000),(43/10),(415766251/1000000000),0,1,(1699024265108473/500000000000000000)⟩
theorem valid572 : certificate572.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid572,?_⟩
  decide +kernel
theorem sound572 : certificate572.Sound :=
  rat_witness_certificate_sound certificate572 valid572 MajorityCertificates.Inputs028.envelope_sound572

def certificate573 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope573,(110951/50000),(159145313/1000000000),(355794286259728427773/250000000000000000),(2155967281/1000000000),(43/10),(1310381583/1000000000),0,(1126069484704612187/1000000000000000000),(2112495677877237/500000000000000000)⟩
theorem valid573 : certificate573.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid573,?_⟩
  decide +kernel
theorem sound573 : certificate573.Sound :=
  rat_witness_certificate_sound certificate573 valid573 MajorityCertificates.Inputs028.envelope_sound573

def certificate574 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope574,(6927/3125),(25257/160000),(1377644565834100502187/1000000000000000000),(2039173929/1000000000),(87/20),(82310231/200000000),0,1,(702176345722279/200000000000000000)⟩
theorem valid574 : certificate574.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid574,?_⟩
  decide +kernel
theorem sound574 : certificate574.Sound :=
  rat_witness_certificate_sound certificate574 valid574 MajorityCertificates.Inputs028.envelope_sound574

def certificate575 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope575,(6927/3125),(25257/160000),(1377644565834100502187/1000000000000000000),(540822217/250000000),(87/20),(1309614077/1000000000),0,(1126106046469652421/1000000000000000000),(4376740157836899/1000000000000000000)⟩
theorem valid575 : certificate575.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid575,?_⟩
  decide +kernel
theorem sound575 : certificate575.Sound :=
  rat_witness_certificate_sound certificate575 valid575 MajorityCertificates.Inputs028.envelope_sound575

def certificate576 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope576,(221433/100000),(157211719/1000000000),(667457408071121279571/500000000000000000),(2047554299/1000000000),(22/5),(6395311/15625000),0,1,(3629694126624757/1000000000000000000)⟩
theorem valid576 : certificate576.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid576,?_⟩
  decide +kernel
theorem sound576 : certificate576.Sound :=
  rat_witness_certificate_sound certificate576 valid576 MajorityCertificates.Inputs028.envelope_sound576

def certificate577 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope577,(221433/100000),(157211719/1000000000),(667457408071121279571/500000000000000000),(33899869/15625000),(22/5),(16361161/12500000),0,(281535667491443529/250000000000000000),(4529762801573033/1000000000000000000)⟩
theorem valid577 : certificate577.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid577,?_⟩
  decide +kernel
theorem sound577 : certificate577.Sound :=
  rat_witness_certificate_sound certificate577 valid577 MajorityCertificates.Inputs028.envelope_sound577

def certificate578 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs028.envelope578,(27651/12500),(4872583/31250000),(1294770104493794485091/1000000000000000000),(2057642013/1000000000),(89/20),(101276841/250000000),0,1,(3751288391673199/1000000000000000000)⟩
theorem valid578 : certificate578.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid578,?_⟩
  decide +kernel
theorem sound578 : certificate578.Sound :=
  rat_witness_certificate_sound certificate578 valid578 MajorityCertificates.Inputs028.envelope_sound578

def certificate579 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs028.envelope579,(27651/12500),(4872583/31250000),(1294770104493794485091/1000000000000000000),(2176704789/1000000000),(89/20),(1308269097/1000000000),0,(563089663461667769/500000000000000000),(2342570468938613/500000000000000000)⟩
theorem valid579 : certificate579.Valid := by
  refine ⟨MajorityCertificates.Inputs028.inputs_valid579,?_⟩
  decide +kernel
theorem sound579 : certificate579.Sound :=
  rat_witness_certificate_sound certificate579 valid579 MajorityCertificates.Inputs028.envelope_sound579

def certificates : List RatWitnessCertificate := [certificate560,certificate561,certificate562,certificate563,certificate564,certificate565,certificate566,certificate567,certificate568,certificate569,certificate570,certificate571,certificate572,certificate573,certificate574,certificate575,certificate576,certificate577,certificate578,certificate579]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound560,List.forall_mem_cons.mpr ⟨sound561,List.forall_mem_cons.mpr ⟨sound562,List.forall_mem_cons.mpr ⟨sound563,List.forall_mem_cons.mpr ⟨sound564,List.forall_mem_cons.mpr ⟨sound565,List.forall_mem_cons.mpr ⟨sound566,List.forall_mem_cons.mpr ⟨sound567,List.forall_mem_cons.mpr ⟨sound568,List.forall_mem_cons.mpr ⟨sound569,List.forall_mem_cons.mpr ⟨sound570,List.forall_mem_cons.mpr ⟨sound571,List.forall_mem_cons.mpr ⟨sound572,List.forall_mem_cons.mpr ⟨sound573,List.forall_mem_cons.mpr ⟨sound574,List.forall_mem_cons.mpr ⟨sound575,List.forall_mem_cons.mpr ⟨sound576,List.forall_mem_cons.mpr ⟨sound577,List.forall_mem_cons.mpr ⟨sound578,List.forall_mem_cons.mpr ⟨sound579,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch028
