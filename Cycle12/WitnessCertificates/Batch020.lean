import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs020

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch020

def certificate400 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope400,(10737/5000),(152055469/1000000000),(50254071499741935531/62500000000000000),(400758791/200000000),(51/20),(50736723/125000000),0,1,(6053000679515833/1000000000000000000)⟩
theorem valid400 : certificate400.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid400,?_⟩
  decide +kernel
theorem sound400 : certificate400.Sound :=
  rat_witness_certificate_sound certificate400 valid400 MajorityCertificates.Inputs020.envelope_sound400

def certificate401 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope401,(10737/5000),(152055469/1000000000),(50254071499741935531/62500000000000000),(1153771781/500000000),(51/20),(127762219/100000000),0,(225391459475980513/200000000000000000),(1417643042661023/250000000000000000)⟩
theorem valid401 : certificate401.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid401,?_⟩
  decide +kernel
theorem sound401 : certificate401.Sound :=
  rat_witness_certificate_sound certificate401 valid401 MajorityCertificates.Inputs020.envelope_sound401

def certificate402 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope402,(42859/20000),(152055469/1000000000),(153938020535635409411/200000000000000000),(402861329/200000000),(51/20),(81089523/200000000),0,1,(6352520547490979/1000000000000000000)⟩
theorem valid402 : certificate402.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid402,?_⟩
  decide +kernel
theorem sound402 : certificate402.Sound :=
  rat_witness_certificate_sound certificate402 valid402 MajorityCertificates.Inputs020.envelope_sound402

def certificate403 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope403,(42859/20000),(152055469/1000000000),(153938020535635409411/200000000000000000),(57791721/25000000),(51/20),(639527409/500000000),0,(1127049087836787949/1000000000000000000),(186623868691587/31250000000000000)⟩
theorem valid403 : certificate403.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid403,?_⟩
  decide +kernel
theorem sound403 : certificate403.Sound :=
  rat_witness_certificate_sound certificate403 valid403 MajorityCertificates.Inputs020.envelope_sound403

def certificate404 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope404,(106931/50000),(75705469/500000000),(737870866433231862963/1000000000000000000),(2024331511/1000000000),(51/20),(403238211/1000000000),0,1,(3364914711391747/500000000000000000)⟩
theorem valid404 : certificate404.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid404,?_⟩
  decide +kernel
theorem sound404 : certificate404.Sound :=
  rat_witness_certificate_sound certificate404 valid404 MajorityCertificates.Inputs020.envelope_sound404

def certificate405 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope405,(106931/50000),(75705469/500000000),(737870866433231862963/1000000000000000000),(463408149/200000000),(51/20),(1280369713/1000000000),0,(1127141915596467181/1000000000000000000),(6276580602573149/1000000000000000000)⟩
theorem valid405 : certificate405.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid405,?_⟩
  decide +kernel
theorem sound405 : certificate405.Sound :=
  rat_witness_certificate_sound certificate405 valid405 MajorityCertificates.Inputs020.envelope_sound405

def certificate406 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope406,(1334/625),(75705469/500000000),(708361321849244584829/1000000000000000000),(505832629/250000000),(13/5),(403836991/1000000000),0,1,(6930608814795809/1000000000000000000)⟩
theorem valid406 : certificate406.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid406,?_⟩
  decide +kernel
theorem sound406 : certificate406.Sound :=
  rat_witness_certificate_sound certificate406 valid406 MajorityCertificates.Inputs020.envelope_sound406

def certificate407 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope407,(1334/625),(75705469/500000000),(708361321849244584829/1000000000000000000),(2325516729/1000000000),(13/5),(320049037/250000000),0,(563617850699323073/500000000000000000),(3268929478856079/500000000000000000)⟩
theorem valid407 : certificate407.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid407,?_⟩
  decide +kernel
theorem sound407 : certificate407.Sound :=
  rat_witness_certificate_sound certificate407 valid407 MajorityCertificates.Inputs020.envelope_sound407

def certificate408 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope408,(213029/100000),(75383203/500000000),(340472333310433663033/500000000000000000),(2036733161/1000000000),(13/5),(40128291/100000000),0,1,(3621740236894439/500000000000000000)⟩
theorem valid408 : certificate408.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid408,?_⟩
  decide +kernel
theorem sound408 : certificate408.Sound :=
  rat_witness_certificate_sound certificate408 valid408 MajorityCertificates.Inputs020.envelope_sound408

def certificate409 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope409,(213029/100000),(75383203/500000000),(340472333310433663033/500000000000000000),(2330359511/1000000000),(13/5),(1281733997/1000000000),0,(563665177988162963/500000000000000000),(6858830485224067/1000000000000000000)⟩
theorem valid409 : certificate409.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid409,?_⟩
  decide +kernel
theorem sound409 : certificate409.Sound :=
  rat_witness_certificate_sound certificate409 valid409 MajorityCertificates.Inputs020.envelope_sound409

def certificate410 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope410,(21263/10000),(48039/320000),(131085861669213648269/200000000000000000),(2036190567/1000000000),(53/20),(400265631/1000000000),0,1,(842132795817753/100000000000000000)⟩
theorem valid410 : certificate410.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid410,?_⟩
  decide +kernel
theorem sound410 : certificate410.Sound :=
  rat_witness_certificate_sound certificate410 valid410 MajorityCertificates.Inputs020.envelope_sound410

def certificate411 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope411,(21263/10000),(48039/320000),(131085861669213648269/200000000000000000),(1169752617/500000000),(53/20),(160219391/125000000),0,(1127425777804372929/1000000000000000000),(7130160566592387/1000000000000000000)⟩
theorem valid411 : certificate411.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid411,?_⟩
  decide +kernel
theorem sound411 : certificate411.Sound :=
  rat_witness_certificate_sound certificate411 valid411 MajorityCertificates.Inputs020.envelope_sound411

def certificate412 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope412,(212241/100000),(4671167/31250000),(2526581676441047349/4000000000000000),(2053101797/1000000000),(53/20),(198569491/500000000),0,1,(3928973055132921/500000000000000000)⟩
theorem valid412 : certificate412.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid412,?_⟩
  decide +kernel
theorem sound412 : certificate412.Sound :=
  rat_witness_certificate_sound certificate412 valid412 MajorityCertificates.Inputs020.envelope_sound412

def certificate413 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope413,(212241/100000),(4671167/31250000),(2526581676441047349/4000000000000000),(1172266527/500000000),(53/20),(1283187783/1000000000),0,(9020175187092547/8000000000000000),(7457019935744193/1000000000000000000)⟩
theorem valid413 : certificate413.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid413,?_⟩
  decide +kernel
theorem sound413 : certificate413.Sound :=
  rat_witness_certificate_sound certificate413 valid413 MajorityCertificates.Inputs020.envelope_sound413

def certificate414 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope414,(211863/100000),(148188281/1000000000),(609442028547261214253/1000000000000000000),(2063474751/1000000000),(27/10),(393053399/1000000000),0,1,(1639636973067571/200000000000000000)⟩
theorem valid414 : certificate414.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid414,?_⟩
  decide +kernel
theorem sound414 : certificate414.Sound :=
  rat_witness_certificate_sound certificate414 valid414 MajorityCertificates.Inputs020.envelope_sound414

def certificate415 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope415,(211863/100000),(148188281/1000000000),(609442028547261214253/1000000000000000000),(294321483/125000000),(27/10),(641661191/500000000),0,(1127618615166805333/1000000000000000000),(7735385326507821/1000000000000000000)⟩
theorem valid415 : certificate415.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid415,?_⟩
  decide +kernel
theorem sound415 : certificate415.Sound :=
  rat_witness_certificate_sound certificate415 valid415 MajorityCertificates.Inputs020.envelope_sound415

def certificate416 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope416,(26437/12500),(23607/160000),(588684561178441291931/1000000000000000000),(129466589/62500000),(27/10),(195495767/500000000),0,1,(4244201433068081/500000000000000000)⟩
theorem valid416 : certificate416.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid416,?_⟩
  decide +kernel
theorem sound416 : certificate416.Sound :=
  rat_witness_certificate_sound certificate416 valid416 MajorityCertificates.Inputs020.envelope_sound416

def certificate417 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope417,(26437/12500),(23607/160000),(588684561178441291931/1000000000000000000),(1179637983/500000000),(27/10),(321219767/250000000),0,(1127715835879673777/1000000000000000000),(8075643332682643/1000000000000000000)⟩
theorem valid417 : certificate417.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid417,?_⟩
  decide +kernel
theorem sound417 : certificate417.Sound :=
  rat_witness_certificate_sound certificate417 valid417 MajorityCertificates.Inputs020.envelope_sound417

def certificate418 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs020.envelope418,(10557/5000),(146899219/1000000000),(284626370994771218563/500000000000000000),(2079545691/1000000000),(11/4),(194463589/500000000),0,1,(4403285351691487/500000000000000000)⟩
theorem valid418 : certificate418.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid418,?_⟩
  decide +kernel
theorem sound418 : certificate418.Sound :=
  rat_witness_certificate_sound certificate418 valid418 MajorityCertificates.Inputs020.envelope_sound418

def certificate419 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs020.envelope419,(10557/5000),(146899219/1000000000),(284626370994771218563/500000000000000000),(94723019/40000000),(11/4),(160638847/125000000),0,(563906733827241141/500000000000000000),(334399614480949/40000000000000000)⟩
theorem valid419 : certificate419.Valid := by
  refine ⟨MajorityCertificates.Inputs020.inputs_valid419,?_⟩
  decide +kernel
theorem sound419 : certificate419.Sound :=
  rat_witness_certificate_sound certificate419 valid419 MajorityCertificates.Inputs020.envelope_sound419

def certificates : List RatWitnessCertificate := [certificate400,certificate401,certificate402,certificate403,certificate404,certificate405,certificate406,certificate407,certificate408,certificate409,certificate410,certificate411,certificate412,certificate413,certificate414,certificate415,certificate416,certificate417,certificate418,certificate419]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound400,List.forall_mem_cons.mpr ⟨sound401,List.forall_mem_cons.mpr ⟨sound402,List.forall_mem_cons.mpr ⟨sound403,List.forall_mem_cons.mpr ⟨sound404,List.forall_mem_cons.mpr ⟨sound405,List.forall_mem_cons.mpr ⟨sound406,List.forall_mem_cons.mpr ⟨sound407,List.forall_mem_cons.mpr ⟨sound408,List.forall_mem_cons.mpr ⟨sound409,List.forall_mem_cons.mpr ⟨sound410,List.forall_mem_cons.mpr ⟨sound411,List.forall_mem_cons.mpr ⟨sound412,List.forall_mem_cons.mpr ⟨sound413,List.forall_mem_cons.mpr ⟨sound414,List.forall_mem_cons.mpr ⟨sound415,List.forall_mem_cons.mpr ⟨sound416,List.forall_mem_cons.mpr ⟨sound417,List.forall_mem_cons.mpr ⟨sound418,List.forall_mem_cons.mpr ⟨sound419,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch020
