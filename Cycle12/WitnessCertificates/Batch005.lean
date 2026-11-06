import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch005

def certificate100 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope100,(202141/100000),(9261803/62500000),(16467182378646085509/50000000000000000),(2046228719/1000000000),(37/20),(50986027/125000000),0,1,(79144450974431/5000000000000000)⟩
theorem valid100 : certificate100.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid100,?_⟩
  decide +kernel
theorem sound100 : certificate100.Sound :=
  rat_witness_certificate_sound certificate100 valid100 MajorityCertificates.Inputs005.envelope_sound100

def certificate101 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope101,(202141/100000),(9261803/62500000),(16467182378646085509/50000000000000000),(1219107589/500000000),(37/20),(262063887/200000000),0,(282521845831525679/250000000000000000),(1713406996608393/125000000000000000)⟩
theorem valid101 : certificate101.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid101,?_⟩
  decide +kernel
theorem sound101 : certificate101.Sound :=
  rat_witness_certificate_sound certificate101 valid101 MajorityCertificates.Inputs005.envelope_sound101

def certificate102 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope102,(8083/4000),(29605543/200000000),(65421735753294979399/200000000000000000),(2050618371/1000000000),(37/20),(25442381/62500000),0,1,(15932492568383909/1000000000000000000)⟩
theorem valid102 : certificate102.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid102,?_⟩
  decide +kernel
theorem sound102 : certificate102.Sound :=
  rat_witness_certificate_sound certificate102 valid102 MajorityCertificates.Inputs005.envelope_sound102

def certificate103 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope103,(8083/4000),(29605543/200000000),(65421735753294979399/200000000000000000),(2441031743/1000000000),(37/20),(1309985507/1000000000),0,(1130123944790763831/1000000000000000000),(13817534106188837/1000000000000000000)⟩
theorem valid103 : certificate103.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid103,?_⟩
  decide +kernel
theorem sound103 : certificate103.Sound :=
  rat_witness_certificate_sound certificate103 valid103 MajorityCertificates.Inputs005.envelope_sound103

def certificate104 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope104,(201949/100000),(36986787/250000000),(162046546899711298817/500000000000000000),(1025981233/500000000),(37/20),(406919839/1000000000),0,1,(16122433242096841/1000000000000000000)⟩
theorem valid104 : certificate104.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid104,?_⟩
  decide +kernel
theorem sound104 : certificate104.Sound :=
  rat_witness_certificate_sound certificate104 valid104 MajorityCertificates.Inputs005.envelope_sound104

def certificate105 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope105,(201949/100000),(36986787/250000000),(162046546899711298817/500000000000000000),(610710051/250000000),(37/20),(327619107/250000000),0,(282543757547480373/250000000000000000),(1745288301884129/125000000000000000)⟩
theorem valid105 : certificate105.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid105,?_⟩
  decide +kernel
theorem sound105 : certificate105.Sound :=
  rat_witness_certificate_sound certificate105 valid105 MajorityCertificates.Inputs005.envelope_sound105

def certificate106 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope106,(5041/2500),(147705449/1000000000),(39675673919527877589/125000000000000000),(1025432727/500000000),(19/10),(406824117/1000000000),0,1,(8243987427291237/500000000000000000)⟩
theorem valid106 : certificate106.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid106,?_⟩
  decide +kernel
theorem sound106 : certificate106.Sound :=
  rat_witness_certificate_sound certificate106 valid106 MajorityCertificates.Inputs005.envelope_sound106

def certificate107 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope107,(5041/2500),(147705449/1000000000),(39675673919527877589/125000000000000000),(487134417/200000000),(19/10),(659056903/500000000),0,(35321643544959143/31250000000000000),(2914065394149237/200000000000000000)⟩
theorem valid107 : certificate107.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid107,?_⟩
  decide +kernel
theorem sound107 : certificate107.Sound :=
  rat_witness_certificate_sound certificate107 valid107 MajorityCertificates.Inputs005.envelope_sound107

def certificate108 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope108,(40279/20000),(9211449/62500000),(311738188183217569999/1000000000000000000),(2057784497/1000000000),(19/10),(405577359/1000000000),0,1,(1682133912675229/100000000000000000)⟩
theorem valid108 : certificate108.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid108,?_⟩
  decide +kernel
theorem sound108 : certificate108.Sound :=
  rat_witness_certificate_sound certificate108 valid108 MajorityCertificates.Inputs005.envelope_sound108

def certificate109 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope109,(40279/20000),(9211449/62500000),(311738188183217569999/1000000000000000000),(487824003/200000000),(19/10),(1319326711/1000000000),0,(226079149631088741/200000000000000000),(14882396783682889/1000000000000000000)⟩
theorem valid109 : certificate109.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid109,?_⟩
  decide +kernel
theorem sound109 : certificate109.Sound :=
  rat_witness_certificate_sound certificate109 valid109 MajorityCertificates.Inputs005.envelope_sound109

def certificate110 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope110,(25167/12500),(36785371/250000000),(30977154396792592491/100000000000000000),(515563303/250000000),(19/10),(101130159/250000000),0,1,(16922674780676677/1000000000000000000)⟩
theorem valid110 : certificate110.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid110,?_⟩
  decide +kernel
theorem sound110 : certificate110.Sound :=
  rat_witness_certificate_sound certificate110 valid110 MajorityCertificates.Inputs005.envelope_sound110

def certificate111 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope111,(25167/12500),(36785371/250000000),(30977154396792592491/100000000000000000),(2442026041/1000000000),(19/10),(659489311/500000000),0,(1130431729855752473/1000000000000000000),(749788919544419/50000000000000000)⟩
theorem valid111 : certificate111.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid111,?_⟩
  decide +kernel
theorem sound111 : certificate111.Sound :=
  rat_witness_certificate_sound certificate111 valid111 MajorityCertificates.Inputs005.envelope_sound111

def certificate112 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope112,(201217/100000),(287071/1953125),(38381348920839597449/125000000000000000),(412716049/200000000),(19/10),(404159033/1000000000),0,1,(2154398048992629/125000000000000000)⟩
theorem valid112 : certificate112.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid112,?_⟩
  decide +kernel
theorem sound112 : certificate112.Sound :=
  rat_witness_certificate_sound certificate112 valid112 MajorityCertificates.Inputs005.envelope_sound112

def certificate113 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope113,(201217/100000),(287071/1953125),(38381348920839597449/125000000000000000),(38182229/15625000),(19/10),(26392291/20000000),0,(565241647700546513/500000000000000000),(15154698806036059/1000000000000000000)⟩
theorem valid113 : certificate113.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid113,?_⟩
  decide +kernel
theorem sound113 : certificate113.Sound :=
  rat_witness_certificate_sound certificate113 valid113 MajorityCertificates.Inputs005.envelope_sound113

def certificate114 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope114,(200917/100000),(146819219/1000000000),(15048211230393984179/50000000000000000),(1031851661/500000000),(19/10),(404221677/1000000000),0,1,(17799805684244561/1000000000000000000)⟩
theorem valid114 : certificate114.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid114,?_⟩
  decide +kernel
theorem sound114 : certificate114.Sound :=
  rat_witness_certificate_sound certificate114 valid114 MajorityCertificates.Inputs005.envelope_sound114

def certificate115 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope115,(200917/100000),(146819219/1000000000),(15048211230393984179/50000000000000000),(2445364413/1000000000),(19/10),(165247361/125000000),0,(1130603001740808669/1000000000000000000),(3881923734943149/250000000000000000)⟩
theorem valid115 : certificate115.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid115,?_⟩
  decide +kernel
theorem sound115 : certificate115.Sound :=
  rat_witness_certificate_sound certificate115 valid115 MajorityCertificates.Inputs005.envelope_sound115

def certificate116 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope116,(200863/100000),(146496953/1000000000),(59831432486578824093/200000000000000000),(2067776443/1000000000),(19/10),(80600223/200000000),0,1,(9008369922735401/500000000000000000)⟩
theorem valid116 : certificate116.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid116,?_⟩
  decide +kernel
theorem sound116 : certificate116.Sound :=
  rat_witness_certificate_sound certificate116 valid116 MajorityCertificates.Inputs005.envelope_sound116

def certificate117 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope117,(200863/100000),(146496953/1000000000),(59831432486578824093/200000000000000000),(612079663/250000000),(19/10),(1321650943/1000000000),0,(1130638499900369271/1000000000000000000),(15643595291777973/1000000000000000000)⟩
theorem valid117 : certificate117.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid117,?_⟩
  decide +kernel
theorem sound117 : certificate117.Sound :=
  rat_witness_certificate_sound certificate117 valid117 MajorityCertificates.Inputs005.envelope_sound117

def certificate118 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs005.envelope118,(200747/100000),(7316791/50000000),(148306153012655465129/500000000000000000),(1036071147/500000000),(19/10),(80430913/200000000),0,1,(17756889553589381/1000000000000000000)⟩
theorem valid118 : certificate118.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid118,?_⟩
  decide +kernel
theorem sound118 : certificate118.Sound :=
  rat_witness_certificate_sound certificate118 valid118 MajorityCertificates.Inputs005.envelope_sound118

def certificate119 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs005.envelope119,(200747/100000),(7316791/50000000),(148306153012655465129/500000000000000000),(1225182263/500000000),(19/10),(165260621/125000000),0,(1130690365993901889/1000000000000000000),(3158301324237303/200000000000000000)⟩
theorem valid119 : certificate119.Valid := by
  refine ⟨MajorityCertificates.Inputs005.inputs_valid119,?_⟩
  decide +kernel
theorem sound119 : certificate119.Sound :=
  rat_witness_certificate_sound certificate119 valid119 MajorityCertificates.Inputs005.envelope_sound119

def certificates : List RatWitnessCertificate := [certificate100,certificate101,certificate102,certificate103,certificate104,certificate105,certificate106,certificate107,certificate108,certificate109,certificate110,certificate111,certificate112,certificate113,certificate114,certificate115,certificate116,certificate117,certificate118,certificate119]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound100,List.forall_mem_cons.mpr ⟨sound101,List.forall_mem_cons.mpr ⟨sound102,List.forall_mem_cons.mpr ⟨sound103,List.forall_mem_cons.mpr ⟨sound104,List.forall_mem_cons.mpr ⟨sound105,List.forall_mem_cons.mpr ⟨sound106,List.forall_mem_cons.mpr ⟨sound107,List.forall_mem_cons.mpr ⟨sound108,List.forall_mem_cons.mpr ⟨sound109,List.forall_mem_cons.mpr ⟨sound110,List.forall_mem_cons.mpr ⟨sound111,List.forall_mem_cons.mpr ⟨sound112,List.forall_mem_cons.mpr ⟨sound113,List.forall_mem_cons.mpr ⟨sound114,List.forall_mem_cons.mpr ⟨sound115,List.forall_mem_cons.mpr ⟨sound116,List.forall_mem_cons.mpr ⟨sound117,List.forall_mem_cons.mpr ⟨sound118,List.forall_mem_cons.mpr ⟨sound119,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch005
