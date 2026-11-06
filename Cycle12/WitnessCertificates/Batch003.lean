import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch003

def certificate60 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope60,(8317/4000),(152055469/1000000000),(512812006704724266291/1000000000000000000),(495913153/250000000),(17/10),(41677521/100000000),0,1,(9605812279967447/1000000000000000000)⟩
theorem valid60 : certificate60.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid60,?_⟩
  decide +kernel
theorem sound60 : certificate60.Sound :=
  rat_witness_certificate_sound certificate60 valid60 MajorityCertificates.Inputs003.envelope_sound60

def certificate61 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope61,(8317/4000),(152055469/1000000000),(512812006704724266291/1000000000000000000),(296134193/125000000),(17/10),(257263217/200000000),0,(564086098429625737/500000000000000000),(8197100169990267/1000000000000000000)⟩
theorem valid61 : certificate61.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid61,?_⟩
  decide +kernel
theorem sound61 : certificate61.Sound :=
  rat_witness_certificate_sound certificate61 valid61 MajorityCertificates.Inputs003.envelope_sound61

def certificate62 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope62,(20769/10000),(152055469/1000000000),(4014106551538133733/8000000000000000),(1991929037/1000000000),(7/4),(83260377/200000000),0,1,(10070743108901181/1000000000000000000)⟩
theorem valid62 : certificate62.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid62,?_⟩
  decide +kernel
theorem sound62 : certificate62.Sound :=
  rat_witness_certificate_sound certificate62 valid62 MajorityCertificates.Inputs003.envelope_sound62

def certificate63 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope63,(20769/10000),(152055469/1000000000),(4014106551538133733/8000000000000000),(2375670203/1000000000),(7/4),(80368871/62500000),0,(1128245881025797181/1000000000000000000),(8388060871840057/1000000000000000000)⟩
theorem valid63 : certificate63.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid63,?_⟩
  decide +kernel
theorem sound63 : certificate63.Sound :=
  rat_witness_certificate_sound certificate63 valid63 MajorityCertificates.Inputs003.envelope_sound63

def certificate64 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope64,(207361/100000),(152055469/1000000000),(97787639010132507129/200000000000000000),(398541423/200000000),(7/4),(208311593/500000000),0,1,(1008460487112929/100000000000000000)⟩
theorem valid64 : certificate64.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid64,?_⟩
  decide +kernel
theorem sound64 : certificate64.Sound :=
  rat_witness_certificate_sound certificate64 valid64 MajorityCertificates.Inputs003.envelope_sound64

def certificate65 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope65,(207361/100000),(152055469/1000000000),(97787639010132507129/200000000000000000),(1189496821/500000000),(7/4),(321736189/250000000),0,(1128336515839029429/1000000000000000000),(431776796750911/50000000000000000)⟩
theorem valid65 : certificate65.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid65,?_⟩
  decide +kernel
theorem sound65 : certificate65.Sound :=
  rat_witness_certificate_sound certificate65 valid65 MajorityCertificates.Inputs003.envelope_sound65

def certificate66 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope66,(51759/25000),(1527/10000),(47666931099808140293/100000000000000000),(124616321/62500000),(7/4),(418871459/1000000000),0,1,(5194884691351533/500000000000000000)⟩
theorem valid66 : certificate66.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid66,?_⟩
  decide +kernel
theorem sound66 : certificate66.Sound :=
  rat_witness_certificate_sound certificate66 valid66 MajorityCertificates.Inputs003.envelope_sound66

def certificate67 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope67,(51759/25000),(1527/10000),(47666931099808140293/100000000000000000),(2380810137/1000000000),(7/4),(322048777/250000000),0,(1128427982235104061/1000000000000000000),(138959405234877/15625000000000000)⟩
theorem valid67 : certificate67.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid67,?_⟩
  decide +kernel
theorem sound67 : certificate67.Sound :=
  rat_witness_certificate_sound certificate67 valid67 MajorityCertificates.Inputs003.envelope_sound67

def certificate68 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope68,(41343/20000),(152055469/1000000000),(29057803057295121243/62500000000000000),(99695331/50000000),(7/4),(41745887/100000000),0,1,(10628256664544447/1000000000000000000)⟩
theorem valid68 : certificate68.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid68,?_⟩
  decide +kernel
theorem sound68 : certificate68.Sound :=
  rat_witness_certificate_sound certificate68 valid68 MajorityCertificates.Inputs003.envelope_sound68

def certificate69 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope69,(41343/20000),(152055469/1000000000),(29057803057295121243/62500000000000000),(95401419/40000000),(7/4),(644650531/500000000),0,(56426012902988289/50000000000000000),(4574592505782367/500000000000000000)⟩
theorem valid69 : certificate69.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid69,?_⟩
  decide +kernel
theorem sound69 : certificate69.Sound :=
  rat_witness_certificate_sound certificate69 valid69 MajorityCertificates.Inputs003.envelope_sound69

def certificate70 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope70,(103199/50000),(152055469/1000000000),(453675255619732797693/1000000000000000000),(125119427/62500000),(7/4),(208537081/500000000),0,1,(1367220121503219/125000000000000000)⟩
theorem valid70 : certificate70.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid70,?_⟩
  decide +kernel
theorem sound70 : certificate70.Sound :=
  rat_witness_certificate_sound certificate70 valid70 MajorityCertificates.Inputs003.envelope_sound70

def certificate71 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope71,(103199/50000),(152055469/1000000000),(453675255619732797693/1000000000000000000),(477612231/200000000),(7/4),(645237093/500000000),0,(1128613320933543747/1000000000000000000),(4705133427593887/500000000000000000)⟩
theorem valid71 : certificate71.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid71,?_⟩
  decide +kernel
theorem sound71 : certificate71.Sound :=
  rat_witness_certificate_sound certificate71 valid71 MajorityCertificates.Inputs003.envelope_sound71

def certificate72 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope72,(103147/50000),(152055469/1000000000),(449289212885837113749/1000000000000000000),(2005069053/1000000000),(7/4),(208451521/500000000),0,1,(5534459729669281/500000000000000000)⟩
theorem valid72 : certificate72.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid72,?_⟩
  decide +kernel
theorem sound72 : certificate72.Sound :=
  rat_witness_certificate_sound certificate72 valid72 MajorityCertificates.Inputs003.envelope_sound72

def certificate73 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope73,(103147/50000),(152055469/1000000000),(449289212885837113749/1000000000000000000),(1195324979/500000000),(7/4),(129024837/100000000),0,(282162631960073793/250000000000000000),(1189354531640119/125000000000000000)⟩
theorem valid73 : certificate73.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid73,?_⟩
  decide +kernel
theorem sound73 : certificate73.Sound :=
  rat_witness_certificate_sound certificate73 valid73 MajorityCertificates.Inputs003.envelope_sound73

def certificate74 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope74,(206139/100000),(152055469/1000000000),(221972292908710853387/500000000000000000),(2000088341/1000000000),(7/4),(417669129/1000000000),0,1,(11172193388873873/1000000000000000000)⟩
theorem valid74 : certificate74.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid74,?_⟩
  decide +kernel
theorem sound74 : certificate74.Sound :=
  rat_witness_certificate_sound certificate74 valid74 MajorityCertificates.Inputs003.envelope_sound74

def certificate75 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope75,(206139/100000),(152055469/1000000000),(221972292908710853387/500000000000000000),(2391953673/1000000000),(7/4),(1290922149/1000000000),0,(56434868685444301/50000000000000000),(965052571766121/100000000000000000)⟩
theorem valid75 : certificate75.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid75,?_⟩
  decide +kernel
theorem sound75 : certificate75.Sound :=
  rat_witness_certificate_sound certificate75 valid75 MajorityCertificates.Inputs003.envelope_sound75

def certificate76 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope76,(102889/50000),(75141787/500000000),(54069082130495480293/125000000000000000),(251613051/125000000),(7/4),(411679337/1000000000),0,1,(11540937509016013/1000000000000000000)⟩
theorem valid76 : certificate76.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid76,?_⟩
  decide +kernel
theorem sound76 : certificate76.Sound :=
  rat_witness_certificate_sound certificate76 valid76 MajorityCertificates.Inputs003.envelope_sound76

def certificate77 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope77,(102889/50000),(75141787/500000000),(54069082130495480293/125000000000000000),(1198252289/500000000),(7/4),(161630827/125000000),0,(1128801680154178073/1000000000000000000),(9951363609584957/1000000000000000000)⟩
theorem valid77 : certificate77.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid77,?_⟩
  decide +kernel
theorem sound77 : certificate77.Sound :=
  rat_witness_certificate_sound certificate77 valid77 MajorityCertificates.Inputs003.envelope_sound77

def certificate78 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs003.envelope78,(102737/50000),(1173461/7812500),(211315119221540813759/500000000000000000),(2015985541/1000000000),(7/4),(411588067/1000000000),0,1,(11859976839516811/1000000000000000000)⟩
theorem valid78 : certificate78.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid78,?_⟩
  decide +kernel
theorem sound78 : certificate78.Sound :=
  rat_witness_certificate_sound certificate78 valid78 MajorityCertificates.Inputs003.envelope_sound78

def certificate79 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs003.envelope79,(102737/50000),(1173461/7812500),(211315119221540813759/500000000000000000),(1199873163/500000000),(7/4),(1294169523/1000000000),0,(564448473841846801/500000000000000000),(5109454940492403/500000000000000000)⟩
theorem valid79 : certificate79.Valid := by
  refine ⟨MajorityCertificates.Inputs003.inputs_valid79,?_⟩
  decide +kernel
theorem sound79 : certificate79.Sound :=
  rat_witness_certificate_sound certificate79 valid79 MajorityCertificates.Inputs003.envelope_sound79

def certificates : List RatWitnessCertificate := [certificate60,certificate61,certificate62,certificate63,certificate64,certificate65,certificate66,certificate67,certificate68,certificate69,certificate70,certificate71,certificate72,certificate73,certificate74,certificate75,certificate76,certificate77,certificate78,certificate79]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound60,List.forall_mem_cons.mpr ⟨sound61,List.forall_mem_cons.mpr ⟨sound62,List.forall_mem_cons.mpr ⟨sound63,List.forall_mem_cons.mpr ⟨sound64,List.forall_mem_cons.mpr ⟨sound65,List.forall_mem_cons.mpr ⟨sound66,List.forall_mem_cons.mpr ⟨sound67,List.forall_mem_cons.mpr ⟨sound68,List.forall_mem_cons.mpr ⟨sound69,List.forall_mem_cons.mpr ⟨sound70,List.forall_mem_cons.mpr ⟨sound71,List.forall_mem_cons.mpr ⟨sound72,List.forall_mem_cons.mpr ⟨sound73,List.forall_mem_cons.mpr ⟨sound74,List.forall_mem_cons.mpr ⟨sound75,List.forall_mem_cons.mpr ⟨sound76,List.forall_mem_cons.mpr ⟨sound77,List.forall_mem_cons.mpr ⟨sound78,List.forall_mem_cons.mpr ⟨sound79,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch003
