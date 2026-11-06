import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs032

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch032

def certificate640 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope640,(218673/100000),(31246289/250000000),(450540175640321153547/500000000000000000),(280929897/125000000),(53/10),(155652959/500000000),0,1,(5733286828967683/1000000000000000000)⟩
theorem valid640 : certificate640.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid640,?_⟩
  decide +kernel
theorem sound640 : certificate640.Sound :=
  rat_witness_certificate_sound certificate640 valid640 MajorityCertificates.Inputs032.envelope_sound640

def certificate641 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope641,(218673/100000),(31246289/250000000),(450540175640321153547/500000000000000000),(2301868231/1000000000),(53/10),(1303151639/1000000000),0,(225342972759935761/200000000000000000),(7226746863148043/1000000000000000000)⟩
theorem valid641 : certificate641.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid641,?_⟩
  decide +kernel
theorem sound641 : certificate641.Sound :=
  rat_witness_certificate_sound certificate641 valid641 MajorityCertificates.Inputs032.envelope_sound641

def certificate642 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope642,(109307/50000),(61848047/500000000),(446476391738544410619/500000000000000000),(563730247/250000000),(107/20),(153794667/500000000),0,1,(578526084388997/100000000000000000)⟩
theorem valid642 : certificate642.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid642,?_⟩
  decide +kernel
theorem sound642 : certificate642.Sound :=
  rat_witness_certificate_sound certificate642 valid642 MajorityCertificates.Inputs032.envelope_sound642

def certificate643 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope643,(109307/50000),(61848047/500000000),(446476391738544410619/500000000000000000),(576937091/250000000),(107/20),(1302675323/1000000000),0,(563365479288837939/500000000000000000),(72947159827011/10000000000000000)⟩
theorem valid643 : certificate643.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid643,?_⟩
  decide +kernel
theorem sound643 : certificate643.Sound :=
  rat_witness_certificate_sound certificate643 valid643 MajorityCertificates.Inputs032.envelope_sound643

def certificate644 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope644,(218557/100000),(122407031/1000000000),(885034598884324527611/1000000000000000000),(2261468611/1000000000),(107/20),(151968077/500000000),0,1,(732219809875579/125000000000000000)⟩
theorem valid644 : certificate644.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid644,?_⟩
  decide +kernel
theorem sound644 : certificate644.Sound :=
  rat_witness_certificate_sound certificate644 valid644 MajorityCertificates.Inputs032.envelope_sound644

def certificate645 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope645,(218557/100000),(122407031/1000000000),(885034598884324527611/1000000000000000000),(462128433/200000000),(107/20),(260671807/200000000),0,(563373459879722171/500000000000000000),(3702765384977131/500000000000000000)⟩
theorem valid645 : certificate645.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid645,?_⟩
  decide +kernel
theorem sound645 : certificate645.Sound :=
  rat_witness_certificate_sound certificate645 valid645 MajorityCertificates.Inputs032.envelope_sound645

def certificate646 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope646,(109251/50000),(121117969/1000000000),(21933004553258183467/25000000000000000),(1134772693/500000000),(27/5),(60047373/200000000),0,1,(6002190818529993/1000000000000000000)⟩
theorem valid646 : certificate646.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid646,?_⟩
  decide +kernel
theorem sound646 : certificate646.Sound :=
  rat_witness_certificate_sound certificate646 valid646 MajorityCertificates.Inputs032.envelope_sound646

def certificate647 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope647,(109251/50000),(121117969/1000000000),(21933004553258183467/25000000000000000),(1158177597/500000000),(27/5),(260599781/200000000),0,(563381371776015883/500000000000000000),(7477572871938423/1000000000000000000)⟩
theorem valid647 : certificate647.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid647,?_⟩
  decide +kernel
theorem sound647 : certificate647.Sound :=
  rat_witness_certificate_sound certificate647 valid647 MajorityCertificates.Inputs032.envelope_sound647

def certificate648 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope648,(13653/6250),(38139/320000),(217451032822346997693/250000000000000000),(142271261/62500000),(109/20),(58981233/200000000),0,1,(6014316591884149/1000000000000000000)⟩
theorem valid648 : certificate648.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid648,?_⟩
  decide +kernel
theorem sound648 : certificate648.Sound :=
  rat_witness_certificate_sound certificate648 valid648 MajorityCertificates.Inputs032.envelope_sound648

def certificate649 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope649,(13653/6250),(38139/320000),(217451032822346997693/250000000000000000),(2323418259/1000000000),(109/20),(1302707973/1000000000),0,(1126778434345290231/1000000000000000000),(471988309385079/62500000000000000)⟩
theorem valid649 : certificate649.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid649,?_⟩
  decide +kernel
theorem sound649 : certificate649.Sound :=
  rat_witness_certificate_sound certificate649 valid649 MajorityCertificates.Inputs032.envelope_sound649

def certificate650 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope650,(43679/20000),(117895313/1000000000),(431240624310649139377/500000000000000000),(227462429/100000000),(109/20),(145838681/500000000),0,1,(1520254889792993/250000000000000000)⟩
theorem valid650 : certificate650.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid650,?_⟩
  decide +kernel
theorem sound650 : certificate650.Sound :=
  rat_witness_certificate_sound certificate650 valid650 MajorityCertificates.Inputs032.envelope_sound650

def certificate651 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope651,(43679/20000),(117895313/1000000000),(431240624310649139377/500000000000000000),(145398981/62500000),(109/20),(52136409/40000000),0,(1126793988630534969/1000000000000000000),(1532862829540439/200000000000000000)⟩
theorem valid651 : certificate651.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid651,?_⟩
  decide +kernel
theorem sound651 : certificate651.Sound :=
  rat_witness_certificate_sound certificate651 valid651 MajorityCertificates.Inputs032.envelope_sound651

def certificate652 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope652,(27293/12500),(18657/160000),(213836632946619844371/250000000000000000),(2290340451/1000000000),(11/2),(14383083/50000000),0,1,(1236895843778783/200000000000000000)⟩
theorem valid652 : certificate652.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid652,?_⟩
  decide +kernel
theorem sound652 : certificate652.Sound :=
  rat_witness_certificate_sound certificate652 valid652 MajorityCertificates.Inputs032.envelope_sound652

def certificate653 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope653,(27293/12500),(18657/160000),(213836632946619844371/250000000000000000),(1166157773/500000000),(11/2),(325753983/250000000),0,(17606396791118769/15625000000000000),(7733275645921067/1000000000000000000)⟩
theorem valid653 : certificate653.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid653,?_⟩
  decide +kernel
theorem sound653 : certificate653.Sound :=
  rat_witness_certificate_sound certificate653 valid653 MajorityCertificates.Inputs032.envelope_sound653

def certificate654 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope654,(43659/20000),(7167041/62500000),(848395165509429942467/1000000000000000000),(143806123/62500000),(111/20),(282256173/1000000000),0,1,(1274358562951069/200000000000000000)⟩
theorem valid654 : certificate654.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid654,?_⟩
  decide +kernel
theorem sound654 : certificate654.Sound :=
  rat_witness_certificate_sound certificate654 valid654 MajorityCertificates.Inputs032.envelope_sound654

def certificate655 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope655,(43659/20000),(7167041/62500000),(848395165509429942467/1000000000000000000),(1169747293/500000000),(111/20),(651388969/500000000),0,(1126824648684445453/1000000000000000000),(156168878800477/20000000000000000)⟩
theorem valid655 : certificate655.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid655,?_⟩
  decide +kernel
theorem sound655 : certificate655.Sound :=
  rat_witness_certificate_sound certificate655 valid655 MajorityCertificates.Inputs032.envelope_sound655

def certificate656 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope656,(241117/100000),(138520313/1000000000),(130298704246109328290933/250000000000000000),(878390407/500000000),(33/5),(92018503/250000000),0,1,(1177551726763/50000000000000000)⟩
theorem valid656 : certificate656.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid656,?_⟩
  decide +kernel
theorem sound656 : certificate656.Sound :=
  rat_witness_certificate_sound certificate656 valid656 MajorityCertificates.Inputs032.envelope_sound656

def certificate657 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope657,(241117/100000),(138520313/1000000000),(130298704246109328290933/250000000000000000),(175133677/100000000),(33/5),(1534288007/1000000000),0,(35156333926031081/31250000000000000),(804739895363/62500000000000000)⟩
theorem valid657 : certificate657.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid657,?_⟩
  decide +kernel
theorem sound657 : certificate657.Sound :=
  rat_witness_certificate_sound certificate657 valid657 MajorityCertificates.Inputs032.envelope_sound657

def certificate658 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs032.envelope658,(120391/50000),(44739/320000),(336055224918426238233403/1000000000000000000),(1849268653/1000000000),(133/20),(361782081/1000000000),0,1,(3366021975547/200000000000000000)⟩
theorem valid658 : certificate658.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid658,?_⟩
  decide +kernel
theorem sound658 : certificate658.Sound :=
  rat_witness_certificate_sound certificate658 valid658 MajorityCertificates.Inputs032.envelope_sound658

def certificate659 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs032.envelope659,(120391/50000),(44739/320000),(336055224918426238233403/1000000000000000000),(877828569/500000000),(133/20),(191112141/125000000),0,(281251042750408327/250000000000000000),(10950517242461/500000000000000000)⟩
theorem valid659 : certificate659.Valid := by
  refine ⟨MajorityCertificates.Inputs032.inputs_valid659,?_⟩
  decide +kernel
theorem sound659 : certificate659.Sound :=
  rat_witness_certificate_sound certificate659 valid659 MajorityCertificates.Inputs032.envelope_sound659

def certificates : List RatWitnessCertificate := [certificate640,certificate641,certificate642,certificate643,certificate644,certificate645,certificate646,certificate647,certificate648,certificate649,certificate650,certificate651,certificate652,certificate653,certificate654,certificate655,certificate656,certificate657,certificate658,certificate659]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound640,List.forall_mem_cons.mpr ⟨sound641,List.forall_mem_cons.mpr ⟨sound642,List.forall_mem_cons.mpr ⟨sound643,List.forall_mem_cons.mpr ⟨sound644,List.forall_mem_cons.mpr ⟨sound645,List.forall_mem_cons.mpr ⟨sound646,List.forall_mem_cons.mpr ⟨sound647,List.forall_mem_cons.mpr ⟨sound648,List.forall_mem_cons.mpr ⟨sound649,List.forall_mem_cons.mpr ⟨sound650,List.forall_mem_cons.mpr ⟨sound651,List.forall_mem_cons.mpr ⟨sound652,List.forall_mem_cons.mpr ⟨sound653,List.forall_mem_cons.mpr ⟨sound654,List.forall_mem_cons.mpr ⟨sound655,List.forall_mem_cons.mpr ⟨sound656,List.forall_mem_cons.mpr ⟨sound657,List.forall_mem_cons.mpr ⟨sound658,List.forall_mem_cons.mpr ⟨sound659,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch032
