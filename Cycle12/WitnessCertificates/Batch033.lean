import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch033

def certificate660 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope660,(30081/12500),(70549219/500000000),(69954983579123564145781/250000000000000000),(1800063491/1000000000),(133/20),(9260209/25000000),0,1,(3995174146393/1000000000000000000)⟩
theorem valid660 : certificate660.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid660,?_⟩
  decide +kernel
theorem sound660 : certificate660.Sound :=
  rat_witness_certificate_sound certificate660 valid660 MajorityCertificates.Inputs033.envelope_sound660

def certificate661 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope661,(30081/12500),(70549219/500000000),(69954983579123564145781/250000000000000000),(439053051/250000000),(133/20),(763353349/500000000),0,(225001002407646243/200000000000000000),(13228713763867/500000000000000000)⟩
theorem valid661 : certificate661.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid661,?_⟩
  decide +kernel
theorem sound661 : certificate661.Sound :=
  rat_witness_certificate_sound certificate661 valid661 MajorityCertificates.Inputs033.envelope_sound661

def certificate662 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope662,(240487/100000),(141742969/1000000000),(236013496621874441686089/1000000000000000000),(1793069209/1000000000),(67/10),(186528351/500000000),0,1,(19973188566971/1000000000000000000)⟩
theorem valid662 : certificate662.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid662,?_⟩
  decide +kernel
theorem sound662 : certificate662.Sound :=
  rat_witness_certificate_sound certificate662 valid662 MajorityCertificates.Inputs033.envelope_sound662

def certificate663 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope663,(240487/100000),(141742969/1000000000),(236013496621874441686089/1000000000000000000),(439662681/250000000),(67/10),(1523694329/1000000000),0,(1125005946304141143/1000000000000000000),(31376818328883/1000000000000000000)⟩
theorem valid663 : certificate663.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid663,?_⟩
  decide +kernel
theorem sound663 : certificate663.Sound :=
  rat_witness_certificate_sound certificate663 valid663 MajorityCertificates.Inputs033.envelope_sound663

def certificate664 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope664,(48029/20000),(143032031/1000000000),(174054143986089853018667/1000000000000000000),(1773085367/1000000000),(67/10),(379138529/1000000000),0,1,(2542932299459/62500000000000000)⟩
theorem valid664 : certificate664.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid664,?_⟩
  decide +kernel
theorem sound664 : certificate664.Sound :=
  rat_witness_certificate_sound certificate664 valid664 MajorityCertificates.Inputs033.envelope_sound664

def certificate665 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope665,(48029/20000),(143032031/1000000000),(174054143986089853018667/1000000000000000000),(1759201201/1000000000),(67/10),(1523296461/1000000000),0,(1125008074549200309/1000000000000000000),(4278209632077/100000000000000000)⟩
theorem valid665 : certificate665.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid665,?_⟩
  decide +kernel
theorem sound665 : certificate665.Sound :=
  rat_witness_certificate_sound certificate665 valid665 MajorityCertificates.Inputs033.envelope_sound665

def certificate666 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope666,(120011/50000),(72160547/500000000),(4774277875570401094503/31250000000000000),(1789737913/1000000000),(27/4),(190396703/500000000),0,1,(6302803889913/200000000000000000)⟩
theorem valid666 : certificate666.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid666,?_⟩
  decide +kernel
theorem sound666 : certificate666.Sound :=
  rat_witness_certificate_sound certificate666 valid666 MajorityCertificates.Inputs033.envelope_sound666

def certificate667 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope667,(120011/50000),(72160547/500000000),(4774277875570401094503/31250000000000000),(1760695749/1000000000),(27/4),(759994369/500000000),0,(562504601906853573/500000000000000000),(10367235635839/200000000000000000)⟩
theorem valid667 : certificate667.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid667,?_⟩
  decide +kernel
theorem sound667 : certificate667.Sound :=
  rat_witness_certificate_sound certificate667 valid667 MajorityCertificates.Inputs033.envelope_sound667

def certificate668 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope668,(239871/100000),(46389/320000),(67395196350995630792803/500000000000000000),(448763501/250000000),(27/4),(382067237/1000000000),0,1,(33217821116081/1000000000000000000)⟩
theorem valid668 : certificate668.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid668,?_⟩
  decide +kernel
theorem sound668 : certificate668.Sound :=
  rat_witness_certificate_sound certificate668 valid668 MajorityCertificates.Inputs033.envelope_sound668

def certificate669 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope669,(239871/100000),(46389/320000),(67395196350995630792803/500000000000000000),(1761925937/1000000000),(27/4),(37962209/25000000),0,(1125010438551232817/1000000000000000000),(27797451580943/500000000000000000)⟩
theorem valid669 : certificate669.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid669,?_⟩
  decide +kernel
theorem sound669 : certificate669.Sound :=
  rat_witness_certificate_sound certificate669 valid669 MajorityCertificates.Inputs033.envelope_sound669

def certificate670 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope670,(47909/20000),(4570459/31250000),(53455027349624857676131/500000000000000000),(1757227271/1000000000),(27/4),(78078173/200000000),0,1,(75123019335427/500000000000000000)⟩
theorem valid670 : certificate670.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid670,?_⟩
  decide +kernel
theorem sound670 : certificate670.Sound :=
  rat_witness_certificate_sound certificate670 valid670 MajorityCertificates.Inputs033.envelope_sound670

def certificate671 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope671,(47909/20000),(4570459/31250000),(53455027349624857676131/500000000000000000),(1762546329/1000000000),(27/4),(1518028403/1000000000),0,(1125013178684834159/1000000000000000000),(5448768689969/62500000000000000)⟩
theorem valid671 : certificate671.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid671,?_⟩
  decide +kernel
theorem sound671 : certificate671.Sound :=
  rat_witness_certificate_sound certificate671 valid671 MajorityCertificates.Inputs033.envelope_sound671

def certificate672 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope672,(239431/100000),(146899219/1000000000),(48347460048084572699147/500000000000000000),(442089019/250000000),(34/5),(97715363/250000000),0,1,(76594057944589/1000000000000000000)⟩
theorem valid672 : certificate672.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid672,?_⟩
  decide +kernel
theorem sound672 : certificate672.Sound :=
  rat_witness_certificate_sound certificate672 valid672 MajorityCertificates.Inputs033.envelope_sound672

def certificate673 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope673,(239431/100000),(146899219/1000000000),(48347460048084572699147/500000000000000000),(1765379739/1000000000),(34/5),(1514299993/1000000000),0,(1125014577871440187/1000000000000000000),(78136079053103/1000000000000000000)⟩
theorem valid673 : certificate673.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid673,?_⟩
  decide +kernel
theorem sound673 : certificate673.Sound :=
  rat_witness_certificate_sound certificate673 valid673 MajorityCertificates.Inputs033.envelope_sound673

def certificate674 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope674,(29911/12500),(148188281/1000000000),(87605946957905369254317/1000000000000000000),(873100277/500000000),(34/5),(198643141/500000000),0,1,(1738865707291/40000000000000000)⟩
theorem valid674 : certificate674.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid674,?_⟩
  decide +kernel
theorem sound674 : certificate674.Sound :=
  rat_witness_certificate_sound certificate674 valid674 MajorityCertificates.Inputs033.envelope_sound674

def certificate675 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope675,(29911/12500),(148188281/1000000000),(87605946957905369254317/1000000000000000000),(882523451/500000000),(34/5),(302708631/200000000),0,(140627012491783721/125000000000000000),(86552531057207/1000000000000000000)⟩
theorem valid675 : certificate675.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid675,?_⟩
  decide +kernel
theorem sound675 : certificate675.Sound :=
  rat_witness_certificate_sound certificate675 valid675 MajorityCertificates.Inputs033.envelope_sound675

def certificate676 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope676,(239147/100000),(148832813/1000000000),(797707745538915745241/10000000000000000),(893028509/500000000),(137/20),(394280949/1000000000),0,1,(2999441743469/40000000000000000)⟩
theorem valid676 : certificate676.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid676,?_⟩
  decide +kernel
theorem sound676 : certificate676.Sound :=
  rat_witness_certificate_sound certificate676 valid676 MajorityCertificates.Inputs033.envelope_sound676

def certificate677 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope677,(239147/100000),(148832813/1000000000),(797707745538915745241/10000000000000000),(110460427/62500000),(137/20),(302149507/200000000),0,(225003538346327081/200000000000000000),(95108547617701/1000000000000000000)⟩
theorem valid677 : certificate677.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid677,?_⟩
  decide +kernel
theorem sound677 : certificate677.Sound :=
  rat_witness_certificate_sound certificate677 valid677 MajorityCertificates.Inputs033.envelope_sound677

def certificate678 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs033.envelope678,(239007/100000),(4671167/31250000),(72967924963157851309997/1000000000000000000),(1795562977/1000000000),(137/20),(39506109/100000000),0,1,(6276285912787/100000000000000000)⟩
theorem valid678 : certificate678.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid678,?_⟩
  decide +kernel
theorem sound678 : certificate678.Sound :=
  rat_witness_certificate_sound certificate678 valid678 MajorityCertificates.Inputs033.envelope_sound678

def certificate679 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs033.envelope679,(239007/100000),(4671167/31250000),(72967924963157851309997/1000000000000000000),(110492781/62500000),(137/20),(1510138843/1000000000),0,(281254838123828529/250000000000000000),(20878043291471/200000000000000000)⟩
theorem valid679 : certificate679.Valid := by
  refine ⟨MajorityCertificates.Inputs033.inputs_valid679,?_⟩
  decide +kernel
theorem sound679 : certificate679.Sound :=
  rat_witness_certificate_sound certificate679 valid679 MajorityCertificates.Inputs033.envelope_sound679

def certificates : List RatWitnessCertificate := [certificate660,certificate661,certificate662,certificate663,certificate664,certificate665,certificate666,certificate667,certificate668,certificate669,certificate670,certificate671,certificate672,certificate673,certificate674,certificate675,certificate676,certificate677,certificate678,certificate679]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound660,List.forall_mem_cons.mpr ⟨sound661,List.forall_mem_cons.mpr ⟨sound662,List.forall_mem_cons.mpr ⟨sound663,List.forall_mem_cons.mpr ⟨sound664,List.forall_mem_cons.mpr ⟨sound665,List.forall_mem_cons.mpr ⟨sound666,List.forall_mem_cons.mpr ⟨sound667,List.forall_mem_cons.mpr ⟨sound668,List.forall_mem_cons.mpr ⟨sound669,List.forall_mem_cons.mpr ⟨sound670,List.forall_mem_cons.mpr ⟨sound671,List.forall_mem_cons.mpr ⟨sound672,List.forall_mem_cons.mpr ⟨sound673,List.forall_mem_cons.mpr ⟨sound674,List.forall_mem_cons.mpr ⟨sound675,List.forall_mem_cons.mpr ⟨sound676,List.forall_mem_cons.mpr ⟨sound677,List.forall_mem_cons.mpr ⟨sound678,List.forall_mem_cons.mpr ⟨sound679,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch033
