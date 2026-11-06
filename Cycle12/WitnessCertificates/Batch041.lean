import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs041

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch041

def certificate820 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope820,(115231/50000),(1527/10000),(1754677969578086812537/500000000000000000),(2148007809/1000000000),(54/5),(382152999/1000000000),0,1,(274313083295999/200000000000000000)⟩
theorem valid820 : certificate820.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid820,?_⟩
  decide +kernel
theorem sound820 : certificate820.Sound :=
  rat_witness_certificate_sound certificate820 valid820 MajorityCertificates.Inputs041.envelope_sound820

def certificate821 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope821,(115231/50000),(1527/10000),(1754677969578086812537/500000000000000000),(975193419/500000000),(54/5),(281241213/200000000),0,(1758464717380601/1562500000000000),(1463921096076593/500000000000000000)⟩
theorem valid821 : certificate821.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid821,?_⟩
  decide +kernel
theorem sound821 : certificate821.Sound :=
  rat_witness_certificate_sound certificate821 valid821 MajorityCertificates.Inputs041.envelope_sound821

def certificate822 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope822,(46087/20000),(75383203/500000000),(1739646561492553482501/500000000000000000),(431306391/200000000),(109/10),(7528853/20000000),0,1,(1385470429830729/1000000000000000000)⟩
theorem valid822 : certificate822.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid822,?_⟩
  decide +kernel
theorem sound822 : certificate822.Sound :=
  rat_witness_certificate_sound certificate822 valid822 MajorityCertificates.Inputs041.envelope_sound822

def certificate823 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope823,(46087/20000),(75383203/500000000),(1739646561492553482501/500000000000000000),(1955415213/1000000000),(109/10),(1405013769/1000000000),0,(1125421076227341643/1000000000000000000),(591466382040387/200000000000000000)⟩
theorem valid823 : certificate823.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid823,?_⟩
  decide +kernel
theorem sound823 : certificate823.Sound :=
  rat_witness_certificate_sound certificate823 valid823 MajorityCertificates.Inputs041.envelope_sound823

def certificate824 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope824,(28801/12500),(4671167/31250000),(3450002997137746146889/1000000000000000000),(2163181203/1000000000),(219/20),(372608059/1000000000),0,1,(699602187558669/500000000000000000)⟩
theorem valid824 : certificate824.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid824,?_⟩
  decide +kernel
theorem sound824 : certificate824.Sound :=
  rat_witness_certificate_sound certificate824 valid824 MajorityCertificates.Inputs041.envelope_sound824

def certificate825 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope825,(28801/12500),(4671167/31250000),(3450002997137746146889/1000000000000000000),(979129113/500000000),(219/20),(702388131/500000000),0,(562712350971019117/500000000000000000),(2993881074271997/1000000000000000000)⟩
theorem valid825 : certificate825.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid825,?_⟩
  decide +kernel
theorem sound825 : certificate825.Sound :=
  rat_witness_certificate_sound certificate825 valid825 MajorityCertificates.Inputs041.envelope_sound825

def certificate826 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope826,(115191/50000),(23607/160000),(1710732776214571575263/500000000000000000),(2171517121/1000000000),(221/20),(366959983/1000000000),0,1,(1413808574566189/1000000000000000000)⟩
theorem valid826 : certificate826.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid826,?_⟩
  decide +kernel
theorem sound826 : certificate826.Sound :=
  rat_witness_certificate_sound certificate826 valid826 MajorityCertificates.Inputs041.envelope_sound826

def certificate827 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope827,(115191/50000),(23607/160000),(1710732776214571575263/500000000000000000),(1963322851/1000000000),(221/20),(35090989/25000000),0,(1125428293649979231/1000000000000000000),(3023716355766787/1000000000000000000)⟩
theorem valid827 : certificate827.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid827,?_⟩
  decide +kernel
theorem sound827 : certificate827.Sound :=
  rat_witness_certificate_sound certificate827 valid827 MajorityCertificates.Inputs041.envelope_sound827

def certificate828 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope828,(230357/100000),(36402539/250000000),(1696830763966484987757/500000000000000000),(1089917991/500000000),(111/10),(90335557/250000000),0,1,(357127350786513/250000000000000000)⟩
theorem valid828 : certificate828.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid828,?_⟩
  decide +kernel
theorem sound828 : certificate828.Sound :=
  rat_witness_certificate_sound certificate828 valid828 MajorityCertificates.Inputs041.envelope_sound828

def certificate829 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope829,(230357/100000),(36402539/250000000),(1696830763966484987757/500000000000000000),(393421073/200000000),(111/10),(43859963/31250000),0,(1125431850552931227/1000000000000000000),(1530481704827463/500000000000000000)⟩
theorem valid829 : certificate829.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid829,?_⟩
  decide +kernel
theorem sound829 : certificate829.Sound :=
  rat_witness_certificate_sound certificate829 valid829 MajorityCertificates.Inputs041.envelope_sound829

def certificate830 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope830,(47/20),(7/50),(2605974084985895537591801/1000000000000000000),(230317233/125000000),32,(183871991/500000000),0,1,(1029582822243/500000000000000000)⟩
theorem valid830 : certificate830.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid830,?_⟩
  decide +kernel
theorem sound830 : certificate830.Sound :=
  rat_witness_certificate_sound certificate830 valid830 MajorityCertificates.Inputs041.envelope_sound830

def certificate831 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope831,(47/20),(7/50),(2605974084985895537591801/1000000000000000000),(1620552909/1000000000),32,(905109959/500000000),0,(1125000551107076713/1000000000000000000),(2200155247/62500000000000000)⟩
theorem valid831 : certificate831.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid831,?_⟩
  decide +kernel
theorem sound831 : certificate831.Sound :=
  rat_witness_certificate_sound certificate831 valid831 MajorityCertificates.Inputs041.envelope_sound831

def certificate832 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs041.envelope832,(47/20),(23/100),(2605974084985895537591801/1000000000000000000),(881845031/500000000),32,(503500017/500000000),(292722683641830949/1000000000000000000),1,(4472621967974437/1000000000000000000)⟩
theorem valid832 : certificate832.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid832,?_⟩
  decide +kernel
theorem sound832 : certificate832.Sound :=
  rat_witness_certificate_sound certificate832 valid832 MajorityCertificates.Inputs041.envelope_sound832

def certificate833 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope833,(47/20),(7/50),(210034515586513729646543/125000000000000000),(892340759/500000000),32,(374323161/1000000000),0,1,(8076206893041/50000000000000000)⟩
theorem valid833 : certificate833.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid833,?_⟩
  decide +kernel
theorem sound833 : certificate833.Sound :=
  rat_witness_certificate_sound certificate833 valid833 MajorityCertificates.Inputs041.envelope_sound833

def certificate834 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope834,(47/20),(7/50),(210034515586513729646543/125000000000000000),(1620496937/1000000000),32,(1448323/800000),0,(1125000854723244783/1000000000000000000),(698391402767/200000000000000000)⟩
theorem valid834 : certificate834.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid834,?_⟩
  decide +kernel
theorem sound834 : certificate834.Sound :=
  rat_witness_certificate_sound certificate834 valid834 MajorityCertificates.Inputs041.envelope_sound834

def certificate835 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs041.envelope835,(47/20),(23/100),(210034515586513729646543/125000000000000000),(35346241/20000000),32,(62948183/62500000),(36547715488055289/125000000000000000),1,(2320559867244761/500000000000000000)⟩
theorem valid835 : certificate835.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid835,?_⟩
  decide +kernel
theorem sound835 : certificate835.Sound :=
  rat_witness_certificate_sound certificate835 valid835 MajorityCertificates.Inputs041.envelope_sound835

def certificate836 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope836,(47/20),(7/50),(587816181513631838837573/500000000000000000),(459816311/250000000),32,(73617967/200000000),0,1,(115680839549/125000000000000000)⟩
theorem valid836 : certificate836.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid836,?_⟩
  decide +kernel
theorem sound836 : certificate836.Sound :=
  rat_witness_certificate_sound certificate836 valid836 MajorityCertificates.Inputs041.envelope_sound836

def certificate837 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs041.envelope837,(47/20),(7/50),(587816181513631838837573/500000000000000000),(1627215987/1000000000),32,(1796357923/1000000000),0,(1125001221616102861/1000000000000000000),(6646013965709/1000000000000000000)⟩
theorem valid837 : certificate837.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid837,?_⟩
  decide +kernel
theorem sound837 : certificate837.Sound :=
  rat_witness_certificate_sound certificate837 valid837 MajorityCertificates.Inputs041.envelope_sound837

def certificate838 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs041.envelope838,(47/20),(23/100),(587816181513631838837573/500000000000000000),(1776315363/1000000000),32,(1007/1000),(18210945373383537/62500000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid838 : certificate838.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid838,?_⟩
  decide +kernel
theorem sound838 : certificate838.Sound :=
  rat_witness_certificate_sound certificate838 valid838 MajorityCertificates.Inputs041.envelope_sound838

def certificate839 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs041.envelope839,(47/20),(7/50),(87027072012813190743797/100000000000000000),(222424539/125000000),32,(374926479/1000000000),0,1,(10273419566273/1000000000000000000)⟩
theorem valid839 : certificate839.Valid := by
  refine ⟨MajorityCertificates.Inputs041.inputs_valid839,?_⟩
  decide +kernel
theorem sound839 : certificate839.Sound :=
  rat_witness_certificate_sound certificate839 valid839 MajorityCertificates.Inputs041.envelope_sound839

def certificates : List RatWitnessCertificate := [certificate820,certificate821,certificate822,certificate823,certificate824,certificate825,certificate826,certificate827,certificate828,certificate829,certificate830,certificate831,certificate832,certificate833,certificate834,certificate835,certificate836,certificate837,certificate838,certificate839]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound820,List.forall_mem_cons.mpr ⟨sound821,List.forall_mem_cons.mpr ⟨sound822,List.forall_mem_cons.mpr ⟨sound823,List.forall_mem_cons.mpr ⟨sound824,List.forall_mem_cons.mpr ⟨sound825,List.forall_mem_cons.mpr ⟨sound826,List.forall_mem_cons.mpr ⟨sound827,List.forall_mem_cons.mpr ⟨sound828,List.forall_mem_cons.mpr ⟨sound829,List.forall_mem_cons.mpr ⟨sound830,List.forall_mem_cons.mpr ⟨sound831,List.forall_mem_cons.mpr ⟨sound832,List.forall_mem_cons.mpr ⟨sound833,List.forall_mem_cons.mpr ⟨sound834,List.forall_mem_cons.mpr ⟨sound835,List.forall_mem_cons.mpr ⟨sound836,List.forall_mem_cons.mpr ⟨sound837,List.forall_mem_cons.mpr ⟨sound838,List.forall_mem_cons.mpr ⟨sound839,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch041
