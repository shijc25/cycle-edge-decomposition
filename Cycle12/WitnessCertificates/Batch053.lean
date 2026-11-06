import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch053

def certificate1060 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs053.envelope1060,(47/20),(63/200),(272404725454788921341/15625000000000000),(15837589/7812500),32,(1007000001/1000000000),(364098756475863417/1000000000000000000),1,(4472589425169451/1000000000000000000)⟩
theorem valid1060 : certificate1060.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1060,?_⟩
  decide +kernel
theorem sound1060 : certificate1060.Sound :=
  rat_witness_certificate_sound certificate1060 valid1060 MajorityCertificates.Inputs053.envelope_sound1060

def certificate1061 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs053.envelope1061,(47/20),(531/2500),(17137809829215648313311/1000000000000000000),(244557361/125000000),32,(141024479/250000000),0,1,(406662702868701/1000000000000000000)⟩
theorem valid1061 : certificate1061.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1061,?_⟩
  decide +kernel
theorem sound1061 : certificate1061.Sound :=
  rat_witness_certificate_sound certificate1061 valid1061 MajorityCertificates.Inputs053.envelope_sound1061

def certificate1062 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs053.envelope1062,(47/20),(531/2500),(17137809829215648313311/1000000000000000000),(42276767/25000000),32,(1564288569/1000000000),0,(1125083806124495487/1000000000000000000),(343649530882249/500000000000000000)⟩
theorem valid1062 : certificate1062.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1062,?_⟩
  decide +kernel
theorem sound1062 : certificate1062.Sound :=
  rat_witness_certificate_sound certificate1062 valid1062 MajorityCertificates.Inputs053.envelope_sound1062

def certificate1063 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs053.envelope1063,(47/20),(63/200),(17137809829215648313311/1000000000000000000),(1018086887/500000000),32,(1007/1000),(181766528126000459/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1063 : certificate1063.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1063,?_⟩
  decide +kernel
theorem sound1063 : certificate1063.Sound :=
  rat_witness_certificate_sound certificate1063 valid1063 MajorityCertificates.Inputs053.envelope_sound1063

def certificate1064 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs053.envelope1064,(47/20),(2133/10000),(2107087418192514216281/125000000000000000),(1966555619/1000000000),32,(28293151/50000000),0,1,(75010997971603/250000000000000000)⟩
theorem valid1064 : certificate1064.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1064,?_⟩
  decide +kernel
theorem sound1064 : certificate1064.Sound :=
  rat_witness_certificate_sound certificate1064 valid1064 MajorityCertificates.Inputs053.envelope_sound1064

def certificate1065 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs053.envelope1065,(47/20),(2133/10000),(2107087418192514216281/125000000000000000),(103252913/62500000),32,(323804107/200000000),0,(1125085203798349483/1000000000000000000),(297157597752733/1000000000000000000)⟩
theorem valid1065 : certificate1065.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1065,?_⟩
  decide +kernel
theorem sound1065 : certificate1065.Sound :=
  rat_witness_certificate_sound certificate1065 valid1065 MajorityCertificates.Inputs053.envelope_sound1065

def certificate1066 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs053.envelope1066,(47/20),(63/200),(2107087418192514216281/125000000000000000),(511319173/250000000),32,(1007/1000),(181485000381743833/500000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1066 : certificate1066.Valid := by
  refine ⟨MajorityCertificates.Inputs053.inputs_valid1066,?_⟩
  decide +kernel
theorem sound1066 : certificate1066.Sound :=
  rat_witness_certificate_sound certificate1066 valid1066 MajorityCertificates.Inputs053.envelope_sound1066

def certificates : List RatWitnessCertificate := [certificate1060,certificate1061,certificate1062,certificate1063,certificate1064,certificate1065,certificate1066]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1060,List.forall_mem_cons.mpr ⟨sound1061,List.forall_mem_cons.mpr ⟨sound1062,List.forall_mem_cons.mpr ⟨sound1063,List.forall_mem_cons.mpr ⟨sound1064,List.forall_mem_cons.mpr ⟨sound1065,List.forall_mem_cons.mpr ⟨sound1066,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch053
