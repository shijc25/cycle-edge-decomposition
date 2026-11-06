import Cycle12.RationalPopulationCertificate
import Cycle12.WitnessCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.PopulationCertificates.Batch053

def certificate1060 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1060,(198806338180814466443/200000000000000000),(3971573173525913566801/1000000000000000000),(110478254501721281/500000000000000000),(243268215566612851/200000000000000000),(228704549/1000000000),(3384165979492301/8000000000000000),0,0,(777288745070569103/1000000000000000000)⟩
theorem valid1060 : certificate1060.Valid := by decide +kernel
theorem sound1060 : certificate1060.Sound := rat_population_certificate_sound certificate1060 valid1060 WitnessCertificates.Batch053.valid1060

def certificate1061 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1061,(958430071261117944869/1000000000000000000),(4049940969758249613629/1000000000000000000),(229314564747262201/1000000000000000000),(102983448523321583/100000000000000000),(1162765663/1000000000),(215382671846094757/1000000000000000000),0,0,(151271012462474691/250000000000000000)⟩
theorem valid1061 : certificate1061.Valid := by decide +kernel
theorem sound1061 : certificate1061.Sound := rat_population_certificate_sound certificate1061 valid1061 WitnessCertificates.Batch053.valid1061

def certificate1062 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1062,(958430071261117944869/1000000000000000000),(4049940969758249613629/1000000000000000000),(229314564747262201/1000000000000000000),(1084022974431506719/1000000000000000000),(3999147313/1000000000),0,(446340424231691861/1000000000000000000),(17634837736743323/25000000000000000),(27615565224615491981/500000000000000000)⟩
theorem valid1062 : certificate1062.Valid := by decide +kernel
theorem sound1062 : certificate1062.Sound := rat_population_certificate_sound certificate1062 valid1062 WitnessCertificates.Batch053.valid1062

def certificate1063 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1063,(958430071261117944869/1000000000000000000),(4049940969758249613629/1000000000000000000),(229314564747262201/1000000000000000000),(1214080676423639823/1000000000000000000),(56437213/250000000),(105695005984255417/250000000000000000),0,0,(195393481198331639/250000000000000000)⟩
theorem valid1063 : certificate1063.Valid := by decide +kernel
theorem sound1063 : certificate1063.Sound := rat_population_certificate_sound certificate1063 valid1063 WitnessCertificates.Batch053.valid1063

def certificate1064 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1064,(231118446031702313983/250000000000000000),(4130869845655909437107/1000000000000000000),(59475863953628191/250000000000000000),(1029203999504749529/1000000000000000000),(72440557/62500000),(21573871685344913/100000000000000000),0,0,(607350989989147791/1000000000000000000)⟩
theorem valid1064 : certificate1064.Valid := by decide +kernel
theorem sound1064 : certificate1064.Sound := rat_population_certificate_sound certificate1064 valid1064 WitnessCertificates.Batch053.valid1064

def certificate1065 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1065,(231118446031702313983/250000000000000000),(4130869845655909437107/1000000000000000000),(59475863953628191/250000000000000000),(1083121520126198641/1000000000000000000),(498845151/125000000),0,(446628970370628887/1000000000000000000),(353108789717492901/500000000000000000),(56572755757340626393/1000000000000000000)⟩
theorem valid1065 : certificate1065.Valid := by decide +kernel
theorem sound1065 : certificate1065.Sound := rat_population_certificate_sound certificate1065 valid1065 WitnessCertificates.Batch053.valid1065

def certificate1066 : RatPopulationCertificate := ⟨WitnessCertificates.Batch053.certificate1066,(231118446031702313983/250000000000000000),(4130869845655909437107/1000000000000000000),(59475863953628191/250000000000000000),(1211809859036950351/1000000000000000000),(55696657/250000000),(422540425856803263/1000000000000000000),0,0,(98235667736918311/125000000000000000)⟩
theorem valid1066 : certificate1066.Valid := by decide +kernel
theorem sound1066 : certificate1066.Sound := rat_population_certificate_sound certificate1066 valid1066 WitnessCertificates.Batch053.valid1066

def certificates : List RatPopulationCertificate := [certificate1060,certificate1061,certificate1062,certificate1063,certificate1064,certificate1065,certificate1066]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1060,List.forall_mem_cons.mpr ⟨sound1061,List.forall_mem_cons.mpr ⟨sound1062,List.forall_mem_cons.mpr ⟨sound1063,List.forall_mem_cons.mpr ⟨sound1064,List.forall_mem_cons.mpr ⟨sound1065,List.forall_mem_cons.mpr ⟨sound1066,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
end Cycle12.PopulationCertificates.Batch053
