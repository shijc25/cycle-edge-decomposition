import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch042

def certificate840 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope840,(47/20),(7/50),(87027072012813190743797/100000000000000000),(1619340131/1000000000),32,(906515519/500000000),0,(1125001650258727663/1000000000000000000),(9611430383111/1000000000000000000)⟩
theorem valid840 : certificate840.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid840,?_⟩
  decide +kernel
theorem sound840 : certificate840.Sound :=
  rat_witness_certificate_sound certificate840 valid840 MajorityCertificates.Inputs042.envelope_sound840

def certificate841 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope841,(47/20),(1/4),(87027072012813190743797/100000000000000000),(1737540189/1000000000),32,(1007000001/1000000000),(158940719618877489/500000000000000000),1,(4472589425169449/1000000000000000000)⟩
theorem valid841 : certificate841.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid841,?_⟩
  decide +kernel
theorem sound841 : certificate841.Sound :=
  rat_witness_certificate_sound certificate841 valid841 MajorityCertificates.Inputs042.envelope_sound841

def certificate842 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope842,(47/20),(7/50),(167845706612490950672187/250000000000000000),(1827160037/1000000000),32,(92348839/250000000),0,1,(6913844715599/1000000000000000000)⟩
theorem valid842 : certificate842.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid842,?_⟩
  decide +kernel
theorem sound842 : certificate842.Sound :=
  rat_witness_certificate_sound certificate842 valid842 MajorityCertificates.Inputs042.envelope_sound842

def certificate843 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope843,(47/20),(7/50),(167845706612490950672187/250000000000000000),(1623546311/1000000000),32,(1804189263/1000000000),0,(1125002139125816361/1000000000000000000),(34715100561/1000000000000000000)⟩
theorem valid843 : certificate843.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid843,?_⟩
  decide +kernel
theorem sound843 : certificate843.Sound :=
  rat_witness_certificate_sound certificate843 valid843 MajorityCertificates.Inputs042.envelope_sound843

def certificate844 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope844,(47/20),(1/4),(167845706612490950672187/250000000000000000),(1743862413/1000000000),32,(1007/1000),(317148130855732429/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid844 : certificate844.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid844,?_⟩
  decide +kernel
theorem sound844 : certificate844.Sound :=
  rat_witness_certificate_sound certificate844 valid844 MajorityCertificates.Inputs042.envelope_sound844

def certificate845 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope845,(47/20),(7/50),(534550273825938603099079/1000000000000000000),(1842214587/1000000000),32,(73556551/200000000),0,1,(9484771398089/500000000000000000)⟩
theorem valid845 : certificate845.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid845,?_⟩
  decide +kernel
theorem sound845 : certificate845.Sound :=
  rat_witness_certificate_sound certificate845 valid845 MajorityCertificates.Inputs042.envelope_sound845

def certificate846 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope846,(47/20),(7/50),(534550273825938603099079/1000000000000000000),(355798391/200000000),32,(1546822091/1000000000),0,(1125002686693751227/1000000000000000000),(6828147719547/500000000000000000)⟩
theorem valid846 : certificate846.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid846,?_⟩
  decide +kernel
theorem sound846 : certificate846.Sound :=
  rat_witness_certificate_sound certificate846 valid846 MajorityCertificates.Inputs042.envelope_sound846

def certificate847 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope847,(47/20),(1/4),(534550273825938603099079/1000000000000000000),(17502147/10000000),32,(1007/1000),(316421975705637641/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid847 : certificate847.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid847,?_⟩
  decide +kernel
theorem sound847 : certificate847.Sound :=
  rat_witness_certificate_sound certificate847 valid847 MajorityCertificates.Inputs042.envelope_sound847

def certificate848 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope848,(47/20),(7/50),(218167913631906075246811/500000000000000000),(1840179751/1000000000),32,(183997793/500000000),0,1,(1020653187273/100000000000000000)⟩
theorem valid848 : certificate848.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid848,?_⟩
  decide +kernel
theorem sound848 : certificate848.Sound :=
  rat_witness_certificate_sound certificate848 valid848 MajorityCertificates.Inputs042.envelope_sound848

def certificate849 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope849,(47/20),(7/50),(218167913631906075246811/500000000000000000),(67036057/40000000),32,(53224961/31250000),0,(1125003291440654481/1000000000000000000),(256069457707/1000000000000000000)⟩
theorem valid849 : certificate849.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid849,?_⟩
  decide +kernel
theorem sound849 : certificate849.Sound :=
  rat_witness_certificate_sound certificate849 valid849 MajorityCertificates.Inputs042.envelope_sound849

def certificate850 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope850,(47/20),(1/4),(218167913631906075246811/500000000000000000),(878307819/500000000),32,(1007/1000),(493282635523697/1562500000000000),1,(447258843902381/100000000000000000)⟩
theorem valid850 : certificate850.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid850,?_⟩
  decide +kernel
theorem sound850 : certificate850.Sound :=
  rat_witness_certificate_sound certificate850 valid850 MajorityCertificates.Inputs042.envelope_sound850

def certificate851 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope851,(47/20),(7/50),(45427313556122745628759/125000000000000000),(1815005839/1000000000),32,(370757753/1000000000),0,1,(30873519990299/500000000000000000)⟩
theorem valid851 : certificate851.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid851,?_⟩
  decide +kernel
theorem sound851 : certificate851.Sound :=
  rat_witness_certificate_sound certificate851 valid851 MajorityCertificates.Inputs042.envelope_sound851

def certificate852 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope852,(47/20),(7/50),(45427313556122745628759/125000000000000000),(1636133137/1000000000),32,(444656801/250000000),0,(562501975923216891/500000000000000000),(4904040158981/250000000000000000)⟩
theorem valid852 : certificate852.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid852,?_⟩
  decide +kernel
theorem sound852 : certificate852.Sound :=
  rat_witness_certificate_sound certificate852 valid852 MajorityCertificates.Inputs042.envelope_sound852

def certificate853 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope853,(47/20),(1/4),(45427313556122745628759/125000000000000000),(352613559/200000000),32,(1007/1000),(314984663120999881/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid853 : certificate853.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid853,?_⟩
  decide +kernel
theorem sound853 : certificate853.Sound :=
  rat_witness_certificate_sound certificate853 valid853 MajorityCertificates.Inputs042.envelope_sound853

def certificate854 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope854,(47/20),(7/50),(76942453293967764291679/250000000000000000),(926876541/500000000),32,(73316227/200000000),0,1,(1267058135723/125000000000000000)⟩
theorem valid854 : certificate854.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid854,?_⟩
  decide +kernel
theorem sound854 : certificate854.Sound :=
  rat_witness_certificate_sound certificate854 valid854 MajorityCertificates.Inputs042.envelope_sound854

def certificate855 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope855,(47/20),(7/50),(76942453293967764291679/250000000000000000),(221358949/125000000),32,(1557721841/1000000000),0,(22500093327856377/20000000000000000),(2386679869861/250000000000000000)⟩
theorem valid855 : certificate855.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid855,?_⟩
  decide +kernel
theorem sound855 : certificate855.Sound :=
  rat_witness_certificate_sound certificate855 valid855 MajorityCertificates.Inputs042.envelope_sound855

def certificate856 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope856,(47/20),(1/4),(76942453293967764291679/250000000000000000),(1769569953/1000000000),32,(1007/1000),(78568382221678263/250000000000000000),1,(4472588439023809/1000000000000000000)⟩
theorem valid856 : certificate856.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid856,?_⟩
  decide +kernel
theorem sound856 : certificate856.Sound :=
  rat_witness_certificate_sound certificate856 valid856 MajorityCertificates.Inputs042.envelope_sound856

def certificate857 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs042.envelope857,(47/20),(7/50),(26431560741512952229391/100000000000000000),(1843898967/1000000000),32,(367605461/1000000000),0,1,(424299933139/25000000000000000)⟩
theorem valid857 : certificate857.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid857,?_⟩
  decide +kernel
theorem sound857 : certificate857.Sound :=
  rat_witness_certificate_sound certificate857 valid857 MajorityCertificates.Inputs042.envelope_sound857

def certificate858 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs042.envelope858,(47/20),(7/50),(26431560741512952229391/100000000000000000),(1743799247/1000000000),32,(1595126807/1000000000),0,(281251358390847439/250000000000000000),(525093886331/200000000000000000)⟩
theorem valid858 : certificate858.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid858,?_⟩
  decide +kernel
theorem sound858 : certificate858.Sound :=
  rat_witness_certificate_sound certificate858 valid858 MajorityCertificates.Inputs042.envelope_sound858

def certificate859 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs042.envelope859,(47/20),(27/100),(26431560741512952229391/100000000000000000),(1732664423/1000000000),32,(1007/1000),(68140819917322713/200000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid859 : certificate859.Valid := by
  refine ⟨MajorityCertificates.Inputs042.inputs_valid859,?_⟩
  decide +kernel
theorem sound859 : certificate859.Sound :=
  rat_witness_certificate_sound certificate859 valid859 MajorityCertificates.Inputs042.envelope_sound859

def certificates : List RatWitnessCertificate := [certificate840,certificate841,certificate842,certificate843,certificate844,certificate845,certificate846,certificate847,certificate848,certificate849,certificate850,certificate851,certificate852,certificate853,certificate854,certificate855,certificate856,certificate857,certificate858,certificate859]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound840,List.forall_mem_cons.mpr ⟨sound841,List.forall_mem_cons.mpr ⟨sound842,List.forall_mem_cons.mpr ⟨sound843,List.forall_mem_cons.mpr ⟨sound844,List.forall_mem_cons.mpr ⟨sound845,List.forall_mem_cons.mpr ⟨sound846,List.forall_mem_cons.mpr ⟨sound847,List.forall_mem_cons.mpr ⟨sound848,List.forall_mem_cons.mpr ⟨sound849,List.forall_mem_cons.mpr ⟨sound850,List.forall_mem_cons.mpr ⟨sound851,List.forall_mem_cons.mpr ⟨sound852,List.forall_mem_cons.mpr ⟨sound853,List.forall_mem_cons.mpr ⟨sound854,List.forall_mem_cons.mpr ⟨sound855,List.forall_mem_cons.mpr ⟨sound856,List.forall_mem_cons.mpr ⟨sound857,List.forall_mem_cons.mpr ⟨sound858,List.forall_mem_cons.mpr ⟨sound859,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch042
