import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch044

def certificate880 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope880,(47/20),(27/100),(118201867122811528571737/1000000000000000000),(355657221/200000000),32,(1007/1000),(167752857353471531/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid880 : certificate880.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid880,?_⟩
  decide +kernel
theorem sound880 : certificate880.Sound :=
  rat_witness_certificate_sound certificate880 valid880 MajorityCertificates.Inputs044.envelope_sound880

def certificate881 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope881,(47/20),(7/50),(108113375975837050826623/1000000000000000000),(1889213003/1000000000),32,(5673501/15625000),0,1,(20846070743167/500000000000000000)⟩
theorem valid881 : certificate881.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid881,?_⟩
  decide +kernel
theorem sound881 : certificate881.Sound :=
  rat_witness_certificate_sound certificate881 valid881 MajorityCertificates.Inputs044.envelope_sound881

def certificate882 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope882,(47/20),(7/50),(108113375975837050826623/1000000000000000000),(35888497/20000000),32,(382262751/250000000),0,(1125013284049171799/1000000000000000000),(78884878026589/1000000000000000000)⟩
theorem valid882 : certificate882.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid882,?_⟩
  decide +kernel
theorem sound882 : certificate882.Sound :=
  rat_witness_certificate_sound certificate882 valid882 MajorityCertificates.Inputs044.envelope_sound882

def certificate883 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope883,(47/20),(7/25),(108113375975837050826623/1000000000000000000),(13479677/7812500),32,(503500389/500000000),(44089589799765589/125000000000000000),1,(4473355659738909/1000000000000000000)⟩
theorem valid883 : certificate883.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid883,?_⟩
  decide +kernel
theorem sound883 : certificate883.Sound :=
  rat_witness_certificate_sound certificate883 valid883 MajorityCertificates.Inputs044.envelope_sound883

def certificate884 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope884,(47/20),(7/50),(49671218117945647540743/500000000000000000),(1903591013/1000000000),32,(361771859/1000000000),0,1,(1576859604463/40000000000000000)⟩
theorem valid884 : certificate884.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid884,?_⟩
  decide +kernel
theorem sound884 : certificate884.Sound :=
  rat_witness_certificate_sound certificate884 valid884 MajorityCertificates.Inputs044.envelope_sound884

def certificate885 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope885,(47/20),(7/50),(49671218117945647540743/500000000000000000),(897667663/500000000),32,(1528116979/1000000000),0,(562507228454533377/500000000000000000),(43387471982557/500000000000000000)⟩
theorem valid885 : certificate885.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid885,?_⟩
  decide +kernel
theorem sound885 : certificate885.Sound :=
  rat_witness_certificate_sound certificate885 valid885 MajorityCertificates.Inputs044.envelope_sound885

def certificate886 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope886,(47/20),(7/25),(49671218117945647540743/500000000000000000),(884905853/500000000),32,(1007/1000),(86880662318942609/250000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid886 : certificate886.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid886,?_⟩
  decide +kernel
theorem sound886 : certificate886.Sound :=
  rat_witness_certificate_sound certificate886 valid886 MajorityCertificates.Inputs044.envelope_sound886

def certificate887 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope887,(47/20),(7/50),(45833768599724083707897/500000000000000000),(1901914883/1000000000),32,(361927931/1000000000),0,1,(12794079029111/250000000000000000)⟩
theorem valid887 : certificate887.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid887,?_⟩
  decide +kernel
theorem sound887 : certificate887.Sound :=
  rat_witness_certificate_sound certificate887 valid887 MajorityCertificates.Inputs044.envelope_sound887

def certificate888 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope888,(47/20),(7/50),(45833768599724083707897/500000000000000000),(35922843/20000000),32,(763659947/500000000),0,(225003133466465547/200000000000000000),(95450029861847/1000000000000000000)⟩
theorem valid888 : certificate888.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid888,?_⟩
  decide +kernel
theorem sound888 : certificate888.Sound :=
  rat_witness_certificate_sound certificate888 valid888 MajorityCertificates.Inputs044.envelope_sound888

def certificate889 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope889,(47/20),(7/25),(45833768599724083707897/500000000000000000),(888268889/500000000),32,(1007/1000),(346781258525637143/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid889 : certificate889.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid889,?_⟩
  decide +kernel
theorem sound889 : certificate889.Sound :=
  rat_witness_certificate_sound certificate889 valid889 MajorityCertificates.Inputs044.envelope_sound889

def certificate890 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope890,(47/20),(7/50),(1326750426848419357023/15625000000000000),(378782781/200000000),32,(90667903/250000000),0,1,(71131327452917/1000000000000000000)⟩
theorem valid890 : certificate890.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid890,?_⟩
  decide +kernel
theorem sound890 : certificate890.Sound :=
  rat_witness_certificate_sound certificate890 valid890 MajorityCertificates.Inputs044.envelope_sound890

def certificate891 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope891,(47/20),(7/50),(1326750426848419357023/15625000000000000),(1796896987/1000000000),32,(190824121/125000000),0,(1125016913823070473/1000000000000000000),(10355230317643/100000000000000000)⟩
theorem valid891 : certificate891.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid891,?_⟩
  decide +kernel
theorem sound891 : certificate891.Sound :=
  rat_witness_certificate_sound certificate891 valid891 MajorityCertificates.Inputs044.envelope_sound891

def certificate892 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope892,(47/20),(7/25),(1326750426848419357023/15625000000000000),(1789774299/1000000000),32,(503512979/500000000),(345363753069836093/1000000000000000000),1,(1124546536924517/250000000000000000)⟩
theorem valid892 : certificate892.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid892,?_⟩
  decide +kernel
theorem sound892 : certificate892.Sound :=
  rat_witness_certificate_sound certificate892 valid892 MajorityCertificates.Inputs044.envelope_sound892

def certificate893 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope893,(47/20),(7/50),(39466809037281437695057/500000000000000000),(958335501/500000000),32,(360612479/1000000000),0,1,(44953611465869/500000000000000000)⟩
theorem valid893 : certificate893.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid893,?_⟩
  decide +kernel
theorem sound893 : certificate893.Sound :=
  rat_witness_certificate_sound certificate893 valid893 MajorityCertificates.Inputs044.envelope_sound893

def certificate894 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope894,(47/20),(7/50),(39466809037281437695057/500000000000000000),(898783097/500000000),32,(1525979347/1000000000),0,(562509097443609111/500000000000000000),(56292584785023/500000000000000000)⟩
theorem valid894 : certificate894.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid894,?_⟩
  decide +kernel
theorem sound894 : certificate894.Sound :=
  rat_witness_certificate_sound certificate894 valid894 MajorityCertificates.Inputs044.envelope_sound894

def certificate895 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope895,(47/20),(7/25),(39466809037281437695057/500000000000000000),(1790160853/1000000000),32,(1007/1000),(345314096062095951/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid895 : certificate895.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid895,?_⟩
  decide +kernel
theorem sound895 : certificate895.Sound :=
  rat_witness_certificate_sound certificate895 valid895 MajorityCertificates.Inputs044.envelope_sound895

def certificate896 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope896,(47/20),(7/50),(73616648279811504845921/1000000000000000000),(1913654061/1000000000),32,(72174349/200000000),0,1,(28635836456073/500000000000000000)⟩
theorem valid896 : certificate896.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid896,?_⟩
  decide +kernel
theorem sound896 : certificate896.Sound :=
  rat_witness_certificate_sound certificate896 valid896 MajorityCertificates.Inputs044.envelope_sound896

def certificate897 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs044.envelope897,(47/20),(7/50),(73616648279811504845921/1000000000000000000),(14047359/7812500),32,(23837253/15625000),0,(56250975451624717/50000000000000000),(12176265727817/100000000000000000)⟩
theorem valid897 : certificate897.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid897,?_⟩
  decide +kernel
theorem sound897 : certificate897.Sound :=
  rat_witness_certificate_sound certificate897 valid897 MajorityCertificates.Inputs044.envelope_sound897

def certificate898 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs044.envelope898,(47/20),(59/200),(73616648279811504845921/1000000000000000000),(440708081/250000000),32,(1007/1000),(91237839550264671/250000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid898 : certificate898.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid898,?_⟩
  decide +kernel
theorem sound898 : certificate898.Sound :=
  rat_witness_certificate_sound certificate898 valid898 MajorityCertificates.Inputs044.envelope_sound898

def certificate899 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs044.envelope899,(47/20),(7/50),(6886630868879403605273/100000000000000000),(962273427/500000000),32,(359918839/1000000000),0,1,(1371070793529/20000000000000000)⟩
theorem valid899 : certificate899.Valid := by
  refine ⟨MajorityCertificates.Inputs044.inputs_valid899,?_⟩
  decide +kernel
theorem sound899 : certificate899.Sound :=
  rat_witness_certificate_sound certificate899 valid899 MajorityCertificates.Inputs044.envelope_sound899

def certificates : List RatWitnessCertificate := [certificate880,certificate881,certificate882,certificate883,certificate884,certificate885,certificate886,certificate887,certificate888,certificate889,certificate890,certificate891,certificate892,certificate893,certificate894,certificate895,certificate896,certificate897,certificate898,certificate899]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound880,List.forall_mem_cons.mpr ⟨sound881,List.forall_mem_cons.mpr ⟨sound882,List.forall_mem_cons.mpr ⟨sound883,List.forall_mem_cons.mpr ⟨sound884,List.forall_mem_cons.mpr ⟨sound885,List.forall_mem_cons.mpr ⟨sound886,List.forall_mem_cons.mpr ⟨sound887,List.forall_mem_cons.mpr ⟨sound888,List.forall_mem_cons.mpr ⟨sound889,List.forall_mem_cons.mpr ⟨sound890,List.forall_mem_cons.mpr ⟨sound891,List.forall_mem_cons.mpr ⟨sound892,List.forall_mem_cons.mpr ⟨sound893,List.forall_mem_cons.mpr ⟨sound894,List.forall_mem_cons.mpr ⟨sound895,List.forall_mem_cons.mpr ⟨sound896,List.forall_mem_cons.mpr ⟨sound897,List.forall_mem_cons.mpr ⟨sound898,List.forall_mem_cons.mpr ⟨sound899,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch044
