import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch045

def certificate900 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope900,(47/20),(7/50),(6886630868879403605273/100000000000000000),(899287783/500000000),32,(1525179801/1000000000),0,(562510427384209701/500000000000000000),(135074393382847/1000000000000000000)⟩
theorem valid900 : certificate900.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid900,?_⟩
  decide +kernel
theorem sound900 : certificate900.Sound :=
  rat_witness_certificate_sound certificate900 valid900 MajorityCertificates.Inputs045.envelope_sound900

def certificate901 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope901,(47/20),(59/200),(6886630868879403605273/100000000000000000),(884869861/500000000),32,(1007/1000),(364168908462408983/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid901 : certificate901.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid901,?_⟩
  decide +kernel
theorem sound901 : certificate901.Sound :=
  rat_witness_certificate_sound certificate901 valid901 MajorityCertificates.Inputs045.envelope_sound901

def certificate902 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope902,(47/20),(7/50),(64604278686172635417061/1000000000000000000),(120531697/62500000),32,(179789413/500000000),0,1,(3675950311439/50000000000000000)⟩
theorem valid902 : certificate902.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid902,?_⟩
  decide +kernel
theorem sound902 : certificate902.Sound :=
  rat_witness_certificate_sound certificate902 valid902 MajorityCertificates.Inputs045.envelope_sound902

def certificate903 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope903,(47/20),(7/50),(64604278686172635417061/1000000000000000000),(179931639/100000000),32,(304898407/200000000),0,(1125022230606314131/1000000000000000000),(70802493049409/500000000000000000)⟩
theorem valid903 : certificate903.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid903,?_⟩
  decide +kernel
theorem sound903 : certificate903.Sound :=
  rat_witness_certificate_sound certificate903 valid903 MajorityCertificates.Inputs045.envelope_sound903

def certificate904 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope904,(47/20),(59/200),(64604278686172635417061/1000000000000000000),(888347361/500000000),32,(1007/1000),(181696717899325713/500000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid904 : certificate904.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid904,?_⟩
  decide +kernel
theorem sound904 : certificate904.Sound :=
  rat_witness_certificate_sound certificate904 valid904 MajorityCertificates.Inputs045.envelope_sound904

def certificate905 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope905,(47/20),(7/50),(60765393535420988496591/1000000000000000000),(387165367/200000000),32,(11217419/31250000),0,1,(3895735891051/50000000000000000)⟩
theorem valid905 : certificate905.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid905,?_⟩
  decide +kernel
theorem sound905 : certificate905.Sound :=
  rat_witness_certificate_sound certificate905 valid905 MajorityCertificates.Inputs045.envelope_sound905

def certificate906 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope906,(47/20),(7/50),(60765393535420988496591/1000000000000000000),(449952761/250000000),32,(1524116237/1000000000),0,(281255908764827353/250000000000000000),(75991223950877/500000000000000000)⟩
theorem valid906 : certificate906.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid906,?_⟩
  decide +kernel
theorem sound906 : certificate906.Sound :=
  rat_witness_certificate_sound certificate906 valid906 MajorityCertificates.Inputs045.envelope_sound906

def certificate907 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope907,(47/20),(59/200),(60765393535420988496591/1000000000000000000),(222972111/125000000),32,(1007/1000),(90654081988607013/250000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid907 : certificate907.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid907,?_⟩
  decide +kernel
theorem sound907 : certificate907.Sound :=
  rat_witness_certificate_sound certificate907 valid907 MajorityCertificates.Inputs045.envelope_sound907

def certificate908 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope908,(47/20),(31/200),(57295072897978197163157/1000000000000000000),(1898320599/1000000000),32,(322413/800000),0,1,(3388153299181/40000000000000000)⟩
theorem valid908 : certificate908.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid908,?_⟩
  decide +kernel
theorem sound908 : certificate908.Sound :=
  rat_witness_certificate_sound certificate908 valid908 MajorityCertificates.Inputs045.envelope_sound908

def certificate909 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope909,(47/20),(31/200),(57295072897978197163157/1000000000000000000),(1750390699/1000000000),32,(1558249373/1000000000),0,(140628133330295593/125000000000000000),(26366845222801/1000000000000000000)⟩
theorem valid909 : certificate909.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid909,?_⟩
  decide +kernel
theorem sound909 : certificate909.Sound :=
  rat_witness_certificate_sound certificate909 valid909 MajorityCertificates.Inputs045.envelope_sound909

def certificate910 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope910,(47/20),(59/200),(57295072897978197163157/1000000000000000000),(223841081/125000000),32,(1007/1000),(361865649978431771/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid910 : certificate910.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid910,?_⟩
  decide +kernel
theorem sound910 : certificate910.Sound :=
  rat_witness_certificate_sound certificate910 valid910 MajorityCertificates.Inputs045.envelope_sound910

def certificate911 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope911,(47/20),(17/100),(54147318024800195909169/1000000000000000000),(1858615187/1000000000),32,(44901581/100000000),0,1,(35216132542557/250000000000000000)⟩
theorem valid911 : certificate911.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid911,?_⟩
  decide +kernel
theorem sound911 : certificate911.Sound :=
  rat_witness_certificate_sound certificate911 valid911 MajorityCertificates.Inputs045.envelope_sound911

def certificate912 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope912,(47/20),(17/100),(54147318024800195909169/1000000000000000000),(1759060013/1000000000),32,(152255127/100000000),0,(1125026523872296473/1000000000000000000),(9622504682487/125000000000000000)⟩
theorem valid912 : certificate912.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid912,?_⟩
  decide +kernel
theorem sound912 : certificate912.Sound :=
  rat_witness_certificate_sound certificate912 valid912 MajorityCertificates.Inputs045.envelope_sound912

def certificate913 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope913,(47/20),(3/10),(54147318024800195909169/1000000000000000000),(1785507869/1000000000),32,(251751641/250000000),(73594039982215867/200000000000000000),1,(4479061456810613/1000000000000000000)⟩
theorem valid913 : certificate913.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid913,?_⟩
  decide +kernel
theorem sound913 : certificate913.Sound :=
  rat_witness_certificate_sound certificate913 valid913 MajorityCertificates.Inputs045.envelope_sound913

def certificate914 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope914,(47/20),(1739/10000),(2051325527390199155699/40000000000000000),(1856654477/1000000000),32,(115082113/250000000),0,1,(91312797837891/1000000000000000000)⟩
theorem valid914 : certificate914.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid914,?_⟩
  decide +kernel
theorem sound914 : certificate914.Sound :=
  rat_witness_certificate_sound certificate914 valid914 MajorityCertificates.Inputs045.envelope_sound914

def certificate915 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope915,(47/20),(1739/10000),(2051325527390199155699/40000000000000000),(1759032483/1000000000),32,(303455891/200000000),0,(140628500658477151/125000000000000000),(18338106310463/100000000000000000)⟩
theorem valid915 : certificate915.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid915,?_⟩
  decide +kernel
theorem sound915 : certificate915.Sound :=
  rat_witness_certificate_sound certificate915 valid915 MajorityCertificates.Inputs045.envelope_sound915

def certificate916 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope916,(47/20),(3/10),(2051325527390199155699/40000000000000000),(1792731649/1000000000),32,(1007/1000),(73437612565701979/200000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid916 : certificate916.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid916,?_⟩
  decide +kernel
theorem sound916 : certificate916.Sound :=
  rat_witness_certificate_sound certificate916 valid916 MajorityCertificates.Inputs045.envelope_sound916

def certificate917 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs045.envelope917,(47/20),(437/2500),(24334652116046352788149/500000000000000000),(929927281/500000000),32,(462555759/1000000000),0,1,(24085900667389/250000000000000000)⟩
theorem valid917 : certificate917.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid917,?_⟩
  decide +kernel
theorem sound917 : certificate917.Sound :=
  rat_witness_certificate_sound certificate917 valid917 MajorityCertificates.Inputs045.envelope_sound917

def certificate918 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs045.envelope918,(47/20),(437/2500),(24334652116046352788149/500000000000000000),(351614411/200000000),32,(758702917/500000000),0,(140628688668698477/125000000000000000),(97668840971177/500000000000000000)⟩
theorem valid918 : certificate918.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid918,?_⟩
  decide +kernel
theorem sound918 : certificate918.Sound :=
  rat_witness_certificate_sound certificate918 valid918 MajorityCertificates.Inputs045.envelope_sound918

def certificate919 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs045.envelope919,(47/20),(3/10),(24334652116046352788149/500000000000000000),(89999529/50000000),32,(1007/1000),(91604338573713993/250000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid919 : certificate919.Valid := by
  refine ⟨MajorityCertificates.Inputs045.inputs_valid919,?_⟩
  decide +kernel
theorem sound919 : certificate919.Sound :=
  rat_witness_certificate_sound certificate919 valid919 MajorityCertificates.Inputs045.envelope_sound919

def certificates : List RatWitnessCertificate := [certificate900,certificate901,certificate902,certificate903,certificate904,certificate905,certificate906,certificate907,certificate908,certificate909,certificate910,certificate911,certificate912,certificate913,certificate914,certificate915,certificate916,certificate917,certificate918,certificate919]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound900,List.forall_mem_cons.mpr ⟨sound901,List.forall_mem_cons.mpr ⟨sound902,List.forall_mem_cons.mpr ⟨sound903,List.forall_mem_cons.mpr ⟨sound904,List.forall_mem_cons.mpr ⟨sound905,List.forall_mem_cons.mpr ⟨sound906,List.forall_mem_cons.mpr ⟨sound907,List.forall_mem_cons.mpr ⟨sound908,List.forall_mem_cons.mpr ⟨sound909,List.forall_mem_cons.mpr ⟨sound910,List.forall_mem_cons.mpr ⟨sound911,List.forall_mem_cons.mpr ⟨sound912,List.forall_mem_cons.mpr ⟨sound913,List.forall_mem_cons.mpr ⟨sound914,List.forall_mem_cons.mpr ⟨sound915,List.forall_mem_cons.mpr ⟨sound916,List.forall_mem_cons.mpr ⟨sound917,List.forall_mem_cons.mpr ⟨sound918,List.forall_mem_cons.mpr ⟨sound919,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch045
