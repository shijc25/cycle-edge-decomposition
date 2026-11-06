import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch012

def certificate240 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope240,(97153/50000),(131430469/1000000000),(194383152808716339419/1000000000000000000),(111426417/50000000),(9/4),(355855859/1000000000),0,1,(28917786350355347/1000000000000000000)⟩
theorem valid240 : certificate240.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid240,?_⟩
  decide +kernel
theorem sound240 : certificate240.Sound :=
  rat_witness_certificate_sound certificate240 valid240 MajorityCertificates.Inputs012.envelope_sound240

def certificate241 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope241,(97153/50000),(131430469/1000000000),(194383152808716339419/1000000000000000000),(514363297/200000000),(9/4),(1371876981/1000000000),0,(1133991225178924843/1000000000000000000),(26872524020008929/1000000000000000000)⟩
theorem valid241 : certificate241.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid241,?_⟩
  decide +kernel
theorem sound241 : certificate241.Sound :=
  rat_witness_certificate_sound certificate241 valid241 MajorityCertificates.Inputs012.envelope_sound241

def certificate242 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope242,(97121/50000),(65392969/500000000),(193384223247665810983/1000000000000000000),(2232431727/1000000000),(9/4),(88457159/250000000),0,1,(3639192115339577/125000000000000000)⟩
theorem valid242 : certificate242.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid242,?_⟩
  decide +kernel
theorem sound242 : certificate242.Sound :=
  rat_witness_certificate_sound certificate242 valid242 MajorityCertificates.Inputs012.envelope_sound242

def certificate243 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope243,(97121/50000),(65392969/500000000),(193384223247665810983/1000000000000000000),(257345467/100000000),(9/4),(1372990579/1000000000),0,(1134040955894788127/1000000000000000000),(27125157044855739/1000000000000000000)⟩
theorem valid243 : certificate243.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid243,?_⟩
  decide +kernel
theorem sound243 : certificate243.Sound :=
  rat_witness_certificate_sound certificate243 valid243 MajorityCertificates.Inputs012.envelope_sound243

def certificate244 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope244,(195091/100000),(15895127/125000000),(192398482326285571833/1000000000000000000),(17599513/7812500),(9/4),(85308633/250000000),0,1,(29396355528534017/1000000000000000000)⟩
theorem valid244 : certificate244.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid244,?_⟩
  decide +kernel
theorem sound244 : certificate244.Sound :=
  rat_witness_certificate_sound certificate244 valid244 MajorityCertificates.Inputs012.envelope_sound244

def certificate245 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope245,(195091/100000),(15895127/125000000),(192398482326285571833/1000000000000000000),(2573786211/1000000000),(9/4),(343044583/250000000),0,(1134047772819496801/1000000000000000000),(5463802587943103/200000000000000000)⟩
theorem valid245 : certificate245.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid245,?_⟩
  decide +kernel
theorem sound245 : certificate245.Sound :=
  rat_witness_certificate_sound certificate245 valid245 MajorityCertificates.Inputs012.envelope_sound245

def certificate246 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope246,(24379/12500),(15844773/125000000),(38285146919970030553/200000000000000000),(2242200081/1000000000),(9/4),(68196487/200000000),0,1,(236953733842873/8000000000000000)⟩
theorem valid246 : certificate246.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid246,?_⟩
  decide +kernel
theorem sound246 : certificate246.Sound :=
  rat_witness_certificate_sound certificate246 valid246 MajorityCertificates.Inputs012.envelope_sound246

def certificate247 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope247,(24379/12500),(15844773/125000000),(38285146919970030553/200000000000000000),(2574936317/1000000000),(9/4),(343311467/250000000),0,(567048403528747333/500000000000000000),(3444524103930529/125000000000000000)⟩
theorem valid247 : certificate247.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid247,?_⟩
  decide +kernel
theorem sound247 : certificate247.Sound :=
  rat_witness_certificate_sound certificate247 valid247 MajorityCertificates.Inputs012.envelope_sound247

def certificate248 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope248,(195043/100000),(63217959/500000000),(191239946813617779739/1000000000000000000),(560840497/250000000),(23/10),(85000651/250000000),0,1,(29730512413409871/1000000000000000000)⟩
theorem valid248 : certificate248.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid248,?_⟩
  decide +kernel
theorem sound248 : certificate248.Sound :=
  rat_witness_certificate_sound certificate248 valid248 MajorityCertificates.Inputs012.envelope_sound248

def certificate249 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope249,(195043/100000),(63217959/500000000),(191239946813617779739/1000000000000000000),(644638167/250000000),(23/10),(1373965017/1000000000),0,(567052591662675639/500000000000000000),(689053908214463/25000000000000000)⟩
theorem valid249 : certificate249.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid249,?_⟩
  decide +kernel
theorem sound249 : certificate249.Sound :=
  rat_witness_certificate_sound certificate249 valid249 MajorityCertificates.Inputs012.envelope_sound249

def certificate250 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope250,(97507/50000),(126194219/1000000000),(38152244869143192641/200000000000000000),(8992831/4000000),(23/10),(169494021/500000000),0,1,(5941564158489577/200000000000000000)⟩
theorem valid250 : certificate250.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid250,?_⟩
  decide +kernel
theorem sound250 : certificate250.Sound :=
  rat_witness_certificate_sound certificate250 valid250 MajorityCertificates.Inputs012.envelope_sound250

def certificate251 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope251,(97507/50000),(126194219/1000000000),(38152244869143192641/200000000000000000),(2579953787/1000000000),(23/10),(1374117123/1000000000),0,(1134129543164248523/1000000000000000000),(13818837706470863/500000000000000000)⟩
theorem valid251 : certificate251.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid251,?_⟩
  decide +kernel
theorem sound251 : certificate251.Sound :=
  rat_witness_certificate_sound certificate251 valid251 MajorityCertificates.Inputs012.envelope_sound251

def certificate252 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope252,(38983/20000),(125871953/1000000000),(189518456652147863977/1000000000000000000),(14068063/6250000),(23/10),(169017029/500000000),0,1,(29910303191367569/1000000000000000000)⟩
theorem valid252 : certificate252.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid252,?_⟩
  decide +kernel
theorem sound252 : certificate252.Sound :=
  rat_witness_certificate_sound certificate252 valid252 MajorityCertificates.Inputs012.envelope_sound252

def certificate253 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope253,(38983/20000),(125871953/1000000000),(189518456652147863977/1000000000000000000),(2580033877/1000000000),(23/10),(344017343/250000000),0,(1134194487393026913/1000000000000000000),(6985786770575683/250000000000000000)⟩
theorem valid253 : certificate253.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid253,?_⟩
  decide +kernel
theorem sound253 : certificate253.Sound :=
  rat_witness_certificate_sound certificate253 valid253 MajorityCertificates.Inputs012.envelope_sound253

def certificate254 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope254,(12183/6250),(15693711/125000000),(189343907653076126043/1000000000000000000),(2248827737/1000000000),(23/10),(10541341/31250000),0,1,(15076940125023649/500000000000000000)⟩
theorem valid254 : certificate254.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid254,?_⟩
  decide +kernel
theorem sound254 : certificate254.Sound :=
  rat_witness_certificate_sound certificate254 valid254 MajorityCertificates.Inputs012.envelope_sound254

def certificate255 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope255,(12183/6250),(15693711/125000000),(189343907653076126043/1000000000000000000),(161397431/62500000),(23/10),(1375427929/1000000000),0,(567101199827815647/500000000000000000),(13982977839065777/500000000000000000)⟩
theorem valid255 : certificate255.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid255,?_⟩
  decide +kernel
theorem sound255 : certificate255.Sound :=
  rat_witness_certificate_sound certificate255 valid255 MajorityCertificates.Inputs012.envelope_sound255

def certificate256 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope256,(1949/1000),(31326997/250000000),(11804854752523603839/62500000000000000),(1124021901/500000000),(23/10),(84042137/250000000),0,1,(6983974771081411/250000000000000000)⟩
theorem valid256 : certificate256.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid256,?_⟩
  decide +kernel
theorem sound256 : certificate256.Sound :=
  rat_witness_certificate_sound certificate256 valid256 MajorityCertificates.Inputs012.envelope_sound256

def certificate257 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope257,(1949/1000),(31326997/250000000),(11804854752523603839/62500000000000000),(2583479671/1000000000),(23/10),(17196543/12500000),0,(1134226593655226871/1000000000000000000),(1122334344014411/40000000000000000)⟩
theorem valid257 : certificate257.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid257,?_⟩
  decide +kernel
theorem sound257 : certificate257.Sound :=
  rat_witness_certificate_sound certificate257 valid257 MajorityCertificates.Inputs012.envelope_sound257

def certificate258 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs012.envelope258,(24359/12500),(125066289/1000000000),(367997090825037559/1953125000000000),(1128332253/500000000),(23/10),(83862377/250000000),0,1,(30153810920320901/1000000000000000000)⟩
theorem valid258 : certificate258.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid258,?_⟩
  decide +kernel
theorem sound258 : certificate258.Sound :=
  rat_witness_certificate_sound certificate258 valid258 MajorityCertificates.Inputs012.envelope_sound258

def certificate259 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs012.envelope259,(24359/12500),(125066289/1000000000),(367997090825037559/1953125000000000),(1288177893/500000000),(23/10),(1380160457/1000000000),0,(283562689271000013/250000000000000000),(14256887691932923/500000000000000000)⟩
theorem valid259 : certificate259.Valid := by
  refine ⟨MajorityCertificates.Inputs012.inputs_valid259,?_⟩
  decide +kernel
theorem sound259 : certificate259.Sound :=
  rat_witness_certificate_sound certificate259 valid259 MajorityCertificates.Inputs012.envelope_sound259

def certificates : List RatWitnessCertificate := [certificate240,certificate241,certificate242,certificate243,certificate244,certificate245,certificate246,certificate247,certificate248,certificate249,certificate250,certificate251,certificate252,certificate253,certificate254,certificate255,certificate256,certificate257,certificate258,certificate259]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound240,List.forall_mem_cons.mpr ⟨sound241,List.forall_mem_cons.mpr ⟨sound242,List.forall_mem_cons.mpr ⟨sound243,List.forall_mem_cons.mpr ⟨sound244,List.forall_mem_cons.mpr ⟨sound245,List.forall_mem_cons.mpr ⟨sound246,List.forall_mem_cons.mpr ⟨sound247,List.forall_mem_cons.mpr ⟨sound248,List.forall_mem_cons.mpr ⟨sound249,List.forall_mem_cons.mpr ⟨sound250,List.forall_mem_cons.mpr ⟨sound251,List.forall_mem_cons.mpr ⟨sound252,List.forall_mem_cons.mpr ⟨sound253,List.forall_mem_cons.mpr ⟨sound254,List.forall_mem_cons.mpr ⟨sound255,List.forall_mem_cons.mpr ⟨sound256,List.forall_mem_cons.mpr ⟨sound257,List.forall_mem_cons.mpr ⟨sound258,List.forall_mem_cons.mpr ⟨sound259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch012
