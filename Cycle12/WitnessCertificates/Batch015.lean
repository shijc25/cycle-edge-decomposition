import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch015

def certificate300 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope300,(4857/2500),(59874453/500000000),(2789993129168606837/15625000000000000),(1146008387/500000000),(12/5),(159626219/500000000),0,1,(16258435397160067/500000000000000000)⟩
theorem valid300 : certificate300.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid300,?_⟩
  decide +kernel
theorem sound300 : certificate300.Sound :=
  rat_witness_certificate_sound certificate300 valid300 MajorityCertificates.Inputs015.envelope_sound300

def certificate301 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope301,(4857/2500),(59874453/500000000),(2789993129168606837/15625000000000000),(2606383431/1000000000),(12/5),(138860229/100000000),0,(1134794718261048787/1000000000000000000),(7602349722463749/250000000000000000)⟩
theorem valid301 : certificate301.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid301,?_⟩
  decide +kernel
theorem sound301 : certificate301.Sound :=
  rat_witness_certificate_sound certificate301 valid301 MajorityCertificates.Inputs015.envelope_sound301

def certificate302 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope302,(194257/100000),(119507207/1000000000),(178163800970004532923/1000000000000000000),(229130909/100000000),(12/5),(79673849/250000000),0,1,(32719282867172671/1000000000000000000)⟩
theorem valid302 : certificate302.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid302,?_⟩
  decide +kernel
theorem sound302 : certificate302.Sound :=
  rat_witness_certificate_sound certificate302 valid302 MajorityCertificates.Inputs015.envelope_sound302

def certificate303 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope303,(194257/100000),(119507207/1000000000),(178163800970004532923/1000000000000000000),(2607629247/1000000000),(12/5),(1388824257/1000000000),0,(1134817793157473647/1000000000000000000),(30491781283398417/1000000000000000000)⟩
theorem valid303 : certificate303.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid303,?_⟩
  decide +kernel
theorem sound303 : certificate303.Sound :=
  rat_witness_certificate_sound certificate303 valid303 MajorityCertificates.Inputs015.envelope_sound303

def certificate304 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope304,(194233/100000),(29816377/250000000),(35554122786682429017/200000000000000000),(287187603/125000000),(12/5),(79402209/250000000),0,1,(509555602155087/15625000000000000)⟩
theorem valid304 : certificate304.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid304,?_⟩
  decide +kernel
theorem sound304 : certificate304.Sound :=
  rat_witness_certificate_sound certificate304 valid304 MajorityCertificates.Inputs015.envelope_sound304

def certificate305 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope305,(194233/100000),(29816377/250000000),(35554122786682429017/200000000000000000),(2608886819/1000000000),(12/5),(86815497/62500000),0,(283710219863925679/250000000000000000),(30574456867578659/1000000000000000000)⟩
theorem valid305 : certificate305.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid305,?_⟩
  decide +kernel
theorem sound305 : certificate305.Sound :=
  rat_witness_certificate_sound certificate305 valid305 MajorityCertificates.Inputs015.envelope_sound305

def certificate306 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope306,(194211/100000),(119023809/1000000000),(44344995454039285709/250000000000000000),(574788869/250000000),(12/5),(158436679/500000000),0,1,(8180047192955141/250000000000000000)⟩
theorem valid306 : certificate306.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid306,?_⟩
  decide +kernel
theorem sound306 : certificate306.Sound :=
  rat_witness_certificate_sound certificate306 valid306 MajorityCertificates.Inputs015.envelope_sound306

def certificate307 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope307,(194211/100000),(119023809/1000000000),(44344995454039285709/250000000000000000),(2609871729/1000000000),(12/5),(1389405507/1000000000),0,(1134863823824306247/1000000000000000000),(15337148727533541/500000000000000000)⟩
theorem valid307 : certificate307.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid307,?_⟩
  decide +kernel
theorem sound307 : certificate307.Sound :=
  rat_witness_certificate_sound certificate307 valid307 MajorityCertificates.Inputs015.envelope_sound307

def certificate308 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope308,(48547/25000),(118782109/1000000000),(35398377488915435619/200000000000000000),(1149152401/500000000),(12/5),(3954087/12500000),0,1,(16464430125123609/500000000000000000)⟩
theorem valid308 : certificate308.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid308,?_⟩
  decide +kernel
theorem sound308 : certificate308.Sound :=
  rat_witness_certificate_sound certificate308 valid308 MajorityCertificates.Inputs015.envelope_sound308

def certificate309 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope309,(48547/25000),(118782109/1000000000),(35398377488915435619/200000000000000000),(1305556211/500000000),(12/5),(1389632319/1000000000),0,(1134886778988656583/1000000000000000000),(15378649729959309/500000000000000000)⟩
theorem valid309 : certificate309.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid309,?_⟩
  decide +kernel
theorem sound309 : certificate309.Sound :=
  rat_witness_certificate_sound certificate309 valid309 MajorityCertificates.Inputs015.envelope_sound309

def certificate310 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope310,(38833/20000),(11854041/100000000),(176606313810354852443/1000000000000000000),(575164927/250000000),(12/5),(315537933/1000000000),0,1,(32998532471796423/1000000000000000000)⟩
theorem valid310 : certificate310.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid310,?_⟩
  decide +kernel
theorem sound310 : certificate310.Sound :=
  rat_witness_certificate_sound certificate310 valid310 MajorityCertificates.Inputs015.envelope_sound310

def certificate311 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope311,(38833/20000),(11854041/100000000),(176606313810354852443/1000000000000000000),(20898809/8000000),(12/5),(277972161/200000000),0,(1134909693637017837/1000000000000000000),(30840462011912921/1000000000000000000)⟩
theorem valid311 : certificate311.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid311,?_⟩
  decide +kernel
theorem sound311 : certificate311.Sound :=
  rat_witness_certificate_sound certificate311 valid311 MajorityCertificates.Inputs015.envelope_sound311

def certificate312 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope312,(194143/100000),(118298711/1000000000),(176223244068692845303/1000000000000000000),(575854677/250000000),(12/5),(12588691/40000000),0,1,(4130574257981889/125000000000000000)⟩
theorem valid312 : certificate312.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid312,?_⟩
  decide +kernel
theorem sound312 : certificate312.Sound :=
  rat_witness_certificate_sound certificate312 valid312 MajorityCertificates.Inputs015.envelope_sound312

def certificate313 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope313,(194143/100000),(118298711/1000000000),(176223244068692845303/1000000000000000000),(261357973/100000000),(12/5),(17376117/12500000),0,(226986503191098239/200000000000000000),(15462094877256493/500000000000000000)⟩
theorem valid313 : certificate313.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid313,?_⟩
  decide +kernel
theorem sound313 : certificate313.Sound :=
  rat_witness_certificate_sound certificate313 valid313 MajorityCertificates.Inputs015.envelope_sound313

def certificate314 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope314,(194121/100000),(23595289/200000000),(175842661536513036111/1000000000000000000),(2306412049/1000000000),(12/5),(313660401/1000000000),0,1,(33098500359480089/1000000000000000000)⟩
theorem valid314 : certificate314.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid314,?_⟩
  decide +kernel
theorem sound314 : certificate314.Sound :=
  rat_witness_certificate_sound certificate314 valid314 MajorityCertificates.Inputs015.envelope_sound314

def certificate315 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope315,(194121/100000),(23595289/200000000),(175842661536513036111/1000000000000000000),(2614987437/1000000000),(12/5),(1390324989/1000000000),0,(567477648452267687/500000000000000000),(31008609774699839/1000000000000000000)⟩
theorem valid315 : certificate315.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid315,?_⟩
  decide +kernel
theorem sound315 : certificate315.Sound :=
  rat_witness_certificate_sound certificate315 valid315 MajorityCertificates.Inputs015.envelope_sound315

def certificate316 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope316,(194099/100000),(58867373/500000000),(21933068711334907873/125000000000000000),(577175723/250000000),(12/5),(312922731/1000000000),0,1,(33360848907741823/1000000000000000000)⟩
theorem valid316 : certificate316.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid316,?_⟩
  decide +kernel
theorem sound316 : certificate316.Sound :=
  rat_witness_certificate_sound certificate316 valid316 MajorityCertificates.Inputs015.envelope_sound316

def certificate317 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope317,(194099/100000),(58867373/500000000),(21933068711334907873/125000000000000000),(2615959783/1000000000),(12/5),(1390692837/1000000000),0,(567489018091880147/500000000000000000),(7777450020417219/250000000000000000)⟩
theorem valid317 : certificate317.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid317,?_⟩
  decide +kernel
theorem sound317 : certificate317.Sound :=
  rat_witness_certificate_sound certificate317 valid317 MajorityCertificates.Inputs015.envelope_sound317

def certificate318 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs015.envelope318,(194077/100000),(117493047/1000000000),(175088892166243367219/1000000000000000000),(2307494731/1000000000),(12/5),(62472349/200000000),0,1,(33412079198293589/1000000000000000000)⟩
theorem valid318 : certificate318.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid318,?_⟩
  decide +kernel
theorem sound318 : certificate318.Sound :=
  rat_witness_certificate_sound certificate318 valid318 MajorityCertificates.Inputs015.envelope_sound318

def certificate319 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs015.envelope319,(194077/100000),(117493047/1000000000),(175088892166243367219/1000000000000000000),(2617181409/1000000000),(12/5),(347731801/250000000),0,(1135000733493259041/1000000000000000000),(3899267918358347/125000000000000000)⟩
theorem valid319 : certificate319.Valid := by
  refine ⟨MajorityCertificates.Inputs015.inputs_valid319,?_⟩
  decide +kernel
theorem sound319 : certificate319.Sound :=
  rat_witness_certificate_sound certificate319 valid319 MajorityCertificates.Inputs015.envelope_sound319

def certificates : List RatWitnessCertificate := [certificate300,certificate301,certificate302,certificate303,certificate304,certificate305,certificate306,certificate307,certificate308,certificate309,certificate310,certificate311,certificate312,certificate313,certificate314,certificate315,certificate316,certificate317,certificate318,certificate319]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound300,List.forall_mem_cons.mpr ⟨sound301,List.forall_mem_cons.mpr ⟨sound302,List.forall_mem_cons.mpr ⟨sound303,List.forall_mem_cons.mpr ⟨sound304,List.forall_mem_cons.mpr ⟨sound305,List.forall_mem_cons.mpr ⟨sound306,List.forall_mem_cons.mpr ⟨sound307,List.forall_mem_cons.mpr ⟨sound308,List.forall_mem_cons.mpr ⟨sound309,List.forall_mem_cons.mpr ⟨sound310,List.forall_mem_cons.mpr ⟨sound311,List.forall_mem_cons.mpr ⟨sound312,List.forall_mem_cons.mpr ⟨sound313,List.forall_mem_cons.mpr ⟨sound314,List.forall_mem_cons.mpr ⟨sound315,List.forall_mem_cons.mpr ⟨sound316,List.forall_mem_cons.mpr ⟨sound317,List.forall_mem_cons.mpr ⟨sound318,List.forall_mem_cons.mpr ⟨sound319,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch015
