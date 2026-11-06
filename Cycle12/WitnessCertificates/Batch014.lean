import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs014

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch014

def certificate280 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope280,(48631/25000),(61082949/500000000),(36532513181200568633/200000000000000000),(1137245713/500000000),(47/20),(326734151/1000000000),0,1,(31558628588687789/1000000000000000000)⟩
theorem valid280 : certificate280.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid280,?_⟩
  decide +kernel
theorem sound280 : certificate280.Sound :=
  rat_witness_certificate_sound certificate280 valid280 MajorityCertificates.Inputs014.envelope_sound280

def certificate281 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope281,(48631/25000),(61082949/500000000),(36532513181200568633/200000000000000000),(518480609/200000000),(47/20),(86557979/62500000),0,(1134561165194105897/1000000000000000000),(14791902329808399/500000000000000000)⟩
theorem valid281 : certificate281.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid281,?_⟩
  decide +kernel
theorem sound281 : certificate281.Sound :=
  rat_witness_certificate_sound certificate281 valid281 MajorityCertificates.Inputs014.envelope_sound281

def certificate282 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope282,(194499/100000),(121924199/1000000000),(182240092104582146113/1000000000000000000),(18219179/8000000),(47/20),(2036823/6250000),0,1,(3950294426469121/125000000000000000)⟩
theorem valid282 : certificate282.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid282,?_⟩
  decide +kernel
theorem sound282 : certificate282.Sound :=
  rat_witness_certificate_sound certificate282 valid282 MajorityCertificates.Inputs014.envelope_sound282

def certificate283 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope283,(194499/100000),(121924199/1000000000),(182240092104582146113/1000000000000000000),(518645299/200000000),(47/20),(138535037/100000000),0,(1134584716807913977/1000000000000000000),(7419432137928933/250000000000000000)⟩
theorem valid283 : certificate283.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid283,?_⟩
  decide +kernel
theorem sound283 : certificate283.Sound :=
  rat_witness_certificate_sound certificate283 valid283 MajorityCertificates.Inputs014.envelope_sound283

def certificate284 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope284,(97237/50000),(48673/400000),(45455093398152637613/250000000000000000),(453917007/200000000),(47/20),(162752709/500000000),0,1,(30472014659581883/1000000000000000000)⟩
theorem valid284 : certificate284.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid284,?_⟩
  decide +kernel
theorem sound284 : certificate284.Sound :=
  rat_witness_certificate_sound certificate284 valid284 MajorityCertificates.Inputs014.envelope_sound284

def certificate285 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope285,(97237/50000),(48673/400000),(45455093398152637613/250000000000000000),(2594339551/1000000000),(47/20),(692861889/500000000),0,(1134608232386307039/1000000000000000000),(7454604975185519/250000000000000000)⟩
theorem valid285 : certificate285.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid285,?_⟩
  decide +kernel
theorem sound285 : certificate285.Sound :=
  rat_witness_certificate_sound certificate285 valid285 MajorityCertificates.Inputs014.envelope_sound285

def certificate286 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope286,(194449/100000),(121440801/1000000000),(181403391249949363959/1000000000000000000),(2281574019/1000000000),(47/20),(162136907/500000000),0,1,(31488690224834909/1000000000000000000)⟩
theorem valid286 : certificate286.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid286,?_⟩
  decide +kernel
theorem sound286 : certificate286.Sound :=
  rat_witness_certificate_sound certificate286 valid286 MajorityCertificates.Inputs014.envelope_sound286

def certificate287 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope287,(194449/100000),(121440801/1000000000),(181403391249949363959/1000000000000000000),(259655207/100000000),(47/20),(173176827/125000000),0,(1134631711620844293/1000000000000000000),(29830160507474979/1000000000000000000)⟩
theorem valid287 : certificate287.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid287,?_⟩
  decide +kernel
theorem sound287 : certificate287.Sound :=
  rat_witness_certificate_sound certificate287 valid287 MajorityCertificates.Inputs014.envelope_sound287

def certificate288 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope288,(24303/12500),(60599551/500000000),(180989126143570984943/1000000000000000000),(2288517571/1000000000),(47/20),(80798199/250000000),0,1,(15827718684110439/500000000000000000)⟩
theorem valid288 : certificate288.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid288,?_⟩
  decide +kernel
theorem sound288 : certificate288.Sound :=
  rat_witness_certificate_sound certificate288 valid288 MajorityCertificates.Inputs014.envelope_sound288

def certificate289 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope289,(24303/12500),(60599551/500000000),(180989126143570984943/1000000000000000000),(2597797831/1000000000),(47/20),(1385639989/1000000000),0,(1134655154203478889/1000000000000000000),(14956913735381829/500000000000000000)⟩
theorem valid289 : certificate289.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid289,?_⟩
  decide +kernel
theorem sound289 : certificate289.Sound :=
  rat_witness_certificate_sound certificate289 valid289 MajorityCertificates.Inputs014.envelope_sound289

def certificate290 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope290,(243/125),(60478701/500000000),(4514438988136114743/25000000000000000),(228631109/100000000),(47/20),(80686611/250000000),0,1,(15948265934529739/500000000000000000)⟩
theorem valid290 : certificate290.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid290,?_⟩
  decide +kernel
theorem sound290 : certificate290.Sound :=
  rat_witness_certificate_sound certificate290 valid290 MajorityCertificates.Inputs014.envelope_sound290

def certificate291 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope291,(243/125),(60478701/500000000),(4514438988136114743/25000000000000000),(2599030447/1000000000),(47/20),(1385865763/1000000000),0,(567339254853477607/500000000000000000),(14998698482049631/500000000000000000)⟩
theorem valid291 : certificate291.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid291,?_⟩
  decide +kernel
theorem sound291 : certificate291.Sound :=
  rat_witness_certificate_sound certificate291 valid291 MajorityCertificates.Inputs014.envelope_sound291

def certificate292 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope292,(311/160),(120715703/1000000000),(36033734566090038479/200000000000000000),(457221763/200000000),(47/20),(161076183/500000000),0,1,(3207954511861031/100000000000000000)⟩
theorem valid292 : certificate292.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid292,?_⟩
  decide +kernel
theorem sound292 : certificate292.Sound :=
  rat_witness_certificate_sound certificate292 valid292 MajorityCertificates.Inputs014.envelope_sound292

def certificate293 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope293,(311/160),(120715703/1000000000),(36033734566090038479/200000000000000000),(2600265811/1000000000),(47/20),(173262039/125000000),0,(567350938967482367/500000000000000000),(3760095432385871/125000000000000000)⟩
theorem valid293 : certificate293.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid293,?_⟩
  decide +kernel
theorem sound293 : certificate293.Sound :=
  rat_witness_certificate_sound certificate293 valid293 MajorityCertificates.Inputs014.envelope_sound293

def certificate294 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope294,(194351/100000),(30118501/250000000),(22470305959290079927/125000000000000000),(459161239/200000000),(47/20),(160396317/500000000),0,1,(5092273717861/160000000000000)⟩
theorem valid294 : certificate294.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid294,?_⟩
  decide +kernel
theorem sound294 : certificate294.Sound :=
  rat_witness_certificate_sound certificate294 valid294 MajorityCertificates.Inputs014.envelope_sound294

def certificate295 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope295,(194351/100000),(30118501/250000000),(22470305959290079927/125000000000000000),(2601188349/1000000000),(47/20),(86654011/62500000),0,(141840644776752197/125000000000000000),(60337863425613/2000000000000000)⟩
theorem valid295 : certificate295.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid295,?_⟩
  decide +kernel
theorem sound295 : certificate295.Sound :=
  rat_witness_certificate_sound certificate295 valid295 MajorityCertificates.Inputs014.envelope_sound295

def certificate296 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope296,(194327/100000),(24046461/200000000),(35871773170322222709/200000000000000000),(2292948981/1000000000),(12/5),(20025081/62500000),0,1,(32125102000871069/1000000000000000000)⟩
theorem valid296 : certificate296.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid296,?_⟩
  decide +kernel
theorem sound296 : certificate296.Sound :=
  rat_witness_certificate_sound certificate296 valid296 MajorityCertificates.Inputs014.envelope_sound296

def certificate297 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope297,(194327/100000),(24046461/200000000),(35871773170322222709/200000000000000000),(2603871457/1000000000),(12/5),(1388163837/1000000000),0,(567374200178890743/500000000000000000),(3780636171426801/125000000000000000)⟩
theorem valid297 : certificate297.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid297,?_⟩
  decide +kernel
theorem sound297 : certificate297.Sound :=
  rat_witness_certificate_sound certificate297 valid297 MajorityCertificates.Inputs014.envelope_sound297

def certificate298 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs014.envelope298,(6072/3125),(23998121/200000000),(178957909333695734639/1000000000000000000),(2289854749/1000000000),(12/5),(320018477/1000000000),0,1,(16195851671782833/500000000000000000)⟩
theorem valid298 : certificate298.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid298,?_⟩
  decide +kernel
theorem sound298 : certificate298.Sound :=
  rat_witness_certificate_sound certificate298 valid298 MajorityCertificates.Inputs014.envelope_sound298

def certificate299 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs014.envelope299,(6072/3125),(23998121/200000000),(178957909333695734639/1000000000000000000),(162820189/62500000),(12/5),(1388381879/1000000000),0,(1134771553431082761/1000000000000000000),(30327285031933253/1000000000000000000)⟩
theorem valid299 : certificate299.Valid := by
  refine ⟨MajorityCertificates.Inputs014.inputs_valid299,?_⟩
  decide +kernel
theorem sound299 : certificate299.Sound :=
  rat_witness_certificate_sound certificate299 valid299 MajorityCertificates.Inputs014.envelope_sound299

def certificates : List RatWitnessCertificate := [certificate280,certificate281,certificate282,certificate283,certificate284,certificate285,certificate286,certificate287,certificate288,certificate289,certificate290,certificate291,certificate292,certificate293,certificate294,certificate295,certificate296,certificate297,certificate298,certificate299]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound280,List.forall_mem_cons.mpr ⟨sound281,List.forall_mem_cons.mpr ⟨sound282,List.forall_mem_cons.mpr ⟨sound283,List.forall_mem_cons.mpr ⟨sound284,List.forall_mem_cons.mpr ⟨sound285,List.forall_mem_cons.mpr ⟨sound286,List.forall_mem_cons.mpr ⟨sound287,List.forall_mem_cons.mpr ⟨sound288,List.forall_mem_cons.mpr ⟨sound289,List.forall_mem_cons.mpr ⟨sound290,List.forall_mem_cons.mpr ⟨sound291,List.forall_mem_cons.mpr ⟨sound292,List.forall_mem_cons.mpr ⟨sound293,List.forall_mem_cons.mpr ⟨sound294,List.forall_mem_cons.mpr ⟨sound295,List.forall_mem_cons.mpr ⟨sound296,List.forall_mem_cons.mpr ⟨sound297,List.forall_mem_cons.mpr ⟨sound298,List.forall_mem_cons.mpr ⟨sound299,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch014
