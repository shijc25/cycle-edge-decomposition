import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs008

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch008

def certificate160 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope160,(197659/100000),(72160547/500000000),(249789381237389577433/1000000000000000000),(1057074763/500000000),2,(198524351/500000000),0,1,(10714934582421327/500000000000000000)⟩
theorem valid160 : certificate160.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid160,?_⟩
  decide +kernel
theorem sound160 : certificate160.Sound :=
  rat_witness_certificate_sound certificate160 valid160 MajorityCertificates.Inputs008.envelope_sound160

def certificate161 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope161,(197659/100000),(72160547/500000000),(249789381237389577433/1000000000000000000),(2491410951/1000000000),2,(1338916881/1000000000),0,(1131868149183600713/1000000000000000000),(973036207989147/50000000000000000)⟩
theorem valid161 : certificate161.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid161,?_⟩
  decide +kernel
theorem sound161 : certificate161.Sound :=
  rat_witness_certificate_sound certificate161 valid161 MajorityCertificates.Inputs008.envelope_sound161

def certificate162 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope162,(4939/2500),(72160547/500000000),(2480156854086673507/10000000000000000),(529088979/250000000),2,(39700623/100000000),0,1,(10788061528761201/500000000000000000)⟩
theorem valid162 : certificate162.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid162,?_⟩
  decide +kernel
theorem sound162 : certificate162.Sound :=
  rat_witness_certificate_sound certificate162 valid162 MajorityCertificates.Inputs008.envelope_sound162

def certificate163 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope163,(4939/2500),(72160547/500000000),(2480156854086673507/10000000000000000),(1246266049/500000000),2,(1339658277/1000000000),0,(141490123103199687/125000000000000000),(9818351610857493/500000000000000000)⟩
theorem valid163 : certificate163.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid163,?_⟩
  decide +kernel
theorem sound163 : certificate163.Sound :=
  rat_witness_certificate_sound certificate163 valid163 MajorityCertificates.Inputs008.envelope_sound163

def certificate164 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope164,(98731/50000),(72160547/500000000),(246268246515930295277/1000000000000000000),(2082718883/1000000000),(41/20),(400961607/1000000000),0,1,(11604381727118023/500000000000000000)⟩
theorem valid164 : certificate164.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid164,?_⟩
  decide +kernel
theorem sound164 : certificate164.Sound :=
  rat_witness_certificate_sound certificate164 valid164 MajorityCertificates.Inputs008.envelope_sound164

def certificate165 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope165,(98731/50000),(72160547/500000000),(246268246515930295277/1000000000000000000),(2495083461/1000000000),(41/20),(1341173099/1000000000),0,(565986903183694869/500000000000000000),(19806692518299793/1000000000000000000)⟩
theorem valid165 : certificate165.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid165,?_⟩
  decide +kernel
theorem sound165 : certificate165.Sound :=
  rat_witness_certificate_sound certificate165 valid165 MajorityCertificates.Inputs008.envelope_sound165

def certificate166 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope166,(198141/100000),(140937871/1000000000),(244546577768143902817/1000000000000000000),(10634453/5000000),(41/20),(385595079/1000000000),0,1,(21943312110361101/1000000000000000000)⟩
theorem valid166 : certificate166.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid166,?_⟩
  decide +kernel
theorem sound166 : certificate166.Sound :=
  rat_witness_certificate_sound certificate166 valid166 MajorityCertificates.Inputs008.envelope_sound166

def certificate167 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope167,(198141/100000),(140937871/1000000000),(244546577768143902817/1000000000000000000),(2494910353/1000000000),(41/20),(167640323/125000000),0,(565999479133626621/500000000000000000),(10009383080984223/500000000000000000)⟩
theorem valid167 : certificate167.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid167,?_⟩
  decide +kernel
theorem sound167 : certificate167.Sound :=
  rat_witness_certificate_sound certificate167 valid167 MajorityCertificates.Inputs008.envelope_sound167

def certificate168 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope168,(6189/3125),(35174043/250000000),(48570040808067511363/200000000000000000),(533974421/250000000),(41/20),(192079897/500000000),0,1,(21862032108312281/1000000000000000000)⟩
theorem valid168 : certificate168.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid168,?_⟩
  decide +kernel
theorem sound168 : certificate168.Sound :=
  rat_witness_certificate_sound certificate168 valid168 MajorityCertificates.Inputs008.envelope_sound168

def certificate169 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope169,(6189/3125),(35174043/250000000),(48570040808067511363/200000000000000000),(2496100407/1000000000),(41/20),(1342038547/1000000000),0,(113205141168827227/100000000000000000),(101076542275439/5000000000000000)⟩
theorem valid169 : certificate169.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid169,?_⟩
  decide +kernel
theorem sound169 : certificate169.Sound :=
  rat_witness_certificate_sound certificate169 valid169 MajorityCertificates.Inputs008.envelope_sound169

def certificate170 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope170,(49489/25000),(70186953/500000000),(241178661540697140603/1000000000000000000),(2133630927/1000000000),(41/20),(383651317/1000000000),0,1,(22248624116552599/1000000000000000000)⟩
theorem valid170 : certificate170.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid170,?_⟩
  decide +kernel
theorem sound170 : certificate170.Sound :=
  rat_witness_certificate_sound certificate170 valid170 MajorityCertificates.Inputs008.envelope_sound170

def certificate171 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope171,(49489/25000),(70186953/500000000),(241178661540697140603/1000000000000000000),(1249225819/500000000),(41/20),(83902779/62500000),0,(70756489934282291/62500000000000000),(20369535996052981/1000000000000000000)⟩
theorem valid171 : certificate171.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid171,?_⟩
  decide +kernel
theorem sound171 : certificate171.Sound :=
  rat_witness_certificate_sound certificate171 valid171 MajorityCertificates.Inputs008.envelope_sound171

def certificate172 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope172,(39573/20000),(140132207/1000000000),(14970718593046750777/62500000000000000),(214140539/100000000),(41/20),(95587111/250000000),0,1,(22217202743553787/1000000000000000000)⟩
theorem valid172 : certificate172.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid172,?_⟩
  decide +kernel
theorem sound172 : certificate172.Sound :=
  rat_witness_certificate_sound certificate172 valid172 MajorityCertificates.Inputs008.envelope_sound172

def certificate173 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope173,(39573/20000),(140132207/1000000000),(14970718593046750777/62500000000000000),(2499614493/1000000000),(41/20),(134336839/100000000),0,(566078118302881959/500000000000000000),(20567961194126517/1000000000000000000)⟩
theorem valid173 : certificate173.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid173,?_⟩
  decide +kernel
theorem sound173 : certificate173.Sound :=
  rat_witness_certificate_sound certificate173 valid173 MajorityCertificates.Inputs008.envelope_sound173

def certificate174 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope174,(7911/4000),(139809941/1000000000),(475816539608415039/2000000000000000),(267611571/125000000),(41/20),(47707341/125000000),0,1,(2817171309854231/125000000000000000)⟩
theorem valid174 : certificate174.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid174,?_⟩
  decide +kernel
theorem sound174 : certificate174.Sound :=
  rat_witness_certificate_sound certificate174 valid174 MajorityCertificates.Inputs008.envelope_sound174

def certificate175 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope175,(7911/4000),(139809941/1000000000),(475816539608415039/2000000000000000),(1250978381/500000000),(41/20),(1343772819/1000000000),0,(566104300607753799/500000000000000000),(2590354959540331/125000000000000000)⟩
theorem valid175 : certificate175.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid175,?_⟩
  decide +kernel
theorem sound175 : certificate175.Sound :=
  rat_witness_certificate_sound certificate175 valid175 MajorityCertificates.Inputs008.envelope_sound175

def certificate176 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope176,(98843/50000),(69784121/500000000),(59077136701526038033/250000000000000000),(2146877949/1000000000),(41/20),(190269991/500000000),0,1,(564287668909131/25000000000000000)⟩
theorem valid176 : certificate176.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid176,?_⟩
  decide +kernel
theorem sound176 : certificate176.Sound :=
  rat_witness_certificate_sound certificate176 valid176 MajorityCertificates.Inputs008.envelope_sound176

def certificate177 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope177,(98843/50000),(69784121/500000000),(59077136701526038033/250000000000000000),(1251547407/500000000),(41/20),(672351879/500000000),0,(283065232332801169/250000000000000000),(2092331710884129/100000000000000000)⟩
theorem valid177 : certificate177.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid177,?_⟩
  decide +kernel
theorem sound177 : certificate177.Sound :=
  rat_witness_certificate_sound certificate177 valid177 MajorityCertificates.Inputs008.envelope_sound177

def certificate178 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs008.envelope178,(197597/100000),(139245977/1000000000),(234731906921777485191/1000000000000000000),(536925863/250000000),(41/20),(94929087/250000000),0,1,(11422313947957031/500000000000000000)⟩
theorem valid178 : certificate178.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid178,?_⟩
  decide +kernel
theorem sound178 : certificate178.Sound :=
  rat_witness_certificate_sound certificate178 valid178 MajorityCertificates.Inputs008.envelope_sound178

def certificate179 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs008.envelope179,(197597/100000),(139245977/1000000000),(234731906921777485191/1000000000000000000),(2505439671/1000000000),(41/20),(336276613/250000000),0,(1132313254702272349/1000000000000000000),(10539312312111913/500000000000000000)⟩
theorem valid179 : certificate179.Valid := by
  refine ⟨MajorityCertificates.Inputs008.inputs_valid179,?_⟩
  decide +kernel
theorem sound179 : certificate179.Sound :=
  rat_witness_certificate_sound certificate179 valid179 MajorityCertificates.Inputs008.envelope_sound179

def certificates : List RatWitnessCertificate := [certificate160,certificate161,certificate162,certificate163,certificate164,certificate165,certificate166,certificate167,certificate168,certificate169,certificate170,certificate171,certificate172,certificate173,certificate174,certificate175,certificate176,certificate177,certificate178,certificate179]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound160,List.forall_mem_cons.mpr ⟨sound161,List.forall_mem_cons.mpr ⟨sound162,List.forall_mem_cons.mpr ⟨sound163,List.forall_mem_cons.mpr ⟨sound164,List.forall_mem_cons.mpr ⟨sound165,List.forall_mem_cons.mpr ⟨sound166,List.forall_mem_cons.mpr ⟨sound167,List.forall_mem_cons.mpr ⟨sound168,List.forall_mem_cons.mpr ⟨sound169,List.forall_mem_cons.mpr ⟨sound170,List.forall_mem_cons.mpr ⟨sound171,List.forall_mem_cons.mpr ⟨sound172,List.forall_mem_cons.mpr ⟨sound173,List.forall_mem_cons.mpr ⟨sound174,List.forall_mem_cons.mpr ⟨sound175,List.forall_mem_cons.mpr ⟨sound176,List.forall_mem_cons.mpr ⟨sound177,List.forall_mem_cons.mpr ⟨sound178,List.forall_mem_cons.mpr ⟨sound179,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch008
