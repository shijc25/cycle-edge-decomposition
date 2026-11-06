import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch009

def certificate180 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope180,(19751/10000),(139004277/1000000000),(116588969202694662563/500000000000000000),(2150535159/1000000000),(41/20),(189457361/500000000),0,1,(23004735207723603/1000000000000000000)⟩
theorem valid180 : certificate180.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid180,?_⟩
  decide +kernel
theorem sound180 : certificate180.Sound :=
  rat_witness_certificate_sound certificate180 valid180 MajorityCertificates.Inputs009.envelope_sound180

def certificate181 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope181,(19751/10000),(139004277/1000000000),(116588969202694662563/500000000000000000),(2506551217/1000000000),(41/20),(269209033/200000000),0,(1132365499766933913/1000000000000000000),(1064063261370663/50000000000000000)⟩
theorem valid181 : certificate181.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid181,?_⟩
  decide +kernel
theorem sound181 : certificate181.Sound :=
  rat_witness_certificate_sound certificate181 valid181 MajorityCertificates.Inputs009.envelope_sound181

def certificate182 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope182,(197423/100000),(34670503/250000000),(57911559766397994477/250000000000000000),(1077269659/500000000),(41/20),(188887033/500000000),0,1,(23150053882451661/1000000000000000000)⟩
theorem valid182 : certificate182.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid182,?_⟩
  decide +kernel
theorem sound182 : certificate182.Sound :=
  rat_witness_certificate_sound certificate182 valid182 MajorityCertificates.Inputs009.envelope_sound182

def certificate183 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope183,(197423/100000),(34670503/250000000),(57911559766397994477/250000000000000000),(156805657/62500000),(41/20),(673222079/500000000),0,(566208867876590269/500000000000000000),(21436952112152783/1000000000000000000)⟩
theorem valid183 : certificate183.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid183,?_⟩
  decide +kernel
theorem sound183 : certificate183.Sound :=
  rat_witness_certificate_sound certificate183 valid183 MajorityCertificates.Inputs009.envelope_sound183

def certificate184 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope184,(197337/100000),(69179873/500000000),(28767052000251793197/125000000000000000),(1078804443/500000000),(21/10),(47090051/125000000),0,1,(23310645902042811/1000000000000000000)⟩
theorem valid184 : certificate184.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid184,?_⟩
  decide +kernel
theorem sound184 : certificate184.Sound :=
  rat_witness_certificate_sound certificate184 valid184 MajorityCertificates.Inputs009.envelope_sound184

def certificate185 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope185,(197337/100000),(69179873/500000000),(28767052000251793197/125000000000000000),(2511187537/1000000000),(21/10),(674229283/500000000),0,(1132469922010548481/1000000000000000000),(10820349285422457/500000000000000000)⟩
theorem valid185 : certificate185.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid185,?_⟩
  decide +kernel
theorem sound185 : certificate185.Sound :=
  rat_witness_certificate_sound certificate185 valid185 MajorityCertificates.Inputs009.envelope_sound185

def certificate186 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope186,(49313/25000),(138118047/1000000000),(9145923414009625841/40000000000000000),(86453643/40000000),(21/10),(187916133/500000000),0,1,(23433049767490481/1000000000000000000)⟩
theorem valid186 : certificate186.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid186,?_⟩
  decide +kernel
theorem sound186 : certificate186.Sound :=
  rat_witness_certificate_sound certificate186 valid186 MajorityCertificates.Inputs009.envelope_sound186

def certificate187 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope187,(49313/25000),(138118047/1000000000),(9145923414009625841/40000000000000000),(628328353/250000000),(21/10),(33722341/25000000),0,(56626102754273201/50000000000000000),(21798988617038939/1000000000000000000)⟩
theorem valid187 : certificate187.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid187,?_⟩
  decide +kernel
theorem sound187 : certificate187.Sound :=
  rat_witness_certificate_sound certificate187 valid187 MajorityCertificates.Inputs009.envelope_sound187

def certificate188 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope188,(12323/6250),(137795781/1000000000),(227180872034970018037/1000000000000000000),(108223839/50000000),(21/10),(374779861/1000000000),0,1,(23613903562597717/1000000000000000000)⟩
theorem valid188 : certificate188.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid188,?_⟩
  decide +kernel
theorem sound188 : certificate188.Sound :=
  rat_witness_certificate_sound certificate188 valid188 MajorityCertificates.Inputs009.envelope_sound188

def certificate189 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope189,(12323/6250),(137795781/1000000000),(227180872034970018037/1000000000000000000),(2514890327/1000000000),(21/10),(337420621/250000000),0,(226514826304751171/200000000000000000),(10995409974422989/500000000000000000)⟩
theorem valid189 : certificate189.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid189,?_⟩
  decide +kernel
theorem sound189 : certificate189.Sound :=
  rat_witness_certificate_sound certificate189 valid189 MajorityCertificates.Inputs009.envelope_sound189

def certificate190 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope190,(39417/20000),(34368379/250000000),(225734409531058096999/1000000000000000000),(2167033907/1000000000),(21/10),(186888469/500000000),0,1,(2974189607747253/125000000000000000)⟩
theorem valid190 : certificate190.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid190,?_⟩
  decide +kernel
theorem sound190 : certificate190.Sound :=
  rat_witness_certificate_sound certificate190 valid190 MajorityCertificates.Inputs009.envelope_sound190

def certificate191 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope191,(39417/20000),(34368379/250000000),(225734409531058096999/1000000000000000000),(2517228433/1000000000),(21/10),(1350080583/1000000000),0,(1132626147870916777/1000000000000000000),(4429268067607709/200000000000000000)⟩
theorem valid191 : certificate191.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid191,?_⟩
  decide +kernel
theorem sound191 : certificate191.Sound :=
  rat_witness_certificate_sound certificate191 valid191 MajorityCertificates.Inputs009.envelope_sound191

def certificate192 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope192,(98501/50000),(109721/800000),(224308339632153902779/1000000000000000000),(2170381909/1000000000),(21/10),(37270457/100000000),0,1,(23961143530321269/1000000000000000000)⟩
theorem valid192 : certificate192.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid192,?_⟩
  decide +kernel
theorem sound192 : certificate192.Sound :=
  rat_witness_certificate_sound certificate192 valid192 MajorityCertificates.Inputs009.envelope_sound192

def certificate193 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope193,(98501/50000),(109721/800000),(224308339632153902779/1000000000000000000),(1259220537/500000000),(21/10),(67552619/50000000),0,(1132678139853814477/1000000000000000000),(5588753035487239/250000000000000000)⟩
theorem valid193 : certificate193.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid193,?_⟩
  decide +kernel
theorem sound193 : certificate193.Sound :=
  rat_witness_certificate_sound certificate193 valid193 MajorityCertificates.Inputs009.envelope_sound193

def certificate194 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope194,(196921/100000),(17103623/125000000),(222902312226657076333/1000000000000000000),(1079433501/500000000),(21/10),(23315543/62500000),0,1,(24642979932975421/1000000000000000000)⟩
theorem valid194 : certificate194.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid194,?_⟩
  decide +kernel
theorem sound194 : certificate194.Sound :=
  rat_witness_certificate_sound certificate194 valid194 MajorityCertificates.Inputs009.envelope_sound194

def certificate195 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope195,(196921/100000),(17103623/125000000),(222902312226657076333/1000000000000000000),(50416253/20000000),(21/10),(168928497/125000000),0,(141591253242196709/125000000000000000),(4501975931612269/200000000000000000)⟩
theorem valid195 : certificate195.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid195,?_⟩
  decide +kernel
theorem sound195 : certificate195.Sound :=
  rat_witness_certificate_sound certificate195 valid195 MajorityCertificates.Inputs009.envelope_sound195

def certificate196 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope196,(4921/2500),(136506719/1000000000),(221515985080731664567/1000000000000000000),(1087753857/500000000),(21/10),(92676297/250000000),0,1,(24340975160738451/1000000000000000000)⟩
theorem valid196 : certificate196.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid196,?_⟩
  decide +kernel
theorem sound196 : certificate196.Sound :=
  rat_witness_certificate_sound certificate196 valid196 MajorityCertificates.Inputs009.envelope_sound196

def certificate197 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope197,(4921/2500),(136506719/1000000000),(221515985080731664567/1000000000000000000),(504399259/200000000),(21/10),(1352408843/1000000000),0,(283195470328337459/250000000000000000),(355012944309087/15625000000000000)⟩
theorem valid197 : certificate197.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid197,?_⟩
  decide +kernel
theorem sound197 : certificate197.Sound :=
  rat_witness_certificate_sound certificate197 valid197 MajorityCertificates.Inputs009.envelope_sound197

def certificate198 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs009.envelope198,(19577/10000),(34791211/250000000),(21816897607164609127/100000000000000000),(67537521/31250000),(21/10),(76221509/200000000),0,1,(25323929085689743/1000000000000000000)⟩
theorem valid198 : certificate198.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid198,?_⟩
  decide +kernel
theorem sound198 : certificate198.Sound :=
  rat_witness_certificate_sound certificate198 valid198 MajorityCertificates.Inputs009.envelope_sound198

def certificate199 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs009.envelope199,(19577/10000),(34791211/250000000),(21816897607164609127/100000000000000000),(2526669043/1000000000),(21/10),(677850323/500000000),0,(1132945343320161617/1000000000000000000),(23102787131753207/1000000000000000000)⟩
theorem valid199 : certificate199.Valid := by
  refine ⟨MajorityCertificates.Inputs009.inputs_valid199,?_⟩
  decide +kernel
theorem sound199 : certificate199.Sound :=
  rat_witness_certificate_sound certificate199 valid199 MajorityCertificates.Inputs009.envelope_sound199

def certificates : List RatWitnessCertificate := [certificate180,certificate181,certificate182,certificate183,certificate184,certificate185,certificate186,certificate187,certificate188,certificate189,certificate190,certificate191,certificate192,certificate193,certificate194,certificate195,certificate196,certificate197,certificate198,certificate199]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound180,List.forall_mem_cons.mpr ⟨sound181,List.forall_mem_cons.mpr ⟨sound182,List.forall_mem_cons.mpr ⟨sound183,List.forall_mem_cons.mpr ⟨sound184,List.forall_mem_cons.mpr ⟨sound185,List.forall_mem_cons.mpr ⟨sound186,List.forall_mem_cons.mpr ⟨sound187,List.forall_mem_cons.mpr ⟨sound188,List.forall_mem_cons.mpr ⟨sound189,List.forall_mem_cons.mpr ⟨sound190,List.forall_mem_cons.mpr ⟨sound191,List.forall_mem_cons.mpr ⟨sound192,List.forall_mem_cons.mpr ⟨sound193,List.forall_mem_cons.mpr ⟨sound194,List.forall_mem_cons.mpr ⟨sound195,List.forall_mem_cons.mpr ⟨sound196,List.forall_mem_cons.mpr ⟨sound197,List.forall_mem_cons.mpr ⟨sound198,List.forall_mem_cons.mpr ⟨sound199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch009
