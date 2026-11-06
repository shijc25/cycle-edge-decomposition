import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs018

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch018

def certificate360 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope360,(56591/25000),(23607/160000),(3192136288045801448521/1000000000000000000),(1876759137/1000000000),(11/5),(393077367/1000000000),0,1,(727767221363309/500000000000000000)⟩
theorem valid360 : certificate360.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid360,?_⟩
  decide +kernel
theorem sound360 : certificate360.Sound :=
  rat_witness_certificate_sound certificate360 valid360 MajorityCertificates.Inputs018.envelope_sound360

def certificate361 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope361,(56591/25000),(23607/160000),(3192136288045801448521/1000000000000000000),(215856417/100000000),(11/5),(320089493/250000000),0,(1125467224116427479/1000000000000000000),(1357800913501989/1000000000000000000)⟩
theorem valid361 : certificate361.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid361,?_⟩
  decide +kernel
theorem sound361 : certificate361.Sound :=
  rat_witness_certificate_sound certificate361 valid361 MajorityCertificates.Inputs018.envelope_sound361

def certificate362 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope362,(112821/50000),(148188281/1000000000),(179417633552813698357/62500000000000000),(37658867/20000000),(9/4),(394952087/1000000000),0,1,(405059610110771/250000000000000000)⟩
theorem valid362 : certificate362.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid362,?_⟩
  decide +kernel
theorem sound362 : certificate362.Sound :=
  rat_witness_certificate_sound certificate362 valid362 MajorityCertificates.Inputs018.envelope_sound362

def certificate363 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope363,(112821/50000),(148188281/1000000000),(179417633552813698357/62500000000000000),(217107771/100000000),(9/4),(79833963/62500000),0,(562760612475014099/500000000000000000),(1497668160271301/1000000000000000000)⟩
theorem valid363 : certificate363.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid363,?_⟩
  decide +kernel
theorem sound363 : certificate363.Sound :=
  rat_witness_certificate_sound certificate363 valid363 MajorityCertificates.Inputs018.envelope_sound363

def certificate364 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope364,(224937/100000),(148832813/1000000000),(2597771268675315586621/1000000000000000000),(1889484339/1000000000),(9/4),(6199789/15625000),0,1,(1796296622404671/1000000000000000000)⟩
theorem valid364 : certificate364.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid364,?_⟩
  decide +kernel
theorem sound364 : certificate364.Sound :=
  rat_witness_certificate_sound certificate364 valid364 MajorityCertificates.Inputs018.envelope_sound364

def certificate365 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope365,(224937/100000),(148832813/1000000000),(2597771268675315586621/1000000000000000000),(2177679991/1000000000),(9/4),(255455993/200000000),0,(562788905242523053/500000000000000000),(415689848236303/250000000000000000)⟩
theorem valid365 : certificate365.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid365,?_⟩
  decide +kernel
theorem sound365 : certificate365.Sound :=
  rat_witness_certificate_sound certificate365 valid365 MajorityCertificates.Inputs018.envelope_sound365

def certificate366 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope366,(28031/12500),(4671167/31250000),(295504222005520176937/125000000000000000),(59235217/31250000),(9/4),(24917021/62500000),0,1,(1976345993730849/1000000000000000000)⟩
theorem valid366 : certificate366.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid366,?_⟩
  decide +kernel
theorem sound366 : certificate366.Sound :=
  rat_witness_certificate_sound certificate366 valid366 MajorityCertificates.Inputs018.envelope_sound366

def certificate367 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope367,(28031/12500),(4671167/31250000),(295504222005520176937/125000000000000000),(436897357/200000000),(9/4),(1277107453/1000000000),0,(281409229201579/250000000000000),(1836244558700953/1000000000000000000)⟩
theorem valid367 : certificate367.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid367,?_⟩
  decide +kernel
theorem sound367 : certificate367.Sound :=
  rat_witness_certificate_sound certificate367 valid367 MajorityCertificates.Inputs018.envelope_sound367

def certificate368 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope368,(27947/12500),(48039/320000),(2162263568793696880991/1000000000000000000),(236670549/125000000),(9/4),(401438737/1000000000),0,1,(426462755302329/200000000000000000)⟩
theorem valid368 : certificate368.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid368,?_⟩
  decide +kernel
theorem sound368 : certificate368.Sound :=
  rat_witness_certificate_sound certificate368 valid368 MajorityCertificates.Inputs018.envelope_sound368

def certificate369 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope369,(27947/12500),(48039/320000),(2162263568793696880991/1000000000000000000),(5478113/2500000),(9/4),(1276943179/1000000000),0,(562849236500856087/500000000000000000),(201470382034871/100000000000000000)⟩
theorem valid369 : certificate369.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid369,?_⟩
  decide +kernel
theorem sound369 : certificate369.Sound :=
  rat_witness_certificate_sound certificate369 valid369 MajorityCertificates.Inputs018.envelope_sound369

def certificate370 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope370,(5573/2500),(75383203/500000000),(496711091993987075701/250000000000000000),(1907858889/1000000000),(23/10),(100602569/250000000),0,1,(590864358938283/250000000000000000)⟩
theorem valid370 : certificate370.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid370,?_⟩
  decide +kernel
theorem sound370 : certificate370.Sound :=
  rat_witness_certificate_sound certificate370 valid370 MajorityCertificates.Inputs018.envelope_sound370

def certificate371 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope371,(5573/2500),(75383203/500000000),(496711091993987075701/250000000000000000),(550827629/250000000),(23/10),(127428711/100000000),0,(1125762412028496887/1000000000000000000),(544461218706903/250000000000000000)⟩
theorem valid371 : certificate371.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid371,?_⟩
  decide +kernel
theorem sound371 : certificate371.Sound :=
  rat_witness_certificate_sound certificate371 valid371 MajorityCertificates.Inputs018.envelope_sound371

def certificate372 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope372,(222279/100000),(75705469/500000000),(1833345959200750119597/1000000000000000000),(382739631/200000000),(23/10),(12634713/31250000),0,1,(2565216566953133/1000000000000000000)⟩
theorem valid372 : certificate372.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid372,?_⟩
  decide +kernel
theorem sound372 : certificate372.Sound :=
  rat_witness_certificate_sound certificate372 valid372 MajorityCertificates.Inputs018.envelope_sound372

def certificate373 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope373,(222279/100000),(75705469/500000000),(1833345959200750119597/1000000000000000000),(1104996453/500000000),(23/10),(637085541/500000000),0,(281457166558976251/250000000000000000),(1184121088716761/500000000000000000)⟩
theorem valid373 : certificate373.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid373,?_⟩
  decide +kernel
theorem sound373 : certificate373.Sound :=
  rat_witness_certificate_sound certificate373 valid373 MajorityCertificates.Inputs018.envelope_sound373

def certificate374 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope374,(55413/25000),(75705469/500000000),(424558827794382929447/250000000000000000),(1914183649/1000000000),(23/10),(50620583/125000000),0,1,(688391051145989/250000000000000000)⟩
theorem valid374 : certificate374.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid374,?_⟩
  decide +kernel
theorem sound374 : certificate374.Sound :=
  rat_witness_certificate_sound certificate374 valid374 MajorityCertificates.Inputs018.envelope_sound374

def certificate375 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope375,(55413/25000),(75705469/500000000),(424558827794382929447/250000000000000000),(443526541/200000000),(23/10),(637040791/500000000),0,(1125897167506603831/1000000000000000000),(2564913245129367/1000000000000000000)⟩
theorem valid375 : certificate375.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid375,?_⟩
  decide +kernel
theorem sound375 : certificate375.Sound :=
  rat_witness_certificate_sound certificate375 valid375 MajorityCertificates.Inputs018.envelope_sound375

def certificate376 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope376,(221041/100000),(152055469/1000000000),(315733330643074098997/200000000000000000),(963781317/500000000),(47/20),(406061959/1000000000),0,1,(2998532062456109/1000000000000000000)⟩
theorem valid376 : certificate376.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid376,?_⟩
  decide +kernel
theorem sound376 : certificate376.Sound :=
  rat_witness_certificate_sound certificate376 valid376 MajorityCertificates.Inputs018.envelope_sound376

def certificate377 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope377,(221041/100000),(152055469/1000000000),(315733330643074098997/200000000000000000),(556975767/250000000),(47/20),(1272400003/1000000000),0,(562983917125319621/500000000000000000),(2748847391843093/1000000000000000000)⟩
theorem valid377 : certificate377.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid377,?_⟩
  decide +kernel
theorem sound377 : certificate377.Sound :=
  rat_witness_certificate_sound certificate377 valid377 MajorityCertificates.Inputs018.envelope_sound377

def certificate378 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs018.envelope378,(220443/100000),(152055469/1000000000),(18404084515066028601/12500000000000000),(967562673/500000000),(47/20),(405957209/1000000000),0,1,(3222842874954319/1000000000000000000)⟩
theorem valid378 : certificate378.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid378,?_⟩
  decide +kernel
theorem sound378 : certificate378.Sound :=
  rat_witness_certificate_sound certificate378 valid378 MajorityCertificates.Inputs018.envelope_sound378

def certificate379 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs018.envelope379,(220443/100000),(152055469/1000000000),(18404084515066028601/12500000000000000),(2233903847/1000000000),(47/20),(39784211/31250000),0,(1126040604195062701/1000000000000000000),(741271309535393/250000000000000000)⟩
theorem valid379 : certificate379.Valid := by
  refine ⟨MajorityCertificates.Inputs018.inputs_valid379,?_⟩
  decide +kernel
theorem sound379 : certificate379.Sound :=
  rat_witness_certificate_sound certificate379 valid379 MajorityCertificates.Inputs018.envelope_sound379

def certificates : List RatWitnessCertificate := [certificate360,certificate361,certificate362,certificate363,certificate364,certificate365,certificate366,certificate367,certificate368,certificate369,certificate370,certificate371,certificate372,certificate373,certificate374,certificate375,certificate376,certificate377,certificate378,certificate379]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound360,List.forall_mem_cons.mpr ⟨sound361,List.forall_mem_cons.mpr ⟨sound362,List.forall_mem_cons.mpr ⟨sound363,List.forall_mem_cons.mpr ⟨sound364,List.forall_mem_cons.mpr ⟨sound365,List.forall_mem_cons.mpr ⟨sound366,List.forall_mem_cons.mpr ⟨sound367,List.forall_mem_cons.mpr ⟨sound368,List.forall_mem_cons.mpr ⟨sound369,List.forall_mem_cons.mpr ⟨sound370,List.forall_mem_cons.mpr ⟨sound371,List.forall_mem_cons.mpr ⟨sound372,List.forall_mem_cons.mpr ⟨sound373,List.forall_mem_cons.mpr ⟨sound374,List.forall_mem_cons.mpr ⟨sound375,List.forall_mem_cons.mpr ⟨sound376,List.forall_mem_cons.mpr ⟨sound377,List.forall_mem_cons.mpr ⟨sound378,List.forall_mem_cons.mpr ⟨sound379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch018
