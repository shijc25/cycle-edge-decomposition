import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch027

def certificate540 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope540,(113343/50000),(80539453/500000000),(2864750281502089248499/1000000000000000000),(238927801/125000000),(19/5),(213512437/500000000),0,1,(204755790035551/125000000000000000)⟩
theorem valid540 : certificate540.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid540,?_⟩
  decide +kernel
theorem sound540 : certificate540.Sound :=
  rat_witness_certificate_sound certificate540 valid540 MajorityCertificates.Inputs027.envelope_sound540

def certificate541 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope541,(113343/50000),(80539453/500000000),(2864750281502089248499/1000000000000000000),(2061845199/1000000000),(19/5),(265340167/200000000),0,(225103979654792833/200000000000000000),(502468286236711/250000000000000000)⟩
theorem valid541 : certificate541.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid541,?_⟩
  decide +kernel
theorem sound541 : certificate541.Sound :=
  rat_witness_certificate_sound certificate541 valid541 MajorityCertificates.Inputs027.envelope_sound541

def certificate542 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope542,(22633/10000),(80861719/500000000),(2707362291713132118157/1000000000000000000),(191657869/100000000),(77/20),(107177823/250000000),0,1,(867612489067847/500000000000000000)⟩
theorem valid542 : certificate542.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid542,?_⟩
  decide +kernel
theorem sound542 : certificate542.Sound :=
  rat_witness_certificate_sound certificate542 valid542 MajorityCertificates.Inputs027.envelope_sound542

def certificate543 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope543,(22633/10000),(80861719/500000000),(2707362291713132118157/1000000000000000000),(2068600857/1000000000),(77/20),(66223887/50000000),0,(281387749708683387/250000000000000000),(531445879390719/250000000000000000)⟩
theorem valid543 : certificate543.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid543,?_⟩
  decide +kernel
theorem sound543 : certificate543.Sound :=
  rat_witness_certificate_sound certificate543 valid543 MajorityCertificates.Inputs027.envelope_sound543

def certificate544 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope544,(112991/50000),(80861719/500000000),(2564153043510182492643/1000000000000000000),(962029261/500000000),(77/20),(214165391/500000000),0,1,(28718047058317/15625000000000000)⟩
theorem valid544 : certificate544.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid544,?_⟩
  decide +kernel
theorem sound544 : certificate544.Sound :=
  rat_witness_certificate_sound certificate544 valid544 MajorityCertificates.Inputs027.envelope_sound544

def certificate545 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope545,(112991/50000),(80861719/500000000),(2564153043510182492643/1000000000000000000),(64769409/31250000),(77/20),(1324434369/1000000000),0,(225116536210797867/200000000000000000),(11295294722529/5000000000000000)⟩
theorem valid545 : certificate545.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid545,?_⟩
  decide +kernel
theorem sound545 : certificate545.Sound :=
  rat_witness_certificate_sound certificate545 valid545 MajorityCertificates.Inputs027.envelope_sound545

def certificate546 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope546,(112821/50000),(162367969/1000000000),(2433461079447895543817/1000000000000000000),(385836087/200000000),(39/10),(43001897/100000000),0,1,(1939030146639717/1000000000000000000)⟩
theorem valid546 : certificate546.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid546,?_⟩
  decide +kernel
theorem sound546 : certificate546.Sound :=
  rat_witness_certificate_sound certificate546 valid546 MajorityCertificates.Inputs027.envelope_sound546

def certificate547 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope547,(112821/50000),(162367969/1000000000),(2433461079447895543817/1000000000000000000),(2079283061/1000000000),(39/10),(1322297371/1000000000),0,(1125614913483430843/1000000000000000000),(1189665438616043/500000000000000000)⟩
theorem valid547 : certificate547.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid547,?_⟩
  decide +kernel
theorem sound547 : certificate547.Sound :=
  rat_witness_certificate_sound certificate547 valid547 MajorityCertificates.Inputs027.envelope_sound547

def certificate548 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope548,(22531/10000),(162367969/1000000000),(1156931639542237074153/500000000000000000),(387250659/200000000),(39/10),(53709669/125000000),0,1,(1020913561117687/500000000000000000)⟩
theorem valid548 : certificate548.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid548,?_⟩
  decide +kernel
theorem sound548 : certificate548.Sound :=
  rat_witness_certificate_sound certificate548 valid548 MajorityCertificates.Inputs027.envelope_sound548

def certificate549 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope549,(22531/10000),(162367969/1000000000),(1156931639542237074153/500000000000000000),(1041598829/500000000),(39/10),(1322296193/1000000000),0,(562823832201694953/500000000000000000),(314807936684959/125000000000000000)⟩
theorem valid549 : certificate549.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid549,?_⟩
  decide +kernel
theorem sound549 : certificate549.Sound :=
  rat_witness_certificate_sound certificate549 valid549 MajorityCertificates.Inputs027.envelope_sound549

def certificate550 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope550,(44997/20000),(162367969/1000000000),(440826974595350230217/200000000000000000),(1943680787/1000000000),(79/20),(429302971/1000000000),0,1,(107559396561899/50000000000000000)⟩
theorem valid550 : certificate550.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid550,?_⟩
  decide +kernel
theorem sound550 : certificate550.Sound :=
  rat_witness_certificate_sound certificate550 valid550 MajorityCertificates.Inputs027.envelope_sound550

def certificate551 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope551,(44997/20000),(162367969/1000000000),(440826974595350230217/200000000000000000),(418121229/200000000),(79/20),(1320284613/1000000000),0,(56284045243069683/50000000000000000),(1321579537701799/500000000000000000)⟩
theorem valid551 : certificate551.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid551,?_⟩
  decide +kernel
theorem sound551 : certificate551.Sound :=
  rat_witness_certificate_sound certificate551 valid551 MajorityCertificates.Inputs027.envelope_sound551

def certificate552 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope552,(224669/100000),(162367969/1000000000),(2103217083560914222659/1000000000000000000),(1950720893/1000000000),4,(107241187/250000000),0,1,(2257696832119587/1000000000000000000)⟩
theorem valid552 : certificate552.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid552,?_⟩
  decide +kernel
theorem sound552 : certificate552.Sound :=
  rat_witness_certificate_sound certificate552 valid552 MajorityCertificates.Inputs027.envelope_sound552

def certificate553 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope553,(224669/100000),(162367969/1000000000),(2103217083560914222659/1000000000000000000),(2097930729/1000000000),4,(1318343903/1000000000),0,(1125714596726411329/1000000000000000000),(346198269471967/125000000000000000)⟩
theorem valid553 : certificate553.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid553,?_⟩
  decide +kernel
theorem sound553 : certificate553.Sound :=
  rat_witness_certificate_sound certificate553 valid553 MajorityCertificates.Inputs027.envelope_sound553

def certificate554 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope554,(224359/100000),(162367969/1000000000),(2010190772826632488059/1000000000000000000),(1957700761/1000000000),4,(428633999/1000000000),0,1,(473150024642369/200000000000000000)⟩
theorem valid554 : certificate554.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid554,?_⟩
  decide +kernel
theorem sound554 : certificate554.Sound :=
  rat_witness_certificate_sound certificate554 valid554 MajorityCertificates.Inputs027.envelope_sound554

def certificate555 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope555,(224359/100000),(162367969/1000000000),(2010190772826632488059/1000000000000000000),(262722587/125000000),4,(659166373/500000000),0,(112574871708471693/100000000000000000),(2897669900417069/1000000000000000000)⟩
theorem valid555 : certificate555.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid555,?_⟩
  decide +kernel
theorem sound555 : certificate555.Sound :=
  rat_witness_certificate_sound certificate555 valid555 MajorityCertificates.Inputs027.envelope_sound555

def certificate556 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope556,(224057/100000),(162367969/1000000000),(1924254854081980321927/1000000000000000000),(982596807/500000000),(81/20),(214127831/500000000),0,1,(62037471769821/25000000000000000)⟩
theorem valid556 : certificate556.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid556,?_⟩
  decide +kernel
theorem sound556 : certificate556.Sound :=
  rat_witness_certificate_sound certificate556 valid556 MajorityCertificates.Inputs027.envelope_sound556

def certificate557 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope557,(224057/100000),(162367969/1000000000),(1924254854081980321927/1000000000000000000),(2108941979/1000000000),(81/20),(1316540341/1000000000),0,(1125783227201195897/1000000000000000000),(761469849235919/250000000000000000)⟩
theorem valid557 : certificate557.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid557,?_⟩
  decide +kernel
theorem sound557 : certificate557.Sound :=
  rat_witness_certificate_sound certificate557 valid557 MajorityCertificates.Inputs027.envelope_sound557

def certificate558 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs027.envelope558,(223763/100000),(162367969/1000000000),(1844708507240218827801/1000000000000000000),(1967435421/1000000000),(41/10),(428368839/1000000000),0,1,(1288528820457829/500000000000000000)⟩
theorem valid558 : certificate558.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid558,?_⟩
  decide +kernel
theorem sound558 : certificate558.Sound :=
  rat_witness_certificate_sound certificate558 valid558 MajorityCertificates.Inputs027.envelope_sound558

def certificate559 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs027.envelope559,(223763/100000),(162367969/1000000000),(1844708507240218827801/1000000000000000000),(529025719/250000000),(41/10),(1314743131/1000000000),0,(1125818094183652897/1000000000000000000),(635425325087003/200000000000000000)⟩
theorem valid559 : certificate559.Valid := by
  refine ⟨MajorityCertificates.Inputs027.inputs_valid559,?_⟩
  decide +kernel
theorem sound559 : certificate559.Sound :=
  rat_witness_certificate_sound certificate559 valid559 MajorityCertificates.Inputs027.envelope_sound559

def certificates : List RatWitnessCertificate := [certificate540,certificate541,certificate542,certificate543,certificate544,certificate545,certificate546,certificate547,certificate548,certificate549,certificate550,certificate551,certificate552,certificate553,certificate554,certificate555,certificate556,certificate557,certificate558,certificate559]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound540,List.forall_mem_cons.mpr ⟨sound541,List.forall_mem_cons.mpr ⟨sound542,List.forall_mem_cons.mpr ⟨sound543,List.forall_mem_cons.mpr ⟨sound544,List.forall_mem_cons.mpr ⟨sound545,List.forall_mem_cons.mpr ⟨sound546,List.forall_mem_cons.mpr ⟨sound547,List.forall_mem_cons.mpr ⟨sound548,List.forall_mem_cons.mpr ⟨sound549,List.forall_mem_cons.mpr ⟨sound550,List.forall_mem_cons.mpr ⟨sound551,List.forall_mem_cons.mpr ⟨sound552,List.forall_mem_cons.mpr ⟨sound553,List.forall_mem_cons.mpr ⟨sound554,List.forall_mem_cons.mpr ⟨sound555,List.forall_mem_cons.mpr ⟨sound556,List.forall_mem_cons.mpr ⟨sound557,List.forall_mem_cons.mpr ⟨sound558,List.forall_mem_cons.mpr ⟨sound559,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch027
