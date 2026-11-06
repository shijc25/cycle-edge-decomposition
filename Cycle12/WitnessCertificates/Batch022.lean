import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch022

def certificate440 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope440,(52067/25000),(132719531/1000000000),(26948029335976110447/62500000000000000),(2183616861/1000000000),3,(172481843/500000000),0,1,(3017605471208453/250000000000000000)⟩
theorem valid440 : certificate440.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid440,?_⟩
  decide +kernel
theorem sound440 : certificate440.Sound :=
  rat_witness_certificate_sound certificate440 valid440 MajorityCertificates.Inputs022.envelope_sound440

def certificate441 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope441,(52067/25000),(132719531/1000000000),(26948029335976110447/62500000000000000),(489055249/200000000),3,(25902619/20000000),0,(1128768199946152099/1000000000000000000),(1462585984046059/125000000000000000)⟩
theorem valid441 : certificate441.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid441,?_⟩
  decide +kernel
theorem sound441 : certificate441.Sound :=
  rat_witness_certificate_sound certificate441 valid441 MajorityCertificates.Inputs022.envelope_sound441

def certificate442 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope442,(41581/20000),(131430469/1000000000),(418600884141280149851/1000000000000000000),(2194965351/1000000000),(61/20),(85267963/250000000),0,1,(12523546265937113/1000000000000000000)⟩
theorem valid442 : certificate442.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid442,?_⟩
  decide +kernel
theorem sound442 : certificate442.Sound :=
  rat_witness_certificate_sound certificate442 valid442 MajorityCertificates.Inputs022.envelope_sound442

def certificate443 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope443,(41581/20000),(131430469/1000000000),(418600884141280149851/1000000000000000000),(49063869/20000000),(61/20),(1297253843/1000000000),0,(141111053871053881/125000000000000000),(2412938394989539/200000000000000000)⟩
theorem valid443 : certificate443.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid443,?_⟩
  decide +kernel
theorem sound443 : certificate443.Sound :=
  rat_witness_certificate_sound certificate443 valid443 MajorityCertificates.Inputs022.envelope_sound443

def certificate444 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope444,(207671/100000),(41439/320000),(204531460842563318341/500000000000000000),(441292593/200000000),(61/20),(335311201/1000000000),0,1,(12950018349728781/1000000000000000000)⟩
theorem valid444 : certificate444.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid444,?_⟩
  decide +kernel
theorem sound444 : certificate444.Sound :=
  rat_witness_certificate_sound certificate444 valid444 MajorityCertificates.Inputs022.envelope_sound444

def certificate445 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope445,(207671/100000),(41439/320000),(204531460842563318341/500000000000000000),(2459495963/1000000000),(61/20),(649534043/500000000),0,(141122980192133699/125000000000000000),(48714747550933/3906250000000000)⟩
theorem valid445 : certificate445.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid445,?_⟩
  decide +kernel
theorem sound445 : certificate445.Sound :=
  rat_witness_certificate_sound certificate445 valid445 MajorityCertificates.Inputs022.envelope_sound445

def certificate446 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope446,(207447/100000),(127563281/1000000000),(400030080820287442667/1000000000000000000),(1108863523/500000000),(31/10),(164780249/500000000),0,1,(13247534217787941/1000000000000000000)⟩
theorem valid446 : certificate446.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid446,?_⟩
  decide +kernel
theorem sound446 : certificate446.Sound :=
  rat_witness_certificate_sound certificate446 valid446 MajorityCertificates.Inputs022.envelope_sound446

def certificate447 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope447,(207447/100000),(127563281/1000000000),(400030080820287442667/1000000000000000000),(493954947/200000000),(31/10),(1299934357/1000000000),0,(1129078463082766291/1000000000000000000),(6396974536468721/500000000000000000)⟩
theorem valid447 : certificate447.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid447,?_⟩
  decide +kernel
theorem sound447 : certificate447.Sound :=
  rat_witness_certificate_sound certificate447 valid447 MajorityCertificates.Inputs022.envelope_sound447

def certificate448 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope448,(207463/100000),(126274219/1000000000),(398079680679526674123/1000000000000000000),(446134361/200000000),(63/20),(40655463/125000000),0,1,(2662373946507043/200000000000000000)⟩
theorem valid448 : certificate448.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid448,?_⟩
  decide +kernel
theorem sound448 : certificate448.Sound :=
  rat_witness_certificate_sound certificate448 valid448 MajorityCertificates.Inputs022.envelope_sound448

def certificate449 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope449,(207463/100000),(126274219/1000000000),(398079680679526674123/1000000000000000000),(2478184403/1000000000),(63/20),(649376707/500000000),0,(1129098185216664103/1000000000000000000),(12874456576474963/1000000000000000000)⟩
theorem valid449 : certificate449.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid449,?_⟩
  decide +kernel
theorem sound449 : certificate449.Sound :=
  rat_witness_certificate_sound certificate449 valid449 MajorityCertificates.Inputs022.envelope_sound449

def certificate450 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope450,(103679/50000),(31246289/250000000),(393845047766373384873/1000000000000000000),(447556853/200000000),(63/20),(321433701/1000000000),0,1,(13482449675101619/1000000000000000000)⟩
theorem valid450 : certificate450.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid450,?_⟩
  decide +kernel
theorem sound450 : certificate450.Sound :=
  rat_witness_certificate_sound certificate450 valid450 MajorityCertificates.Inputs022.envelope_sound450

def certificate451 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope451,(103679/50000),(31246289/250000000),(393845047766373384873/1000000000000000000),(2482441237/1000000000),(63/20),(324870293/250000000),0,(564572239368411361/500000000000000000),(13067264950856999/1000000000000000000)⟩
theorem valid451 : certificate451.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid451,?_⟩
  decide +kernel
theorem sound451 : certificate451.Sound :=
  rat_witness_certificate_sound certificate451 valid451 MajorityCertificates.Inputs022.envelope_sound451

def certificate452 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope452,(41451/20000),(39789/320000),(12178821694455002887/31250000000000000),(446435453/200000000),(16/5),(1601067/5000000),0,1,(2783143564131401/200000000000000000)⟩
theorem valid452 : certificate452.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid452,?_⟩
  decide +kernel
theorem sound452 : certificate452.Sound :=
  rat_witness_certificate_sound certificate452 valid452 MajorityCertificates.Inputs022.envelope_sound452

def certificate453 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope453,(41451/20000),(39789/320000),(12178821694455002887/31250000000000000),(2488140543/1000000000),(16/5),(649909157/500000000),0,(112919053638480393/100000000000000000),(2641091449217617/200000000000000000)⟩
theorem valid453 : certificate453.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid453,?_⟩
  decide +kernel
theorem sound453 : certificate453.Sound :=
  rat_witness_certificate_sound certificate453 valid453 MajorityCertificates.Inputs022.envelope_sound453

def certificate454 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope454,(41431/20000),(123051563/1000000000),(192854032378345754617/500000000000000000),(1117187281/500000000),(16/5),(158357047/500000000),0,1,(3525152834114483/250000000000000000)⟩
theorem valid454 : certificate454.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid454,?_⟩
  decide +kernel
theorem sound454 : certificate454.Sound :=
  rat_witness_certificate_sound certificate454 valid454 MajorityCertificates.Inputs022.envelope_sound454

def certificate455 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope455,(41431/20000),(123051563/1000000000),(192854032378345754617/500000000000000000),(623082169/250000000),(16/5),(130059409/100000000),0,(14115454083815833/12500000000000000),(536224461106749/40000000000000000)⟩
theorem valid455 : certificate455.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid455,?_⟩
  decide +kernel
theorem sound455 : certificate455.Sound :=
  rat_witness_certificate_sound certificate455 valid455 MajorityCertificates.Inputs022.envelope_sound455

def certificate456 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope456,(207057/100000),(122407031/1000000000),(190899570021150208329/500000000000000000),(2243152401/1000000000),(16/5),(78638633/250000000),0,1,(7130128197654349/500000000000000000)⟩
theorem valid456 : certificate456.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid456,?_⟩
  decide +kernel
theorem sound456 : certificate456.Sound :=
  rat_witness_certificate_sound certificate456 valid456 MajorityCertificates.Inputs022.envelope_sound456

def certificate457 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope457,(207057/100000),(122407031/1000000000),(190899570021150208329/500000000000000000),(623802041/250000000),(16/5),(40666127/31250000),0,(1129281858847044609/1000000000000000000),(13598835910865769/1000000000000000000)⟩
theorem valid457 : certificate457.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid457,?_⟩
  decide +kernel
theorem sound457 : certificate457.Sound :=
  rat_witness_certificate_sound certificate457 valid457 MajorityCertificates.Inputs022.envelope_sound457

def certificate458 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs022.envelope458,(206961/100000),(121117969/1000000000),(94498107574152091661/250000000000000000),(70366049/31250000),(13/4),(31069463/100000000),0,1,(14474409276913873/1000000000000000000)⟩
theorem valid458 : certificate458.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid458,?_⟩
  decide +kernel
theorem sound458 : certificate458.Sound :=
  rat_witness_certificate_sound certificate458 valid458 MajorityCertificates.Inputs022.envelope_sound458

def certificate459 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs022.envelope459,(206961/100000),(121117969/1000000000),(94498107574152091661/250000000000000000),(2502653849/1000000000),(13/4),(650775383/500000000),0,(1129327121963958547/1000000000000000000),(6863486027391837/500000000000000000)⟩
theorem valid459 : certificate459.Valid := by
  refine ⟨MajorityCertificates.Inputs022.inputs_valid459,?_⟩
  decide +kernel
theorem sound459 : certificate459.Sound :=
  rat_witness_certificate_sound certificate459 valid459 MajorityCertificates.Inputs022.envelope_sound459

def certificates : List RatWitnessCertificate := [certificate440,certificate441,certificate442,certificate443,certificate444,certificate445,certificate446,certificate447,certificate448,certificate449,certificate450,certificate451,certificate452,certificate453,certificate454,certificate455,certificate456,certificate457,certificate458,certificate459]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound440,List.forall_mem_cons.mpr ⟨sound441,List.forall_mem_cons.mpr ⟨sound442,List.forall_mem_cons.mpr ⟨sound443,List.forall_mem_cons.mpr ⟨sound444,List.forall_mem_cons.mpr ⟨sound445,List.forall_mem_cons.mpr ⟨sound446,List.forall_mem_cons.mpr ⟨sound447,List.forall_mem_cons.mpr ⟨sound448,List.forall_mem_cons.mpr ⟨sound449,List.forall_mem_cons.mpr ⟨sound450,List.forall_mem_cons.mpr ⟨sound451,List.forall_mem_cons.mpr ⟨sound452,List.forall_mem_cons.mpr ⟨sound453,List.forall_mem_cons.mpr ⟨sound454,List.forall_mem_cons.mpr ⟨sound455,List.forall_mem_cons.mpr ⟨sound456,List.forall_mem_cons.mpr ⟨sound457,List.forall_mem_cons.mpr ⟨sound458,List.forall_mem_cons.mpr ⟨sound459,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch022
