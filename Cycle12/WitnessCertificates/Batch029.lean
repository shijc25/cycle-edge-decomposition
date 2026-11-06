import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch029

def certificate580 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope580,(110589/50000),(49689/320000),(80158553512351214387/62500000000000000),(2068557039/1000000000),(9/2),(402523031/1000000000),0,1,(196455750007741/50000000000000000)⟩
theorem valid580 : certificate580.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid580,?_⟩
  decide +kernel
theorem sound580 : certificate580.Sound :=
  rat_witness_certificate_sound certificate580 valid580 MajorityCertificates.Inputs029.envelope_sound580

def certificate581 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope581,(110589/50000),(49689/320000),(80158553512351214387/62500000000000000),(2182386011/1000000000),(9/2),(653210731/500000000),0,(11261907466007627/10000000000000000),(4738800492912883/1000000000000000000)⟩
theorem valid581 : certificate581.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid581,?_⟩
  decide +kernel
theorem sound581 : certificate581.Sound :=
  rat_witness_certificate_sound certificate581 valid581 MajorityCertificates.Inputs029.envelope_sound581

def certificate582 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope582,(221071/100000),(77316797/500000000),(252775851496208918281/200000000000000000),(414501571/200000000),(9/2),(400486259/1000000000),0,1,(3851668811880989/1000000000000000000)⟩
theorem valid582 : certificate582.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid582,?_⟩
  decide +kernel
theorem sound582 : certificate582.Sound :=
  rat_witness_certificate_sound certificate582 valid582 MajorityCertificates.Inputs029.envelope_sound582

def certificate583 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope583,(221071/100000),(77316797/500000000),(252775851496208918281/200000000000000000),(109215807/50000000),(9/2),(130687757/100000000),0,(563104462309680459/500000000000000000),(2415642440374297/500000000000000000)⟩
theorem valid583 : certificate583.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid583,?_⟩
  decide +kernel
theorem sound583 : certificate583.Sound :=
  rat_witness_certificate_sound certificate583 valid583 MajorityCertificates.Inputs029.envelope_sound583

def certificate584 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope584,(44193/20000),(153989063/1000000000),(249155291543208661207/200000000000000000),(2077157027/1000000000),(91/20),(398436479/1000000000),0,1,(3901245938444373/1000000000000000000)⟩
theorem valid584 : certificate584.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid584,?_⟩
  decide +kernel
theorem sound584 : certificate584.Sound :=
  rat_witness_certificate_sound certificate584 valid584 MajorityCertificates.Inputs029.envelope_sound584

def certificate585 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope585,(44193/20000),(153989063/1000000000),(249155291543208661207/200000000000000000),(1094768513/500000000),(91/20),(163224451/125000000),0,(225245419135671817/200000000000000000),(2446781089198177/500000000000000000)⟩
theorem valid585 : certificate585.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid585,?_⟩
  decide +kernel
theorem sound585 : certificate585.Sound :=
  rat_witness_certificate_sound certificate585 valid585 MajorityCertificates.Inputs029.envelope_sound585

def certificate586 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope586,(110431/50000),(153344531/1000000000),(1228207792147495211257/1000000000000000000),(2066437043/1000000000),(91/20),(198792279/500000000),0,1,(201358379775689/50000000000000000)⟩
theorem valid586 : certificate586.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid586,?_⟩
  decide +kernel
theorem sound586 : certificate586.Sound :=
  rat_witness_certificate_sound certificate586 valid586 MajorityCertificates.Inputs029.envelope_sound586

def certificate587 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope587,(110431/50000),(153344531/1000000000),(1228207792147495211257/1000000000000000000),(1095717161/500000000),(91/20),(130626333/100000000),0,(281561311123062989/250000000000000000),(4987101870237313/1000000000000000000)⟩
theorem valid587 : certificate587.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid587,?_⟩
  decide +kernel
theorem sound587 : certificate587.Sound :=
  rat_witness_certificate_sound certificate587 valid587 MajorityCertificates.Inputs029.envelope_sound587

def certificate588 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope588,(220759/100000),(1527/10000),(30278839599139293129/25000000000000000),(2087323917/1000000000),(23/5),(394289037/1000000000),0,1,(4022125455515617/1000000000000000000)⟩
theorem valid588 : certificate588.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid588,?_⟩
  decide +kernel
theorem sound588 : certificate588.Sound :=
  rat_witness_certificate_sound certificate588 valid588 MajorityCertificates.Inputs029.envelope_sound588

def certificate589 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope589,(220759/100000),(1527/10000),(30278839599139293129/25000000000000000),(219639713/100000000),(23/5),(326334451/250000000),0,(112626338373828441/100000000000000000),(5052285659264379/1000000000000000000)⟩
theorem valid589 : certificate589.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid589,?_⟩
  decide +kernel
theorem sound589 : certificate589.Sound :=
  rat_witness_certificate_sound certificate589 valid589 MajorityCertificates.Inputs029.envelope_sound589

def certificate590 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope590,(220659/100000),(152055469/1000000000),(597297544153012880923/500000000000000000),(1046151263/500000000),(23/5),(392229493/1000000000),0,1,(4083545879261849/1000000000000000000)⟩
theorem valid590 : certificate590.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid590,?_⟩
  decide +kernel
theorem sound590 : certificate590.Sound :=
  rat_witness_certificate_sound certificate590 valid590 MajorityCertificates.Inputs029.envelope_sound590

def certificate591 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope591,(220659/100000),(152055469/1000000000),(597297544153012880923/500000000000000000),(1099132773/500000000),(23/5),(1305819463/1000000000),0,(563140746119645273/500000000000000000),(5146977173470157/1000000000000000000)⟩
theorem valid591 : certificate591.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid591,?_⟩
  decide +kernel
theorem sound591 : certificate591.Sound :=
  rat_witness_certificate_sound certificate591 valid591 MajorityCertificates.Inputs029.envelope_sound591

def certificate592 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope592,(220379/100000),(75383203/500000000),(1156382762462842116309/1000000000000000000),(2098231283/1000000000),(23/5),(388494867/1000000000),0,1,(530285490221711/125000000000000000)⟩
theorem valid592 : certificate592.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid592,?_⟩
  decide +kernel
theorem sound592 : certificate592.Sound :=
  rat_witness_certificate_sound certificate592 valid592 MajorityCertificates.Inputs029.envelope_sound592

def certificate593 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope593,(220379/100000),(75383203/500000000),(1156382762462842116309/1000000000000000000),(440273241/200000000),(23/5),(4086443/3125000),0,(225265112220456239/200000000000000000),(5351272468260523/1000000000000000000)⟩
theorem valid593 : certificate593.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid593,?_⟩
  decide +kernel
theorem sound593 : certificate593.Sound :=
  rat_witness_certificate_sound certificate593 valid593 MajorityCertificates.Inputs029.envelope_sound593

def certificate594 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope594,(220367/100000),(4671167/31250000),(573859666037521547669/500000000000000000),(2115113151/1000000000),(93/20),(383778847/1000000000),0,1,(4419418883029493/1000000000000000000)⟩
theorem valid594 : certificate594.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid594,?_⟩
  decide +kernel
theorem sound594 : certificate594.Sound :=
  rat_witness_certificate_sound certificate594 valid594 MajorityCertificates.Inputs029.envelope_sound594

def certificate595 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope595,(220367/100000),(4671167/31250000),(573859666037521547669/500000000000000000),(2207800931/1000000000),(93/20),(1305970213/1000000000),0,(1126335648984345409/1000000000000000000),(5406076440314317/1000000000000000000)⟩
theorem valid595 : certificate595.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid595,?_⟩
  decide +kernel
theorem sound595 : certificate595.Sound :=
  rat_witness_certificate_sound certificate595 valid595 MajorityCertificates.Inputs029.envelope_sound595

def certificate596 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope596,(220273/100000),(148832813/1000000000),(1132973115748863439211/1000000000000000000),(2114259779/1000000000),(47/10),(95526973/250000000),0,1,(433027611187279/100000000000000000)⟩
theorem valid596 : certificate596.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid596,?_⟩
  decide +kernel
theorem sound596 : certificate596.Sound :=
  rat_witness_certificate_sound certificate596 valid596 MajorityCertificates.Inputs029.envelope_sound596

def certificate597 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope597,(220273/100000),(148832813/1000000000),(1132973115748863439211/1000000000000000000),(2212622121/1000000000),(47/10),(652573259/500000000),0,(1126353627333544413/1000000000000000000),(2736380559074773/500000000000000000)⟩
theorem valid597 : certificate597.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid597,?_⟩
  decide +kernel
theorem sound597 : certificate597.Sound :=
  rat_witness_certificate_sound certificate597 valid597 MajorityCertificates.Inputs029.envelope_sound597

def certificate598 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs029.envelope598,(220003/100000),(23607/160000),(1098394204114735108467/1000000000000000000),(2120332869/1000000000),(47/10),(5912361/15625000),0,1,(2246931109441537/500000000000000000)⟩
theorem valid598 : certificate598.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid598,?_⟩
  decide +kernel
theorem sound598 : certificate598.Sound :=
  rat_witness_certificate_sound certificate598 valid598 MajorityCertificates.Inputs029.envelope_sound598

def certificate599 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs029.envelope599,(220003/100000),(23607/160000),(1098394204114735108467/1000000000000000000),(1107925947/500000000),(47/10),(65346781/50000000),0,(281599499426508171/250000000000000000),(567917166004207/100000000000000000)⟩
theorem valid599 : certificate599.Valid := by
  refine ⟨MajorityCertificates.Inputs029.inputs_valid599,?_⟩
  decide +kernel
theorem sound599 : certificate599.Sound :=
  rat_witness_certificate_sound certificate599 valid599 MajorityCertificates.Inputs029.envelope_sound599

def certificates : List RatWitnessCertificate := [certificate580,certificate581,certificate582,certificate583,certificate584,certificate585,certificate586,certificate587,certificate588,certificate589,certificate590,certificate591,certificate592,certificate593,certificate594,certificate595,certificate596,certificate597,certificate598,certificate599]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound580,List.forall_mem_cons.mpr ⟨sound581,List.forall_mem_cons.mpr ⟨sound582,List.forall_mem_cons.mpr ⟨sound583,List.forall_mem_cons.mpr ⟨sound584,List.forall_mem_cons.mpr ⟨sound585,List.forall_mem_cons.mpr ⟨sound586,List.forall_mem_cons.mpr ⟨sound587,List.forall_mem_cons.mpr ⟨sound588,List.forall_mem_cons.mpr ⟨sound589,List.forall_mem_cons.mpr ⟨sound590,List.forall_mem_cons.mpr ⟨sound591,List.forall_mem_cons.mpr ⟨sound592,List.forall_mem_cons.mpr ⟨sound593,List.forall_mem_cons.mpr ⟨sound594,List.forall_mem_cons.mpr ⟨sound595,List.forall_mem_cons.mpr ⟨sound596,List.forall_mem_cons.mpr ⟨sound597,List.forall_mem_cons.mpr ⟨sound598,List.forall_mem_cons.mpr ⟨sound599,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch029
