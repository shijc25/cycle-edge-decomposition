import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs036

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch036

def certificate720 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope720,(117717/50000),(86017969/500000000),(7361664530051213017487/500000000000000000),(364347627/200000000),(149/20),(45862267/100000000),0,1,(314991251537871/1000000000000000000)⟩
theorem valid720 : certificate720.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid720,?_⟩
  decide +kernel
theorem sound720 : certificate720.Sound :=
  rat_witness_certificate_sound certificate720 valid720 MajorityCertificates.Inputs036.envelope_sound720

def certificate721 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope721,(117717/50000),(86017969/500000000),(7361664530051213017487/500000000000000000),(1795693421/1000000000),(149/20),(294874427/200000000),0,(1125097370592352501/1000000000000000000),(559688846661289/1000000000000000000)⟩
theorem valid721 : certificate721.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid721,?_⟩
  decide +kernel
theorem sound721 : certificate721.Sound :=
  rat_witness_certificate_sound certificate721 valid721 MajorityCertificates.Inputs036.envelope_sound721

def certificate722 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope722,(58809/25000),(6933/40000),(13773261092007900957361/1000000000000000000),(365416947/200000000),(15/2),(115474659/250000000),0,1,(339250573016779/1000000000000000000)⟩
theorem valid722 : certificate722.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid722,?_⟩
  decide +kernel
theorem sound722 : certificate722.Sound :=
  rat_witness_certificate_sound certificate722 valid722 MajorityCertificates.Inputs036.envelope_sound722

def certificate723 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope723,(58809/25000),(6933/40000),(13773261092007900957361/1000000000000000000),(449462311/250000000),(15/2),(736063489/500000000),0,(1125104175234942191/1000000000000000000),(300697354703197/500000000000000000)⟩
theorem valid723 : certificate723.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid723,?_⟩
  decide +kernel
theorem sound723 : certificate723.Sound :=
  rat_witness_certificate_sound certificate723 valid723 MajorityCertificates.Inputs036.envelope_sound723

def certificate724 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope724,(117521/50000),(174614063/1000000000),(1615106879914194358303/125000000000000000),(1829695879/1000000000),(151/20),(232752177/500000000),0,1,(362246091251111/1000000000000000000)⟩
theorem valid724 : certificate724.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid724,?_⟩
  decide +kernel
theorem sound724 : certificate724.Sound :=
  rat_witness_certificate_sound certificate724 valid724 MajorityCertificates.Inputs036.envelope_sound724

def certificate725 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope725,(117521/50000),(174614063/1000000000),(1615106879914194358303/125000000000000000),(899973829/500000000),(151/20),(734981673/500000000),0,(70319446250404877/62500000000000000),(644543605889797/1000000000000000000)⟩
theorem valid725 : certificate725.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid725,?_⟩
  decide +kernel
theorem sound725 : certificate725.Sound :=
  rat_witness_certificate_sound certificate725 valid725 MajorityCertificates.Inputs036.envelope_sound725

def certificate726 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope726,(58713/25000),(56289/320000),(12153077954679282224127/1000000000000000000),(1832298593/1000000000),(38/5),(469118391/1000000000),0,1,(48225832907147/125000000000000000)⟩
theorem valid726 : certificate726.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid726,?_⟩
  decide +kernel
theorem sound726 : certificate726.Sound :=
  rat_witness_certificate_sound certificate726 valid726 MajorityCertificates.Inputs036.envelope_sound726

def certificate727 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope727,(58713/25000),(56289/320000),(12153077954679282224127/1000000000000000000),(901017969/500000000),(38/5),(366957157/250000000),0,(1125118257511537283/1000000000000000000),(688860653409523/1000000000000000000)⟩
theorem valid727 : certificate727.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid727,?_⟩
  decide +kernel
theorem sound727 : certificate727.Sound :=
  rat_witness_certificate_sound certificate727 valid727 MajorityCertificates.Inputs036.envelope_sound727

def certificate728 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope728,(117333/50000),(44298047/250000000),(11459013770357306654367/1000000000000000000),(1834891279/1000000000),(153/20),(47274093/100000000),0,1,(51239502282337/125000000000000000)⟩
theorem valid728 : certificate728.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid728,?_⟩
  decide +kernel
theorem sound728 : certificate728.Sound :=
  rat_witness_certificate_sound certificate728 valid728 MajorityCertificates.Inputs036.envelope_sound728

def certificate729 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope729,(117333/50000),(44298047/250000000),(11459013770357306654367/1000000000000000000),(112754071/62500000),(153/20),(293154787/200000000),0,(281281380080968231/250000000000000000),(367247004149677/500000000000000000)⟩
theorem valid729 : certificate729.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid729,?_⟩
  decide +kernel
theorem sound729 : certificate729.Sound :=
  rat_witness_certificate_sound certificate729 valid729 MajorityCertificates.Inputs036.envelope_sound729

def certificate730 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope730,(58621/25000),(28557/160000),(10829462736502444557451/1000000000000000000),(91874523/50000000),(77/10),(29773127/62500000),0,1,(86918855257317/200000000000000000)⟩
theorem valid730 : certificate730.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid730,?_⟩
  decide +kernel
theorem sound730 : certificate730.Sound :=
  rat_witness_certificate_sound certificate730 valid730 MajorityCertificates.Inputs036.envelope_sound730

def certificate731 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope731,(58621/25000),(28557/160000),(10829462736502444557451/1000000000000000000),(903050439/500000000),(77/10),(182965971/125000000),0,(1125132920987684677/1000000000000000000),(780955907503663/1000000000000000000)⟩
theorem valid731 : certificate731.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid731,?_⟩
  decide +kernel
theorem sound731 : certificate731.Sound :=
  rat_witness_certificate_sound certificate731 valid731 MajorityCertificates.Inputs036.envelope_sound731

def certificate732 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope732,(117153/50000),(179125781/1000000000),(1282078338356391269001/125000000000000000),(921024799/500000000),(31/4),(238954449/500000000),0,1,(459353225836477/1000000000000000000)⟩
theorem valid732 : certificate732.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid732,?_⟩
  decide +kernel
theorem sound732 : certificate732.Sound :=
  rat_witness_certificate_sound certificate732 valid732 MajorityCertificates.Inputs036.envelope_sound732

def certificate733 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope733,(117153/50000),(179125781/1000000000),(1282078338356391269001/125000000000000000),(452158887/250000000),(31/4),(730974593/500000000),0,(1125140452018960369/1000000000000000000),(415124925570053/500000000000000000)⟩
theorem valid733 : certificate733.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid733,?_⟩
  decide +kernel
theorem sound733 : certificate733.Sound :=
  rat_witness_certificate_sound certificate733 valid733 MajorityCertificates.Inputs036.envelope_sound733

def certificate734 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope734,(58533/25000),(45103711/250000000),(9733859852215415768657/1000000000000000000),(1844710761/1000000000),(39/5),(120385227/250000000),0,1,(485302583876189/1000000000000000000)⟩
theorem valid734 : certificate734.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid734,?_⟩
  decide +kernel
theorem sound734 : certificate734.Sound :=
  rat_witness_certificate_sound certificate734 valid734 MajorityCertificates.Inputs036.envelope_sound734

def certificate735 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope735,(58533/25000),(45103711/250000000),(9733859852215415768657/1000000000000000000),(1810488771/1000000000),(39/5),(1460137053/1000000000),0,(562574052953447327/500000000000000000),(446701332876323/500000000000000000)⟩
theorem valid735 : certificate735.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid735,?_⟩
  decide +kernel
theorem sound735 : certificate735.Sound :=
  rat_witness_certificate_sound certificate735 valid735 MajorityCertificates.Inputs036.envelope_sound735

def certificate736 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope736,(116981/50000),(90851953/500000000),(9255469691434617884019/1000000000000000000),(184569821/100000000),(157/20),(242686907/500000000),0,1,(127401175158899/250000000000000000)⟩
theorem valid736 : certificate736.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid736,?_⟩
  decide +kernel
theorem sound736 : certificate736.Sound :=
  rat_witness_certificate_sound certificate736 valid736 MajorityCertificates.Inputs036.envelope_sound736

def certificate737 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope737,(116981/50000),(90851953/500000000),(9255469691434617884019/1000000000000000000),(906166999/500000000),(157/20),(364574817/250000000),0,(1125155875115392197/1000000000000000000),(185991460354843/200000000000000000)⟩
theorem valid737 : certificate737.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid737,?_⟩
  decide +kernel
theorem sound737 : certificate737.Sound :=
  rat_witness_certificate_sound certificate737 valid737 MajorityCertificates.Inputs036.envelope_sound737

def certificate738 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs036.envelope738,(58449/25000),(91174219/500000000),(8816557147355995766017/1000000000000000000),(1851848287/1000000000),(159/20),(12168399/25000000),0,1,(53737251577351/100000000000000000)⟩
theorem valid738 : certificate738.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid738,?_⟩
  decide +kernel
theorem sound738 : certificate738.Sound :=
  rat_witness_certificate_sound certificate738 valid738 MajorityCertificates.Inputs036.envelope_sound738

def certificate739 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs036.envelope739,(58449/25000),(91174219/500000000),(8816557147355995766017/1000000000000000000),(1816244597/1000000000),(159/20),(1455179123/1000000000),0,(225032750416932501/200000000000000000),(994165515730693/1000000000000000000)⟩
theorem valid739 : certificate739.Valid := by
  refine ⟨MajorityCertificates.Inputs036.inputs_valid739,?_⟩
  decide +kernel
theorem sound739 : certificate739.Sound :=
  rat_witness_certificate_sound certificate739 valid739 MajorityCertificates.Inputs036.envelope_sound739

def certificates : List RatWitnessCertificate := [certificate720,certificate721,certificate722,certificate723,certificate724,certificate725,certificate726,certificate727,certificate728,certificate729,certificate730,certificate731,certificate732,certificate733,certificate734,certificate735,certificate736,certificate737,certificate738,certificate739]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound720,List.forall_mem_cons.mpr ⟨sound721,List.forall_mem_cons.mpr ⟨sound722,List.forall_mem_cons.mpr ⟨sound723,List.forall_mem_cons.mpr ⟨sound724,List.forall_mem_cons.mpr ⟨sound725,List.forall_mem_cons.mpr ⟨sound726,List.forall_mem_cons.mpr ⟨sound727,List.forall_mem_cons.mpr ⟨sound728,List.forall_mem_cons.mpr ⟨sound729,List.forall_mem_cons.mpr ⟨sound730,List.forall_mem_cons.mpr ⟨sound731,List.forall_mem_cons.mpr ⟨sound732,List.forall_mem_cons.mpr ⟨sound733,List.forall_mem_cons.mpr ⟨sound734,List.forall_mem_cons.mpr ⟨sound735,List.forall_mem_cons.mpr ⟨sound736,List.forall_mem_cons.mpr ⟨sound737,List.forall_mem_cons.mpr ⟨sound738,List.forall_mem_cons.mpr ⟨sound739,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch036
