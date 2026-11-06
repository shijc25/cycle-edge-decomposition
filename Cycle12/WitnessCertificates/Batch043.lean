import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs043

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch043

def certificate860 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope860,(47/20),(7/50),(229720465311909498745229/1000000000000000000),(1867732743/1000000000),32,(73034429/200000000),0,1,(1545843803911/125000000000000000)⟩
theorem valid860 : certificate860.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid860,?_⟩
  decide +kernel
theorem sound860 : certificate860.Sound :=
  rat_witness_certificate_sound certificate860 valid860 MajorityCertificates.Inputs043.envelope_sound860

def certificate861 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope861,(47/20),(7/50),(229720465311909498745229/1000000000000000000),(1788049011/1000000000),32,(1535861047/1000000000),0,(112500625184359747/100000000000000000),(33147474641927/1000000000000000000)⟩
theorem valid861 : certificate861.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid861,?_⟩
  decide +kernel
theorem sound861 : certificate861.Sound :=
  rat_witness_certificate_sound certificate861 valid861 MajorityCertificates.Inputs043.envelope_sound861

def certificate862 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope862,(47/20),(27/100),(229720465311909498745229/1000000000000000000),(86950573/50000000),32,(1007/1000),(169973972866041243/500000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid862 : certificate862.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid862,?_⟩
  decide +kernel
theorem sound862 : certificate862.Sound :=
  rat_witness_certificate_sound certificate862 valid862 MajorityCertificates.Inputs043.envelope_sound862

def certificate863 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope863,(47/20),(7/50),(40343640626005903294591/200000000000000000),(232645889/125000000),32,(73166431/200000000),0,1,(26427371218303/1000000000000000000)⟩
theorem valid863 : certificate863.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid863,?_⟩
  decide +kernel
theorem sound863 : certificate863.Sound :=
  rat_witness_certificate_sound certificate863 valid863 MajorityCertificates.Inputs043.envelope_sound863

def certificate864 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope864,(47/20),(7/50),(40343640626005903294591/200000000000000000),(892525283/500000000),32,(153994973/100000000),0,(45000284788831093/40000000000000000),(132320169300023/1000000000000000000)⟩
theorem valid864 : certificate864.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid864,?_⟩
  decide +kernel
theorem sound864 : certificate864.Sound :=
  rat_witness_certificate_sound certificate864 valid864 MajorityCertificates.Inputs043.envelope_sound864

def certificate865 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope865,(47/20),(27/100),(40343640626005903294591/200000000000000000),(174541811/100000000),32,(1007/1000),(339195764892277929/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid865 : certificate865.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid865,?_⟩
  decide +kernel
theorem sound865 : certificate865.Sound :=
  rat_witness_certificate_sound certificate865 valid865 MajorityCertificates.Inputs043.envelope_sound865

def certificate866 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope866,(47/20),(7/50),(89362533641297081802843/500000000000000000),(116419431/62500000),32,(22854809/62500000),0,1,(12992374411273/500000000000000000)⟩
theorem valid866 : certificate866.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid866,?_⟩
  decide +kernel
theorem sound866 : certificate866.Sound :=
  rat_witness_certificate_sound certificate866 valid866 MajorityCertificates.Inputs043.envelope_sound866

def certificate867 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope867,(47/20),(7/50),(89362533641297081802843/500000000000000000),(358013209/200000000),32,(1533622743/1000000000),0,(562504017842078037/500000000000000000),(45707610940211/1000000000000000000)⟩
theorem valid867 : certificate867.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid867,?_⟩
  decide +kernel
theorem sound867 : certificate867.Sound :=
  rat_witness_certificate_sound certificate867 valid867 MajorityCertificates.Inputs043.envelope_sound867

def certificate868 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope868,(47/20),(27/100),(89362533641297081802843/500000000000000000),(27373447/15625000),32,(503500001/500000000),(6768916697356243/20000000000000000),1,(894518082263017/200000000000000000)⟩
theorem valid868 : certificate868.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid868,?_⟩
  decide +kernel
theorem sound868 : certificate868.Sound :=
  rat_witness_certificate_sound certificate868 valid868 MajorityCertificates.Inputs043.envelope_sound868

def certificate869 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope869,(47/20),(7/50),(39901735358418733875897/250000000000000000),(467093351/250000000),32,(365113393/1000000000),0,1,(5843235513389/200000000000000000)⟩
theorem valid869 : certificate869.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid869,?_⟩
  decide +kernel
theorem sound869 : certificate869.Sound :=
  rat_witness_certificate_sound certificate869 valid869 MajorityCertificates.Inputs043.envelope_sound869

def certificate870 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope870,(47/20),(7/50),(39901735358418733875897/250000000000000000),(895528791/500000000),32,(1532539923/1000000000),0,(1125008998224853309/1000000000000000000),(51657684898817/1000000000000000000)⟩
theorem valid870 : certificate870.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid870,?_⟩
  decide +kernel
theorem sound870 : certificate870.Sound :=
  rat_witness_certificate_sound certificate870 valid870 MajorityCertificates.Inputs043.envelope_sound870

def certificate871 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope871,(47/20),(27/100),(39901735358418733875897/250000000000000000),(879205741/500000000),32,(1007/1000),(337703746358031419/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid871 : certificate871.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid871,?_⟩
  decide +kernel
theorem sound871 : certificate871.Sound :=
  rat_witness_certificate_sound certificate871 valid871 MajorityCertificates.Inputs043.envelope_sound871

def certificate872 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope872,(47/20),(7/50),(71767124962822745430191/500000000000000000),(939184761/500000000),32,(364132979/1000000000),0,1,(4920449571903/250000000000000000)⟩
theorem valid872 : certificate872.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid872,?_⟩
  decide +kernel
theorem sound872 : certificate872.Sound :=
  rat_witness_certificate_sound certificate872 valid872 MajorityCertificates.Inputs043.envelope_sound872

def certificate873 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope873,(47/20),(7/50),(71767124962822745430191/500000000000000000),(1668470433/1000000000),32,(1717719277/1000000000),0,(225002001167175607/200000000000000000),(4168420619211/1000000000000000000)⟩
theorem valid873 : certificate873.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid873,?_⟩
  decide +kernel
theorem sound873 : certificate873.Sound :=
  rat_witness_certificate_sound certificate873 valid873 MajorityCertificates.Inputs043.envelope_sound873

def certificate874 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope874,(47/20),(27/100),(71767124962822745430191/500000000000000000),(1764973591/1000000000),32,(1007/1000),(336966928659616793/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid874 : certificate874.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid874,?_⟩
  decide +kernel
theorem sound874 : certificate874.Sound :=
  rat_witness_certificate_sound certificate874 valid874 MajorityCertificates.Inputs043.envelope_sound874

def certificate875 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope875,(47/20),(7/50),(6494436180428026453419/50000000000000000),(939747599/500000000),32,(364028587/1000000000),0,1,(17965086929471/500000000000000000)⟩
theorem valid875 : certificate875.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid875,?_⟩
  decide +kernel
theorem sound875 : certificate875.Sound :=
  rat_witness_certificate_sound certificate875 valid875 MajorityCertificates.Inputs043.envelope_sound875

def certificate876 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope876,(47/20),(7/50),(6494436180428026453419/50000000000000000),(358585387/200000000),32,(1530546977/1000000000),0,(281252764253030311/250000000000000000),(32327234062201/500000000000000000)⟩
theorem valid876 : certificate876.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid876,?_⟩
  decide +kernel
theorem sound876 : certificate876.Sound :=
  rat_witness_certificate_sound certificate876 valid876 MajorityCertificates.Inputs043.envelope_sound876

def certificate877 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs043.envelope877,(47/20),(27/100),(6494436180428026453419/50000000000000000),(1771606983/1000000000),32,(1007/1000),(336233268575043249/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid877 : certificate877.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid877,?_⟩
  decide +kernel
theorem sound877 : certificate877.Sound :=
  rat_witness_certificate_sound certificate877 valid877 MajorityCertificates.Inputs043.envelope_sound877

def certificate878 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs043.envelope878,(47/20),(7/50),(118201867122811528571737/1000000000000000000),(1882525907/1000000000),32,(90935109/250000000),0,1,(1476762143627/31250000000000000)⟩
theorem valid878 : certificate878.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid878,?_⟩
  decide +kernel
theorem sound878 : certificate878.Sound :=
  rat_witness_certificate_sound certificate878 valid878 MajorityCertificates.Inputs043.envelope_sound878

def certificate879 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs043.envelope879,(47/20),(7/50),(118201867122811528571737/1000000000000000000),(1793801539/1000000000),32,(764819797/500000000),0,(562506075125172701/500000000000000000),(35854830013581/500000000000000000)⟩
theorem valid879 : certificate879.Valid := by
  refine ⟨MajorityCertificates.Inputs043.inputs_valid879,?_⟩
  decide +kernel
theorem sound879 : certificate879.Sound :=
  rat_witness_certificate_sound certificate879 valid879 MajorityCertificates.Inputs043.envelope_sound879

def certificates : List RatWitnessCertificate := [certificate860,certificate861,certificate862,certificate863,certificate864,certificate865,certificate866,certificate867,certificate868,certificate869,certificate870,certificate871,certificate872,certificate873,certificate874,certificate875,certificate876,certificate877,certificate878,certificate879]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound860,List.forall_mem_cons.mpr ⟨sound861,List.forall_mem_cons.mpr ⟨sound862,List.forall_mem_cons.mpr ⟨sound863,List.forall_mem_cons.mpr ⟨sound864,List.forall_mem_cons.mpr ⟨sound865,List.forall_mem_cons.mpr ⟨sound866,List.forall_mem_cons.mpr ⟨sound867,List.forall_mem_cons.mpr ⟨sound868,List.forall_mem_cons.mpr ⟨sound869,List.forall_mem_cons.mpr ⟨sound870,List.forall_mem_cons.mpr ⟨sound871,List.forall_mem_cons.mpr ⟨sound872,List.forall_mem_cons.mpr ⟨sound873,List.forall_mem_cons.mpr ⟨sound874,List.forall_mem_cons.mpr ⟨sound875,List.forall_mem_cons.mpr ⟨sound876,List.forall_mem_cons.mpr ⟨sound877,List.forall_mem_cons.mpr ⟨sound878,List.forall_mem_cons.mpr ⟨sound879,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch043
