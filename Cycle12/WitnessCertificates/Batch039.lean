import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch039

def certificate780 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope780,(7229/3125),(90851953/500000000),(1118653101311841638807/250000000000000000),(1989861929/1000000000),(189/20),(236946781/500000000),0,1,(1069050649535161/1000000000000000000)⟩
theorem valid780 : certificate780.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid780,?_⟩
  decide +kernel
theorem sound780 : certificate780.Sound :=
  rat_witness_certificate_sound certificate780 valid780 MajorityCertificates.Inputs039.envelope_sound780

def certificate781 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope781,(7229/3125),(90851953/500000000),(1118653101311841638807/250000000000000000),(1880060677/1000000000),(189/20),(177665377/125000000),0,(1125326127979501179/1000000000000000000),(1074418083213153/500000000000000000)⟩
theorem valid781 : certificate781.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid781,?_⟩
  decide +kernel
theorem sound781 : certificate781.Sound :=
  rat_witness_certificate_sound certificate781 valid781 MajorityCertificates.Inputs039.envelope_sound781

def certificate782 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope782,(231281/100000),(57939/320000),(2209443003729267056791/500000000000000000),(1995219629/1000000000),(19/2),(235810693/500000000),0,1,(2705616924123/2500000000000000)⟩
theorem valid782 : certificate782.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid782,?_⟩
  decide +kernel
theorem sound782 : certificate782.Sound :=
  rat_witness_certificate_sound certificate782 valid782 MajorityCertificates.Inputs039.envelope_sound782

def certificate783 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope783,(231281/100000),(57939/320000),(2209443003729267056791/500000000000000000),(941093257/500000000),(19/2),(1420698043/1000000000),0,(562665154415667829/500000000000000000),(2190173730289459/1000000000000000000)⟩
theorem valid783 : certificate783.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid783,?_⟩
  decide +kernel
theorem sound783 : certificate783.Sound :=
  rat_witness_certificate_sound certificate783 valid783 MajorityCertificates.Inputs039.envelope_sound783

def certificate784 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope784,(115567/50000),(179770313/1000000000),(4287112671482551050437/1000000000000000000),(2001670907/1000000000),(191/20),(93501689/200000000),0,1,(69920803186093/62500000000000000)⟩
theorem valid784 : certificate784.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid784,?_⟩
  decide +kernel
theorem sound784 : certificate784.Sound :=
  rat_witness_certificate_sound certificate784 valid784 MajorityCertificates.Inputs039.envelope_sound784

def certificate785 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope785,(115567/50000),(179770313/1000000000),(4287112671482551050437/1000000000000000000),(471197317/250000000),(191/20),(142126849/100000000),0,(562670340267547861/500000000000000000),(2259092881473027/1000000000000000000)⟩
theorem valid785 : certificate785.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid785,?_⟩
  decide +kernel
theorem sound785 : certificate785.Sound :=
  rat_witness_certificate_sound certificate785 valid785 MajorityCertificates.Inputs039.envelope_sound785

def certificate786 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope786,(115523/50000),(177836719/1000000000),(837271614066183087231/200000000000000000),(251801541/125000000),(193/20),(115247157/250000000),0,1,(229339070448639/200000000000000000)⟩
theorem valid786 : certificate786.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid786,?_⟩
  decide +kernel
theorem sound786 : certificate786.Sound :=
  rat_witness_certificate_sound certificate786 valid786 MajorityCertificates.Inputs039.envelope_sound786

def certificate787 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope787,(115523/50000),(177836719/1000000000),(837271614066183087231/200000000000000000),(236231883/125000000),(193/20),(1419956483/1000000000),0,(140668626838488633/125000000000000000),(46555799185807/20000000000000000)⟩
theorem valid787 : certificate787.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid787,?_⟩
  decide +kernel
theorem sound787 : certificate787.Sound :=
  rat_witness_certificate_sound certificate787 valid787 MajorityCertificates.Inputs039.envelope_sound787

def certificate788 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope788,(231059/100000),(22068457/125000000),(4162450143084543733863/1000000000000000000),(1012747413/500000000),(39/4),(456398429/1000000000),0,1,(1147267020442819/1000000000000000000)⟩
theorem valid788 : certificate788.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid788,?_⟩
  decide +kernel
theorem sound788 : certificate788.Sound :=
  rat_witness_certificate_sound certificate788 valid788 MajorityCertificates.Inputs039.envelope_sound788

def certificate789 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope789,(231059/100000),(22068457/125000000),(4162450143084543733863/1000000000000000000),(75783181/40000000),(39/4),(354332327/250000000),0,(562675500040636153/500000000000000000),(1174765068759551/500000000000000000)⟩
theorem valid789 : certificate789.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid789,?_⟩
  decide +kernel
theorem sound789 : certificate789.Sound :=
  rat_witness_certificate_sound certificate789 valid789 MajorityCertificates.Inputs039.envelope_sound789

def certificate790 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope790,(115509/50000),(87629297/500000000),(12860221213138014157/3125000000000000),(1016438111/500000000),(49/5),(28261279/62500000),0,1,(1161949960353931/1000000000000000000)⟩
theorem valid790 : certificate790.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid790,?_⟩
  decide +kernel
theorem sound790 : certificate790.Sound :=
  rat_witness_certificate_sound certificate790 valid790 MajorityCertificates.Inputs039.envelope_sound790

def certificate791 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope791,(115509/50000),(87629297/500000000),(12860221213138014157/3125000000000000),(1897455509/1000000000),(49/5),(1416737649/1000000000),0,(1125355088118779717/1000000000000000000),(477292950494341/200000000000000000)⟩
theorem valid791 : certificate791.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid791,?_⟩
  decide +kernel
theorem sound791 : certificate791.Sound :=
  rat_witness_certificate_sound certificate791 valid791 MajorityCertificates.Inputs039.envelope_sound791

def certificate792 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope792,(230977/100000),(174614063/1000000000),(4069359556869383403307/1000000000000000000),(2038184279/1000000000),(99/10),(449976911/1000000000),0,1,(293722283976133/250000000000000000)⟩
theorem valid792 : certificate792.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid792,?_⟩
  decide +kernel
theorem sound792 : certificate792.Sound :=
  rat_witness_certificate_sound certificate792 valid792 MajorityCertificates.Inputs039.envelope_sound792

def certificate793 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope793,(230977/100000),(174614063/1000000000),(4069359556869383403307/1000000000000000000),(1900935007/1000000000),(99/10),(176877097/125000000),0,(1125359159037728183/1000000000000000000),(2413241820361921/1000000000000000000)⟩
theorem valid793 : certificate793.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid793,?_⟩
  decide +kernel
theorem sound793 : certificate793.Sound :=
  rat_witness_certificate_sound certificate793 valid793 MajorityCertificates.Inputs039.envelope_sound793

def certificate794 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope794,(28867/12500),(6933/40000),(4024676736448661465887/1000000000000000000),(1022469157/500000000),(199/20),(445837411/1000000000),0,1,(5929132921519/5000000000000000)⟩
theorem valid794 : certificate794.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid794,?_⟩
  decide +kernel
theorem sound794 : certificate794.Sound :=
  rat_witness_certificate_sound certificate794 valid794 MajorityCertificates.Inputs039.envelope_sound794

def certificate795 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope795,(28867/12500),(6933/40000),(4024676736448661465887/1000000000000000000),(475940511/250000000),(199/20),(1414499069/1000000000),0,(1125363211987920817/1000000000000000000),(1223966172798099/500000000000000000)⟩
theorem valid795 : certificate795.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid795,?_⟩
  decide +kernel
theorem sound795 : certificate795.Sound :=
  rat_witness_certificate_sound certificate795 valid795 MajorityCertificates.Inputs039.envelope_sound795

def certificate796 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope796,(230897/100000),(86017969/500000000),(995296067866497899553/250000000000000000),(2052304553/1000000000),10,(110417853/250000000),0,1,(1200754754073243/1000000000000000000)⟩
theorem valid796 : certificate796.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid796,?_⟩
  decide +kernel
theorem sound796 : certificate796.Sound :=
  rat_witness_certificate_sound certificate796 valid796 MajorityCertificates.Inputs039.envelope_sound796

def certificate797 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope797,(230897/100000),(86017969/500000000),(995296067866497899553/250000000000000000),(119160619/62500000),10,(1414004069/1000000000),0,(1125367242941078507/1000000000000000000),(496523331325943/200000000000000000)⟩
theorem valid797 : certificate797.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid797,?_⟩
  decide +kernel
theorem sound797 : certificate797.Sound :=
  rat_witness_certificate_sound certificate797 valid797 MajorityCertificates.Inputs039.envelope_sound797

def certificate798 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs039.envelope798,(230859/100000),(54639/320000),(1969422841286305343947/500000000000000000),(2058995213/1000000000),(201/20),(437571679/1000000000),0,1,(1211575020657649/1000000000000000000)⟩
theorem valid798 : certificate798.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid798,?_⟩
  decide +kernel
theorem sound798 : certificate798.Sound :=
  rat_witness_certificate_sound certificate798 valid798 MajorityCertificates.Inputs039.envelope_sound798

def certificate799 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs039.envelope799,(230859/100000),(54639/320000),(1969422841286305343947/500000000000000000),(954688729/500000000),(201/20),(1413522339/1000000000),0,(281342813139326001/250000000000000000),(629390440745259/250000000000000000)⟩
theorem valid799 : certificate799.Valid := by
  refine ⟨MajorityCertificates.Inputs039.inputs_valid799,?_⟩
  decide +kernel
theorem sound799 : certificate799.Sound :=
  rat_witness_certificate_sound certificate799 valid799 MajorityCertificates.Inputs039.envelope_sound799

def certificates : List RatWitnessCertificate := [certificate780,certificate781,certificate782,certificate783,certificate784,certificate785,certificate786,certificate787,certificate788,certificate789,certificate790,certificate791,certificate792,certificate793,certificate794,certificate795,certificate796,certificate797,certificate798,certificate799]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound780,List.forall_mem_cons.mpr ⟨sound781,List.forall_mem_cons.mpr ⟨sound782,List.forall_mem_cons.mpr ⟨sound783,List.forall_mem_cons.mpr ⟨sound784,List.forall_mem_cons.mpr ⟨sound785,List.forall_mem_cons.mpr ⟨sound786,List.forall_mem_cons.mpr ⟨sound787,List.forall_mem_cons.mpr ⟨sound788,List.forall_mem_cons.mpr ⟨sound789,List.forall_mem_cons.mpr ⟨sound790,List.forall_mem_cons.mpr ⟨sound791,List.forall_mem_cons.mpr ⟨sound792,List.forall_mem_cons.mpr ⟨sound793,List.forall_mem_cons.mpr ⟨sound794,List.forall_mem_cons.mpr ⟨sound795,List.forall_mem_cons.mpr ⟨sound796,List.forall_mem_cons.mpr ⟨sound797,List.forall_mem_cons.mpr ⟨sound798,List.forall_mem_cons.mpr ⟨sound799,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch039
