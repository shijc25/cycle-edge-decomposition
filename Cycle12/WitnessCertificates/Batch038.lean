import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs038

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch038

def certificate760 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope760,(14513/6250),(188149219/1000000000),(569274093020212457171/100000000000000000),(953694093/500000000),(173/20),(499530799/1000000000),0,1,(421399128233001/500000000000000000)⟩
theorem valid760 : certificate760.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid760,?_⟩
  decide +kernel
theorem sound760 : certificate760.Sound :=
  rat_witness_certificate_sound certificate760 valid760 MajorityCertificates.Inputs038.envelope_sound760

def certificate761 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope761,(14513/6250),(188149219/1000000000),(569274093020212457171/100000000000000000),(46120871/25000000),(173/20),(1436717913/1000000000),0,(1125255359396774347/1000000000000000000),(322384408215687/200000000000000000)⟩
theorem valid761 : certificate761.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid761,?_⟩
  decide +kernel
theorem sound761 : certificate761.Sound :=
  rat_witness_certificate_sound certificate761 valid761 MajorityCertificates.Inputs038.envelope_sound761

def certificate762 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope762,(46417/20000),(11719043/62500000),(5510612223659443130943/1000000000000000000),(1916323991/1000000000),(35/4),(496857443/1000000000),0,1,(217715623327287/250000000000000000)⟩
theorem valid762 : certificate762.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid762,?_⟩
  decide +kernel
theorem sound762 : certificate762.Sound :=
  rat_witness_certificate_sound certificate762 valid762 MajorityCertificates.Inputs038.envelope_sound762

def certificate763 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope763,(46417/20000),(11719043/62500000),(5510612223659443130943/1000000000000000000),(1849272331/1000000000),(35/4),(143454059/100000000),0,(1125263940535933027/1000000000000000000),(20901893941399/12500000000000000)⟩
theorem valid763 : certificate763.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid763,?_⟩
  decide +kernel
theorem sound763 : certificate763.Sound :=
  rat_witness_certificate_sound certificate763 valid763 MajorityCertificates.Inputs038.envelope_sound763

def certificate764 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope764,(115983/50000),(11719043/62500000),(5339694884310694289539/1000000000000000000),(240026733/125000000),(177/20),(49660093/100000000),0,1,(44745102500929/50000000000000000)⟩
theorem valid764 : certificate764.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid764,?_⟩
  decide +kernel
theorem sound764 : certificate764.Sound :=
  rat_witness_certificate_sound certificate764 valid764 MajorityCertificates.Inputs038.envelope_sound764

def certificate765 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope765,(115983/50000),(11719043/62500000),(5339694884310694289539/1000000000000000000),(92649709/50000000),(177/20),(1432386759/1000000000),0,(14065906628958881/12500000000000000),(1732961402011981/1000000000000000000)⟩
theorem valid765 : certificate765.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid765,?_⟩
  decide +kernel
theorem sound765 : certificate765.Sound :=
  rat_witness_certificate_sound certificate765 valid765 MajorityCertificates.Inputs038.envelope_sound765

def certificate766 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope766,(4637/2000),(46715039/250000000),(5179117747129619376949/1000000000000000000),(965985211/500000000),(89/10),(61708681/125000000),0,1,(92650945856007/100000000000000000)⟩
theorem valid766 : certificate766.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid766,?_⟩
  decide +kernel
theorem sound766 : certificate766.Sound :=
  rat_witness_certificate_sound certificate766 valid766 MajorityCertificates.Inputs038.envelope_sound766

def certificate767 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope767,(4637/2000),(46715039/250000000),(5179117747129619376949/1000000000000000000),(92788859/50000000),(89/10),(143171919/100000000),0,(225056224459100497/200000000000000000),(360011419807081/200000000000000000)⟩
theorem valid767 : certificate767.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid767,?_⟩
  decide +kernel
theorem sound767 : certificate767.Sound :=
  rat_witness_certificate_sound certificate767 valid767 MajorityCertificates.Inputs038.envelope_sound767

def certificate768 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope768,(231737/100000),(59589/320000),(5028094937505649710709/1000000000000000000),(97046467/50000000),9,(491036063/1000000000),0,1,(95476981437393/100000000000000000)⟩
theorem valid768 : certificate768.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid768,?_⟩
  decide +kernel
theorem sound768 : certificate768.Sound :=
  rat_witness_certificate_sound certificate768 valid768 MajorityCertificates.Inputs038.envelope_sound768

def certificate769 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope769,(231737/100000),(59589/320000),(5028094937505649710709/1000000000000000000),(929988261/500000000),9,(1429786423/1000000000),0,(1125289708944201879/1000000000000000000),(465609621423997/250000000000000000)⟩
theorem valid769 : certificate769.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid769,?_⟩
  decide +kernel
theorem sound769 : certificate769.Sound :=
  rat_witness_certificate_sound certificate769 valid769 MajorityCertificates.Inputs038.envelope_sound769

def certificate770 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope770,(57907/25000),(92785547/500000000),(4885916049529217336309/1000000000000000000),(1949732417/1000000000),(91/10),(122108153/250000000),0,1,(122771009892537/125000000000000000)⟩
theorem valid770 : certificate770.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid770,?_⟩
  decide +kernel
theorem sound770 : certificate770.Sound :=
  rat_witness_certificate_sound certificate770 valid770 MajorityCertificates.Inputs038.envelope_sound770

def certificate771 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope771,(57907/25000),(92785547/500000000),(4885916049529217336309/1000000000000000000),(932074181/500000000),(91/10),(1427884601/1000000000),0,(1125298281465702071/1000000000000000000),(962732812443283/500000000000000000)⟩
theorem valid771 : certificate771.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid771,?_⟩
  decide +kernel
theorem sound771 : certificate771.Sound :=
  rat_witness_certificate_sound certificate771 valid771 MajorityCertificates.Inputs038.envelope_sound771

def certificate772 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope772,(115761/50000),(184926563/1000000000),(2375968812101934089673/500000000000000000),(1958744729/1000000000),(46/5),(60728233/125000000),0,1,(1010656769415599/1000000000000000000)⟩
theorem valid772 : certificate772.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid772,?_⟩
  decide +kernel
theorem sound772 : certificate772.Sound :=
  rat_witness_certificate_sound certificate772 valid772 MajorityCertificates.Inputs038.envelope_sound772

def certificate773 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope773,(115761/50000),(184926563/1000000000),(2375968812101934089673/500000000000000000),(467041487/250000000),(46/5),(1426135867/1000000000),0,(562653416793361323/500000000000000000),(497420578846787/250000000000000000)⟩
theorem valid773 : certificate773.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid773,?_⟩
  decide +kernel
theorem sound773 : certificate773.Sound :=
  rat_witness_certificate_sound certificate773 valid773 MajorityCertificates.Inputs038.envelope_sound773

def certificate774 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope774,(11571/5000),(14691/80000),(4625575734360181354019/1000000000000000000),(984730591/500000000),(37/4),(240600439/500000000),0,1,(518669924226239/500000000000000000)⟩
theorem valid774 : certificate774.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid774,?_⟩
  decide +kernel
theorem sound774 : certificate774.Sound :=
  rat_witness_certificate_sound certificate774 valid774 MajorityCertificates.Inputs038.envelope_sound774

def certificate775 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope775,(11571/5000),(14691/80000),(4625575734360181354019/1000000000000000000),(1871305493/1000000000),(37/4),(285156447/200000000),0,(562657678242621123/500000000000000000),(1030149516493893/500000000000000000)⟩
theorem valid775 : certificate775.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid775,?_⟩
  decide +kernel
theorem sound775 : certificate775.Sound :=
  rat_witness_certificate_sound certificate775 valid775 MajorityCertificates.Inputs038.envelope_sound775

def certificate776 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope776,(9257/4000),(182992969/1000000000),(4590923125678254077949/1000000000000000000),(989473091/500000000),(187/20),(95695493/200000000),0,1,(260322057549307/250000000000000000)⟩
theorem valid776 : certificate776.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid776,?_⟩
  decide +kernel
theorem sound776 : certificate776.Sound :=
  rat_witness_certificate_sound certificate776 valid776 MajorityCertificates.Inputs038.envelope_sound776

def certificate777 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope777,(9257/4000),(182992969/1000000000),(4590923125678254077949/1000000000000000000),(937771691/500000000),(187/20),(355711297/250000000),0,(1125317730474598069/1000000000000000000),(416815701925271/200000000000000000)⟩
theorem valid777 : certificate777.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid777,?_⟩
  decide +kernel
theorem sound777 : certificate777.Sound :=
  rat_witness_certificate_sound certificate777 valid777 MajorityCertificates.Inputs038.envelope_sound777

def certificate778 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs038.envelope778,(14461/6250),(91174219/500000000),(2265969628524573106277/500000000000000000),(1984518853/1000000000),(47/5),(476171917/1000000000),0,1,(1055854475436769/1000000000000000000)⟩
theorem valid778 : certificate778.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid778,?_⟩
  decide +kernel
theorem sound778 : certificate778.Sound :=
  rat_witness_certificate_sound certificate778 valid778 MajorityCertificates.Inputs038.envelope_sound778

def certificate779 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs038.envelope779,(14461/6250),(91174219/500000000),(2265969628524573106277/500000000000000000),(1877810687/1000000000),(47/5),(711037783/500000000),0,(1125321934883495849/1000000000000000000),(423340235437081/200000000000000000)⟩
theorem valid779 : certificate779.Valid := by
  refine ⟨MajorityCertificates.Inputs038.inputs_valid779,?_⟩
  decide +kernel
theorem sound779 : certificate779.Sound :=
  rat_witness_certificate_sound certificate779 valid779 MajorityCertificates.Inputs038.envelope_sound779

def certificates : List RatWitnessCertificate := [certificate760,certificate761,certificate762,certificate763,certificate764,certificate765,certificate766,certificate767,certificate768,certificate769,certificate770,certificate771,certificate772,certificate773,certificate774,certificate775,certificate776,certificate777,certificate778,certificate779]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound760,List.forall_mem_cons.mpr ⟨sound761,List.forall_mem_cons.mpr ⟨sound762,List.forall_mem_cons.mpr ⟨sound763,List.forall_mem_cons.mpr ⟨sound764,List.forall_mem_cons.mpr ⟨sound765,List.forall_mem_cons.mpr ⟨sound766,List.forall_mem_cons.mpr ⟨sound767,List.forall_mem_cons.mpr ⟨sound768,List.forall_mem_cons.mpr ⟨sound769,List.forall_mem_cons.mpr ⟨sound770,List.forall_mem_cons.mpr ⟨sound771,List.forall_mem_cons.mpr ⟨sound772,List.forall_mem_cons.mpr ⟨sound773,List.forall_mem_cons.mpr ⟨sound774,List.forall_mem_cons.mpr ⟨sound775,List.forall_mem_cons.mpr ⟨sound776,List.forall_mem_cons.mpr ⟨sound777,List.forall_mem_cons.mpr ⟨sound778,List.forall_mem_cons.mpr ⟨sound779,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch038
