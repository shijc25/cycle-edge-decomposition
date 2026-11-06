import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch006

def certificate120 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope120,(25079/12500),(4567959/31250000),(29410909641871090571/100000000000000000),(129224109/62500000),(19/10),(201280619/500000000),0,1,(1865337385141901/100000000000000000)⟩
theorem valid120 : certificate120.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid120,?_⟩
  decide +kernel
theorem sound120 : certificate120.Sound :=
  rat_witness_certificate_sound certificate120 valid120 MajorityCertificates.Inputs006.envelope_sound120

def certificate121 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope121,(25079/12500),(4567959/31250000),(29410909641871090571/100000000000000000),(490325857/200000000),(19/10),(26457951/20000000),0,(1130742292223240627/1000000000000000000),(3991286971397407/250000000000000000)⟩
theorem valid121 : certificate121.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid121,?_⟩
  decide +kernel
theorem sound121 : certificate121.Sound :=
  rat_witness_certificate_sound certificate121 valid121 MajorityCertificates.Inputs006.envelope_sound121

def certificate122 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope122,(100259/50000),(29202711/200000000),(145823326486021788289/500000000000000000),(518988841/250000000),(19/10),(200613687/500000000),0,1,(3624716262704283/200000000000000000)⟩
theorem valid122 : certificate122.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid122,?_⟩
  decide +kernel
theorem sound122 : certificate122.Sound :=
  rat_witness_certificate_sound certificate122 valid122 MajorityCertificates.Inputs006.envelope_sound122

def certificate123 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope123,(100259/50000),(29202711/200000000),(145823326486021788289/500000000000000000),(306708157/125000000),(19/10),(330832887/250000000),0,(70674642204987673/62500000000000000),(8056932884057883/500000000000000000)⟩
theorem valid123 : certificate123.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid123,?_⟩
  decide +kernel
theorem sound123 : certificate123.Sound :=
  rat_witness_certificate_sound certificate123 valid123 MajorityCertificates.Inputs006.envelope_sound123

def certificate124 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope124,(50057/25000),(29154371/200000000),(17880499278205887779/62500000000000000),(2075267547/1000000000),(39/20),(200535283/500000000),0,1,(18525832173662303/1000000000000000000)⟩
theorem valid124 : certificate124.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid124,?_⟩
  decide +kernel
theorem sound124 : certificate124.Sound :=
  rat_witness_certificate_sound certificate124 valid124 MajorityCertificates.Inputs006.envelope_sound124

def certificate125 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope125,(50057/25000),(29154371/200000000),(17880499278205887779/62500000000000000),(2456274453/1000000000),(39/20),(331633949/250000000),0,(565457953928746117/500000000000000000),(16500281713273063/1000000000000000000)⟩
theorem valid125 : certificate125.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid125,?_⟩
  decide +kernel
theorem sound125 : certificate125.Sound :=
  rat_witness_certificate_sound certificate125 valid125 MajorityCertificates.Inputs006.envelope_sound125

def certificate126 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope126,(200181/100000),(14544959/100000000),(284495464265982334187/1000000000000000000),(2083050907/1000000000),(39/20),(199700009/500000000),0,1,(923854462074151/50000000000000000)⟩
theorem valid126 : certificate126.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid126,?_⟩
  decide +kernel
theorem sound126 : certificate126.Sound :=
  rat_witness_certificate_sound certificate126 valid126 MajorityCertificates.Inputs006.envelope_sound126

def certificate127 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope127,(200181/100000),(14544959/100000000),(284495464265982334187/1000000000000000000),(2459277403/1000000000),(39/20),(663079531/500000000),0,(282737640515171771/250000000000000000),(16614355637323123/1000000000000000000)⟩
theorem valid127 : certificate127.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid127,?_⟩
  decide +kernel
theorem sound127 : certificate127.Sound :=
  rat_witness_certificate_sound certificate127 valid127 MajorityCertificates.Inputs006.envelope_sound127

def certificate128 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope128,(20007/10000),(145288457/1000000000),(35273467744402477229/125000000000000000),(1042311967/500000000),(39/20),(399001323/1000000000),0,1,(2346611273304627/125000000000000000)⟩
theorem valid128 : certificate128.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid128,?_⟩
  decide +kernel
theorem sound128 : certificate128.Sound :=
  rat_witness_certificate_sound certificate128 valid128 MajorityCertificates.Inputs006.envelope_sound128

def certificate129 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope129,(20007/10000),(145288457/1000000000),(35273467744402477229/125000000000000000),(1230675303/500000000),(39/20),(2590982/1953125),0,(282750692399065083/250000000000000000),(16763617652531573/1000000000000000000)⟩
theorem valid129 : certificate129.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid129,?_⟩
  decide +kernel
theorem sound129 : certificate129.Sound :=
  rat_witness_certificate_sound certificate129 valid129 MajorityCertificates.Inputs006.envelope_sound129

def certificate130 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope130,(199961/100000),(72523379/500000000),(279916723399605254071/1000000000000000000),(65220839/31250000),(39/20),(398232313/1000000000),0,1,(189134591845649/10000000000000000)⟩
theorem valid130 : certificate130.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid130,?_⟩
  decide +kernel
theorem sound130 : certificate130.Sound :=
  rat_witness_certificate_sound certificate130 valid130 MajorityCertificates.Inputs006.envelope_sound130

def certificate131 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope131,(199961/100000),(72523379/500000000),(279916723399605254071/1000000000000000000),(2462703757/1000000000),(39/20),(33185513/25000000),0,(1131054987457034177/1000000000000000000),(1694248547148687/100000000000000000)⟩
theorem valid131 : certificate131.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid131,?_⟩
  decide +kernel
theorem sound131 : certificate131.Sound :=
  rat_witness_certificate_sound certificate131 valid131 MajorityCertificates.Inputs006.envelope_sound131

def certificate132 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope132,(49963/25000),(231817/1600000),(277681659324691596311/1000000000000000000),(2088719529/1000000000),(39/20),(24862731/62500000),0,1,(9571374745885839/500000000000000000)⟩
theorem valid132 : certificate132.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid132,?_⟩
  decide +kernel
theorem sound132 : certificate132.Sound :=
  rat_witness_certificate_sound certificate132 valid132 MajorityCertificates.Inputs006.envelope_sound132

def certificate133 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope133,(49963/25000),(231817/1600000),(277681659324691596311/1000000000000000000),(1231960899/500000000),(39/20),(664129209/500000000),0,(282776818206784901/250000000000000000),(2140235680809759/125000000000000000)⟩
theorem valid133 : certificate133.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid133,?_⟩
  decide +kernel
theorem sound133 : certificate133.Sound :=
  rat_witness_certificate_sound certificate133 valid133 MajorityCertificates.Inputs006.envelope_sound133

def certificate134 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope134,(6242/3125),(72321963/500000000),(137740909997000893777/500000000000000000),(2090956707/1000000000),(39/20),(397065591/1000000000),0,1,(9659543499585613/500000000000000000)⟩
theorem valid134 : certificate134.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid134,?_⟩
  decide +kernel
theorem sound134 : certificate134.Sound :=
  rat_witness_certificate_sound certificate134 valid134 MajorityCertificates.Inputs006.envelope_sound134

def certificate135 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope135,(6242/3125),(72321963/500000000),(137740909997000893777/500000000000000000),(1233210943/500000000),(39/20),(53141367/40000000),0,(565579796110781527/500000000000000000),(17261601033569953/1000000000000000000)⟩
theorem valid135 : certificate135.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid135,?_⟩
  decide +kernel
theorem sound135 : certificate135.Sound :=
  rat_witness_certificate_sound certificate135 valid135 MajorityCertificates.Inputs006.envelope_sound135

def certificate136 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope136,(199637/100000),(144482793/1000000000),(273316494600652788773/1000000000000000000),(1046054433/500000000),(39/20),(198351993/500000000),0,1,(9807417994622857/500000000000000000)⟩
theorem valid136 : certificate136.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid136,?_⟩
  decide +kernel
theorem sound136 : certificate136.Sound :=
  rat_witness_certificate_sound certificate136 valid136 MajorityCertificates.Inputs006.envelope_sound136

def certificate137 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope137,(199637/100000),(144482793/1000000000),(273316494600652788773/1000000000000000000),(2467613807/1000000000),(39/20),(66469013/50000000),0,(565605971138258767/500000000000000000),(3488591932857647/200000000000000000)⟩
theorem valid137 : certificate137.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid137,?_⟩
  decide +kernel
theorem sound137 : certificate137.Sound :=
  rat_witness_certificate_sound certificate137 valid137 MajorityCertificates.Inputs006.envelope_sound137

def certificate138 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs006.envelope138,(199531/100000),(72120547/500000000),(33898123835131850651/125000000000000000),(209491231/100000000),(39/20),(12371139/31250000),0,1,(9841111148733423/500000000000000000)⟩
theorem valid138 : certificate138.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid138,?_⟩
  decide +kernel
theorem sound138 : certificate138.Sound :=
  rat_witness_certificate_sound certificate138 valid138 MajorityCertificates.Inputs006.envelope_sound138

def certificate139 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs006.envelope139,(199531/100000),(72120547/500000000),(33898123835131850651/125000000000000000),(2469106331/1000000000),(39/20),(20783549/15625000),0,(565632159811010479/500000000000000000),(8809778830044911/500000000000000000)⟩
theorem valid139 : certificate139.Valid := by
  refine ⟨MajorityCertificates.Inputs006.inputs_valid139,?_⟩
  decide +kernel
theorem sound139 : certificate139.Sound :=
  rat_witness_certificate_sound certificate139 valid139 MajorityCertificates.Inputs006.envelope_sound139

def certificates : List RatWitnessCertificate := [certificate120,certificate121,certificate122,certificate123,certificate124,certificate125,certificate126,certificate127,certificate128,certificate129,certificate130,certificate131,certificate132,certificate133,certificate134,certificate135,certificate136,certificate137,certificate138,certificate139]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound120,List.forall_mem_cons.mpr ⟨sound121,List.forall_mem_cons.mpr ⟨sound122,List.forall_mem_cons.mpr ⟨sound123,List.forall_mem_cons.mpr ⟨sound124,List.forall_mem_cons.mpr ⟨sound125,List.forall_mem_cons.mpr ⟨sound126,List.forall_mem_cons.mpr ⟨sound127,List.forall_mem_cons.mpr ⟨sound128,List.forall_mem_cons.mpr ⟨sound129,List.forall_mem_cons.mpr ⟨sound130,List.forall_mem_cons.mpr ⟨sound131,List.forall_mem_cons.mpr ⟨sound132,List.forall_mem_cons.mpr ⟨sound133,List.forall_mem_cons.mpr ⟨sound134,List.forall_mem_cons.mpr ⟨sound135,List.forall_mem_cons.mpr ⟨sound136,List.forall_mem_cons.mpr ⟨sound137,List.forall_mem_cons.mpr ⟨sound138,List.forall_mem_cons.mpr ⟨sound139,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch006
