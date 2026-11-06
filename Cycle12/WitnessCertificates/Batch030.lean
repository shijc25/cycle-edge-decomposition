import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs030

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch030

def certificate600 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope600,(109913/50000),(36402539/250000000),(535882737577125299899/500000000000000000),(2132150081/1000000000),(19/4),(372439131/1000000000),0,1,(1155308916477511/250000000000000000)⟩
theorem valid600 : certificate600.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid600,?_⟩
  decide +kernel
theorem sound600 : certificate600.Sound :=
  rat_witness_certificate_sound certificate600 valid600 MajorityCertificates.Inputs030.envelope_sound600

def certificate601 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope601,(109913/50000),(36402539/250000000),(535882737577125299899/500000000000000000),(2223434227/1000000000),(19/4),(1306697907/1000000000),0,(140804240134343497/125000000000000000),(5846688030570963/1000000000000000000)⟩
theorem valid601 : certificate601.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid601,?_⟩
  decide +kernel
theorem sound601 : certificate601.Sound :=
  rat_witness_certificate_sound certificate601 valid601 MajorityCertificates.Inputs030.envelope_sound601

def certificate602 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope602,(219827/100000),(72160547/500000000),(266295555735450815613/250000000000000000),(2143204759/1000000000),(24/5),(368176543/1000000000),0,1,(580607772467331/125000000000000000)⟩
theorem valid602 : certificate602.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid602,?_⟩
  decide +kernel
theorem sound602 : certificate602.Sound :=
  rat_witness_certificate_sound certificate602 valid602 MajorityCertificates.Inputs030.envelope_sound602

def certificate603 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope603,(219827/100000),(72160547/500000000),(266295555735450815613/250000000000000000),(2229754101/1000000000),(24/5),(1305110727/1000000000),0,(1126442785549198931/1000000000000000000),(5901616025131987/1000000000000000000)⟩
theorem valid603 : certificate603.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid603,?_⟩
  decide +kernel
theorem sound603 : certificate603.Sound :=
  rat_witness_certificate_sound certificate603 valid603 MajorityCertificates.Inputs030.envelope_sound603

def certificate604 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope604,(219743/100000),(143032031/1000000000),(1052721501435622198073/1000000000000000000),(1071293703/500000000),(97/20),(364764357/1000000000),0,1,(469084398062279/100000000000000000)⟩
theorem valid604 : certificate604.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid604,?_⟩
  decide +kernel
theorem sound604 : certificate604.Sound :=
  rat_witness_certificate_sound certificate604 valid604 MajorityCertificates.Inputs030.envelope_sound604

def certificate605 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope605,(219743/100000),(143032031/1000000000),(1052721501435622198073/1000000000000000000),(1117724201/500000000),(97/20),(65222489/50000000),0,(1126460439189801431/1000000000000000000),(238839527843059/40000000000000000)⟩
theorem valid605 : certificate605.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid605,?_⟩
  decide +kernel
theorem sound605 : certificate605.Sound :=
  rat_witness_certificate_sound certificate605 valid605 MajorityCertificates.Inputs030.envelope_sound605

def certificate606 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope606,(10983/5000),(11391/80000),(260149748406860929449/250000000000000000),(1077628099/500000000),(97/20),(362275473/1000000000),0,1,(2384885914051837/500000000000000000)⟩
theorem valid606 : certificate606.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid606,?_⟩
  decide +kernel
theorem sound606 : certificate606.Sound :=
  rat_witness_certificate_sound certificate606 valid606 MajorityCertificates.Inputs030.envelope_sound606

def certificate607 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope607,(10983/5000),(11391/80000),(260149748406860929449/250000000000000000),(2237177897/1000000000),(97/20),(130500093/100000000),0,(563239014432040067/500000000000000000),(6072106757780307/1000000000000000000)⟩
theorem valid607 : certificate607.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid607,?_⟩
  decide +kernel
theorem sound607 : certificate607.Sound :=
  rat_witness_certificate_sound certificate607 valid607 MajorityCertificates.Inputs030.envelope_sound607

def certificate608 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope608,(219579/100000),(70549219/500000000),(1028803876931968117943/1000000000000000000),(540557319/250000000),(49/10),(358402211/1000000000),0,1,(4837521270437589/1000000000000000000)⟩
theorem valid608 : certificate608.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid608,?_⟩
  decide +kernel
theorem sound608 : certificate608.Sound :=
  rat_witness_certificate_sound certificate608 valid608 MajorityCertificates.Inputs030.envelope_sound608

def certificate609 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope609,(219579/100000),(70549219/500000000),(1028803876931968117943/1000000000000000000),(2242931491/1000000000),(49/10),(130433517/100000000),0,(1126495543858645791/1000000000000000000),(6140671009140629/1000000000000000000)⟩
theorem valid609 : certificate609.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid609,?_⟩
  decide +kernel
theorem sound609 : certificate609.Sound :=
  rat_witness_certificate_sound certificate609 valid609 MajorityCertificates.Inputs030.envelope_sound609

def certificate610 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope610,(439/200),(44739/320000),(1017325787371704994593/1000000000000000000),(2169040219/1000000000),(99/20),(177276353/500000000),0,1,(1225895625067137/250000000000000000)⟩
theorem valid610 : certificate610.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid610,?_⟩
  decide +kernel
theorem sound610 : certificate610.Sound :=
  rat_witness_certificate_sound certificate610 valid610 MajorityCertificates.Inputs030.envelope_sound610

def certificate611 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope611,(439/200),(44739/320000),(1017325787371704994593/1000000000000000000),(449767961/200000000),(99/20),(162951239/125000000),0,(112651298004473193/100000000000000000),(1551639855447429/250000000000000000)⟩
theorem valid611 : certificate611.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid611,?_⟩
  decide +kernel
theorem sound611 : certificate611.Sound :=
  rat_witness_certificate_sound certificate611 valid611 MajorityCertificates.Inputs030.envelope_sound611

def certificate612 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope612,(109711/50000),(34791211/250000000),(1006154796753945849399/1000000000000000000),(2173940921/1000000000),(99/20),(352579299/1000000000),0,1,(4965938582397393/1000000000000000000)⟩
theorem valid612 : certificate612.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid612,?_⟩
  decide +kernel
theorem sound612 : certificate612.Sound :=
  rat_witness_certificate_sound certificate612 valid612 MajorityCertificates.Inputs030.envelope_sound612

def certificate613 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope613,(109711/50000),(34791211/250000000),(1006154796753945849399/1000000000000000000),(9002161/4000000),(99/20),(1304176891/1000000000),0,(225306068058232347/200000000000000000),(3154452329580357/500000000000000000)⟩
theorem valid613 : certificate613.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid613,?_⟩
  decide +kernel
theorem sound613 : certificate613.Sound :=
  rat_witness_certificate_sound certificate613 valid613 MajorityCertificates.Inputs030.envelope_sound613

def certificate614 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope614,(109673/50000),(137875781/1000000000),(995281391174424987399/1000000000000000000),(136116487/62500000),5,(69784429/200000000),0,1,(502618733902497/100000000000000000)⟩
theorem valid614 : certificate614.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid614,?_⟩
  decide +kernel
theorem sound614 : certificate614.Sound :=
  rat_witness_certificate_sound certificate614 valid614 MajorityCertificates.Inputs030.envelope_sound614

def certificate615 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope615,(109673/50000),(137875781/1000000000),(995281391174424987399/1000000000000000000),(451231147/200000000),5,(6518149/5000000),0,(225309522736536033/200000000000000000),(3189931050218787/500000000000000000)⟩
theorem valid615 : certificate615.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid615,?_⟩
  decide +kernel
theorem sound615 : certificate615.Sound :=
  rat_witness_certificate_sound certificate615 valid615 MajorityCertificates.Inputs030.envelope_sound615

def certificate616 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope616,(27409/12500),(136586719/1000000000),(98469645076024067049/100000000000000000),(2187447799/1000000000),5,(172472261/500000000),0,1,(1019944663115687/200000000000000000)⟩
theorem valid616 : certificate616.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid616,?_⟩
  decide +kernel
theorem sound616 : certificate616.Sound :=
  rat_witness_certificate_sound certificate616 valid616 MajorityCertificates.Inputs030.envelope_sound616

def certificate617 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope617,(27409/12500),(136586719/1000000000),(98469645076024067049/100000000000000000),(1129466593/500000000),5,(81515393/62500000),0,(281641199034944561/250000000000000000),(81058557600049/12500000000000000)⟩
theorem valid617 : certificate617.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid617,?_⟩
  decide +kernel
theorem sound617 : certificate617.Sound :=
  rat_witness_certificate_sound certificate617 valid617 MajorityCertificates.Inputs030.envelope_sound617

def certificate618 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs030.envelope618,(219199/100000),(16912207/125000000),(19487824611421009993/20000000000000000),(548608093/250000000),(101/20),(341135569/1000000000),0,1,(5169802094074843/1000000000000000000)⟩
theorem valid618 : certificate618.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid618,?_⟩
  decide +kernel
theorem sound618 : certificate618.Sound :=
  rat_witness_certificate_sound certificate618 valid618 MajorityCertificates.Inputs030.envelope_sound618

def certificate619 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs030.envelope619,(219199/100000),(16912207/125000000),(19487824611421009993/20000000000000000),(1132323071/500000000),(101/20),(130368241/100000000),0,(1126581890826303963/1000000000000000000),(6554328312906531/1000000000000000000)⟩
theorem valid619 : certificate619.Valid := by
  refine ⟨MajorityCertificates.Inputs030.inputs_valid619,?_⟩
  decide +kernel
theorem sound619 : certificate619.Sound :=
  rat_witness_certificate_sound certificate619 valid619 MajorityCertificates.Inputs030.envelope_sound619

def certificates : List RatWitnessCertificate := [certificate600,certificate601,certificate602,certificate603,certificate604,certificate605,certificate606,certificate607,certificate608,certificate609,certificate610,certificate611,certificate612,certificate613,certificate614,certificate615,certificate616,certificate617,certificate618,certificate619]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound600,List.forall_mem_cons.mpr ⟨sound601,List.forall_mem_cons.mpr ⟨sound602,List.forall_mem_cons.mpr ⟨sound603,List.forall_mem_cons.mpr ⟨sound604,List.forall_mem_cons.mpr ⟨sound605,List.forall_mem_cons.mpr ⟨sound606,List.forall_mem_cons.mpr ⟨sound607,List.forall_mem_cons.mpr ⟨sound608,List.forall_mem_cons.mpr ⟨sound609,List.forall_mem_cons.mpr ⟨sound610,List.forall_mem_cons.mpr ⟨sound611,List.forall_mem_cons.mpr ⟨sound612,List.forall_mem_cons.mpr ⟨sound613,List.forall_mem_cons.mpr ⟨sound614,List.forall_mem_cons.mpr ⟨sound615,List.forall_mem_cons.mpr ⟨sound616,List.forall_mem_cons.mpr ⟨sound617,List.forall_mem_cons.mpr ⟨sound618,List.forall_mem_cons.mpr ⟨sound619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch030
