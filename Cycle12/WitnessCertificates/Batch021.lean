import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch021

def certificate420 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope420,(42159/20000),(36402539/250000000),(551038808552737177489/1000000000000000000),(1045177947/500000000),(11/4),(96208493/250000000),0,1,(9204522776505381/1000000000000000000)⟩
theorem valid420 : certificate420.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid420,?_⟩
  decide +kernel
theorem sound420 : certificate420.Sound :=
  rat_witness_certificate_sound certificate420 valid420 MajorityCertificates.Inputs021.envelope_sound420

def certificate421 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope421,(42159/20000),(36402539/250000000),(551038808552737177489/1000000000000000000),(2373597167/1000000000),(11/4),(257353161/200000000),0,(563955708539512789/500000000000000000),(1742641969003349/200000000000000000)⟩
theorem valid421 : certificate421.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid421,?_⟩
  decide +kernel
theorem sound421 : certificate421.Sound :=
  rat_witness_certificate_sound certificate421 valid421 MajorityCertificates.Inputs021.envelope_sound421

def certificate422 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope422,(10523/5000),(72160547/500000000),(266972989700765776997/500000000000000000),(419921769/200000000),(14/5),(95211963/250000000),0,1,(9487181862614769/1000000000000000000)⟩
theorem valid422 : certificate422.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid422,?_⟩
  decide +kernel
theorem sound422 : certificate422.Sound :=
  rat_witness_certificate_sound certificate422 valid422 MajorityCertificates.Inputs021.envelope_sound422

def certificate423 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope423,(10523/5000),(72160547/500000000),(266972989700765776997/500000000000000000),(2383211319/1000000000),(14/5),(643578437/500000000),0,(1128009604596215341/1000000000000000000),(9006669916131303/1000000000000000000)⟩
theorem valid423 : certificate423.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid423,?_⟩
  decide +kernel
theorem sound423 : certificate423.Sound :=
  rat_witness_certificate_sound certificate423 valid423 MajorityCertificates.Inputs021.envelope_sound423

def certificate424 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope424,(42027/20000),(143676563/1000000000),(828619419953648943/1600000000000000),(526955533/250000000),(14/5),(378768571/1000000000),0,1,(9783089665309481/1000000000000000000)⟩
theorem valid424 : certificate424.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid424,?_⟩
  decide +kernel
theorem sound424 : certificate424.Sound :=
  rat_witness_certificate_sound certificate424 valid424 MajorityCertificates.Inputs021.envelope_sound424

def certificate425 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope425,(42027/20000),(143676563/1000000000),(828619419953648943/1600000000000000),(298471697/125000000),(14/5),(644362751/500000000),0,(3525337304344471/3125000000000000),(585264862804759/62500000000000000)⟩
theorem valid425 : certificate425.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid425,?_⟩
  decide +kernel
theorem sound425 : certificate425.Sound :=
  rat_witness_certificate_sound certificate425 valid425 MajorityCertificates.Inputs021.envelope_sound425

def certificate426 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope426,(209821/100000),(11391/80000),(100556738944896641207/200000000000000000),(2118680107/1000000000),(57/20),(23421403/62500000),0,1,(517657277575271/50000000000000000)⟩
theorem valid426 : certificate426.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid426,?_⟩
  decide +kernel
theorem sound426 : certificate426.Sound :=
  rat_witness_certificate_sound certificate426 valid426 MajorityCertificates.Inputs021.envelope_sound426

def certificate427 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope427,(209821/100000),(11391/80000),(100556738944896641207/200000000000000000),(3835103/1600000),(57/20),(1289343707/1000000000),0,(1128206307004547189/1000000000000000000),(4835040733720163/500000000000000000)⟩
theorem valid427 : certificate427.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid427,?_⟩
  decide +kernel
theorem sound427 : certificate427.Sound :=
  rat_witness_certificate_sound certificate427 valid427 MajorityCertificates.Inputs021.envelope_sound427

def certificate428 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope428,(209517/100000),(70549219/500000000),(244282304990708490629/500000000000000000),(33252221/15625000),(57/20),(92706431/250000000),0,1,(544385342372263/50000000000000000)⟩
theorem valid428 : certificate428.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid428,?_⟩
  decide +kernel
theorem sound428 : certificate428.Sound :=
  rat_witness_certificate_sound certificate428 valid428 MajorityCertificates.Inputs021.envelope_sound428

def certificate429 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope429,(209517/100000),(70549219/500000000),(244282304990708490629/500000000000000000),(480479579/200000000),(57/20),(1290996639/1000000000),0,(1128304634370673983/1000000000000000000),(5020085104204799/500000000000000000)⟩
theorem valid429 : certificate429.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid429,?_⟩
  decide +kernel
theorem sound429 : certificate429.Sound :=
  rat_witness_certificate_sound certificate429 valid429 MajorityCertificates.Inputs021.envelope_sound429

def certificate430 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope430,(209223/100000),(34791211/250000000),(237582768369219431269/500000000000000000),(4180028/1953125),(29/10),(364776969/1000000000),0,1,(679718358087351/62500000000000000)⟩
theorem valid430 : certificate430.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid430,?_⟩
  decide +kernel
theorem sound430 : certificate430.Sound :=
  rat_witness_certificate_sound certificate430 valid430 MajorityCertificates.Inputs021.envelope_sound430

def certificate431 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope431,(209223/100000),(34791211/250000000),(237582768369219431269/500000000000000000),(1206505361/500000000),(29/10),(1291528673/1000000000),0,(1128402825911467729/1000000000000000000),(517169692074823/50000000000000000)⟩
theorem valid431 : certificate431.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid431,?_⟩
  decide +kernel
theorem sound431 : certificate431.Sound :=
  rat_witness_certificate_sound certificate431 valid431 MajorityCertificates.Inputs021.envelope_sound431

def certificate432 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope432,(10447/5000),(137875781/1000000000),(462528081660201628653/1000000000000000000),(2150166527/1000000000),(29/10),(11274141/31250000),0,1,(11137948627442567/1000000000000000000)⟩
theorem valid432 : certificate432.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid432,?_⟩
  decide +kernel
theorem sound432 : certificate432.Sound :=
  rat_witness_certificate_sound certificate432 valid432 MajorityCertificates.Inputs021.envelope_sound432

def certificate433 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope433,(10447/5000),(137875781/1000000000),(462528081660201628653/1000000000000000000),(1209180393/500000000),(29/10),(1293215419/1000000000),0,(1128500771152518099/1000000000000000000),(107231026545569/10000000000000000)⟩
theorem valid433 : certificate433.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid433,?_⟩
  decide +kernel
theorem sound433 : certificate433.Sound :=
  rat_witness_certificate_sound certificate433 valid433 MajorityCertificates.Inputs021.envelope_sound433

def certificate434 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope434,(104333/50000),(136586719/1000000000),(450599157594054054609/1000000000000000000),(1078088377/500000000),(59/20),(44635727/125000000),0,1,(11465544587861279/1000000000000000000)⟩
theorem valid434 : certificate434.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid434,?_⟩
  decide +kernel
theorem sound434 : certificate434.Sound :=
  rat_witness_certificate_sound certificate434 valid434 MajorityCertificates.Inputs021.envelope_sound434

def certificate435 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope435,(104333/50000),(136586719/1000000000),(450599157594054054609/1000000000000000000),(37929533/15625000),(59/20),(1293915283/1000000000),0,(282149602372991227/250000000000000000),(2207189647778413/200000000000000000)⟩
theorem valid435 : certificate435.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid435,?_⟩
  decide +kernel
theorem sound435 : certificate435.Sound :=
  rat_witness_certificate_sound certificate435 valid435 MajorityCertificates.Inputs021.envelope_sound435

def certificate436 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope436,(104201/50000),(43089/320000),(27458151097991125517/62500000000000000),(271580879/125000000),(59/20),(350879669/1000000000),0,1,(5915825525788253/500000000000000000)⟩
theorem valid436 : certificate436.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid436,?_⟩
  decide +kernel
theorem sound436 : certificate436.Sound :=
  rat_witness_certificate_sound certificate436 valid436 MajorityCertificates.Inputs021.envelope_sound436

def certificate437 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope437,(104201/50000),(43089/320000),(27458151097991125517/62500000000000000),(608465569/250000000),(59/20),(1295683789/1000000000),0,(1128695630988592563/1000000000000000000),(457142912121679/40000000000000000)⟩
theorem valid437 : certificate437.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid437,?_⟩
  decide +kernel
theorem sound437 : certificate437.Sound :=
  rat_witness_certificate_sound certificate437 valid437 MajorityCertificates.Inputs021.envelope_sound437

def certificate438 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs021.envelope438,(208393/100000),(133364063/1000000000),(436437688724035953827/1000000000000000000),(2184070539/1000000000),3,(86639327/250000000),0,1,(5953163392491853/500000000000000000)⟩
theorem valid438 : certificate438.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid438,?_⟩
  decide +kernel
theorem sound438 : certificate438.Sound :=
  rat_witness_certificate_sound certificate438 valid438 MajorityCertificates.Inputs021.envelope_sound438

def certificate439 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs021.envelope439,(208393/100000),(133364063/1000000000),(436437688724035953827/1000000000000000000),(48847579/20000000),3,(647200437/500000000),0,(225744069970383149/200000000000000000),(11511169512991139/1000000000000000000)⟩
theorem valid439 : certificate439.Valid := by
  refine ⟨MajorityCertificates.Inputs021.inputs_valid439,?_⟩
  decide +kernel
theorem sound439 : certificate439.Sound :=
  rat_witness_certificate_sound certificate439 valid439 MajorityCertificates.Inputs021.envelope_sound439

def certificates : List RatWitnessCertificate := [certificate420,certificate421,certificate422,certificate423,certificate424,certificate425,certificate426,certificate427,certificate428,certificate429,certificate430,certificate431,certificate432,certificate433,certificate434,certificate435,certificate436,certificate437,certificate438,certificate439]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound420,List.forall_mem_cons.mpr ⟨sound421,List.forall_mem_cons.mpr ⟨sound422,List.forall_mem_cons.mpr ⟨sound423,List.forall_mem_cons.mpr ⟨sound424,List.forall_mem_cons.mpr ⟨sound425,List.forall_mem_cons.mpr ⟨sound426,List.forall_mem_cons.mpr ⟨sound427,List.forall_mem_cons.mpr ⟨sound428,List.forall_mem_cons.mpr ⟨sound429,List.forall_mem_cons.mpr ⟨sound430,List.forall_mem_cons.mpr ⟨sound431,List.forall_mem_cons.mpr ⟨sound432,List.forall_mem_cons.mpr ⟨sound433,List.forall_mem_cons.mpr ⟨sound434,List.forall_mem_cons.mpr ⟨sound435,List.forall_mem_cons.mpr ⟨sound436,List.forall_mem_cons.mpr ⟨sound437,List.forall_mem_cons.mpr ⟨sound438,List.forall_mem_cons.mpr ⟨sound439,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch021
